"""
╔══════════════════════════════════════════════════════════════╗
║           TSLA SMART ALERT SYSTEM — Bloomberg-Style         ║
║         Buy/Sell Signals · Institutional Flows · SMS         ║
╚══════════════════════════════════════════════════════════════╝

Features:
  - RSI, MACD, Bollinger Bands, EMA crossovers for signals
  - SEC EDGAR 13F institutional holdings (real data, free)
  - SMS alerts via Twilio
  - Live browser dashboard at http://localhost:5050

Setup:
  1. pip install flask yfinance pandas numpy requests twilio python-dotenv
  2. Rename .env.example → .env
  3. python tsla_monitor.py
"""

import os
import sys
import json
import threading
import time
from datetime import datetime, timedelta

import requests
import yfinance as yf
import pandas as pd
import numpy as np

def _yf_history(symbol, retries=3, **kwargs):
    """yfinance retry wrapper — no session injection (breaks 0.2.x+ curl_cffi)."""
    for attempt in range(retries):
        try:
            df = yf.Ticker(symbol).history(**kwargs)
            if df is not None and not df.empty: return df
            if attempt < retries-1: time.sleep(2+attempt*2)
        except Exception as e:
            print(f"  yfinance {symbol} attempt {attempt+1}/{retries}: {str(e)[:100]}")
            if attempt < retries-1: time.sleep(3+attempt*3)
    return None
from flask import Flask, jsonify, render_template_string, request
from dotenv import load_dotenv
try:
    import pytz
except ImportError:
    pytz = None

load_dotenv()

# ── Schwab API client (optional — falls back to yfinance if not configured) ──
try:
    import schwab_client as sc
    _SCHWAB_OK = sc.is_configured()
    if _SCHWAB_OK:
        print(f"[SCHWAB] Credentials found — Schwab API enabled", flush=True)
    else:
        print("[SCHWAB] No credentials — using yfinance (set SCHWAB_APP_KEY + SCHWAB_APP_SECRET)", flush=True)
except ImportError:
    print("[SCHWAB] schwab_client.py not found — using yfinance", flush=True)
    class sc:
        @staticmethod
        def is_configured(): return False
        @staticmethod
        def get_client(): return None
        @staticmethod
        def get_quote(s): return {}
        @staticmethod
        def get_price_history(s, **kw):
            import pandas as pd; return pd.DataFrame()
        @staticmethod
        def get_option_chain(s, **kw): return {}
        @staticmethod
        def get_positions(): return []
        @staticmethod
        def get_account_summary(): return {}
        @staticmethod
        def get_auth_url(): return None, "schwab_client.py not installed"
        @staticmethod
        def complete_auth_from_url(u): return False, "not installed", ""
    _SCHWAB_OK = False

# ─────────────────────────────────────────────
#  CONFIG
# ─────────────────────────────────────────────
TICKER          = "TSLA"
CHECK_INTERVAL  = 300   # seconds (5 min)

# ── WhatsApp via Green API (free tier — real WhatsApp messages) ──
# HOW TO SET UP (takes ~5 minutes, no activation message needed):
#   1. Go to https://green-api.com and click "Console" → register free
#   2. Click "Create Instance" → choose the FREE tier
#   3. Click "Scan QR Code" and scan with your WhatsApp phone camera
#   4. Copy your idInstance (a number like 1101234567)
#      and apiTokenInstance (a long string) from the instance page
#   5. Set these 3 variables in Railway → Variables:
#      GREEN_INSTANCE  = your idInstance
#      GREEN_TOKEN     = your apiTokenInstance
#      GREEN_PHONE     = your number with country code, e.g. 919547025845
#                        (India = 91 prefix, USA = 1 prefix — no + sign)

GREEN_INSTANCE = os.getenv("GREEN_INSTANCE", "")   # e.g. 1101234567
GREEN_TOKEN    = os.getenv("GREEN_TOKEN",    "")   # long token from Green API
GREEN_PHONE    = os.getenv("GREEN_PHONE",    "")   # e.g. 919547025845
WA_ENABLED     = bool(GREEN_INSTANCE and GREEN_TOKEN and GREEN_PHONE)
ANTHROPIC_KEY  = os.getenv("ANTHROPIC_API_KEY", "")   # Claude API key for Spock

# Minimum minutes between the same type of alert (prevents spam)
WA_THROTTLE_MIN = 60  # Increased to reduce spam

SEC_HEADERS = {"User-Agent": "tsla-alert-system rajmohan.rammohan@gmail.com"}

app = Flask(__name__)

# ─────────────────────────────────────────────
#  GLOBAL STATE
# ─────────────────────────────────────────────
# Alert quality tracking — stores outcomes of past alerts
_alert_outcomes = []   # [{alert_key, signal, price_at_alert, price_after_1h, price_after_1d, profitable}]

state = {
    "price": None,
    "signal": "HOLD",
    "signal_strength": 0,
    "indicators": {},
    "ichimoku": {},
    "hmm": {},
    "institutional_models": {},
    "mm_data":   {},   # Market maker: GEX, Max Pain, options flow
    "uoa_data":  {},   # Unusual options activity — sweeps, whales, flow
    "ml_signal": {"signal":"HOLD","confidence":0,"probability":0.5,"available":False},
    "master_signal": {"action":"HOLD","score":0,"conviction":0,"risk":"MEDIUM",
                      "color":"#00e5ff","reasons":[],"bull_votes":0,"bear_votes":0},
    "dark_pool": {},   # Dark pool levels
    "poc_data":  {},   # Volume Profile: POC, VAH, VAL
    "spy_data":  {},   # SPY/macro market context
    "news_data": {},   # Real-time news sentiment
    "ext_data":  {},   # Pre/post market + overnight activity
    "sizing":    {},   # CTA position sizing recommendation
    "peak_data": {},   # Precision top detection (9 leading signals)
    "entry_data":{},   # Precision entry detection (when+how much to buy)
    "alerts_log": [],
    "institutional": [],
    "last_updated": None,
    "price_history": [],
    "ichimoku_history": [],
    "darthvader": {},  # DarthVader 1.0 institutional intelligence
}

# ── Spock AI cache ──
_spock_cache = {
    "last_analysis":    None,
    "last_trigger":     None,
    "last_ts":          0,
    "last_dv_state":    None,
    "last_risk_mode":   None,
    "last_whale_count": 0,
    "running":          False,
    "quick_read":       None,
    "quick_running":    False,
}
SPOCK_COOLDOWN = 600  # seconds between auto-triggers


# ═══════════════════════════════════════════════════════════════
#  TECHNICAL ANALYSIS
# ═══════════════════════════════════════════════════════════════

def calculate_rsi(prices, period=14):
    delta = prices.diff()
    gain = delta.where(delta > 0, 0).rolling(period).mean()
    loss = -delta.where(delta < 0, 0).rolling(period).mean()
    rs = gain / loss
    return round((100 - (100 / (1 + rs))).iloc[-1], 2)


def calculate_macd(prices):
    ema12 = prices.ewm(span=12, adjust=False).mean()
    ema26 = prices.ewm(span=26, adjust=False).mean()
    macd  = ema12 - ema26
    sig   = macd.ewm(span=9, adjust=False).mean()
    hist  = macd - sig
    return round(macd.iloc[-1], 4), round(sig.iloc[-1], 4), round(hist.iloc[-1], 4)


def calculate_bollinger(prices, period=20):
    sma = prices.rolling(period).mean()
    std = prices.rolling(period).std()
    return round((sma + 2*std).iloc[-1], 2), round(sma.iloc[-1], 2), round((sma - 2*std).iloc[-1], 2)


def calculate_ema(prices, span):
    return round(prices.ewm(span=span, adjust=False).mean().iloc[-1], 2)



# ═══════════════════════════════════════════════════════════════
#  ICHIMOKU CLOUD
# ═══════════════════════════════════════════════════════════════

def calculate_ichimoku(high, low, close):
    """
    Ichimoku Kinko Hyo — full implementation
    Returns current values and history for cloud rendering.
    """
    def mid(h, l, p): return (h.rolling(p).max() + l.rolling(p).min()) / 2

    tenkan   = mid(high, low, 9)    # Conversion Line
    kijun    = mid(high, low, 26)   # Base Line
    span_a   = ((tenkan + kijun) / 2).shift(26)   # Leading Span A
    span_b   = mid(high, low, 52).shift(26)        # Leading Span B
    chikou   = close.shift(-26)                    # Lagging Span

    # Current values
    t_val = round(tenkan.iloc[-1], 2)
    k_val = round(kijun.iloc[-1], 2)
    sa_val = round(span_a.iloc[-1], 2) if not pd.isna(span_a.iloc[-1]) else None
    sb_val = round(span_b.iloc[-1], 2) if not pd.isna(span_b.iloc[-1]) else None
    price_now = round(close.iloc[-1], 2)

    # Cloud signal interpretation
    cloud_signal = "NEUTRAL"
    cloud_details = []

    if sa_val and sb_val:
        cloud_top = max(sa_val, sb_val)
        cloud_bot = min(sa_val, sb_val)
        if price_now > cloud_top:
            cloud_signal = "BULLISH"
            cloud_details.append("Price above cloud ▲")
        elif price_now < cloud_bot:
            cloud_signal = "BEARISH"
            cloud_details.append("Price below cloud ▼")
        else:
            cloud_signal = "NEUTRAL"
            cloud_details.append("Price inside cloud ↔")

        if sa_val > sb_val:
            cloud_details.append("Green cloud (bullish)")
        else:
            cloud_details.append("Red cloud (bearish)")

    if t_val and k_val:
        if t_val > k_val:
            cloud_details.append("TK cross bullish ▲")
        else:
            cloud_details.append("TK cross bearish ▼")

    # Build history for chart (last 90 days)
    history = []
    for i in range(-90, 0):
        try:
            history.append({
                "date":    str(close.index[i].date()),
                "tenkan":  round(tenkan.iloc[i], 2)  if not pd.isna(tenkan.iloc[i])  else None,
                "kijun":   round(kijun.iloc[i], 2)   if not pd.isna(kijun.iloc[i])   else None,
                "span_a":  round(span_a.iloc[i], 2)  if not pd.isna(span_a.iloc[i])  else None,
                "span_b":  round(span_b.iloc[i], 2)  if not pd.isna(span_b.iloc[i])  else None,
                "close":   round(close.iloc[i], 2),
            })
        except Exception:
            continue

    return {
        "tenkan":        t_val,
        "kijun":         k_val,
        "span_a":        sa_val,
        "span_b":        sb_val,
        "cloud_signal":  cloud_signal,
        "cloud_details": cloud_details,
        "history":       history,
    }


# ═══════════════════════════════════════════════════════════════
#  HIDDEN MARKOV MODEL — Market Regime Detection
# ═══════════════════════════════════════════════════════════════

class GaussianHMM:
    """
    3-state Gaussian HMM implemented from scratch with numpy.
    States: 0=BEARISH  1=NEUTRAL  2=BULLISH
    Trained on log-returns using Baum-Welch EM algorithm.
    """
    def __init__(self, n_states=3, n_iter=50):
        self.n_states = n_states
        self.n_iter   = n_iter

    def _gaussian(self, x, mu, sigma):
        sigma = max(sigma, 1e-6)
        return (1.0 / (sigma * np.sqrt(2 * np.pi))) * np.exp(-0.5 * ((x - mu) / sigma) ** 2)

    def fit(self, obs):
        T = len(obs)
        K = self.n_states

        # Init parameters
        self.pi    = np.ones(K) / K
        self.A     = np.full((K, K), 1.0/K)
        sorted_obs = np.sort(obs)
        thirds     = np.array_split(sorted_obs, K)
        self.mu    = np.array([t.mean() for t in thirds])
        self.sigma = np.array([max(t.std(), 1e-4) for t in thirds])

        for _ in range(self.n_iter):
            # Forward pass
            alpha = np.zeros((T, K))
            for k in range(K):
                alpha[0, k] = self.pi[k] * self._gaussian(obs[0], self.mu[k], self.sigma[k])
            alpha[0] /= alpha[0].sum() + 1e-12
            for t in range(1, T):
                for k in range(K):
                    alpha[t, k] = sum(alpha[t-1, j] * self.A[j, k] for j in range(K)) *                                   self._gaussian(obs[t], self.mu[k], self.sigma[k])
                alpha[t] /= alpha[t].sum() + 1e-12

            # Backward pass
            beta = np.zeros((T, K))
            beta[-1] = 1.0
            for t in range(T-2, -1, -1):
                for j in range(K):
                    beta[t, j] = sum(self.A[j, k] * self._gaussian(obs[t+1], self.mu[k], self.sigma[k]) * beta[t+1, k]
                                     for k in range(K))
                beta[t] /= beta[t].sum() + 1e-12

            # Gamma & Xi
            gamma = alpha * beta
            gamma /= gamma.sum(axis=1, keepdims=True) + 1e-12

            # M-step
            self.pi = gamma[0]
            for j in range(K):
                for k in range(K):
                    num = sum(alpha[t, j] * self.A[j, k] * self._gaussian(obs[t+1], self.mu[k], self.sigma[k]) * beta[t+1, k]
                              for t in range(T-1))
                    self.A[j, k] = num + 1e-12
                self.A[j] /= self.A[j].sum()
            for k in range(K):
                g = gamma[:, k]
                self.mu[k]    = (g * obs).sum() / (g.sum() + 1e-12)
                self.sigma[k] = np.sqrt((g * (obs - self.mu[k])**2).sum() / (g.sum() + 1e-12))

        return self

    def predict(self, obs):
        T = len(obs)
        K = self.n_states
        viterbi = np.zeros((T, K))
        backptr = np.zeros((T, K), dtype=int)
        for k in range(K):
            viterbi[0, k] = np.log(self.pi[k] + 1e-12) + np.log(self._gaussian(obs[0], self.mu[k], self.sigma[k]) + 1e-12)
        for t in range(1, T):
            for k in range(K):
                scores = viterbi[t-1] + np.log(self.A[:, k] + 1e-12)
                backptr[t, k] = np.argmax(scores)
                viterbi[t, k] = scores[backptr[t, k]] + np.log(self._gaussian(obs[t], self.mu[k], self.sigma[k]) + 1e-12)
        states = np.zeros(T, dtype=int)
        states[-1] = np.argmax(viterbi[-1])
        for t in range(T-2, -1, -1):
            states[t] = backptr[t+1, states[t+1]]
        return states


def calculate_hmm(closes):
    """
    Fit HMM on log-returns and return current market regime.
    States are auto-labeled by mean return: lowest=BEARISH, highest=BULLISH.
    """
    try:
        returns = np.diff(np.log(closes.values))
        if len(returns) < 30:
            return {"regime": "UNKNOWN", "confidence": 0, "details": "Not enough data"}

        # Normalize
        obs = (returns - returns.mean()) / (returns.std() + 1e-8)

        model = GaussianHMM(n_states=3, n_iter=60)
        model.fit(obs)
        states = model.predict(obs)

        # Label states by mean return
        state_means = {k: returns[states == k].mean() if (states == k).any() else 0 for k in range(3)}
        sorted_states = sorted(state_means, key=state_means.get)
        labels = {sorted_states[0]: "BEARISH", sorted_states[1]: "NEUTRAL", sorted_states[2]: "BULLISH"}
        label_colors = {"BEARISH": "#ff3355", "NEUTRAL": "#ffb300", "BULLISH": "#00ff88"}

        current_state  = states[-1]
        current_regime = labels[current_state]

        # Confidence = probability mass in current state over last 10 days
        recent = states[-10:]
        confidence = int(round((recent == current_state).mean() * 100))

        # Transition probability to next regime
        trans_row = model.A[current_state]
        next_state = np.argmax(trans_row)
        next_regime = labels[next_state]
        next_prob   = round(trans_row[next_state] * 100, 1)

        # State history for chart
        history = []
        for i, (s, r) in enumerate(zip(states[-60:], returns[-60:])):
            history.append({
                "idx":    i,
                "state":  labels[s],
                "return": round(float(r) * 100, 3),
                "color":  label_colors[labels[s]],
            })

        return {
            "regime":      current_regime,
            "confidence":  confidence,
            "next_regime": next_regime,
            "next_prob":   next_prob,
            "state_means": {labels[k]: round(float(v)*100, 4) for k, v in state_means.items()},
            "history":     history,
            "color":       label_colors[current_regime],
        }
    except Exception as e:
        print(f"⚠️ HMM error: {e}")
        return {"regime": "UNKNOWN", "confidence": 0, "details": str(e)}


def generate_signal(indicators, price):
    """
    Multi-factor scoring engine — max raw score ~200 before volume amplification.
    Each factor is weighted by reliability and confluence importance.

    Factor weights:
      RSI            ±30   (momentum overbought/oversold)
      MACD Line      ±25   (trend direction)
      MACD Histogram ±20   (momentum acceleration — KEY addition)
      MACD Divergence±15   (price vs MACD divergence)
      EMA crossover  ±20   (trend structure)
      Bollinger      ±15   (mean reversion)
      Ichimoku Cloud ±25   (trend + support/resistance)
      TK Cross       ±10   (short-term momentum)
      HMM Regime     ±20   (probabilistic market state)
      Volume Spike   ×1.3  (confirmation amplifier)
      Volume Trend   ±10   (sustained buying/selling pressure)
    """
    score = 0
    reasons = []

    # ── RSI ──
    rsi = indicators["rsi"]
    if rsi < 25:
        score += 30; reasons.append(f"RSI extremely oversold ({rsi})")
    elif rsi < 35:
        score += 20; reasons.append(f"RSI oversold ({rsi})")
    elif rsi < 45:
        score += 10
    elif rsi > 75:
        score -= 30; reasons.append(f"RSI extremely overbought ({rsi})")
    elif rsi > 65:
        score -= 20; reasons.append(f"RSI overbought ({rsi})")
    elif rsi > 55:
        score -= 10

    # ── MACD Line Cross ──
    macd     = indicators["macd"]
    macd_sig = indicators["macd_signal"]
    macd_hist= indicators["macd_hist"]
    prev_hist= indicators.get("prev_macd_hist", macd_hist)

    if macd > macd_sig:
        score += 25; reasons.append("MACD bullish crossover ▲")
    else:
        score -= 25; reasons.append("MACD bearish crossover ▼")

    # ── MACD Histogram Momentum (acceleration) ──
    # Histogram expanding in direction = strong momentum
    if macd_hist > 0:
        if macd_hist > prev_hist:
            score += 20; reasons.append("MACD histogram expanding bullish ▲▲")
        else:
            score += 10; reasons.append("MACD histogram positive but contracting")
    else:
        if macd_hist < prev_hist:
            score -= 20; reasons.append("MACD histogram expanding bearish ▼▼")
        else:
            score -= 10; reasons.append("MACD histogram negative but contracting")

    # ── MACD Zero-Line Cross ──
    if macd > 0 and macd_sig > 0:
        score += 10; reasons.append("MACD above zero line (bullish)")
    elif macd < 0 and macd_sig < 0:
        score -= 10; reasons.append("MACD below zero line (bearish)")

    # ── EMA crossover ──
    ema50, ema200 = indicators["ema50"], indicators["ema200"]
    if ema50 > ema200:
        score += 20; reasons.append("Golden cross (EMA50>EMA200) ▲")
    else:
        score -= 20; reasons.append("Death cross (EMA50<EMA200) ▼")

    # ── Bollinger Bands ──
    bb_upper = indicators["bb_upper"]
    bb_lower = indicators["bb_lower"]
    bb_mid   = indicators["bb_mid"]
    bb_width = (bb_upper - bb_lower) / (bb_mid + 1e-9)  # band width = volatility proxy
    if price < bb_lower:
        score += 15; reasons.append("Price below lower Bollinger band (oversold)")
    elif price > bb_upper:
        score -= 15; reasons.append("Price above upper Bollinger band (overbought)")
    # Squeeze: narrow bands → big move coming (direction TBD by other signals)
    if bb_width < 0.08:
        score = int(score * 1.1)  # amplify when squeeze detected

    # ── Ichimoku Cloud ──
    ichi = indicators.get("ichimoku_signal", "NEUTRAL")
    if ichi == "BULLISH":
        score += 25; reasons.append("Price above Ichimoku cloud ☁▲")
    elif ichi == "BEARISH":
        score -= 25; reasons.append("Price below Ichimoku cloud ☁▼")

    tenkan = indicators.get("tenkan")
    kijun  = indicators.get("kijun")
    if tenkan and kijun:
        if tenkan > kijun:
            score += 10; reasons.append("TK bullish cross ▲")
        else:
            score -= 10; reasons.append("TK bearish cross ▼")

    # ── HMM Regime ──
    regime   = indicators.get("hmm_regime", "NEUTRAL")
    hmm_conf = indicators.get("hmm_confidence", 50) / 100
    if regime == "BULLISH":
        pts = int(20 * hmm_conf)
        score += pts; reasons.append(f"HMM: BULLISH regime ({int(hmm_conf*100)}% conf) +{pts}")
    elif regime == "BEARISH":
        pts = int(20 * hmm_conf)
        score -= pts; reasons.append(f"HMM: BEARISH regime ({int(hmm_conf*100)}% conf) -{pts}")

    # ── Volume Spike — confirmation amplifier ──
    vol_ratio = indicators.get("volume_ratio", 1.0)
    vol_trend = indicators.get("volume_trend", 0)  # +1 rising, -1 falling, 0 flat

    if vol_ratio > 2.0:
        # Massive volume spike — strong confirmation, amplify signal
        score = int(score * 1.3)
        reasons.append(f"HUGE volume spike ({vol_ratio}x avg) — signal amplified ×1.3")
    elif vol_ratio > 1.5:
        score = int(score * 1.15)
        reasons.append(f"Volume spike ({vol_ratio}x avg) — signal amplified ×1.15")
    elif vol_ratio < 0.5:
        # Very low volume — weaken signal (false move risk)
        score = int(score * 0.8)
        reasons.append(f"Low volume ({vol_ratio}x avg) — signal weakened ×0.8")

    # ── Volume Trend (rising OBV = buying pressure) ──
    obv_trend = indicators.get("obv_trend", 0)
    if obv_trend > 0:
        score += 10; reasons.append("OBV rising — accumulation pressure ▲")
    elif obv_trend < 0:
        score -= 10; reasons.append("OBV falling — distribution pressure ▼")

    # ════════════════════════════════════════════════════
    # INSTITUTIONAL / WALL STREET MODEL SCORING
    # Each model contributes independently — confluence
    # across models = high-probability signal
    # ════════════════════════════════════════════════════

    # ── VWAP (Goldman / Morgan Stanley execution benchmark) ──
    vwap      = indicators.get("vwap")
    if vwap:
        if price < vwap * 0.99:
            score += 15; reasons.append(f"Price below VWAP (${vwap}) — institutional buy zone ▲")
        elif price > vwap * 1.01:
            score -= 15; reasons.append(f"Price above VWAP (${vwap}) — institutional sell zone ▼")
        else:
            reasons.append(f"Price at VWAP (${vwap}) — neutral execution zone")

    # ── Kalman Filter (Renaissance / Two Sigma trend filter) ──
    kalman_sig = indicators.get("kalman_signal", "NEUTRAL")
    if kalman_sig == "BULLISH":
        score += 20; reasons.append("Kalman Filter: bullish trend + accelerating ▲")
    elif kalman_sig == "BEARISH":
        score -= 20; reasons.append("Kalman Filter: bearish trend + accelerating ▼")

    # ── Z-Score (Citadel / Millennium stat arb) ──
    zscore = indicators.get("zscore", 0)
    if zscore < -2.0:
        score += 20; reasons.append(f"Z-Score={zscore}: statistically oversold — mean reversion BUY ▲")
    elif zscore < -1.0:
        score += 10; reasons.append(f"Z-Score={zscore}: mildly oversold")
    elif zscore > 2.0:
        score -= 20; reasons.append(f"Z-Score={zscore}: statistically overbought — mean reversion SELL ▼")
    elif zscore > 1.0:
        score -= 10; reasons.append(f"Z-Score={zscore}: mildly overbought")

    # ── Monte Carlo (JPMorgan / Goldman risk desk) ──
    mc_prob = indicators.get("mc_prob_up", 50)
    if mc_prob > 62:
        score += 18; reasons.append(f"Monte Carlo: {mc_prob}% probability of upside ▲")
    elif mc_prob > 55:
        score += 10; reasons.append(f"Monte Carlo: {mc_prob}% slight upside edge ▲")
    elif mc_prob < 38:
        score -= 18; reasons.append(f"Monte Carlo: {mc_prob}% probability of downside ▼")
    elif mc_prob < 45:
        score -= 10; reasons.append(f"Monte Carlo: {mc_prob}% slight downside edge ▼")

    # ── Factor Model (AQR / BlackRock Systematic momentum) ──
    factor_sig = indicators.get("factor_signal", "NEUTRAL")
    factor_map = {"STRONG_BUY": 20, "BUY": 12, "NEUTRAL": 0, "SELL": -12, "STRONG_SELL": -20}
    fscore = factor_map.get(factor_sig, 0)
    if fscore != 0:
        score += fscore
        reasons.append(f"AQR Factor Model: {factor_sig} ({'+' if fscore>0 else ''}{fscore})")

    # ── Smart Money Index (institutional flow vs retail) ──
    smi_sig = indicators.get("smi_signal", "NEUTRAL")
    if smi_sig == "ACCUMULATING":
        score += 18; reasons.append("Smart Money Index: institutions ACCUMULATING ▲")
    elif smi_sig == "DISTRIBUTING":
        score -= 18; reasons.append("Smart Money Index: institutions DISTRIBUTING ▼")

    # ════════════════════════════════════════════════════
    # MARKET MAKER SCORING — Options flow, GEX, Max Pain
    # ════════════════════════════════════════════════════

    # ── GEX: tells us if MMs amplify or suppress the move ──
    mm_gex      = indicators.get("mm_gex_total", 0)
    mm_gex_sig  = indicators.get("mm_gex_signal", "NEUTRAL")
    mm_hedging  = indicators.get("mm_hedging", "NEUTRAL")
    mm_max_pain = indicators.get("mm_max_pain")
    mm_pc_ratio = indicators.get("mm_pc_ratio")

    # Negative GEX → dealers chase moves → amplify our existing signal
    if mm_gex < -100:
        score = int(score * 1.20)
        reasons.append(f"⚡ NEGATIVE GEX ({mm_gex:+.0f}M) — dealers amplifying the move ×1.2")
    elif mm_gex > 500:
        # Strong positive GEX → price pinning → dampen signal (range-bound)
        score = int(score * 0.75)
        reasons.append(f"📌 STRONG POSITIVE GEX ({mm_gex:+.0f}M) — dealers pinning price, signal weakened ×0.75")
    elif mm_gex > 100:
        score = int(score * 0.90)
        reasons.append(f"📌 Positive GEX ({mm_gex:+.0f}M) — mild pinning effect")

    # ── Dealer hedging direction adds to score ──
    if "BUYING" in mm_hedging:
        score += 15; reasons.append(f"MM Hedging: dealers BUYING to pull price to max pain ▲")
    elif "SELLING" in mm_hedging:
        score -= 15; reasons.append(f"MM Hedging: dealers SELLING above max pain ▼")
    elif "CHASING" in mm_hedging:
        score = int(score * 1.10)
        reasons.append("MM Hedging: dealers chasing — trend acceleration mode")

    # ── Max Pain gravity: price within 3% of max pain = gravitational pull ──
    if mm_max_pain and price > 0:
        dist_mp = (mm_max_pain - price) / price * 100
        if 0 < dist_mp < 3:
            score += 12; reasons.append(f"Max Pain magnet at ${mm_max_pain} ({dist_mp:+.1f}%) — price getting pulled UP ▲")
        elif -3 < dist_mp < 0:
            score -= 12; reasons.append(f"Max Pain magnet at ${mm_max_pain} ({dist_mp:+.1f}%) — price getting pulled DOWN ▼")

    # ── Put/Call Ratio: extreme readings = contrarian signal ──
    if mm_pc_ratio:
        if mm_pc_ratio > 1.5:
            score += 10; reasons.append(f"P/C Ratio {mm_pc_ratio} — extreme bearishness = contrarian BUY ▲")
        elif mm_pc_ratio > 1.2:
            score += 5
        elif mm_pc_ratio < 0.5:
            score -= 10; reasons.append(f"P/C Ratio {mm_pc_ratio} — extreme complacency = contrarian SELL ▼")
        elif mm_pc_ratio < 0.7:
            score -= 5

    # ── Call Wall above = ceiling, Put Wall below = floor ──
    call_walls = indicators.get("mm_call_walls", [])
    put_walls  = indicators.get("mm_put_walls", [])
    if call_walls and price > 0:
        nearest_call_wall = call_walls[0].get("strike", 0) if call_walls else 0
        if nearest_call_wall and (nearest_call_wall - price) / price < 0.015:
            score -= 12; reasons.append(f"Call Wall at ${nearest_call_wall} — heavy resistance directly above ▼")
    if put_walls and price > 0:
        nearest_put_wall = put_walls[0].get("strike", 0) if put_walls else 0
        if nearest_put_wall and (price - nearest_put_wall) / price < 0.015:
            score += 12; reasons.append(f"Put Wall at ${nearest_put_wall} — heavy support directly below ▲")

    # ── 0DTE flag: extreme volatility day, weaken signal (unreliable) ──
    if indicators.get("mm_zero_dte"):
        score = int(score * 0.80)
        reasons.append("⚠️ 0DTE expiry today — extreme MM hedging activity, signal unreliable ×0.8")

    # ════════════════════════════════════════════════════
    # SPY / MACRO SCORING — market context for TSLA
    # TSLA beta ~2x means macro moves are AMPLIFIED
    # ════════════════════════════════════════════════════

    macro_score  = indicators.get("spy_macro_score", 0)
    spy_trend    = indicators.get("spy_trend", "UNKNOWN")
    vix          = indicators.get("vix", 20) or 20
    vix_regime   = indicators.get("vix_regime", "NORMAL")
    spy_chg      = indicators.get("spy_change_pct", 0) or 0
    beta         = indicators.get("beta_20d", 2.0) or 2.0
    expected_mv  = indicators.get("expected_tsla_move", 0) or 0
    div_warn     = indicators.get("divergence_warning", False)
    rs_sig       = indicators.get("rs_signal", "INLINE")

    # SPY trend regime — most important macro factor
    if spy_trend == "BULL MARKET":
        score += 25; reasons.append("SPY bull market — strong macro tailwind for TSLA ▲▲")
    elif spy_trend == "UPTREND":
        score += 15; reasons.append("SPY uptrend — macro tailwind ▲")
    elif spy_trend == "DOWNTREND":
        score -= 20; reasons.append("SPY downtrend — macro headwind ▼")
    elif spy_trend == "BEAR MARKET":
        score -= 30; reasons.append("SPY bear market — severe headwind, beta amplifies losses ▼▼")

    # VIX fear level — directly suppresses risk assets
    if vix_regime == "EXTREME FEAR":
        score -= 30; reasons.append(f"VIX {vix} EXTREME FEAR — risk-off panic, TSLA hit hard ▼▼")
    elif vix_regime == "HIGH FEAR":
        score -= 18; reasons.append(f"VIX {vix} high fear — institutions reducing risk ▼")
    elif vix_regime == "ELEVATED":
        score -= 8
    elif vix_regime == "COMPLACENT":
        score += 8; reasons.append(f"VIX {vix} complacent — risk-on environment ▲")

    # Today's SPY move × beta = expected TSLA impact
    if spy_chg > 1.5:
        score += 18; reasons.append(f"SPY up {spy_chg:+.1f}% → TSLA expected {expected_mv:+.1f}% (beta {beta}x) ▲")
    elif spy_chg > 0.5:
        score += 8
    elif spy_chg < -1.5:
        score -= 22; reasons.append(f"SPY down {spy_chg:.1f}% → TSLA expected {expected_mv:.1f}% (beta {beta}x) ▼")
    elif spy_chg < -0.5:
        score -= 10

    # Relative strength vs SPY
    if rs_sig == "LEADING":
        score += 12; reasons.append("TSLA leading SPY — strong relative momentum ▲")
    elif rs_sig == "LAGGING":
        score -= 12; reasons.append("TSLA lagging SPY — relative weakness ▼")

    # Divergence warning: TSLA underperforming even on SPY up day
    if div_warn:
        score -= 10; reasons.append("⚠ TSLA/SPY divergence — TSLA underperforming, watch for reversal")

    # ════════════════════════════════════════════════════
    # NEWS SENTIMENT SCORING
    # Real-time news directly impacts price — scored by
    # recency-weighted NLP keyword analysis
    # ════════════════════════════════════════════════════

    news_score  = indicators.get("news_score", 0)
    news_signal = indicators.get("news_signal", "NEUTRAL")
    news_bull   = indicators.get("news_bull_ct", 0)
    news_bear   = indicators.get("news_bear_ct", 0)

    if   news_score >= 25:
        score += 25; reasons.append(f"📰 News VERY BULLISH (score:{news_score}, {news_bull} bullish articles) ▲▲")
    elif news_score >= 10:
        score += 15; reasons.append(f"📰 News BULLISH (score:{news_score}) ▲")
    elif news_score <= -25:
        score -= 25; reasons.append(f"📰 News VERY BEARISH (score:{news_score}, {news_bear} bearish articles) ▼▼")
    elif news_score <= -10:
        score -= 15; reasons.append(f"📰 News BEARISH (score:{news_score}) ▼")

    # ════════════════════════════════════════════════════
    # EXTENDED HOURS SCORING
    # Pre/post market moves reveal institutional conviction
    # before regular market participants can react
    # ════════════════════════════════════════════════════

    ext_score  = indicators.get("ext_score", 0)
    session    = indicators.get("session", "UNKNOWN")
    pm_pct     = indicators.get("premarket_change_pct", 0) or 0
    ah_pct     = indicators.get("afterhours_change_pct", 0) or 0
    gap_pct    = indicators.get("overnight_gap_pct", 0) or 0
    gap_dir    = indicators.get("gap_direction", "NONE")

    # Pre-market signals (most predictive for next open)
    if   pm_pct >= 3:  score += 25; reasons.append(f"⏰ Pre-market surging +{pm_pct}% — institutions accumulating ▲▲")
    elif pm_pct >= 1:  score += 12; reasons.append(f"⏰ Pre-market +{pm_pct}% — positive open expected ▲")
    elif pm_pct <= -3: score -= 25; reasons.append(f"⏰ Pre-market crashing {pm_pct}% — heavy selling ▼▼")
    elif pm_pct <= -1: score -= 12; reasons.append(f"⏰ Pre-market {pm_pct}% — negative open expected ▼")

    # After-hours signals (carry into next pre-market)
    if   ah_pct >= 3:  score += 20; reasons.append(f"🌙 After-hours +{ah_pct}% — strong post-close conviction ▲")
    elif ah_pct >= 1:  score += 10
    elif ah_pct <= -3: score -= 20; reasons.append(f"🌙 After-hours {ah_pct}% — post-close sellers in control ▼")
    elif ah_pct <= -1: score -= 10

    # Overnight gap — large gaps set the tone for the day
    if   gap_dir == "UP"   and abs(gap_pct) >= 2: score += 12; reasons.append(f"↑ Overnight gap up {gap_pct:+.1f}%")
    elif gap_dir == "DOWN" and abs(gap_pct) >= 2: score -= 12; reasons.append(f"↓ Overnight gap down {gap_pct:.1f}%")

    # ── Confluence Bonus: when 4+ models agree, amplify ──    # ── Confluence Bonus: when 4+ models agree, amplify ──    # ════════════════════════════════════════════════════
    # EXTENDED HOURS SCORING
    # Pre/post market moves reveal institutional conviction
    # before regular market participants can react
    # ════════════════════════════════════════════════════

    ext_score  = indicators.get("ext_score", 0)
    session    = indicators.get("session", "UNKNOWN")
    pm_pct     = indicators.get("premarket_change_pct", 0) or 0
    ah_pct     = indicators.get("afterhours_change_pct", 0) or 0
    gap_pct    = indicators.get("overnight_gap_pct", 0) or 0
    gap_dir    = indicators.get("gap_direction", "NONE")

    # Pre-market signals (most predictive for next open)
    if   pm_pct >= 3:  score += 25; reasons.append(f"⏰ Pre-market surging +{pm_pct}% — institutions accumulating ▲▲")
    elif pm_pct >= 1:  score += 12; reasons.append(f"⏰ Pre-market +{pm_pct}% — positive open expected ▲")
    elif pm_pct <= -3: score -= 25; reasons.append(f"⏰ Pre-market crashing {pm_pct}% — heavy selling ▼▼")
    elif pm_pct <= -1: score -= 12; reasons.append(f"⏰ Pre-market {pm_pct}% — negative open expected ▼")

    # After-hours signals (carry into next pre-market)
    if   ah_pct >= 3:  score += 20; reasons.append(f"🌙 After-hours +{ah_pct}% — strong post-close conviction ▲")
    elif ah_pct >= 1:  score += 10
    elif ah_pct <= -3: score -= 20; reasons.append(f"🌙 After-hours {ah_pct}% — post-close sellers in control ▼")
    elif ah_pct <= -1: score -= 10

    # Overnight gap — large gaps set the tone for the day
    if   gap_dir == "UP"   and abs(gap_pct) >= 2: score += 12; reasons.append(f"↑ Overnight gap up {gap_pct:+.1f}%")
    elif gap_dir == "DOWN" and abs(gap_pct) >= 2: score -= 12; reasons.append(f"↓ Overnight gap down {gap_pct:.1f}%")

    # ── Confluence Bonus: when 4+ models agree, amplify ──    # ── Confluence Bonus: when 4+ models agree, amplify ──    # ════════════════════════════════════════════════════
    # NEWS SENTIMENT SCORING
    # Real-time news directly impacts price — scored by
    # recency-weighted NLP keyword analysis
    # ════════════════════════════════════════════════════

    news_score  = indicators.get("news_score", 0)
    news_signal = indicators.get("news_signal", "NEUTRAL")
    news_bull   = indicators.get("news_bull_ct", 0)
    news_bear   = indicators.get("news_bear_ct", 0)

    if   news_score >= 25:
        score += 25; reasons.append(f"📰 News VERY BULLISH (score:{news_score}, {news_bull} bullish articles) ▲▲")
    elif news_score >= 10:
        score += 15; reasons.append(f"📰 News BULLISH (score:{news_score}) ▲")
    elif news_score <= -25:
        score -= 25; reasons.append(f"📰 News VERY BEARISH (score:{news_score}, {news_bear} bearish articles) ▼▼")
    elif news_score <= -10:
        score -= 15; reasons.append(f"📰 News BEARISH (score:{news_score}) ▼")

    # ════════════════════════════════════════════════════
    # EXTENDED HOURS SCORING
    # Pre/post market moves reveal institutional conviction
    # before regular market participants can react
    # ════════════════════════════════════════════════════

    ext_score  = indicators.get("ext_score", 0)
    session    = indicators.get("session", "UNKNOWN")
    pm_pct     = indicators.get("premarket_change_pct", 0) or 0
    ah_pct     = indicators.get("afterhours_change_pct", 0) or 0
    gap_pct    = indicators.get("overnight_gap_pct", 0) or 0
    gap_dir    = indicators.get("gap_direction", "NONE")

    # Pre-market signals (most predictive for next open)
    if   pm_pct >= 3:  score += 25; reasons.append(f"⏰ Pre-market surging +{pm_pct}% — institutions accumulating ▲▲")
    elif pm_pct >= 1:  score += 12; reasons.append(f"⏰ Pre-market +{pm_pct}% — positive open expected ▲")
    elif pm_pct <= -3: score -= 25; reasons.append(f"⏰ Pre-market crashing {pm_pct}% — heavy selling ▼▼")
    elif pm_pct <= -1: score -= 12; reasons.append(f"⏰ Pre-market {pm_pct}% — negative open expected ▼")

    # After-hours signals (carry into next pre-market)
    if   ah_pct >= 3:  score += 20; reasons.append(f"🌙 After-hours +{ah_pct}% — strong post-close conviction ▲")
    elif ah_pct >= 1:  score += 10
    elif ah_pct <= -3: score -= 20; reasons.append(f"🌙 After-hours {ah_pct}% — post-close sellers in control ▼")
    elif ah_pct <= -1: score -= 10

    # Overnight gap — large gaps set the tone for the day
    if   gap_dir == "UP"   and abs(gap_pct) >= 2: score += 12; reasons.append(f"↑ Overnight gap up {gap_pct:+.1f}%")
    elif gap_dir == "DOWN" and abs(gap_pct) >= 2: score -= 12; reasons.append(f"↓ Overnight gap down {gap_pct:.1f}%")

    # ── Confluence Bonus: when 4+ models agree, amplify ──    # ── Confluence Bonus: when 4+ models agree, amplify ──    # ════════════════════════════════════════════════════
    # EXTENDED HOURS SCORING
    # Pre/post market moves reveal institutional conviction
    # before regular market participants can react
    # ════════════════════════════════════════════════════

    ext_score  = indicators.get("ext_score", 0)
    session    = indicators.get("session", "UNKNOWN")
    pm_pct     = indicators.get("premarket_change_pct", 0) or 0
    ah_pct     = indicators.get("afterhours_change_pct", 0) or 0
    gap_pct    = indicators.get("overnight_gap_pct", 0) or 0
    gap_dir    = indicators.get("gap_direction", "NONE")

    # Pre-market signals (most predictive for next open)
    if   pm_pct >= 3:  score += 25; reasons.append(f"⏰ Pre-market surging +{pm_pct}% — institutions accumulating ▲▲")
    elif pm_pct >= 1:  score += 12; reasons.append(f"⏰ Pre-market +{pm_pct}% — positive open expected ▲")
    elif pm_pct <= -3: score -= 25; reasons.append(f"⏰ Pre-market crashing {pm_pct}% — heavy selling ▼▼")
    elif pm_pct <= -1: score -= 12; reasons.append(f"⏰ Pre-market {pm_pct}% — negative open expected ▼")

    # After-hours signals (carry into next pre-market)
    if   ah_pct >= 3:  score += 20; reasons.append(f"🌙 After-hours +{ah_pct}% — strong post-close conviction ▲")
    elif ah_pct >= 1:  score += 10
    elif ah_pct <= -3: score -= 20; reasons.append(f"🌙 After-hours {ah_pct}% — post-close sellers in control ▼")
    elif ah_pct <= -1: score -= 10

    # Overnight gap — large gaps set the tone for the day
    if   gap_dir == "UP"   and abs(gap_pct) >= 2: score += 12; reasons.append(f"↑ Overnight gap up {gap_pct:+.1f}%")
    elif gap_dir == "DOWN" and abs(gap_pct) >= 2: score -= 12; reasons.append(f"↓ Overnight gap down {gap_pct:.1f}%")

    # ── Confluence Bonus: when 4+ models agree, amplify ──    # ── Confluence Bonus: when 4+ models agree, amplify ──
    bullish_models = sum([
        1 if kalman_sig == "BULLISH" else 0,
        1 if zscore < -1 else 0,
        1 if mc_prob > 55 else 0,
        1 if factor_sig in ("BUY","STRONG_BUY") else 0,
        1 if smi_sig == "ACCUMULATING" else 0,
        1 if (vwap and price < vwap) else 0,
    ])
    bearish_models = sum([
        1 if kalman_sig == "BEARISH" else 0,
        1 if zscore > 1 else 0,
        1 if mc_prob < 45 else 0,
        1 if factor_sig in ("SELL","STRONG_SELL") else 0,
        1 if smi_sig == "DISTRIBUTING" else 0,
        1 if (vwap and price > vwap) else 0,
    ])
    if bullish_models >= 4:
        score = int(score * 1.25)
        reasons.append(f"🔥 CONFLUENCE: {bullish_models}/6 institutional models BULLISH — signal amplified ×1.25")
    elif bearish_models >= 4:
        score = int(score * 1.25)
        reasons.append(f"🔥 CONFLUENCE: {bearish_models}/6 institutional models BEARISH — signal amplified ×1.25")

    # ══════════════════════════════════════════════════════
    # SPY / MACRO SCORING — biggest amplifier in the system
    # Macro environment is the tide that lifts/sinks all boats
    # ══════════════════════════════════════════════════════
    macro_score  = indicators.get("macro_score", 0)
    macro_signal = indicators.get("macro_signal", "NEUTRAL")
    vix          = indicators.get("vix", 20) or 20
    vix_regime   = indicators.get("vix_regime", "NORMAL")
    spy_trend    = indicators.get("spy_trend", "UNKNOWN")
    spy_chg      = indicators.get("spy_change_pct", 0) or 0
    spy_beta     = indicators.get("spy_beta", 2.0) or 2.0
    rs_signal    = indicators.get("rs_signal", "INLINE")

    # SPY macro score contributes ±35 pts to signal
    if macro_score >= 40:
        score += 35; reasons.append(f"SPY: STRONG TAILWIND — {spy_trend}, macro amplifying BUY ▲▲")
    elif macro_score >= 15:
        score += 20; reasons.append(f"SPY: TAILWIND — {spy_trend} supports upside ▲")
    elif macro_score >= -15:
        pass  # neutral — no adjustment
    elif macro_score >= -35:
        score -= 20; reasons.append(f"SPY: HEADWIND — {spy_trend} pressuring TSLA ▼")
    else:
        score -= 35; reasons.append(f"SPY: STRONG HEADWIND — {spy_trend}, macro amplifying SELL ▼▼")

    # VIX regime — fear spikes kill risk assets regardless of technicals
    if vix_regime == "EXTREME FEAR":
        score = int(score * 0.5)   # halve the signal — market in panic
        reasons.append(f"🚨 VIX={vix} EXTREME FEAR — panic mode, all longs at risk ×0.5")
    elif vix_regime == "HIGH FEAR":
        score = int(score * 0.75)
        reasons.append(f"⚠ VIX={vix} HIGH FEAR — risk-off pressure ×0.75")
    elif vix_regime == "COMPLACENT" and score > 0:
        score = int(score * 0.90)  # complacency = don't chase
        reasons.append(f"VIX={vix} complacent — low fear, watch for reversal")

    # SPY day move × beta = expected TSLA impact (reality check)
    expected_tsla = round(spy_chg * spy_beta, 1)
    if abs(spy_chg) > 1.5:
        reasons.append(f"SPY {spy_chg:+.1f}% × beta {spy_beta} = TSLA expected {expected_tsla:+.1f}% today")

    # TSLA relative strength vs SPY — tells you if TSLA is a leader or laggard
    if rs_signal == "LEADING":
        score += 10; reasons.append("TSLA leading SPY — relative strength confirms BUY ▲")
    elif rs_signal == "LAGGING":
        score -= 10; reasons.append("TSLA lagging SPY — relative weakness ▼")

    # Divergence warning — TSLA dropping while SPY holds = TSLA-specific problem
    if indicators.get("divergence_warning"):
        score -= 15; reasons.append("⚠ TSLA underperforming SPY — stock-specific selling pressure ▼")

    strength = min(abs(score), 100)
    # VIX-aware thresholds: in high-fear markets need more conviction to BUY
    vix_now = indicators.get("vix", 20) or 20
    if vix_now >= 30:
        buy_thresh  = 45
        sell_thresh = -20
    elif vix_now >= 25:
        buy_thresh  = 40
        sell_thresh = -22
    else:
        buy_thresh  = 35
        sell_thresh = -25

    # Momentum guard: require stronger signal when price is in downtrend
    _ret1 = float(indicators.get("ret_1b", 0) or 0)
    _ret3 = float(indicators.get("ret_3b", 0) or 0)
    _falling = _ret1 < -0.002 and _ret3 < -0.003  # price falling last 3 bars
    _rising  = _ret1 >  0.002 and _ret3 >  0.003  # price rising last 3 bars
    if _falling:
        buy_thresh  += 8   # need more evidence to BUY into falling price
    if _rising:
        sell_thresh -= 8   # need more evidence to SELL into rising price

    signal = "BUY" if score >= buy_thresh else "SELL" if score <= sell_thresh else "HOLD"
    return signal, strength, reasons




# ═══════════════════════════════════════════════════════════════
#  SPY / MACRO MARKET MONITOR
#  SPY movement directly impacts TSLA via beta & correlation
# ═══════════════════════════════════════════════════════════════

def calculate_spy_analysis(tsla_closes, tsla_price):
    """
    Tracks SPY, QQQ, VIX, TLT to compute macro impact on TSLA.
    TSLA beta to SPY ~2x — every SPY move gets amplified.
    """
    result = {
        "spy_price": None, "spy_change_pct": None,
        "qqq_price": None, "qqq_change_pct": None,
        "vix": None, "vix_regime": "UNKNOWN",
        "beta_20d": None, "beta_60d": None,
        "correlation_60d": None,
        "expected_tsla_move": None, "actual_tsla_move": None,
        "tsla_spy_deviation": None,
        "spy_trend": "UNKNOWN", "spy_signal": "NEUTRAL",
        "spy_rsi": None,
        "divergence": None, "divergence_warning": False,
        "relative_strength": None, "rs_signal": "NEUTRAL",
        "macro_score": 0, "macro_signal": "NEUTRAL",
        "macro_reasons": [],
        "spy_history": [], "vix_history": [], "rs_history": [],
        "key_levels": {},
        "tlt_5d_change": None, "bonds_signal": "NEUTRAL",
    }
    try:
        print("  🌍 Fetching SPY, QQQ, VIX, TLT...")
        spy_hist = yf.Ticker("SPY").history(period="6mo", interval="1d")
        qqq_hist = yf.Ticker("QQQ").history(period="6mo", interval="1d")
        vix_hist = yf.Ticker("^VIX").history(period="6mo", interval="1d")
        tlt_hist = yf.Ticker("TLT").history(period="3mo", interval="1d")
        if spy_hist.empty:
            print("  ⚠️ SPY hist empty - using fallback", flush=True)
            # Don't return - try to populate what we can from other tickers
            spy_closes = None
        else:
            spy_closes = spy_hist["Close"]
        qqq_closes = qqq_hist["Close"] if not qqq_hist.empty else None
        vix_closes = vix_hist["Close"] if not vix_hist.empty else None
        tlt_closes = tlt_hist["Close"] if not tlt_hist.empty else None
        spy_price  = round(float(spy_closes.iloc[-1]), 2)
        result["spy_price"] = spy_price
        spy_chg = round((float(spy_closes.iloc[-1]) / float(spy_closes.iloc[-2]) - 1) * 100, 2) if len(spy_closes) > 1 else 0
        result["spy_change_pct"] = spy_chg

        if qqq_closes is not None and len(qqq_closes) > 14:
            qqq_price = float(qqq_closes.iloc[-1])
            result["qqq_price"]      = round(qqq_price, 2)
            result["qqq_change_pct"] = round((qqq_price / float(qqq_closes.iloc[-2]) - 1) * 100, 2)
            # QQQ RSI
            _qd = qqq_closes.diff()
            _qg = _qd.where(_qd > 0, 0).rolling(14).mean()
            _ql = -_qd.where(_qd < 0, 0).rolling(14).mean()
            qqq_rsi = round(float((100 - 100/(1 + _qg/(_ql + 1e-9))).iloc[-1]), 1)
            result["qqq_rsi"]    = qqq_rsi
            result["qqq_ob"]     = qqq_rsi > 70   # overbought
            result["qqq_os"]     = qqq_rsi < 30   # oversold
            # QQQ MACD
            _qema12 = qqq_closes.ewm(span=12, adjust=False).mean()
            _qema26 = qqq_closes.ewm(span=26, adjust=False).mean()
            _qmacd  = _qema12 - _qema26
            _qsig   = _qmacd.ewm(span=9, adjust=False).mean()
            result["qqq_macd_hist"] = round(float((_qmacd - _qsig).iloc[-1]), 4)
            result["qqq_macd_bull"] = result["qqq_macd_hist"] > 0
            # QQQ trend
            _qema20  = float(qqq_closes.ewm(span=20, adjust=False).mean().iloc[-1])
            _qema50  = float(qqq_closes.ewm(span=50, adjust=False).mean().iloc[-1])
            _qema200 = float(qqq_closes.ewm(span=200, adjust=False).mean().iloc[-1])
            result["qqq_above_20ema"]  = qqq_price > _qema20
            result["qqq_above_50ema"]  = qqq_price > _qema50
            result["qqq_above_200ema"] = qqq_price > _qema200
            result["qqq_trend"] = (
                "BULL"  if qqq_price > _qema20 and qqq_price > _qema50 else
                "BEAR"  if qqq_price < _qema20 and qqq_price < _qema50 else "MIXED"
            )
            # QQQ 5-day momentum
            result["qqq_mom_5d"] = round((qqq_price / float(qqq_closes.iloc[-6]) - 1)*100, 2) if len(qqq_closes) > 5 else 0

        # VIX
        if vix_closes is not None and len(vix_closes):
            vix = round(float(vix_closes.iloc[-1]), 2)
            result["vix"] = vix
            result["vix_regime"] = (
                "EXTREME FEAR" if vix >= 35 else "HIGH FEAR" if vix >= 25 else
                "ELEVATED"     if vix >= 18 else "NORMAL"    if vix >= 12 else "COMPLACENT"
            )
            result["vix_history"] = [
                {"date": str(vix_closes.index[i].date()), "vix": round(float(vix_closes.iloc[i]), 2)}
                for i in range(-60, 0) if abs(i) <= len(vix_closes)
            ]

        # Align returns — skip if SPY data unavailable
        if spy_closes is None:
            result["macro_signal"] = "SPY UNAVAILABLE"
            return result
        tsla_ret = tsla_closes.pct_change().dropna()
        spy_ret  = spy_closes.pct_change().dropna()
        common   = tsla_ret.index.intersection(spy_ret.index)
        if len(common) < 20:
            result["macro_signal"] = "INSUFFICIENT DATA"; return result
        tr = tsla_ret.loc[common]
        sr = spy_ret.loc[common]

        # Rolling beta
        cov20 = tr.rolling(20).cov(sr); var20 = sr.rolling(20).var()
        cov60 = tr.rolling(60).cov(sr); var60 = sr.rolling(60).var()
        beta_20 = round(float((cov20 / (var20 + 1e-12)).iloc[-1]), 2)
        beta_60 = round(float((cov60 / (var60 + 1e-12)).iloc[-1]), 2)
        result["beta_20d"] = beta_20
        result["beta_60d"] = beta_60
        result["correlation_60d"] = round(float(tr.iloc[-60:].corr(sr.iloc[-60:])), 3)

        # Expected vs actual TSLA move
        expected = round(spy_chg * beta_20, 2)
        actual   = round((float(tsla_closes.iloc[-1]) / float(tsla_closes.iloc[-2]) - 1) * 100, 2) if len(tsla_closes) > 1 else 0
        result["expected_tsla_move"] = expected
        result["actual_tsla_move"]   = actual
        deviation = round(actual - expected, 2)
        result["tsla_spy_deviation"] = deviation
        if abs(deviation) > 2.0:
            if deviation > 2:
                result["divergence"] = f"TSLA outperforming SPY by {deviation:+.1f}% — relative strength"
            else:
                result["divergence"] = f"TSLA underperforming SPY by {abs(deviation):.1f}% — relative weakness ⚠"
                result["divergence_warning"] = True
        else:
            result["divergence"] = f"TSLA tracking SPY normally (dev: {deviation:+.1f}%)"

        # Relative strength 20d
        tsla_p20 = (float(tsla_closes.iloc[-1]) / float(tsla_closes.iloc[-21]) - 1) * 100 if len(tsla_closes) > 21 else 0
        spy_p20  = (float(spy_closes.iloc[-1])  / float(spy_closes.iloc[-21])  - 1) * 100 if len(spy_closes)  > 21 else 0
        rs = round(tsla_p20 - spy_p20, 2)
        result["relative_strength"] = rs
        result["tsla_perf_20d"]     = round(tsla_p20, 2)
        result["spy_perf_20d"]      = round(spy_p20, 2)
        result["rs_signal"] = (
            "LEADING"    if rs > 5  else "OUTPERFORM" if rs > 1  else
            "LAGGING"    if rs < -5 else "UNDERPERFORM" if rs < -1 else "INLINE"
        )

        # SPY trend regime
        spy_ema20  = float(spy_closes.ewm(span=20).mean().iloc[-1])
        spy_ema50  = float(spy_closes.ewm(span=50).mean().iloc[-1])
        spy_ema200 = float(spy_closes.ewm(span=200).mean().iloc[-1])

        # RSI on SPY
        spy_delta = spy_closes.diff()
        spy_gain  = spy_delta.where(spy_delta > 0, 0).rolling(14).mean()
        spy_loss  = -spy_delta.where(spy_delta < 0, 0).rolling(14).mean()
        spy_rsi   = round(float((100 - 100 / (1 + spy_gain / (spy_loss + 1e-9))).iloc[-1]), 1)
        result["spy_rsi"]    = spy_rsi
        result["spy_ema20"]  = round(spy_ema20, 2)
        result["spy_ema50"]  = round(spy_ema50, 2)
        result["spy_ema200"] = round(spy_ema200, 2)
        result["spy_ob"]     = spy_rsi > 70
        result["spy_os"]     = spy_rsi < 30
        # SPY MACD
        _sema12 = spy_closes.ewm(span=12, adjust=False).mean()
        _sema26 = spy_closes.ewm(span=26, adjust=False).mean()
        _smacd  = _sema12 - _sema26
        _ssig   = _smacd.ewm(span=9, adjust=False).mean()
        spy_macd_hist = float((_smacd - _ssig).iloc[-1])
        result["spy_macd_hist"] = round(spy_macd_hist, 4)
        result["spy_macd_bull"] = spy_macd_hist > 0
        # SPY Bollinger %B
        _sma20 = float(spy_closes.rolling(20).mean().iloc[-1])
        _sstd  = float(spy_closes.rolling(20).std().iloc[-1] or 1)
        spy_bb_pct = (spy_price - (_sma20 - 2*_sstd)) / (4*_sstd + 1e-9)
        result["spy_bb_pct"] = round(spy_bb_pct, 3)
        result["spy_bb_ob"]  = spy_bb_pct > 0.9   # near upper band
        result["spy_bb_os"]  = spy_bb_pct < 0.1   # near lower band
        # SPY 5-day momentum
        result["spy_mom_5d"] = round((spy_price / float(spy_closes.iloc[-6]) - 1)*100, 2) if len(spy_closes) > 5 else 0

        above_200 = spy_price > spy_ema200
        above_50  = spy_price > spy_ema50
        gx        = spy_ema50 > spy_ema200
        result["spy_trend"] = (
            "BULL MARKET" if above_200 and above_50 and gx else
            "UPTREND"     if above_200 and above_50       else
            "MIXED"       if above_200                    else
            "BEAR MARKET" if not above_200 and not above_50 else "DOWNTREND"
        )

        spy_52wh = round(float(spy_closes.iloc[-252:].max()), 2) if len(spy_closes) >= 252 else round(float(spy_closes.max()), 2)
        spy_52wl = round(float(spy_closes.iloc[-252:].min()), 2) if len(spy_closes) >= 252 else round(float(spy_closes.min()), 2)
        result["key_levels"] = {
            "spy_52w_high": spy_52wh, "spy_52w_low": spy_52wl,
            "spy_ema20": round(spy_ema20, 2), "spy_ema50": round(spy_ema50, 2),
            "spy_ema200": round(spy_ema200, 2),
            "pct_from_52w_high": round((spy_price / spy_52wh - 1) * 100, 2),
        }

        # TLT bonds
        if tlt_closes is not None and len(tlt_closes) > 5:
            tlt_chg = (float(tlt_closes.iloc[-1]) / float(tlt_closes.iloc[-5]) - 1) * 100
            result["tlt_5d_change"] = round(tlt_chg, 2)
            result["bonds_signal"]  = "RISK-OFF ROTATION" if tlt_chg > 1.5 else "NEUTRAL"

        # SPY history for chart
        spy_ema20_ser = spy_closes.ewm(span=20).mean()
        spy_ema50_ser = spy_closes.ewm(span=50).mean()
        result["spy_history"] = [
            {"date":  str(spy_closes.index[i].date()),
             "price": round(float(spy_closes.iloc[i]), 2),
             "ema20": round(float(spy_ema20_ser.iloc[i]), 2),
             "ema50": round(float(spy_ema50_ser.iloc[i]), 2)}
            for i in range(-60, 0)
        ]

        # RS chart — normalized to 100 at 60 days ago
        base_tsla = float(tsla_closes.iloc[-60]) if len(tsla_closes) >= 60 else float(tsla_closes.iloc[0])
        base_spy  = float(spy_closes.iloc[-60])  if len(spy_closes)  >= 60 else float(spy_closes.iloc[0])
        base_qqq  = float(qqq_closes.iloc[-60])  if qqq_closes is not None and len(qqq_closes) >= 60 else None
        result["rs_history"] = []
        for i in range(-60, 0):
            try:
                entry = {
                    "date": str(tsla_closes.index[i].date()),
                    "tsla": round(float(tsla_closes.iloc[i]) / base_tsla * 100, 2),
                    "spy":  round(float(spy_closes.iloc[i])  / base_spy  * 100, 2),
                }
                if base_qqq:
                    entry["qqq"] = round(float(qqq_closes.iloc[i]) / base_qqq * 100, 2)
                result["rs_history"].append(entry)
            except Exception:
                continue

        # ══════════════════════════════════════
        # MACRO SCORE — fed into generate_signal
        # ══════════════════════════════════════
        macro_score   = 0
        macro_reasons = []

        spy_trend = result["spy_trend"]
        if   spy_trend == "BULL MARKET": macro_score += 30; macro_reasons.append("SPY bull market — strong tailwind ▲▲")
        elif spy_trend == "UPTREND":     macro_score += 18; macro_reasons.append("SPY uptrend — macro tailwind ▲")
        elif spy_trend == "DOWNTREND":   macro_score -= 20; macro_reasons.append("SPY downtrend — headwind ▼")
        elif spy_trend == "BEAR MARKET": macro_score -= 35; macro_reasons.append("SPY bear market — severe headwind ▼▼")

        if   spy_chg >  1.5: macro_score += 20; macro_reasons.append(f"SPY +{spy_chg}% → TSLA expected {expected:+.1f}% ▲")
        elif spy_chg >  0.5: macro_score += 10
        elif spy_chg < -1.5: macro_score -= 25; macro_reasons.append(f"SPY {spy_chg}% → TSLA expected {expected:.1f}% ▼")
        elif spy_chg < -0.5: macro_score -= 12

        vix = result.get("vix", 20) or 20
        if   vix >= 35: macro_score -= 30; macro_reasons.append(f"VIX {vix} EXTREME FEAR ▼▼")
        elif vix >= 25: macro_score -= 18; macro_reasons.append(f"VIX {vix} high fear ▼")
        elif vix >= 20: macro_score -= 8
        elif vix <  13: macro_score += 8;  macro_reasons.append(f"VIX {vix} complacent — risk-on ▲")
        elif vix <  16: macro_score += 4

        if   rs >  5: macro_score += 15; macro_reasons.append(f"TSLA leading SPY by {rs:+.1f}% ▲")
        elif rs >  1: macro_score += 8
        elif rs < -5: macro_score -= 15; macro_reasons.append(f"TSLA lagging SPY by {abs(rs):.1f}% ▼")
        elif rs < -1: macro_score -= 8

        if result["divergence_warning"]:
            macro_score -= 12; macro_reasons.append(("⚠ Divergence: " + str(result.get("divergence",""))))

        qqq_chg = result.get("qqq_change_pct", 0) or 0
        if   qqq_chg >  1.0: macro_score += 10; macro_reasons.append(f"QQQ +{qqq_chg}% tech sector bid ▲")
        elif qqq_chg < -1.0: macro_score -= 10; macro_reasons.append(f"QQQ {qqq_chg}% tech selling ▼")

        if result.get("bonds_signal") == "RISK-OFF ROTATION":
            macro_score -= 10; macro_reasons.append("TLT rising — risk-off rotation ▼")

        if   spy_rsi > 70: macro_score -= 10; macro_reasons.append(f"SPY RSI={spy_rsi} overbought ▼")
        elif spy_rsi < 30: macro_score += 10; macro_reasons.append(f"SPY RSI={spy_rsi} oversold ▲")

        result["macro_score"]   = macro_score
        result["macro_signal"]  = (
            "STRONG TAILWIND" if macro_score >= 40 else "TAILWIND"        if macro_score >= 15 else
            "NEUTRAL"         if macro_score >= -15 else "HEADWIND"       if macro_score >= -35 else
            "STRONG HEADWIND"
        )
        result["macro_reasons"] = macro_reasons
        result["spy_signal"]    = result["macro_signal"]

        print(f"  🌍 SPY ${spy_price} ({spy_chg:+.1f}%) | VIX:{vix} {result.get("vix_regime","")} | Beta:{beta_20}x | RS:{rs:+.1f}% | Macro:{result.get("macro_signal","")}")

    except Exception as e:
        print(f"  ❌ SPY error: {e}")
        import traceback; traceback.print_exc()
        result["macro_signal"]  = "ERROR"
        result["macro_reasons"] = [str(e)]

    return result

# ═══════════════════════════════════════════════════════════════
#  INSTITUTIONAL TRADING MODELS
#  Used by Goldman Sachs, Renaissance, Citadel, Two Sigma, etc.
# ═══════════════════════════════════════════════════════════════

# ── 1. VWAP + VWAP BANDS (used by every institutional desk) ──
def calculate_vwap(high, low, close, volume):
    """
    Volume Weighted Average Price — the primary execution benchmark
    for institutional orders. Buy below VWAP = favorable fill.
    Used by: Goldman, Morgan Stanley, all major algo desks.
    """
    typical = (high + close + low) / 3
    vwap = (typical * volume).cumsum() / volume.cumsum()
    # Standard deviation bands (±1, ±2)
    cum_vol  = volume.cumsum()
    cum_vwap = (typical * volume).cumsum() / cum_vol
    variance = ((typical - cum_vwap) ** 2 * volume).cumsum() / cum_vol
    std = np.sqrt(variance)
    return {
        "vwap":    round(vwap.iloc[-1], 2),
        "upper1":  round((vwap + std).iloc[-1], 2),
        "lower1":  round((vwap - std).iloc[-1], 2),
        "upper2":  round((vwap + 2*std).iloc[-1], 2),
        "lower2":  round((vwap - 2*std).iloc[-1], 2),
        "history": [
            {"date": str(close.index[i].date()), "vwap": round(vwap.iloc[i], 2),
             "u1": round((vwap+std).iloc[i],2), "l1": round((vwap-std).iloc[i],2)}
            for i in range(-60, 0)
        ]
    }


# ── 2. KALMAN FILTER (Renaissance Technologies, AQR) ──
def calculate_kalman_filter(prices):
    """
    Kalman Filter — dynamic trend estimator with noise reduction.
    Produces a 'true price' by filtering out random noise.
    Used by: Renaissance Technologies, Two Sigma, DE Shaw.
    Outperforms simple moving averages for trend following.
    """
    n      = len(prices)
    obs    = prices.values.astype(float)
    # State: [price, velocity]
    x      = np.array([obs[0], 0.0])
    P      = np.eye(2) * 1.0
    F      = np.array([[1, 1], [0, 1]])       # transition
    H      = np.array([[1, 0]])                # observation
    Q      = np.array([[0.01, 0], [0, 0.001]])  # process noise
    R      = np.array([[0.5]])                  # measurement noise

    filtered = []
    velocities = []
    for z in obs:
        # Predict
        x = F @ x
        P = F @ P @ F.T + Q
        # Update
        S = H @ P @ H.T + R
        K = P @ H.T @ np.linalg.inv(S)
        x = x + K @ (np.array([[z]]) - H @ x.reshape(-1,1)).flatten()
        P = (np.eye(2) - K @ H) @ P
        filtered.append(round(float(x[0]), 2))
        velocities.append(round(float(x[1]), 4))

    trend_dir = "UP" if velocities[-1] > 0 else "DOWN"
    acceleration = round(velocities[-1] - velocities[-2], 4) if len(velocities) > 1 else 0
    return {
        "filtered_price": filtered[-1],
        "velocity":       round(velocities[-1], 4),
        "acceleration":   acceleration,
        "trend":          trend_dir,
        "signal":         "BULLISH" if velocities[-1] > 0 and acceleration > 0
                          else "BEARISH" if velocities[-1] < 0 and acceleration < 0
                          else "NEUTRAL",
        "history":        [{"date": str(prices.index[i].date()), "filtered": filtered[i]}
                           for i in range(-60, 0) if i < len(filtered)]
    }


# ── 3. MEAN REVERSION Z-SCORE (Stat Arb desks — Citadel, Millenium) ──
def calculate_zscore(prices, window=20):
    """
    Statistical Arbitrage Z-Score — measures how many standard deviations
    the current price is from its rolling mean.
    Z > +2 = overbought (short signal)
    Z < -2 = oversold (long signal)
    Used by: Citadel, Millennium, Point72 stat arb desks.
    """
    rolling_mean = prices.rolling(window).mean()
    rolling_std  = prices.rolling(window).std()
    zscore       = (prices - rolling_mean) / (rolling_std + 1e-9)
    z_now        = round(zscore.iloc[-1], 3)

    signal = "OVERSOLD" if z_now < -2 else "OVERBOUGHT" if z_now > 2 else              "MILDLY_LONG" if z_now < -1 else "MILDLY_SHORT" if z_now > 1 else "NEUTRAL"

    return {
        "zscore":       z_now,
        "signal":       signal,
        "rolling_mean": round(rolling_mean.iloc[-1], 2),
        "rolling_std":  round(rolling_std.iloc[-1], 2),
        "history":      [{"date": str(prices.index[i].date()), "z": round(zscore.iloc[i], 3)}
                         for i in range(-60, 0) if not pd.isna(zscore.iloc[i])]
    }


# ── 4. KELLY CRITERION (optimal position sizing — used by Renaissance) ──
def calculate_kelly(prices, risk_free=0.05):
    """
    Kelly Criterion — mathematically optimal bet size for maximum
    long-term growth. Used by Renaissance, Bridgewater.
    Kelly % = (edge / odds) = (Win% * AvgWin - Loss% * AvgLoss) / AvgWin
    """
    returns  = prices.pct_change().dropna()
    wins     = returns[returns > 0]
    losses   = returns[returns < 0]
    if len(wins) == 0 or len(losses) == 0:
        return {"kelly_pct": 0, "signal": "NEUTRAL"}

    win_rate  = len(wins) / len(returns)
    loss_rate = 1 - win_rate
    avg_win   = wins.mean()
    avg_loss  = abs(losses.mean())
    odds      = avg_win / (avg_loss + 1e-9)

    kelly_full = win_rate - (loss_rate / odds)
    kelly_half = kelly_full / 2  # "half-Kelly" — safer, used in practice
    kelly_pct  = max(min(kelly_half * 100, 100), -100)  # clamp

    sharpe     = (returns.mean() - risk_free/252) / (returns.std() + 1e-9) * np.sqrt(252)
    max_dd     = ((prices / prices.cummax()) - 1).min()

    return {
        "kelly_pct":   round(kelly_pct, 2),
        "kelly_full":  round(kelly_full * 100, 2),
        "win_rate":    round(win_rate * 100, 1),
        "avg_win":     round(avg_win * 100, 3),
        "avg_loss":    round(avg_loss * 100, 3),
        "sharpe":      round(sharpe, 3),
        "max_drawdown":round(max_dd * 100, 2),
        "signal":      "SIZE_UP" if kelly_half > 0.15 else
                       "NORMAL"  if kelly_half > 0.05 else
                       "SIZE_DOWN" if kelly_half > 0 else "AVOID",
    }


# ── 5. MONTE CARLO VaR (Value at Risk — Goldman, JPMorgan Risk Desks) ──
def calculate_monte_carlo_var(prices, simulations=5000, horizon=10, confidence=0.95):
    """
    Monte Carlo simulation — models thousands of possible price paths
    to estimate Value at Risk (VaR) and upside potential.
    Used by: Every major bank and hedge fund for risk management.
    Goldman Sachs, JPMorgan, Morgan Stanley all run daily VaR.
    """
    returns   = np.log(prices / prices.shift(1)).dropna()
    mu        = returns.mean()
    sigma     = returns.std()
    S0        = prices.iloc[-1]

    np.random.seed(42)
    rand      = np.random.normal(mu, sigma, (simulations, horizon))
    paths     = S0 * np.exp(np.cumsum(rand, axis=1))
    final     = paths[:, -1]

    var_95    = round(float(np.percentile(final - S0, (1 - confidence) * 100)), 2)
    var_99    = round(float(np.percentile(final - S0, 1)), 2)
    cvar_95   = round(float(final[final - S0 <= var_95].mean() - S0), 2)  # Expected Shortfall
    upside_95 = round(float(np.percentile(final - S0, 95)), 2)
    median    = round(float(np.median(final)), 2)
    prob_up   = round(float((final > S0).mean() * 100), 1)

    # Sample paths for chart (20 paths)
    sample_paths = []
    for i in range(0, min(20, simulations), max(1, simulations//20)):
        sample_paths.append([round(float(v), 2) for v in paths[i]])

    return {
        "var_95":      var_95,
        "var_99":      var_99,
        "cvar_95":     cvar_95,
        "upside_95":   upside_95,
        "median_price":median,
        "prob_up":     prob_up,
        "current":     round(S0, 2),
        "horizon_days":horizon,
        "simulations": simulations,
        "sample_paths":sample_paths,
        "signal":      "BULLISH" if prob_up > 55 else "BEARISH" if prob_up < 45 else "NEUTRAL",
    }


# ── 6. MOMENTUM FACTOR MODEL (Fama-French + AQR Momentum) ──
def calculate_factor_model(prices, volumes):
    """
    Multi-Factor Momentum Model — derived from Fama-French & AQR.
    Combines: Price Momentum, Volume Momentum, Volatility Regime.
    Used by: AQR Capital, Dimensional Fund Advisors, BlackRock Systematic.
    """
    returns = prices.pct_change().dropna()

    # Price Momentum (12-1 month: last 12mo return excluding last month)
    if len(prices) >= 252:
        mom_12_1 = (prices.iloc[-22] / prices.iloc[-252]) - 1
    elif len(prices) >= 60:
        mom_12_1 = (prices.iloc[-1] / prices.iloc[-60]) - 1
    else:
        mom_12_1 = 0

    # Short-term reversal (1 month)
    mom_1    = (prices.iloc[-1] / prices.iloc[-22]) - 1 if len(prices) >= 22 else 0

    # Volatility (realized vol, annualized)
    vol_20   = returns.iloc[-20:].std() * np.sqrt(252) if len(returns) >= 20 else 0

    # Volume Momentum (rising volume trend = institutional buying)
    vol_sma5  = volumes.iloc[-5:].mean()
    vol_sma20 = volumes.iloc[-20:].mean()
    vol_mom   = (vol_sma5 / (vol_sma20 + 1e-9)) - 1

    # Composite momentum score
    mom_score = (mom_12_1 * 0.5) + (mom_1 * 0.2) + (vol_mom * 0.3)

    # Risk-adjusted momentum (Sharpe-like)
    sharpe_mom = mom_12_1 / (vol_20 + 1e-9)

    signal = "STRONG_BUY"  if sharpe_mom > 0.5  else              "BUY"         if sharpe_mom > 0.1  else              "STRONG_SELL" if sharpe_mom < -0.5 else              "SELL"        if sharpe_mom < -0.1 else "NEUTRAL"

    return {
        "momentum_12_1":  round(mom_12_1 * 100, 2),
        "momentum_1m":    round(mom_1 * 100, 2),
        "volatility_ann": round(vol_20 * 100, 2),
        "volume_momentum":round(vol_mom * 100, 2),
        "sharpe_momentum":round(sharpe_mom, 3),
        "composite_score":round(mom_score * 100, 3),
        "signal":         signal,
    }


# ── 7. SMART MONEY INDEX (Institutional Flow Proxy) ──
def calculate_smart_money_index(opens, closes, volumes):
    """
    Smart Money Index — measures institutional vs retail activity.
    Theory: Retail trades emotionally at open; Institutions trade
    strategically in the last 30 min. SMI = yesterday_SMI - open_move + close_move
    Used by: Macro hedge funds, CTA strategies.
    """
    open_move  = closes - opens  # full-day move
    first_move = opens - opens.shift(1)    # gap/open move (retail sentiment)
    last_move  = closes - closes.shift(1)  # net daily (smart money)

    # SMI = cumulative: subtract panic open buys, add smart close activity
    smi = (last_move - first_move).cumsum()
    smi_norm = (smi - smi.rolling(20).mean()) / (smi.rolling(20).std() + 1e-9)

    smi_now  = round(smi_norm.iloc[-1], 3)
    trend_5  = smi_norm.iloc[-5:].mean()

    signal = "ACCUMULATING" if smi_now > 0.5 and trend_5 > 0 else              "DISTRIBUTING" if smi_now < -0.5 and trend_5 < 0 else              "NEUTRAL"

    return {
        "smi_zscore": smi_now,
        "trend_5d":   round(trend_5, 3),
        "signal":     signal,
        "history":    [{"date": str(closes.index[i].date()), "smi": round(smi_norm.iloc[i], 3)}
                       for i in range(-60, 0) if not pd.isna(smi_norm.iloc[i])]
    }


# ═══════════════════════════════════════════════════════════════
#  OPTIMAL EXIT ENGINE — Peak Detection & Downturn Warning
#  Tells you the best price to sell BEFORE the downturn starts
# ═══════════════════════════════════════════════════════════════

def calculate_exit_analysis(closes, highs, lows, volumes, indicators, inst_models):
    """
    Multi-model peak detection system.
    Combines 8 methods to identify the optimal sell window
    before a downturn begins — not after it has started.

    Methods:
      1. Fibonacci Extension Targets  — price targets from last swing
      2. Resistance Level Detection   — historical price ceilings
      3. Divergence Detection         — price up but momentum fading
      4. Distribution Pattern         — volume/price topping signals
      5. Parabolic SAR                — trailing stop acceleration
      6. Stochastic Oscillator        — overbought with bearish cross
      7. Rate of Change Deceleration  — momentum losing steam
      8. Multi-model Topping Score    — all signals combined
    """
    price   = float(closes.iloc[-1])
    results = {}

    # ─────────────────────────────────────────────
    # 1. FIBONACCI EXTENSION TARGETS
    # Find last significant swing low → compute extension levels
    # ─────────────────────────────────────────────
    try:
        window = min(60, len(closes))
        swing_low_idx  = closes.iloc[-window:].idxmin()
        swing_high_idx = closes.iloc[-window:].idxmax()
        swing_low  = closes[swing_low_idx]
        swing_high = closes[swing_high_idx]
        diff = swing_high - swing_low

        fibs = {
            "0.0%":   round(swing_low, 2),
            "23.6%":  round(swing_low + 0.236 * diff, 2),
            "38.2%":  round(swing_low + 0.382 * diff, 2),
            "50.0%":  round(swing_low + 0.500 * diff, 2),
            "61.8%":  round(swing_low + 0.618 * diff, 2),
            "78.6%":  round(swing_low + 0.786 * diff, 2),
            "100%":   round(swing_high, 2),
            "127.2%": round(swing_high + 0.272 * diff, 2),
            "161.8%": round(swing_high + 0.618 * diff, 2),
            "261.8%": round(swing_high + 1.618 * diff, 2),
        }

        # Nearest resistance above current price
        fib_targets_above = {k: v for k, v in fibs.items() if v > price * 1.002}
        nearest_fib = min(fib_targets_above.values()) if fib_targets_above else None
        nearest_fib_key = next((k for k, v in fib_targets_above.items() if v == nearest_fib), None)

        results["fibonacci"] = {
            "levels":       fibs,
            "nearest_resistance": nearest_fib,
            "nearest_label": nearest_fib_key,
            "swing_low":    round(swing_low, 2),
            "swing_high":   round(swing_high, 2),
        }
    except Exception as e:
        results["fibonacci"] = {"error": str(e)}

    # ─────────────────────────────────────────────
    # 2. KEY RESISTANCE LEVELS (Historical price ceilings)
    # ─────────────────────────────────────────────
    try:
        n = len(closes)
        resistance_levels = []
        # Find local highs in rolling windows
        for i in range(5, n - 5):
            if highs.iloc[i] == highs.iloc[max(0,i-5):i+6].max():
                resistance_levels.append(round(float(highs.iloc[i]), 2))

        # Cluster nearby levels (within 1%)
        clustered = []
        for r in sorted(set(resistance_levels)):
            if not clustered or r > clustered[-1] * 1.01:
                clustered.append(r)

        # Levels above current price (sell targets)
        above = [r for r in clustered if r > price * 1.005][:5]
        # Levels below (support)
        below = [r for r in clustered if r < price * 0.995][-5:]

        results["resistance"] = {
            "levels_above": above,
            "levels_below": below,
            "nearest_target": above[0] if above else None,
            "strong_target":  above[1] if len(above) > 1 else (above[0] if above else None),
        }
    except Exception as e:
        results["resistance"] = {"error": str(e)}

    # ─────────────────────────────────────────────
    # 3. BEARISH DIVERGENCE DETECTION
    # Price making new highs but momentum falling = classic topping
    # ─────────────────────────────────────────────
    try:
        divergences = []
        lookback = 20

        # RSI divergence: price higher high, RSI lower high
        price_now   = closes.iloc[-1]
        price_prev  = closes.iloc[-lookback]
        rsi_now     = indicators.get("rsi", 50)
        rsi_series  = _calc_rsi_series(closes)
        rsi_prev    = rsi_series.iloc[-lookback] if len(rsi_series) > lookback else rsi_now

        price_up = price_now > price_prev * 1.02
        rsi_down = rsi_now < rsi_prev - 3

        if price_up and rsi_down:
            divergences.append({
                "type": "RSI Bearish Divergence",
                "severity": "HIGH",
                "detail": f"Price +{round((price_now/price_prev-1)*100,1)}% but RSI fell {round(rsi_prev-rsi_now,1)} pts — momentum fading"
            })

        # MACD divergence: price higher, MACD histogram lower
        macd_now  = indicators.get("macd_hist", 0)
        if price_up and macd_now < -0.01:
            divergences.append({
                "type": "MACD Bearish Divergence",
                "severity": "HIGH",
                "detail": "Price rising but MACD histogram negative — trend exhaustion"
            })

        # Volume divergence: price up on falling volume = weak move
        vol_ratio = indicators.get("volume_ratio", 1)
        if price_up and vol_ratio < 0.8:
            divergences.append({
                "type": "Volume Divergence",
                "severity": "MEDIUM",
                "detail": f"Price rising on {vol_ratio}x avg volume — no institutional conviction"
            })

        results["divergences"] = {
            "found": divergences,
            "count": len(divergences),
            "bearish": len(divergences) > 0,
        }
    except Exception as e:
        results["divergences"] = {"found": [], "count": 0, "bearish": False}

    # ─────────────────────────────────────────────
    # 4. DISTRIBUTION PATTERN (Wyckoff — smart money selling)
    # Price range tightening near highs + volume declining
    # ─────────────────────────────────────────────
    try:
        recent_highs = highs.iloc[-10:]
        recent_lows  = lows.iloc[-10:]
        recent_vols  = volumes.iloc[-10:]
        avg_vol_20   = volumes.iloc[-20:].mean()

        price_range  = (recent_highs - recent_lows).mean()
        full_range   = (highs.iloc[-60:] - lows.iloc[-60:]).mean()
        range_pct    = price_range / (full_range + 1e-9)

        vol_declining = recent_vols.mean() < avg_vol_20 * 0.85
        near_high     = price > closes.iloc[-20:].max() * 0.97
        tight_range   = range_pct < 0.7

        distribution_score = sum([
            2 if vol_declining else 0,
            2 if near_high else 0,
            1 if tight_range else 0,
        ])

        dist_signal = "TOPPING" if distribution_score >= 4 else                       "WARNING" if distribution_score >= 2 else "NEUTRAL"

        results["distribution"] = {
            "score":          distribution_score,
            "signal":         dist_signal,
            "vol_declining":  vol_declining,
            "near_high":      near_high,
            "tight_range":    tight_range,
            "avg_range_ratio":round(range_pct, 2),
        }
    except Exception as e:
        results["distribution"] = {"signal": "UNKNOWN", "score": 0}

    # ─────────────────────────────────────────────
    # 5. PARABOLIC SAR (trailing stop — acceleration model)
    # When price crosses below SAR = trend reversal signal
    # ─────────────────────────────────────────────
    try:
        psar, trend = _calc_psar(highs.values, lows.values, closes.values)
        psar_now    = round(psar, 2)
        psar_trend  = "BULLISH" if trend == 1 else "BEARISH"
        dist_to_sar = round(((price - psar_now) / price) * 100, 2)

        results["parabolic_sar"] = {
            "sar":       psar_now,
            "trend":     psar_trend,
            "dist_pct":  dist_to_sar,
            "signal":    "HOLD" if trend == 1 and dist_to_sar > 2 else
                         "NEAR_STOP" if trend == 1 and dist_to_sar <= 2 else
                         "SELL_NOW",
        }
    except Exception as e:
        results["parabolic_sar"] = {"signal": "UNKNOWN", "sar": None}

    # ─────────────────────────────────────────────
    # 6. STOCHASTIC OSCILLATOR (overbought + bearish cross)
    # ─────────────────────────────────────────────
    try:
        k, d = _calc_stochastic(highs, lows, closes, k_period=14, d_period=3)
        stoch_signal = "OVERBOUGHT_SELL" if k > 80 and k < d else                        "OVERBOUGHT"      if k > 80 else                        "OVERSOLD_BUY"    if k < 20 and k > d else                        "OVERSOLD"        if k < 20 else "NEUTRAL"
        results["stochastic"] = {
            "k": round(k, 1), "d": round(d, 1),
            "signal": stoch_signal,
            "bearish_cross": k < d and k > 70,
        }
    except Exception as e:
        results["stochastic"] = {"k": 50, "d": 50, "signal": "NEUTRAL"}

    # ─────────────────────────────────────────────
    # 7. RATE OF CHANGE DECELERATION
    # Momentum losing steam = early warning before reversal
    # ─────────────────────────────────────────────
    try:
        roc5  = ((closes.iloc[-1] / closes.iloc[-6])  - 1) * 100
        roc10 = ((closes.iloc[-1] / closes.iloc[-11]) - 1) * 100
        roc20 = ((closes.iloc[-1] / closes.iloc[-21]) - 1) * 100

        # Deceleration: short-term ROC < medium-term ROC (momentum slowing)
        decelerating = roc5 < roc10 * 0.5 and roc10 > 0

        results["rate_of_change"] = {
            "roc_5d":        round(roc5, 2),
            "roc_10d":       round(roc10, 2),
            "roc_20d":       round(roc20, 2),
            "decelerating":  decelerating,
            "signal":        "DECELERATING" if decelerating and roc5 < 1 else
                             "STRONG"       if roc5 > 3 else
                             "WEAKENING"    if roc5 < roc20 else "NORMAL",
        }
    except Exception as e:
        results["rate_of_change"] = {"signal": "UNKNOWN"}

    # ─────────────────────────────────────────────
    # 8. COMPOSITE EXIT SCORE & OPTIMAL SELL PRICE
    # ─────────────────────────────────────────────
    try:
        exit_score = 0
        exit_reasons = []

        # RSI overbought
        rsi = indicators.get("rsi", 50)
        if rsi > 75:   exit_score += 25; exit_reasons.append(f"RSI extremely overbought ({rsi})")
        elif rsi > 65: exit_score += 15; exit_reasons.append(f"RSI overbought ({rsi})")
        elif rsi > 55: exit_score += 5

        # Divergences
        div_count = results.get("divergences", {}).get("count", 0)
        exit_score += div_count * 20
        for d in results.get("divergences", {}).get("found", []):
            exit_reasons.append(d["type"] + ": " + d["detail"])

        # Distribution
        dist = results.get("distribution", {})
        if dist.get("signal") == "TOPPING":
            exit_score += 25; exit_reasons.append("Wyckoff distribution: topping pattern")
        elif dist.get("signal") == "WARNING":
            exit_score += 12; exit_reasons.append("Distribution warning: volume declining at highs")

        # Parabolic SAR
        psar_sig = results.get("parabolic_sar", {}).get("signal", "")
        if psar_sig == "SELL_NOW":   exit_score += 20; exit_reasons.append("Parabolic SAR: trend reversal triggered")
        elif psar_sig == "NEAR_STOP": exit_score += 10; exit_reasons.append("Parabolic SAR: price near stop level")

        # Stochastic
        stoch = results.get("stochastic", {})
        if stoch.get("signal") == "OVERBOUGHT_SELL":
            exit_score += 20; exit_reasons.append(f"Stochastic bearish cross at overbought (K={stoch.get("k")})")
        elif stoch.get("signal") == "OVERBOUGHT":
            exit_score += 10; exit_reasons.append(f"Stochastic overbought (K={stoch.get("k")})")

        # ROC deceleration
        roc = results.get("rate_of_change", {})
        if roc.get("signal") == "DECELERATING":
            exit_score += 15; exit_reasons.append("Momentum decelerating — move losing steam")
        elif roc.get("signal") == "WEAKENING":
            exit_score += 8

        # Institutional: Smart money distributing
        smi = indicators.get("smi_signal", "")
        if smi == "DISTRIBUTING":
            exit_score += 20; exit_reasons.append("Smart Money: institutions distributing/selling")

        # Z-score overbought
        z = indicators.get("zscore", 0)
        if z > 2:    exit_score += 15; exit_reasons.append(f"Z-score overbought ({z}σ above mean)")
        elif z > 1.5: exit_score += 8

        # Near Fibonacci resistance
        fib = results.get("fibonacci", {})
        if fib.get("nearest_resistance"):
            dist_to_res = (fib["nearest_resistance"] - price) / price * 100
            if dist_to_res < 1.5:
                exit_score += 15; exit_reasons.append(("Within 1.5% of Fibonacci resistance $" + str(fib.get("nearest_resistance",""))))
            elif dist_to_res < 3:
                exit_score += 8; exit_reasons.append(f"Approaching Fibonacci resistance ${fib.get("nearest_resistance","")}")

        # Determine urgency
        if exit_score >= 70:
            urgency = "SELL NOW"
            urgency_color = "#ff1744"
        elif exit_score >= 45:
            urgency = "PREPARE TO SELL"
            urgency_color = "#ff6d00"
        elif exit_score >= 25:
            urgency = "WATCH CLOSELY"
            urgency_color = "#ffd600"
        else:
            urgency = "HOLD — NO TOP YET"
            urgency_color = "#00e676"

        # Compute optimal sell price range
        # Use Fibonacci + resistance + SAR to define the zone
        targets = []
        if fib.get("nearest_resistance"): targets.append(fib["nearest_resistance"])
        if results.get("resistance", {}).get("nearest_target"): targets.append(results["resistance"]["nearest_target"])
        if results.get("parabolic_sar", {}).get("sar"): targets.append(results["parabolic_sar"]["sar"] * 1.005)

        targets = sorted([t for t in targets if t > price and t < price * 1.25])

        optimal_sell_low  = round(targets[0], 2) if targets else round(price * 1.02, 2)
        optimal_sell_high = round(targets[1] if len(targets) > 1 else targets[0] * 1.015 if targets else price * 1.04, 2)

        # Stop loss suggestion (2% below SAR or 3% below current)
        sar_val = results.get("parabolic_sar", {}).get("sar")
        stop_loss = round(sar_val * 0.995 if sar_val and sar_val < price else price * 0.97, 2)

        # ══════════════════════════════════════════════════════════════
        # 3-TRANCHE SELL PLAN
        # Mirror of the buy tranche plan — staged exits to capture
        # maximum upside without leaving money on the table.
        #
        # Core philosophy:
        #   T1 — Sell into first strength (lock in profit, reduce risk)
        #   T2 — Sell at primary resistance (where price usually stalls)
        #   T3 — Final tranche at extension target (if trend continues)
        #
        # Never sell all at once — markets always squeeze a bit higher
        # after you think the top is in. Staged exits capture that.
        # ══════════════════════════════════════════════════════════════
        sell_tranche_plan = []
        try:
            # ── Collect all resistance targets above price ──
            res_above   = results.get("resistance", {}).get("levels_above", [])
            fib_levels  = results.get("fibonacci", {}).get("levels", {})
            call_walls  = [cw.get("strike") for cw in inst_models.get("call_walls", [])
                           if isinstance(cw, dict) and cw.get("strike", 0) > price] if inst_models else []

            # Fib extension targets (profit targets above swing high)
            fib_ext_127 = fib_levels.get("127.2%")
            fib_ext_162 = fib_levels.get("161.8%")
            fib_61      = fib_levels.get("61.8%")  # retrace level now as potential ceiling

            # ── T1: First resistance / initial profit lock ──
            # Nearest level: first resistance OR 2% above price
            t1_candidates = sorted([r for r in [
                res_above[0] if res_above else None,
                fib_ext_127 if fib_ext_127 and fib_ext_127 > price else None,
                round(price * 1.03, 2),   # minimum 3% gain
            ] if r and r > price * 1.005])
            t1_price = round(t1_candidates[0], 2) if t1_candidates else round(price * 1.03, 2)

            # ── T2: Primary resistance / main target ──
            t2_candidates = sorted([r for r in [
                res_above[1] if len(res_above) > 1 else None,
                res_above[0] if res_above and res_above[0] > t1_price * 1.01 else None,
                fib_ext_127  if fib_ext_127 and fib_ext_127 > t1_price * 1.01 else None,
                call_walls[0] if call_walls else None,
                round(price * 1.06, 2),
            ] if r and r > t1_price * 1.005])
            t2_price = round(t2_candidates[0], 2) if t2_candidates else round(t1_price * 1.03, 2)

            # ── T3: Extension target — let the winner run ──
            t3_candidates = sorted([r for r in [
                res_above[2] if len(res_above) > 2 else None,
                fib_ext_162  if fib_ext_162 and fib_ext_162 > t2_price * 1.01 else None,
                call_walls[1] if len(call_walls) > 1 else None,
                round(price * 1.12, 2),
            ] if r and r > t2_price * 1.005])
            t3_price = round(t3_candidates[0], 2) if t3_candidates else round(t2_price * 1.04, 2)

            # ── Scale tranche sizes by exit score ──
            # Low score (25–44): conservative — sell more early
            # Med score (45–64): balanced — standard 40/35/25
            # High score (65+):  aggressive — hold more for bigger target
            if exit_score >= 65:
                t1_pct, t2_pct, t3_pct = 30, 40, 30   # hold more for the big move
                t1_label = "Initial Trim"
            elif exit_score >= 45:
                t1_pct, t2_pct, t3_pct = 40, 35, 25   # balanced
                t1_label = "Lock Profit"
            else:
                t1_pct, t2_pct, t3_pct = 50, 35, 15   # conservative — capture what's there
                t1_label = "Early Exit"

            # ── Profit % for each tranche ──
            t1_gain = round((t1_price / price - 1) * 100, 1)
            t2_gain = round((t2_price / price - 1) * 100, 1)
            t3_gain = round((t3_price / price - 1) * 100, 1)

            # ── Trailing stop that ratchets up with each tranche ──
            trail_t1 = round(t1_price * 0.97, 2)   # -3% from T1
            trail_t2 = round(t2_price * 0.965, 2)  # -3.5% from T2
            trail_t3 = round(t3_price * 0.96, 2)   # -4% from T3

            sell_tranche_plan = [
                {
                    "number":      1,
                    "label":       t1_label,
                    "pct_holding": t1_pct,
                    "price":       t1_price,
                    "gain_pct":    t1_gain,
                    "trailing_stop": trail_t1,
                    "color":       "#ffd600",
                    "trigger":     f"Price reaches ${t1_price} (+{t1_gain}%)",
                    "rationale":   f"Sell {t1_pct}% of position — lock in profit, eliminate stress, keep {100-t1_pct}% for upside",
                    "resistance_source": "1st resistance" if res_above else "Fib extension",
                    "new_stop":    stop_loss,
                },
                {
                    "number":      2,
                    "label":       "Main Target",
                    "pct_holding": t2_pct,
                    "price":       t2_price,
                    "gain_pct":    t2_gain,
                    "trailing_stop": trail_t2,
                    "color":       "#ff6d00",
                    "trigger":     f"Price reaches ${t2_price} (+{t2_gain}%)",
                    "rationale":   f"Sell {t2_pct}% more — primary resistance zone, historically where rallies pause",
                    "resistance_source": "2nd resistance / call wall",
                    "new_stop":    trail_t1,
                },
                {
                    "number":      3,
                    "label":       "Let It Run",
                    "pct_holding": t3_pct,
                    "price":       t3_price,
                    "gain_pct":    t3_gain,
                    "trailing_stop": trail_t3,
                    "color":       "#ff1744",
                    "trigger":     f"Price reaches ${t3_price} (+{t3_gain}%)",
                    "rationale":   f"Sell final {t3_pct}% — Fibonacci extension / maximum greed zone. Trailing stop at ${trail_t2}",
                    "resistance_source": "Fib 161.8% / 3rd resistance",
                    "new_stop":    trail_t2,
                },
            ]

            # Blended average exit price (weighted by tranche size)
            avg_exit = round(
                (t1_price * t1_pct + t2_price * t2_pct + t3_price * t3_pct) /
                (t1_pct + t2_pct + t3_pct), 2
            )
            avg_gain = round((avg_exit / price - 1) * 100, 1)

        except Exception as e:
            print(f"  ⚠️ Sell tranche error: {e}")
            avg_exit = optimal_sell_high
            avg_gain = round((optimal_sell_high / price - 1) * 100, 1) if price > 0 else 0

        results["exit_analysis"] = {
            "exit_score":        exit_score,
            "urgency":           urgency,
            "urgency_color":     urgency_color,
            "exit_reasons":      exit_reasons,
            "optimal_sell_low":  optimal_sell_low,
            "optimal_sell_high": optimal_sell_high,
            "stop_loss":         stop_loss,
            "current_price":     round(price, 2),
            "upside_to_target":  round((optimal_sell_low - price) / price * 100, 1),
            # ── Sell tranche plan ──
            "sell_tranches":     sell_tranche_plan,
            "avg_exit_price":    avg_exit,
            "avg_gain_pct":      avg_gain,
            "resistance_above":  res_above[:4] if 'res_above' in dir() else [],
        }

    except Exception as e:
        results["exit_analysis"] = {"exit_score": 0, "urgency": "UNKNOWN", "exit_reasons": [str(e)]}

    return results


# ── Helper: RSI series ──
def _calc_rsi_series(prices, period=14):
    delta = prices.diff()
    gain  = delta.where(delta > 0, 0).rolling(period).mean()
    loss  = -delta.where(delta < 0, 0).rolling(period).mean()
    rs    = gain / (loss + 1e-9)
    return 100 - (100 / (1 + rs))


# ── Helper: Parabolic SAR ──
def _calc_psar(highs, lows, closes, af_start=0.02, af_max=0.2):
    n      = len(closes)
    trend  = 1       # 1=bull, -1=bear
    af     = af_start
    ep     = lows[0]
    psar   = highs[0]
    for i in range(2, n):
        if trend == 1:
            psar = psar + af * (ep - psar)
            psar = min(psar, lows[i-1], lows[i-2])
            if lows[i] < psar:
                trend = -1; psar = ep; ep = highs[i]; af = af_start
            else:
                if highs[i] > ep:
                    ep = highs[i]; af = min(af + af_start, af_max)
        else:
            psar = psar + af * (ep - psar)
            psar = max(psar, highs[i-1], highs[i-2])
            if highs[i] > psar:
                trend = 1; psar = ep; ep = lows[i]; af = af_start
            else:
                if lows[i] < ep:
                    ep = lows[i]; af = min(af + af_start, af_max)
    return psar, trend


# ── Helper: Stochastic Oscillator ──
def _calc_stochastic(highs, lows, closes, k_period=14, d_period=3):
    low_min  = lows.rolling(k_period).min()
    high_max = highs.rolling(k_period).max()
    k_raw    = 100 * (closes - low_min) / (high_max - low_min + 1e-9)
    k        = k_raw.rolling(d_period).mean()
    d        = k.rolling(d_period).mean()
    return float(k.iloc[-1]), float(d.iloc[-1])


# ═══════════════════════════════════════════════════════════════
#  MARKET MAKER ENGINE
#  How MMs actually move TSLA — options flow, gamma, pinning
# ═══════════════════════════════════════════════════════════════
#
#  Market makers (Citadel Securities, Virtu, Susquehanna) profit
#  from the bid-ask spread but MUST hedge their options exposure.
#  This creates entirely predictable buying/selling pressure:
#
#  GEX > 0  → MMs are LONG gamma → they SELL into rallies, BUY dips
#             = price gets PINNED, low volatility
#  GEX < 0  → MMs are SHORT gamma → they CHASE the move
#             = price ACCELERATES, high volatility, trending market
#
#  Max Pain  → Strike where options writers profit most
#             = price tends to GRAVITATE here into expiration
#
#  Dark Pool → Large off-exchange blocks = institutional entry/exit
#             = often acts as support/resistance next day


# ═══════════════════════════════════════════════════════════════
#  UNUSUAL OPTIONS ACTIVITY ENGINE (UOA)
#
#  What professional flow desks watch every day:
#
#  1. Volume / OI Ratio — fresh bets vs existing positions
#     Vol/OI > 5×  = UNUSUAL  (someone opened a new position)
#     Vol/OI > 10× = VERY UNUSUAL (aggressive/urgent)
#     Vol/OI > 20× = EXTREME (whale sweep)
#
#  2. Premium Spent — total dollars flowing into a strike
#     Volume × Last Price × 100 = premium dollar value
#     >$500K on a single strike = institutional size
#     >$2M = whale-level conviction
#
#  3. Call vs Put Flow Bias — net directional sentiment
#     Where is the smart money betting? Calls or puts?
#     Net call premium > net put premium = bullish flow
#
#  4. OI Change — fresh opens vs rolls
#     Volume >> OI means brand new position (not a roll)
#     This is the key signal — new money, new bet
#
#  5. Strike Sweep Detection — price/time clustering
#     Same strike printing high volume = sweep in progress
#     Sweeps are aggressive — trader paid market, didn't wait
#
#  Data source: yfinance options chain (volume + OI per strike)
#  Refreshes every analysis cycle with live chain
# ═══════════════════════════════════════════════════════════════

def calculate_unusual_options_activity(ticker_symbol, current_price):
    """
    Scans the full options chain across nearest 4 expiries.
    Returns:
    - unusual_calls: list of unusually active call strikes
    - unusual_puts:  list of unusually active put strikes
    - top_sweeps:    highest-conviction directional bets
    - net_flow:      BULLISH / BEARISH / NEUTRAL (net premium flow)
    - flow_score:    0–100 conviction of directional flow
    - whale_alerts:  strikes with >$1M premium in single expiry
    - total_call_premium: total $ flowing into calls
    - total_put_premium:  total $ flowing into puts
    - uoa_signal:    summary signal for dashboard
    """
    result = {
        "unusual_calls":       [],
        "unusual_puts":        [],
        "top_sweeps":          [],
        "whale_alerts":        [],
        "net_flow":            "NEUTRAL",
        "flow_score":          0,
        "flow_color":          "var(--text-dim)",
        "total_call_premium":  0,
        "total_put_premium":   0,
        "net_premium":         0,
        "call_put_premium_ratio": None,
        "most_active_strike":  None,
        "most_active_expiry":  None,
        "uoa_signal":          "NO UNUSUAL ACTIVITY",
        "uoa_reasons":         [],
        "strike_heatmap":      [],  # for chart display
        "expiries_scanned":    0,
        "total_unusual":       0,
    }

    try:
        import math
        tkr      = yf.Ticker(ticker_symbol)
        print(f"  [UOA] Fetching options for {ticker_symbol}...", flush=True)
        expiries = tkr.options
        if not expiries:
            print(f"  [UOA] tkr.options empty/None for {ticker_symbol}", flush=True)
            result["uoa_signal"] = "NO OPTIONS DATA"
            return result
        print(f"  [UOA] Got {len(expiries)} expiries: {list(expiries)[:3]}", flush=True)

        # Scan nearest 4 expiries — captures weekly and monthly flow
        # Detect if market is closed (volume will be 0)
        _after_hours_mode = False
        try:
            _test_chain = tkr.option_chain(expiries[0])
            _test_vol = _test_chain.calls["volume"].sum() + _test_chain.puts["volume"].sum()
            _after_hours_mode = (_test_vol == 0)
            if _after_hours_mode: print(f"  [UOA] After-hours mode — using OI-based detection", flush=True)
        except: pass
        scan_expiries = expiries[:4]
        result["expiries_scanned"] = len(scan_expiries)

        all_unusual   = []   # all flagged strikes across expiries
        whale_alerts  = []
        heatmap       = {}   # strike → {call_premium, put_premium, call_vol_oi, put_vol_oi}
        total_call_prem = 0
        total_put_prem  = 0

        today      = datetime.now().date()
        price_lo   = current_price * 0.75    # scan ±25% of current price
        price_hi   = current_price * 1.25

        for exp in scan_expiries:
            try:
                exp_date   = datetime.strptime(exp, "%Y-%m-%d").date()
                dte        = max((exp_date - today).days, 0)
                chain      = tkr.option_chain(exp)
                calls      = chain.calls
                puts       = chain.puts

                # Filter to relevant strikes
                calls = calls[
                    (calls["strike"] >= price_lo) &
                    (calls["strike"] <= price_hi) &
                    (calls["volume"].fillna(0) > 0)
                ].copy()
                puts = puts[
                    (puts["strike"] >= price_lo) &
                    (puts["strike"] <= price_hi) &
                    (puts["volume"].fillna(0) > 0)
                ].copy()

                # ── CALLS — scan for unusual volume ──
                for _, row in calls.iterrows():
                    strike   = float(row["strike"])
                    volume   = float(0 if (row["volume"] != row["volume"]) else (row["volume"] or 0))
                    oi       = float(row["openInterest"]  or 1)
                    iv       = float(row["impliedVolatility"] or 0.3) * 100
                    last     = float(0 if (row["lastPrice"] != row["lastPrice"]) else (row["lastPrice"] or 0))
                    bid      = float(row.get("bid", last) or last)
                    ask      = float(row.get("ask", last) or last)
                    mid      = (bid + ask) / 2 if ask > 0 else last
                    moneyness = "ITM" if strike < current_price else "ATM" if abs(strike - current_price)/current_price < 0.02 else "OTM"

                    vol_oi_ratio = volume / max(oi, 1)
                    eff_vol        = volume if volume > 0 else 0
                    premium_usd    = eff_vol * mid * 100 if eff_vol > 0 else oi * mid * 100 * 0.10
                    oi_size_flag   = (oi * mid * 100) >= 500_000
                    total_call_prem += premium_usd

                    # Update heatmap
                    s = round(strike)
                    heatmap.setdefault(s, {"call_premium":0,"put_premium":0,"call_vol_oi":0,"put_vol_oi":0})
                    heatmap[s]["call_premium"]  += premium_usd
                    heatmap[s]["call_vol_oi"]    = max(heatmap[s]["call_vol_oi"], vol_oi_ratio)

                    # Whale check: >$500K on single strike/expiry OR large OI position
                    _whale_thresh = 200_000 if _after_hours_mode else 500_000
                    if premium_usd >= _whale_thresh or (volume == 0 and oi_size_flag):
                        whale_alerts.append({
                            "type":        "CALL",
                            "strike":      strike,
                            "expiry":      exp,
                            "dte":         dte,
                            "volume":      int(volume or 0),
                            "oi":          int(oi or 0),
                            "vol_oi":      round(vol_oi_ratio, 1),
                            "premium_usd":   round(premium_usd),
                            "premium_fmt": f"${premium_usd/1e6:.2f}M" if premium_usd >= 1e6 else f"${premium_usd/1e3:.0f}K",
                            "iv":          round(iv, 1),
                            "moneyness":   moneyness,
                            "mid":         round(mid, 2),
                            "direction":   "BULLISH",
                            "severity":    "WHALE" if premium_usd >= 2_000_000 else "LARGE",
                        })

                    # Unusual: vol/OI ≥ 5×
                    if vol_oi_ratio >= 5 or (volume == 0 and oi_size_flag):
                        all_unusual.append({
                            "type":        "CALL",
                            "strike":      strike,
                            "expiry":      exp,
                            "dte":         dte,
                            "volume":      int(volume or 0),
                            "oi":          int(oi or 0),
                            "vol_oi":      round(vol_oi_ratio, 1),
                            "premium_usd":   round(premium_usd),
                            "premium_fmt": f"${premium_usd/1e6:.2f}M" if premium_usd >= 1e6 else f"${premium_usd/1e3:.0f}K",
                            "iv":          round(iv, 1),
                            "moneyness":   moneyness,
                            "mid":         round(mid, 2),
                            "direction":   "BULLISH",
                            "severity":    (
                                "EXTREME"  if vol_oi_ratio >= 20 else
                                "VERY HIGH" if vol_oi_ratio >= 10 else
                                "HIGH"
                            ),
                        })

                # ── PUTS — scan for unusual volume ──
                for _, row in puts.iterrows():
                    strike   = float(row["strike"])
                    volume   = float(0 if (row["volume"] != row["volume"]) else (row["volume"] or 0))
                    oi       = float(row["openInterest"]  or 1)
                    iv       = float(row["impliedVolatility"] or 0.3) * 100
                    last     = float(0 if (row["lastPrice"] != row["lastPrice"]) else (row["lastPrice"] or 0))
                    bid      = float(row.get("bid", last) or last)
                    ask      = float(row.get("ask", last) or last)
                    mid      = (bid + ask) / 2 if ask > 0 else last
                    moneyness = "ITM" if strike > current_price else "ATM" if abs(strike - current_price)/current_price < 0.02 else "OTM"

                    vol_oi_ratio = volume / max(oi, 1)
                    eff_vol        = volume if volume > 0 else 0
                    premium_usd    = eff_vol * mid * 100 if eff_vol > 0 else oi * mid * 100 * 0.10
                    oi_size_flag   = (oi * mid * 100) >= 500_000
                    total_put_prem += premium_usd

                    # Update heatmap
                    s = round(strike)
                    heatmap.setdefault(s, {"call_premium":0,"put_premium":0,"call_vol_oi":0,"put_vol_oi":0})
                    heatmap[s]["put_premium"] += premium_usd
                    heatmap[s]["put_vol_oi"]   = max(heatmap[s]["put_vol_oi"], vol_oi_ratio)

                    _whale_thresh = 200_000 if _after_hours_mode else 500_000
                    if premium_usd >= _whale_thresh or (volume == 0 and oi_size_flag):
                        whale_alerts.append({
                            "type":        "PUT",
                            "strike":      strike,
                            "expiry":      exp,
                            "dte":         dte,
                            "volume":      int(volume or 0),
                            "oi":          int(oi or 0),
                            "vol_oi":      round(vol_oi_ratio, 1),
                            "premium_usd":   round(premium_usd),
                            "premium_fmt": f"${premium_usd/1e6:.2f}M" if premium_usd >= 1e6 else f"${premium_usd/1e3:.0f}K",
                            "iv":          round(iv, 1),
                            "moneyness":   moneyness,
                            "mid":         round(mid, 2),
                            "direction":   "BEARISH",
                            "severity":    "WHALE" if premium_usd >= 2_000_000 else "LARGE",
                        })

                    if vol_oi_ratio >= 5 or (volume == 0 and oi_size_flag):
                        all_unusual.append({
                            "type":        "PUT",
                            "strike":      strike,
                            "expiry":      exp,
                            "dte":         dte,
                            "volume":      int(volume or 0),
                            "oi":          int(oi or 0),
                            "vol_oi":      round(vol_oi_ratio, 1),
                            "premium_usd":   round(premium_usd),
                            "premium_fmt": f"${premium_usd/1e6:.2f}M" if premium_usd >= 1e6 else f"${premium_usd/1e3:.0f}K",
                            "iv":          round(iv, 1),
                            "moneyness":   moneyness,
                            "mid":         round(mid, 2),
                            "direction":   "BEARISH",
                            "severity":    (
                                "EXTREME"  if vol_oi_ratio >= 20 else
                                "VERY HIGH" if vol_oi_ratio >= 10 else
                                "HIGH"
                            ),
                        })

            except Exception as e:
                print(f"  ⚠️ UOA chain error ({exp}): {e}")
                continue

        # ── Sort and classify ──
        all_unusual.sort(key=lambda x: -x["vol_oi"])
        whale_alerts.sort(key=lambda x: -x["premium_usd"])

        result["unusual_calls"]      = [u for u in all_unusual if u["type"] == "CALL"][:10]
        result["unusual_puts"]       = [u for u in all_unusual if u["type"] == "PUT"][:10]
        result["whale_alerts"]       = whale_alerts[:8]
        result["total_unusual"]      = len(all_unusual)
        result["total_call_premium"] = round(total_call_prem)
        result["total_put_premium"]  = round(total_put_prem)
        result["net_premium"]        = round(total_call_prem - total_put_prem)

        # Top sweeps = unusual with highest premium
        top_sweeps = sorted(all_unusual, key=lambda x: -x["premium_usd"])[:6]
        result["top_sweeps"] = top_sweeps

        # Most active strike
        if heatmap:
            best_strike = max(heatmap, key=lambda s: heatmap[s]["call_premium"] + heatmap[s]["put_premium"])
            result["most_active_strike"] = best_strike

        # ── Net Flow Direction ──
        net = total_call_prem - total_put_prem
        total_prem = total_call_prem + total_put_prem

        if total_prem > 0:
            call_pct = total_call_prem / total_prem * 100
            result["call_put_premium_ratio"] = round(call_pct, 1)

            if call_pct >= 70:
                result["net_flow"]   = "STRONGLY BULLISH"
                result["flow_color"] = "#00ff88"
                result["flow_score"] = min(int((call_pct - 50) * 2), 100)
            elif call_pct >= 58:
                result["net_flow"]   = "BULLISH"
                result["flow_color"] = "#69f0ae"
                result["flow_score"] = int((call_pct - 50) * 1.5)
            elif call_pct <= 30:
                result["net_flow"]   = "STRONGLY BEARISH"
                result["flow_color"] = "#ff1744"
                result["flow_score"] = min(int((50 - call_pct) * 2), 100)
            elif call_pct <= 42:
                result["net_flow"]   = "BEARISH"
                result["flow_color"] = "#ff6d00"
                result["flow_score"] = int((50 - call_pct) * 1.5)
            else:
                result["net_flow"]   = "NEUTRAL"
                result["flow_color"] = "var(--text-dim)"
                result["flow_score"] = 0

        # ── Strike Heatmap for chart ──
        result["strike_heatmap"] = sorted([
            {
                "strike":       s,
                "call_premium": round(v["call_premium"]),
                "put_premium":  round(v["put_premium"]),
                "call_vol_oi":  round(v["call_vol_oi"], 1),
                "put_vol_oi":   round(v["put_vol_oi"], 1),
                "net":          round(v["call_premium"] - v["put_premium"]),
            }
            for s, v in heatmap.items()
            if v["call_premium"] + v["put_premium"] > 10_000  # filter noise
        ], key=lambda x: x["strike"])

        # ── UOA Signal ──
        whale_count = len(whale_alerts)
        extreme_count = sum(1 for u in all_unusual if u["severity"] == "EXTREME")
        call_whales = sum(1 for w in whale_alerts if w["type"] == "CALL")
        put_whales  = sum(1 for w in whale_alerts if w["type"] == "PUT")

        reasons = []
        if whale_count > 0:
            reasons.append(("🐋 "+str(whale_count)+" whale trade"+("s" if whale_count>1 else "")+" detected (>"+(" ".join(set(w["premium_fmt"] for w in whale_alerts[:2])))+" premium)"))
        if extreme_count > 0:
            reasons.append(f"⚡ {extreme_count} strike(s) with vol/OI > 20× — aggressive sweep in progress")
        if len(all_unusual) >= 5:
            reasons.append(f"📊 {len(all_unusual)} strikes showing unusual volume across {len(scan_expiries)} expiries")
        if call_whales > put_whales and call_whales > 0:
            reasons.append(f"🟢 Call whales dominating — {call_whales} large call bets vs {put_whales} put bets")
        elif put_whales > call_whales and put_whales > 0:
            reasons.append(f"🔴 Put whales dominating — {put_whales} large put bets vs {call_whales} call bets")
        if total_prem > 5_000_000:
            reasons.append(f"💰 Total premium flow: ${total_prem/1e6:.1f}M (calls ${total_call_prem/1e6:.1f}M / puts ${total_put_prem/1e6:.1f}M)")

        result["uoa_reasons"] = reasons

        if whale_count >= 2 or extreme_count >= 1:
            mkt_note = " (OI-BASED)" if _after_hours_mode else ""
            _nf = result["net_flow"]
            result["uoa_signal"] = f"🚨 WHALE ACTIVITY DETECTED{mkt_note} — {_nf}"
        elif len(all_unusual) >= 5:
            result["uoa_signal"] = f"⚡ UNUSUAL SWEEP FLOW — {result.get("net_flow","")}"
        elif len(all_unusual) >= 2:
            result["uoa_signal"] = ("👁 ELEVATED ACTIVITY — " + str(result.get("net_flow","")))
        else:
            result["uoa_signal"] = f"✅ NORMAL — {result.get("net_flow","")}"

        fmt_net = f"${abs(net)/1e6:.2f}M" if abs(net) >= 1e6 else f"${abs(net)/1e3:.0f}K"
        direction = "CALL" if net > 0 else "PUT"
        print(f"  🔍 UOA: {len(all_unusual)} unusual | {whale_count} whales | Net flow: {result.get("net_flow","")} ({direction} heavy by {fmt_net})")

    except Exception as e:
        print(f"  ❌ UOA error: {e}")
        import traceback; traceback.print_exc()
        result["uoa_signal"] = f"ERROR: {str(e)[:40]}"

    return result



def calculate_market_maker_data(ticker_symbol, current_price):
    """
    Fetches live options chain from Yahoo Finance and computes:
    - GEX (Gamma Exposure) per strike
    - Net GEX (positive = pinning, negative = trending)
    - Max Pain strike
    - Put/Call OI ratio
    - Key dealer hedging levels
    - IV rank + term structure
    - 0DTE risk flag
    """
    result = {
        "gex_total":        0,
        "gex_signal":       "UNKNOWN",
        "max_pain":         None,
        "pc_ratio":         None,
        "iv_rank":          None,
        "iv_signal":        "UNKNOWN",
        "nearest_expiry":   None,
        "dealer_walls":     [],
        "call_walls":       [],
        "put_walls":        [],
        "gex_by_strike":    [],
        "oi_by_strike":     [],
        "zero_dte_risk":    False,
        "pin_risk":         False,
        "hedging_pressure": "NEUTRAL",
        "summary":          "",
        "expiries_analyzed":0,
    }

    try:
        tkr = yf.Ticker(ticker_symbol)

        # ── Get options expiry dates ──
        expiries = tkr.options
        if not expiries:
            result["summary"] = "No options data available"
            return result

        result["expiries_analyzed"] = len(expiries)
        result["nearest_expiry"]    = expiries[0]

        # Check 0DTE risk (expiry is today or tomorrow)
        today = datetime.now().date()
        try:
            exp_date = datetime.strptime(expiries[0], "%Y-%m-%d").date()
            days_to_exp = (exp_date - today).days
            result["zero_dte_risk"] = days_to_exp <= 1
            result["days_to_expiry"] = days_to_exp
        except Exception:
            result["days_to_expiry"] = 999

        # ── Aggregate across nearest 3 expiries ──
        total_call_oi = 0
        total_put_oi  = 0
        iv_list       = []
        gex_map       = {}   # strike → net_gex
        oi_map        = {}   # strike → {call_oi, put_oi}
        max_pain_map  = {}   # strike → total pain

        for exp in expiries[:3]:
            try:
                chain  = tkr.option_chain(exp)
                calls  = chain.calls
                puts   = chain.puts

                # Filter to strikes within 20% of current price (relevant range)
                lo, hi = current_price * 0.80, current_price * 1.20
                calls  = calls[(calls["strike"] >= lo) & (calls["strike"] <= hi)]
                puts   = puts[ (puts["strike"]  >= lo) & (puts["strike"]  <= hi)]

                total_call_oi += calls["openInterest"].fillna(0).sum()
                total_put_oi  += puts["openInterest"].fillna(0).sum()

                # Collect IVs
                iv_list.extend(calls["impliedVolatility"].dropna().tolist())
                iv_list.extend(puts["impliedVolatility"].dropna().tolist())

                # GEX per strike:
                # GEX = OI × Gamma × 100 × Spot²
                # Calls: dealer is SHORT calls → LONG gamma → positive GEX
                # Puts:  dealer is LONG puts   → SHORT gamma → negative GEX
                # (Assumes dealer sold calls and bought puts — typical retail flow)
                for _, row in calls.iterrows():
                    s   = round(float(row["strike"]), 0)
                    oi  = float(0 if (row["openInterest"] != row["openInterest"]) else (row["openInterest"] or 0))
                    # Approximate gamma from IV + moneyness (Black-Scholes approximation)
                    iv  = float(row["impliedVolatility"] or 0.5)
                    gamma_approx = _approx_gamma(current_price, s, iv, max(days_to_exp, 1) / 365)
                    gex = oi * gamma_approx * 100 * (current_price ** 2) / 1e9  # scale to millions
                    gex_map[s] = gex_map.get(s, 0) + gex
                    oi_map.setdefault(s, {"call_oi": 0, "put_oi": 0})
                    oi_map[s]["call_oi"] += oi

                for _, row in puts.iterrows():
                    s   = round(float(row["strike"]), 0)
                    oi  = float(0 if (row["openInterest"] != row["openInterest"]) else (row["openInterest"] or 0))
                    iv  = float(row["impliedVolatility"] or 0.5)
                    gamma_approx = _approx_gamma(current_price, s, iv, max(days_to_exp, 1) / 365)
                    gex = -(oi * gamma_approx * 100 * (current_price ** 2) / 1e9)
                    gex_map[s] = gex_map.get(s, 0) + gex
                    oi_map.setdefault(s, {"call_oi": 0, "put_oi": 0})
                    oi_map[s]["put_oi"] += oi

                # Max Pain: for each strike, sum total OI loss for all options
                all_strikes = sorted(set(
                    calls["strike"].tolist() + puts["strike"].tolist()
                ))
                for s_test in all_strikes:
                    pain = 0
                    # Call pain: calls ITM at s_test
                    pain += (calls[calls["strike"] < s_test]["openInterest"].fillna(0) *
                             (s_test - calls[calls["strike"] < s_test]["strike"])).sum()
                    # Put pain: puts ITM at s_test
                    pain += (puts[puts["strike"] > s_test]["openInterest"].fillna(0) *
                             (puts[puts["strike"] > s_test]["strike"] - s_test)).sum()
                    max_pain_map[s_test] = max_pain_map.get(s_test, 0) + pain

            except Exception as e:
                print(f"  ⚠️ Options chain error ({exp}): {e}")
                continue

        # ── Max Pain ──
        if max_pain_map:
            result["max_pain"] = round(min(max_pain_map, key=max_pain_map.get), 2)
            pain_dist = abs(current_price - result["max_pain"]) / current_price * 100
            result["pin_risk"] = pain_dist < 2.0 and result["days_to_expiry"] <= 5

        # ── Put/Call Ratio ──
        if total_call_oi > 0:
            result["pc_ratio"]    = round(total_put_oi / total_call_oi, 2)
            result["total_call_oi"] = int(total_call_oi or 0)
            result["total_put_oi"]  = int(total_put_oi or 0)

        # ── IV Rank / Signal ──
        if iv_list:
            iv_now   = round(float(np.median(iv_list)) * 100, 1)
            iv_high  = round(float(np.percentile(iv_list, 90)) * 100, 1)
            iv_low   = round(float(np.percentile(iv_list, 10)) * 100, 1)
            iv_rank  = round((iv_now - iv_low) / (iv_high - iv_low + 1e-9) * 100, 1) if iv_high > iv_low else 50
            result["iv_current"] = iv_now
            result["iv_rank"]    = iv_rank
            result["iv_signal"]  = (
                "IV CRUSH RISK"   if iv_rank > 80 else
                "HIGH IV"         if iv_rank > 60 else
                "LOW IV — CHEAP"  if iv_rank < 20 else
                "NORMAL IV"
            )

        # ── Net GEX ──
        gex_total = sum(gex_map.values())
        result["gex_total"] = round(gex_total, 2)
        result["gex_signal"] = (
            "STRONG PIN — Low Vol Expected" if gex_total > 500 else
            "MILD PIN"                       if gex_total > 100 else
            "NEUTRAL"                        if abs(gex_total) < 100 else
            "MILD TREND"                     if gex_total > -500 else
            "STRONG TREND — High Vol Expected"
        )

        # ── Dealer Hedging Pressure ──
        # Near max pain + positive GEX = dealers will sell into any rally
        # Below max pain + negative GEX = dealers will buy any dip (short covering)
        mp = result["max_pain"] or current_price
        if gex_total > 100 and current_price > mp:
            result["hedging_pressure"] = "SELLING — Dealers hedging above max pain"
        elif gex_total > 100 and current_price < mp:
            result["hedging_pressure"] = "BUYING — Dealers pulling price up to max pain"
        elif gex_total < -100:
            result["hedging_pressure"] = "CHASING — Dealers amplifying the move"
        else:
            result["hedging_pressure"] = "NEUTRAL"

        # ── Call Walls (highest call OI = price resistance) ──
        sorted_strikes = sorted(oi_map.keys())
        call_walls = sorted(
            [(s, oi_map[s]["call_oi"]) for s in sorted_strikes if s > current_price],
            key=lambda x: -x[1]
        )[:4]
        put_walls = sorted(
            [(s, oi_map[s]["put_oi"]) for s in sorted_strikes if s < current_price],
            key=lambda x: -x[1]
        )[:4]
        result["call_walls"] = [{"strike": s, "oi": int(oi)} for s, oi in call_walls]
        result["put_walls"]  = [{"strike": s, "oi": int(oi)} for s, oi in put_walls]

        # ── GEX by Strike (for chart) ──
        result["gex_by_strike"] = [
            {"strike": s, "gex": round(g, 2),
             "color": "#00ff88" if g > 0 else "#ff3355"}
            for s, g in sorted(gex_map.items())
            if abs(g) > 0.1
        ]

        # ── OI by Strike (for chart) ──
        result["oi_by_strike"] = [
            {"strike": s,
             "call_oi": int(oi_map[s]["call_oi"]),
             "put_oi":  int(oi_map[s]["put_oi"])}
            for s in sorted(oi_map.keys())
        ]

        # ── Summary ──
        pc  = result.get("pc_ratio", "?")
        gex = result["gex_total"]
        mp2 = result["max_pain"]
        result["summary"] = (
            f"GEX: {gex:+.0f}M ({result.get("gex_signal","")}) | "
            f"Max Pain: ${mp2} | "
            f"P/C: {pc} | "
            f"IV Rank: {result.get("iv_rank","?")}% | "
            f"Hedging: {result.get("hedging_pressure","")}"
        )

        # MM summary printed again after Schwab override in run_analysis (more accurate)

    except Exception as e:
        print(f"  ❌ Market Maker data error: {e}")
        result["summary"] = f"Error: {str(e)[:60]}"

    return result


def _approx_gamma(spot, strike, iv, t):
    """
    Black-Scholes gamma approximation (simplified).
    Returns approximate gamma for a given option.
    """
    try:
        if t <= 0 or iv <= 0: return 0
        import math
        d1 = (math.log(spot / strike) + 0.5 * iv**2 * t) / (iv * math.sqrt(t))
        phi = math.exp(-0.5 * d1**2) / math.sqrt(2 * math.pi)
        return phi / (spot * iv * math.sqrt(t))
    except Exception:
        return 0


def calculate_dark_pool_levels(closes, volumes, highs, lows):
    """
    Dark Pool Level Estimation.
    Dark pools are off-exchange venues where institutions trade large blocks.
    We can't see dark pool data directly, but we can detect their footprints:

    1. Unusually high volume at a specific price → dark pool print
    2. Price consolidation → accumulation/distribution
    3. Volume gap days → dark pool triggered move
    Used by: Citadel, Jane Street, Virtu to front-run retail order flow.
    """
    dp_levels = []

    # Method 1: High volume price levels (POC clusters from last 90 days)
    price_vol = {}
    for i in range(len(closes) - 1, max(len(closes) - 91, 0), -1):
        try:
            p  = round(float(closes.iloc[i]), 0)
            v  = float(volumes.iloc[i])
            hi = float(highs.iloc[i])
            lo = float(lows.iloc[i])
            # Distribute volume across range
            steps = max(int((hi - lo) / 0.5), 1)
            for s in range(steps):
                price_bin = round(lo + (s / steps) * (hi - lo), 0)
                price_vol[price_bin] = price_vol.get(price_bin, 0) + v / steps
        except Exception:
            continue

    if price_vol:
        avg_vol = np.mean(list(price_vol.values()))
        # Significant levels = 2x average volume at that price
        for price_lvl, vol in sorted(price_vol.items()):
            if vol > avg_vol * 2.0:
                dp_levels.append({
                    "price":  price_lvl,
                    "volume": int(vol),
                    "type":   "HIGH_VOLUME_NODE",
                    "strength": round(vol / avg_vol, 1)
                })

    # Method 2: Detect "volume gaps" — days where price gapped on huge volume
    vol_gaps = []
    for i in range(1, min(len(closes), 60)):
        try:
            gap_pct = abs(float(closes.iloc[-(i)]) - float(closes.iloc[-(i+1)])) / float(closes.iloc[-(i+1)]) * 100
            vol_mult = float(volumes.iloc[-(i)]) / float(volumes.iloc[-20:].mean())
            if gap_pct > 1.5 and vol_mult > 2.0:
                vol_gaps.append({
                    "price":    round(float(closes.iloc[-(i)]), 2),
                    "date":     str(closes.index[-(i)].date()),
                    "gap_pct":  round(gap_pct, 2),
                    "vol_mult": round(vol_mult, 1),
                })
        except Exception:
            continue

    # Sort levels by proximity to current price
    current = float(closes.iloc[-1])
    dp_levels_sorted = sorted(
        dp_levels,
        key=lambda x: abs(x["price"] - current)
    )[:10]

    # Identify nearest support/resistance
    above = [l for l in dp_levels_sorted if l["price"] > current * 1.005][:3]
    below = [l for l in dp_levels_sorted if l["price"] < current * 0.995][:3]

    return {
        "levels":           dp_levels_sorted,
        "nearest_above":    above,
        "nearest_below":    below,
        "volume_gaps":      vol_gaps[:5],
        "total_levels":     len(dp_levels),
    }


# ═══════════════════════════════════════════════════════════════
#  REAL-TIME NEWS ENGINE
#  Multi-source news aggregator with NLP sentiment scoring
#  Sources: Yahoo Finance, RSS feeds (Reuters, MarketWatch,
#           SeekingAlpha, Benzinga, SEC EDGAR 8-K filings)
#  No API keys required — all free sources
# ═══════════════════════════════════════════════════════════════

import xml.etree.ElementTree as ET
import html
import re as _re

# ── Keywords that move TSLA specifically ──
NEWS_KEYWORDS = {
    # Tier 1 — immediate high-impact (±30 pts)
    "CRITICAL_BULL": [
        "delivery record", "deliveries beat", "record deliveries",
        "earnings beat", "raised guidance", "raised price target",
        "fsd approval", "full self-driving approved", "robotaxi approved",
        "cybertruck sold out", "elon musk buys", "buyback", "share repurchase",
        "analyst upgrade", "strong buy", "price target raised",
        "better than expected", "blowout quarter",
    ],
    "CRITICAL_BEAR": [
        "recall", "nhtsa investigation", "crash", "fatal accident",
        "earnings miss", "guidance cut", "lowered guidance",
        "deliveries miss", "below expectations", "margin compression",
        "price cut", "elon musk sells", "elon sells shares",
        "sec investigation", "doj probe", "class action",
        "analyst downgrade", "sell rating", "price target cut",
        "layoffs", "production halt", "factory fire",
    ],
    # Tier 2 — significant impact (±15 pts)
    "BULL": [
        "tesla", "tsla", "model y", "model 3", "cybertruck", "semi",
        "gigafactory", "supercharger", "energy storage", "megapack",
        "elon musk", "autopilot", "new contract", "partnership",
        "expansion", "production ramp", "market share gains",
        "ev demand", "electric vehicle boom",
    ],
    "BEAR": [
        "competition", "price war", "byd", "rivian", "ford ev",
        "gm ev", "rate hike", "interest rates", "consumer spending",
        "china slowdown", "tesla competitor", "market share loss",
        "ev demand slowing", "subsidy cut", "tariff", "trade war",
        "short seller", "fraud allegation",
    ],
    # Tier 3 — macro context (±8 pts)
    "MACRO_BULL": [
        "fed rate cut", "soft landing", "inflation cooling",
        "strong jobs", "consumer confidence", "market rally",
        "risk on", "tech rally", "nasdaq rally",
    ],
    "MACRO_BEAR": [
        "fed rate hike", "recession", "inflation surge",
        "jobs report miss", "market selloff", "risk off",
        "tech selloff", "nasdaq selloff", "banking crisis",
    ],
}


def fetch_news():
    """
    Aggregates news from 6 sources, scores sentiment, ranks impact.
    Returns list of articles sorted by impact score, newest first.
    No API keys required.
    """
    articles = []

    # ── Source 1: Yahoo Finance via yfinance ──
    try:
        tkr = yf.Ticker(TICKER)
        yf_news = tkr.news or []
        for item in yf_news[:20]:
            title   = item.get("title", "")
            summary = item.get("summary", "") or item.get("description", "")
            pub_ts  = item.get("providerPublishTime") or item.get("published", 0)
            pub_dt  = datetime.fromtimestamp(pub_ts).strftime("%Y-%m-%d %H:%M") if pub_ts else "—"
            link    = item.get("link", "") or item.get("url", "")
            source  = item.get("publisher", "Yahoo Finance")
            articles.append({
                "title":   title,
                "summary": summary[:200] if summary else "",
                "date":    pub_dt,
                "source":  source,
                "url":     link,
                "raw_ts":  pub_ts or 0,
            })
    except Exception as e:
        print(f"  ⚠️ Yahoo Finance news error: {e}")

    # ── Source 2: RSS feeds — using reliable sources that work on Railway ──
    rss_feeds = [
        # Ticker-specific feeds (most reliable)
        ("Benzinga",       f"https://www.benzinga.com/stock/{TICKER.lower()}/feed"),
        ("Yahoo Finance",  f"https://finance.yahoo.com/rss/headline?s={TICKER}"),
        ("Finviz",         f"https://finviz.com/rss.ashx?t={TICKER}"),
        # Market-wide feeds
        ("MarketWatch",    "https://feeds.content.dowjones.io/public/rss/mw_topstories"),
        ("Investopedia",   "https://www.investopedia.com/feedbuilder/feed/getfeed?feedName=rss_headline"),
        ("Electrek",       "https://electrek.co/feed/"),
        ("Seeking Alpha",  f"https://seekingalpha.com/feed/symbol/{TICKER}"),
    ]

    rss_headers = {
        "User-Agent": "Mozilla/5.0 (compatible; TSLA-Monitor/1.0)",
        "Accept": "application/rss+xml, application/xml, text/xml",
    }

    for feed_name, feed_url in rss_feeds:
        try:
            resp = requests.get(feed_url, headers=rss_headers, timeout=6)
            if resp.status_code != 200:
                continue
            root = ET.fromstring(resp.content)
            # Handle both RSS 2.0 and Atom formats
            items = root.findall(".//item") or root.findall(".//{http://www.w3.org/2005/Atom}entry")
            for item in items[:10]:
                def get_text(tag, ns=""):
                    el = item.find(f"{ns}{tag}")
                    return html.unescape(el.text.strip()) if el is not None and el.text else ""
                title   = get_text("title") or get_text("{http://www.w3.org/2005/Atom}title")
                summary = get_text("description") or get_text("summary") or get_text("{http://www.w3.org/2005/Atom}summary")
                pub_raw = get_text("pubDate") or get_text("{http://www.w3.org/2005/Atom}published") or ""
                link    = get_text("link") or ""
                if not title:
                    continue
                # Parse date
                try:
                    from email.utils import parsedate_to_datetime
                    pub_dt = parsedate_to_datetime(pub_raw).strftime("%Y-%m-%d %H:%M")
                    pub_ts = parsedate_to_datetime(pub_raw).timestamp()
                except Exception:
                    pub_dt = pub_raw[:16] if pub_raw else "—"
                    pub_ts = 0
                articles.append({
                    "title":   title,
                    "summary": _re.sub(r"<[^>]+>", "", summary)[:200],
                    "date":    pub_dt,
                    "source":  feed_name,
                    "url":     link,
                    "raw_ts":  pub_ts,
                })
        except Exception as e:
            print(f"  ⚠️ RSS {feed_name} error: {e}")

    # ── Source 3: SEC EDGAR 8-K filings for TSLA ──
    try:
        tsla_cik = "0001318605"
        url = f"https://data.sec.gov/submissions/CIK{tsla_cik}.json"
        resp = requests.get(url, headers=SEC_HEADERS, timeout=8)
        if resp.status_code == 200:
            data = resp.json()
            recent = data.get("filings", {}).get("recent", {})
            forms = recent.get("form", [])
            dates = recent.get("filingDate", [])
            descs = recent.get("primaryDocument", [])
            accns = recent.get("accessionNumber", [])
            for i, form in enumerate(forms[:20]):
                if form in ("8-K", "8-K/A", "4"):
                    date_str = dates[i] if i < len(dates) else "—"
                    accn     = accns[i].replace("-","") if i < len(accns) else ""
                    link     = f"https://www.sec.gov/Archives/edgar/data/{tsla_cik.lstrip('0')}/{accn}/{descs[i]}" if accn and i < len(descs) else ""
                    label    = "SEC 8-K" if form == "8-K" else "SEC Form 4 (insider)" if form == "4" else form
                    articles.append({
                        "title":   f"[{label}] TSLA SEC Filing — {date_str}",
                        "summary": "Official SEC filing — check for material events, insider trades, or earnings guidance.",
                        "date":    date_str + " 00:00",
                        "source":  "SEC EDGAR",
                        "url":     link,
                        "raw_ts":  0,
                        "is_sec":  True,
                        "form":    form,
                    })
    except Exception as e:
        print(f"  ⚠️ SEC 8-K error: {e}")

    # ── Deduplicate by title similarity ──
    seen_titles = set()
    deduped = []
    for a in articles:
        key = _re.sub(r"[^a-z0-9]", "", a["title"].lower())[:60]
        if key not in seen_titles:
            seen_titles.add(key)
            deduped.append(a)

    # ── Score each article ──
    for a in deduped:
        a["sentiment_score"], a["sentiment"], a["impact_level"], a["matched_keywords"] = \
            _score_article(a["title"], a.get("summary", ""))

    # ── Sort: highest impact first, then newest ──
    deduped.sort(key=lambda x: (-abs(x["sentiment_score"]), -x.get("raw_ts", 0)))

    # Keep top 50
    return deduped[:50]


def _score_article(title, summary=""):
    """
    NLP-free keyword sentiment scorer.
    Returns: (score, sentiment_label, impact_level, matched_keywords)
    """
    text = (title + " " + summary).lower()
    score    = 0
    matched  = []

    # Tier 1 — Critical (±30)
    for kw in NEWS_KEYWORDS["CRITICAL_BULL"]:
        if kw in text:
            score += 30; matched.append(("🚀 " + kw, 30))
    for kw in NEWS_KEYWORDS["CRITICAL_BEAR"]:
        if kw in text:
            score -= 30; matched.append(("🔴 " + kw, -30))

    # Tier 2 — Significant (±15)
    for kw in NEWS_KEYWORDS["BULL"]:
        if kw in text:
            score += 8; matched.append(("▲ " + kw, 8))
    for kw in NEWS_KEYWORDS["BEAR"]:
        if kw in text:
            score -= 8; matched.append(("▼ " + kw, -8))

    # Tier 3 — Macro (±5)
    for kw in NEWS_KEYWORDS["MACRO_BULL"]:
        if kw in text:
            score += 5; matched.append(("↑ " + kw, 5))
    for kw in NEWS_KEYWORDS["MACRO_BEAR"]:
        if kw in text:
            score -= 5; matched.append(("↓ " + kw, -5))

    # Cap
    score = max(min(score, 100), -100)

    sentiment = (
        "VERY BULLISH" if score >= 40 else
        "BULLISH"      if score >= 15 else
        "BEARISH"      if score <= -40 else
        "BEARISH"      if score <= -15 else
        "NEUTRAL"
    )
    impact = (
        "🔥 HIGH"   if abs(score) >= 40 else
        "⚡ MEDIUM" if abs(score) >= 15 else
        "📰 LOW"
    )
    # Sort by magnitude
    matched.sort(key=lambda x: -abs(x[1]))
    return score, sentiment, impact, [m[0] for m in matched[:5]]


def calculate_news_sentiment(articles):
    """
    Aggregates article scores into an overall news sentiment signal.
    Weights recent articles more heavily.
    Returns net score, signal, and breakdown.
    """
    if not articles:
        return {"score": 0, "signal": "NEUTRAL", "articles": [], "breakdown": {}}

    now_ts = time.time()
    weighted_score = 0
    weights_sum    = 0
    high_impact    = []
    bull_count     = 0
    bear_count     = 0
    neutral_count  = 0

    for a in articles[:30]:
        score = a.get("sentiment_score", 0)
        ts    = a.get("raw_ts", 0)
        # Recency weight: full weight if <6h, half if <24h, quarter if older
        age_h = (now_ts - ts) / 3600 if ts > 0 else 48
        if   age_h < 1:  weight = 3.0
        elif age_h < 6:  weight = 2.0
        elif age_h < 24: weight = 1.0
        else:            weight = 0.3
        weighted_score += score * weight
        weights_sum    += weight
        if   score >= 15:  bull_count += 1
        elif score <= -15: bear_count += 1
        else:              neutral_count += 1
        if abs(score) >= 40:
            high_impact.append(a)

    net_score = round(weighted_score / (weights_sum + 1e-9), 1)
    signal = (
        "VERY BULLISH" if net_score >= 25 else
        "BULLISH"      if net_score >= 10 else
        "BEARISH"      if net_score <= -25 else
        "BEARISH"      if net_score <= -10 else
        "NEUTRAL"
    )

    return {
        "score":        net_score,
        "signal":       signal,
        "bull_count":   bull_count,
        "bear_count":   bear_count,
        "neutral_count":neutral_count,
        "total":        len(articles),
        "high_impact":  high_impact[:5],
        "articles":     articles,
        "last_updated": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
    }


# ═══════════════════════════════════════════════════════════════
#  EXTENDED HOURS TRADING ENGINE
#  Pre-market (4:00–9:30 AM ET), After-hours (4:00–8:00 PM ET),
#  Overnight gap analysis
#
#  Why it matters:
#  • 70% of TSLA's biggest single-day moves START in pre-market
#  • Earnings, news events, Elon tweets all hit overnight
#  • Gap-up / gap-down at open = MM positioning signal
#  • Pre-market volume reveals institutional conviction level
# ═══════════════════════════════════════════════════════════════

def calculate_extended_hours(ticker_symbol):
    """
    Fetches 5-day intraday data (1-min and 5-min intervals) with
    pre/post market included, then computes:

    1. Current session type (pre-market, regular, after-hours, overnight)
    2. Pre-market price, change, volume, VWAP
    3. After-hours price, change, volume
    4. Overnight gap (yesterday close → today pre-market)
    5. Gap fill probability (historical gap fill rate)
    6. Pre-market trend (rising, falling, flat)
    7. Volume comparison (pre-market vol vs avg pre-market vol)
    8. Key pre-market levels (high, low, VWAP)
    9. After-hours momentum signal
    10. 5-day extended hours history for charting
    """
    result = {
        "session":             "UNKNOWN",
        "market_status":       "UNKNOWN",
        "regular_close":       None,
        "regular_open":        None,
        "premarket_price":     None,
        "premarket_change":    None,
        "premarket_change_pct":None,
        "premarket_high":      None,
        "premarket_low":       None,
        "premarket_volume":    None,
        "premarket_vwap":      None,
        "premarket_trend":     "FLAT",
        "afterhours_price":    None,
        "afterhours_change":   None,
        "afterhours_change_pct":None,
        "afterhours_volume":   None,
        "overnight_gap":       None,
        "overnight_gap_pct":   None,
        "gap_direction":       "NONE",
        "gap_fill_prob":       None,
        "ext_signal":          "NEUTRAL",
        "ext_score":           0,
        "ext_reasons":         [],
        "intraday_history":    [],
        "session_history":     [],
    }

    try:
        tkr = yf.Ticker(ticker_symbol)

        # ── Determine current session ──
        from datetime import timezone
        import pytz
        et = pytz.timezone("America/New_York")
        now_et = datetime.now(et)
        now_time = now_et.time()
        from datetime import time as dtime
        is_weekday = now_et.weekday() < 5

        PRE_START  = dtime(4,  0)
        MKT_START  = dtime(9, 30)
        MKT_END    = dtime(16, 0)
        POST_END   = dtime(20, 0)

        if not is_weekday:
            session = "WEEKEND"
        elif PRE_START <= now_time < MKT_START:
            session = "PRE-MARKET"
        elif MKT_START <= now_time < MKT_END:
            session = "REGULAR"
        elif MKT_END <= now_time < POST_END:
            session = "AFTER-HOURS"
        else:
            session = "OVERNIGHT"

        result["session"] = session
        result["market_status"] = session
        result["current_et_time"] = now_et.strftime("%H:%M ET")

        # ── Fetch 5-day 1-minute data WITH pre/post market ──
        hist_1m = tkr.history(period="5d", interval="1m", prepost=True)
        hist_5m = tkr.history(period="5d", interval="5m", prepost=True)

        if hist_1m.empty and hist_5m.empty:
            result["ext_signal"] = "NO INTRADAY DATA"
            return result

        hist = hist_1m if not hist_1m.empty else hist_5m

        # ── Get last regular session close ──
        hist_day = tkr.history(period="10d", interval="1d")
        if not hist_day.empty:
            result["regular_close"] = round(float(hist_day["Close"].iloc[-1]), 2)
            result["regular_open"]  = round(float(hist_day["Open"].iloc[-1]),  2)
            prev_close = round(float(hist_day["Close"].iloc[-2]), 2) if len(hist_day) > 1 else result["regular_close"]
            result["prev_close"] = prev_close
        else:
            prev_close = None

        # ── Filter to today's data ──
        today_str = now_et.strftime("%Y-%m-%d")
        # Convert index to ET for filtering
        try:
            hist.index = hist.index.tz_convert(et)
        except Exception:
            try:
                hist.index = hist.index.tz_localize("UTC").tz_convert(et)
            except Exception:
                pass

        today_data = hist[hist.index.strftime("%Y-%m-%d") == today_str] if len(hist) > 0 else hist.iloc[0:0]

        # ── Separate pre-market, regular, after-hours ──
        if len(today_data) > 0:
            pre  = today_data[today_data.index.time < MKT_START]
            reg  = today_data[(today_data.index.time >= MKT_START) & (today_data.index.time < MKT_END)]
            post = today_data[today_data.index.time >= MKT_END]
        else:
            # Fallback: use last available data
            pre  = hist.iloc[0:0]
            reg  = hist.iloc[0:0]
            post = hist.iloc[0:0]

        # ── Pre-market analysis ──
        if len(pre) > 0:
            pm_open  = round(float(pre["Close"].iloc[0]),  2)
            pm_close = round(float(pre["Close"].iloc[-1]), 2)
            pm_high  = round(float(pre["High"].max()),     2)
            pm_low   = round(float(pre["Low"].min()),      2)
            pm_vol   = int(pre["Volume"].sum())

            result["premarket_price"]  = pm_close
            result["premarket_high"]   = pm_high
            result["premarket_low"]    = pm_low
            result["premarket_volume"] = pm_vol

            # Pre-market VWAP
            pm_typical = (pre["High"] + pre["Low"] + pre["Close"]) / 3
            pm_vwap    = round(float((pm_typical * pre["Volume"]).sum() / (pre["Volume"].sum() + 1e-9)), 2)
            result["premarket_vwap"] = pm_vwap

            # Pre-market change vs yesterday close
            if prev_close:
                pm_chg     = round(pm_close - prev_close, 2)
                pm_chg_pct = round((pm_close / prev_close - 1) * 100, 2)
                result["premarket_change"]     = pm_chg
                result["premarket_change_pct"] = pm_chg_pct

            # Pre-market trend (first 25% vs last 25% of bars)
            n = len(pre)
            if n >= 4:
                first_q = pre["Close"].iloc[:n//4].mean()
                last_q  = pre["Close"].iloc[-n//4:].mean()
                if last_q > first_q * 1.002:
                    result["premarket_trend"] = "RISING"
                elif last_q < first_q * 0.998:
                    result["premarket_trend"] = "FALLING"
                else:
                    result["premarket_trend"] = "FLAT"

        # ── After-hours analysis ──
        if len(post) > 0:
            ah_close = round(float(post["Close"].iloc[-1]), 2)
            ah_vol   = int(post["Volume"].sum())
            reg_close = round(float(reg["Close"].iloc[-1]), 2) if len(reg) > 0 else result["regular_close"]

            result["afterhours_price"]  = ah_close
            result["afterhours_volume"] = ah_vol

            if reg_close:
                ah_chg     = round(ah_close - reg_close, 2)
                ah_chg_pct = round((ah_close / reg_close - 1) * 100, 2)
                result["afterhours_change"]     = ah_chg
                result["afterhours_change_pct"] = ah_chg_pct
        else:
            # Fallback: use fast_info for real-time extended hours price
            try:
                fi = tkr.fast_info
                ah_price = getattr(fi, 'last_price', None) or getattr(fi, 'postMarketPrice', None)
                reg_ref  = result.get("regular_close") or getattr(fi, 'regular_market_previous_close', None)
                if ah_price and session in ("AFTER-HOURS", "OVERNIGHT"):
                    result["afterhours_price"] = round(float(ah_price), 2)
                    if reg_ref:
                        ah_chg = round(ah_price - reg_ref, 2)
                        result["afterhours_change"]     = ah_chg
                        result["afterhours_change_pct"] = round((ah_price/reg_ref - 1)*100, 2)
                elif ah_price and session == "PRE-MARKET":
                    result["premarket_price"] = round(float(ah_price), 2)
                    if reg_ref:
                        pm_chg = round(ah_price - reg_ref, 2)
                        result["premarket_change"]     = pm_chg
                        result["premarket_change_pct"] = round((ah_price/reg_ref - 1)*100, 2)
            except Exception as _fi_e:
                print(f"  ⚠️ fast_info fallback error: {_fi_e}")

        # ── Overnight gap analysis ──
        if prev_close and result.get("premarket_price"):
            gap     = round(result["premarket_price"] - prev_close, 2)
            gap_pct = round((result["premarket_price"] / prev_close - 1) * 100, 2)
            result["overnight_gap"]     = gap
            result["overnight_gap_pct"] = gap_pct
            result["gap_direction"] = "UP" if gap > 0.5 else "DOWN" if gap < -0.5 else "FLAT"

            # Gap fill probability (based on gap size — empirical)
            abs_gap_pct = abs(gap_pct)
            if abs_gap_pct < 0.5:
                fill_prob = 85
            elif abs_gap_pct < 1.5:
                fill_prob = 70
            elif abs_gap_pct < 3.0:
                fill_prob = 55
            elif abs_gap_pct < 5.0:
                fill_prob = 35
            else:
                fill_prob = 20  # large gaps rarely fill same day
            result["gap_fill_prob"] = fill_prob

        elif prev_close and result.get("regular_open") and result.get("regular_close"):
            # Check gap from prev close to today open
            gap     = round(result["regular_open"] - prev_close, 2)
            gap_pct = round((result["regular_open"] / prev_close - 1) * 100, 2)
            result["overnight_gap"]     = gap
            result["overnight_gap_pct"] = gap_pct
            result["gap_direction"] = "UP" if gap > 0.5 else "DOWN" if gap < -0.5 else "FLAT"
            abs_gap = abs(gap_pct)
            result["gap_fill_prob"] = 85 if abs_gap < 0.5 else 70 if abs_gap < 1.5 else 55 if abs_gap < 3 else 35 if abs_gap < 5 else 20

        # ── Build intraday history for chart (last 2 days) ──
        try:
            cutoff = hist.index[-1] - pd.Timedelta(days=2)
            recent = hist[hist.index >= cutoff]
            result["intraday_history"] = [
                {
                    "dt":      bar.Index.strftime("%m/%d %H:%M"),
                    "price":   round(float(bar.Close), 2),
                    "volume":  int(bar.Volume),
                    "session": (
                        "pre"   if bar.Index.time() < MKT_START else
                        "post"  if bar.Index.time() >= MKT_END  else
                        "reg"
                    )
                }
                for bar in recent.itertuples()
            ][-200:]  # cap at 200 bars
        except Exception as e:
            print(f"  ⚠️ Intraday history error: {e}")

        # ══════════════════════════════════════════
        # EXTENDED HOURS SIGNAL SCORING
        # ══════════════════════════════════════════
        ext_score   = 0
        ext_reasons = []

        # Pre-market move
        pm_pct = result.get("premarket_change_pct", 0) or 0
        if   pm_pct >= 4:
            ext_score += 30; ext_reasons.append(f"Pre-market surging +{pm_pct}% — strong institutional buying ▲▲")
        elif pm_pct >= 2:
            ext_score += 20; ext_reasons.append(f"Pre-market up +{pm_pct}% ▲")
        elif pm_pct >= 0.5:
            ext_score += 10; ext_reasons.append(f"Pre-market up +{pm_pct}% ▲")
        elif pm_pct <= -4:
            ext_score -= 30; ext_reasons.append(f"Pre-market crashing {pm_pct}% — heavy selling ▼▼")
        elif pm_pct <= -2:
            ext_score -= 20; ext_reasons.append(f"Pre-market down {pm_pct}% ▼")
        elif pm_pct <= -0.5:
            ext_score -= 10; ext_reasons.append(f"Pre-market down {pm_pct}% ▼")

        # Pre-market trend direction
        pm_trend = result.get("premarket_trend", "FLAT")
        if pm_trend == "RISING":
            ext_score += 10; ext_reasons.append("Pre-market trend: RISING — momentum building into open ▲")
        elif pm_trend == "FALLING":
            ext_score -= 10; ext_reasons.append("Pre-market trend: FALLING — selling pressure into open ▼")

        # After-hours move
        ah_pct = result.get("afterhours_change_pct", 0) or 0
        if   ah_pct >= 3:
            ext_score += 25; ext_reasons.append(f"After-hours +{ah_pct}% — strong post-close buying ▲")
        elif ah_pct >= 1:
            ext_score += 12; ext_reasons.append(f"After-hours +{ah_pct}% ▲")
        elif ah_pct <= -3:
            ext_score -= 25; ext_reasons.append(f"After-hours {ah_pct}% — heavy post-close selling ▼")
        elif ah_pct <= -1:
            ext_score -= 12; ext_reasons.append(f"After-hours {ah_pct}% ▼")

        # Gap analysis
        gap_dir  = result.get("gap_direction", "FLAT")
        gap_pct2 = result.get("overnight_gap_pct", 0) or 0
        fill_p   = result.get("gap_fill_prob", 50)
        if gap_dir == "UP" and abs(gap_pct2) >= 2:
            ext_score += 15; ext_reasons.append(f"Gap UP {gap_pct2:+.1f}% overnight ({fill_p}% fill probability)")
        elif gap_dir == "DOWN" and abs(gap_pct2) >= 2:
            ext_score -= 15; ext_reasons.append(f"Gap DOWN {gap_pct2:.1f}% overnight ({fill_p}% fill probability)")

        # Price vs pre-market VWAP
        pm_vwap = result.get("premarket_vwap")
        pm_price = result.get("premarket_price")
        if pm_vwap and pm_price:
            if pm_price > pm_vwap * 1.005:
                ext_score += 8; ext_reasons.append(f"Price above pre-market VWAP (${pm_vwap}) ▲")
            elif pm_price < pm_vwap * 0.995:
                ext_score -= 8; ext_reasons.append(f"Price below pre-market VWAP (${pm_vwap}) ▼")

        result["ext_score"]   = ext_score
        result["ext_reasons"] = ext_reasons
        result["ext_signal"]  = (
            "STRONG BULLISH" if ext_score >= 30 else
            "BULLISH"        if ext_score >= 15 else
            "BEARISH"        if ext_score <= -30 else
            "BEARISH"        if ext_score <= -15 else
            "NEUTRAL"
        )

        print(f"  ⏰ Session:{session} | PM:{pm_pct:+.1f}% | AH:{ah_pct:+.1f}% | Gap:{gap_pct2:+.1f}% | Ext Score:{ext_score}")

    except Exception as e:
        print(f"  ❌ Extended hours error: {e}")
        import traceback; traceback.print_exc()
        result["ext_signal"] = "ERROR"

    return result


# ═══════════════════════════════════════════════════════════════
#  CTA POSITION SIZING ENGINE
#  Replicates how systematic macro / CTA hedge funds size positions
#
#  Core formula:
#  Position = (Portfolio × TargetVol) / (AssetVol × √252)
#           × TrendSignal
#           × CorrelationAdjustment
#           × RegimeMultiplier
#
#  Each multiplier is derived from live market data already
#  computed by the other engines — no extra API calls needed.
# ═══════════════════════════════════════════════════════════════

def calculate_cta_sizing(
    closes, volumes, indicators, spy_data, hmm_result,
    inst_models, mm_data, news_data, ext_data,
    portfolio_value=100_000,
    target_vol=0.12,        # 12% annualised — typical CTA target
):
    """
    Returns a complete position sizing recommendation including:
    - Raw volatility-scaled base exposure
    - Trend signal (0–1) from multi-timeframe momentum
    - Correlation adjustment (reduces size when TSLA/SPY corr is high)
    - Regime multiplier (HMM + VIX + GEX combined)
    - Final recommended dollar exposure and share count
    - Confidence band (conservative / base / aggressive)
    - Full breakdown of every factor so you can see the reasoning
    """
    result = {
        "portfolio_value":     portfolio_value,
        "target_vol":          target_vol,
        "asset_vol_daily":     None,
        "asset_vol_annual":    None,
        "base_exposure":       None,
        "base_exposure_pct":   None,
        "trend_signal":        None,
        "trend_breakdown":     {},
        "correlation_factor":  None,
        "regime_multiplier":   None,
        "regime_breakdown":    {},
        "final_exposure":      None,
        "final_exposure_pct":  None,
        "share_count":         None,
        "conservative_shares": None,
        "aggressive_shares":   None,
        "dollar_at_risk":      None,
        "max_loss_1pct_spy":   None,
        "sizing_signal":       "HOLD",
        "sizing_reasons":      [],
        "factor_table":        [],
        "vol_history":         [],
    }

    try:
        price = float(closes.iloc[-1])

        # ══════════════════════════════════════════════════
        # STEP 1 — ASSET VOLATILITY
        # Annualised realised vol from daily returns
        # Uses 20-day (short) and 60-day (long) — blend both
        # ══════════════════════════════════════════════════
        returns   = closes.pct_change().dropna()
        vol_20d   = float(returns.iloc[-20:].std())  * (252 ** 0.5)
        vol_60d   = float(returns.iloc[-60:].std())  * (252 ** 0.5)
        vol_blend = round((vol_20d * 0.6 + vol_60d * 0.4), 4)  # weight recent more

        result["asset_vol_daily"]  = round(float(returns.iloc[-20:].std()), 4)
        result["asset_vol_annual"] = round(vol_blend, 4)
        result["vol_20d"]          = round(vol_20d, 4)
        result["vol_60d"]          = round(vol_60d, 4)

        # Rolling vol history for chart
        roll_vol = returns.rolling(20).std() * (252 ** 0.5)
        result["vol_history"] = [
            {"date": str(roll_vol.index[i].date()), "vol": round(float(roll_vol.iloc[i]) * 100, 2)}
            for i in range(-60, 0) if not np.isnan(roll_vol.iloc[i])
        ]

        # ══════════════════════════════════════════════════
        # STEP 2 — BASE EXPOSURE (Vol-Scaled)
        # Base = Portfolio × (TargetVol / AssetVol)
        # This is the core CTA mechanic — bigger size in calm
        # markets, smaller size in volatile markets
        # ══════════════════════════════════════════════════
        base_ratio    = target_vol / (vol_blend + 1e-9)
        base_ratio    = min(base_ratio, 2.0)   # cap at 2x leverage
        base_exposure = round(portfolio_value * base_ratio, 2)
        base_pct      = round(base_ratio * 100, 1)

        result["base_exposure"]     = base_exposure
        result["base_exposure_pct"] = base_pct
        result["vol_ratio"]         = round(base_ratio, 3)

        # ══════════════════════════════════════════════════
        # STEP 3 — TREND SIGNAL (0.0 to 1.0)
        # Multi-timeframe momentum — CTA funds use this to
        # only be long when trend confirms the position
        # ══════════════════════════════════════════════════
        trend_components = {}

        # 3a. Price vs EMAs (short / medium / long)
        ema20  = float(closes.ewm(span=20).mean().iloc[-1])
        ema50  = float(closes.ewm(span=50).mean().iloc[-1])
        ema200 = float(closes.ewm(span=200).mean().iloc[-1])
        above_ema20  = price > ema20
        above_ema50  = price > ema50
        above_ema200 = price > ema200
        ema_score = (above_ema20 + above_ema50 + above_ema200) / 3
        trend_components["ema_alignment"] = round(ema_score, 2)

        # 3b. Momentum (1m, 3m, 6m) — Fama-French style
        mom_1m = (float(closes.iloc[-1]) / float(closes.iloc[-21])  - 1) if len(closes) > 21 else 0
        mom_3m = (float(closes.iloc[-1]) / float(closes.iloc[-63])  - 1) if len(closes) > 63 else 0
        mom_6m = (float(closes.iloc[-1]) / float(closes.iloc[-126]) - 1) if len(closes) > 126 else 0
        # Normalise each to 0-1 using tanh (smooth sigmoid)
        import math
        mom_score = (math.tanh(mom_1m * 5) + math.tanh(mom_3m * 3) + math.tanh(mom_6m * 2)) / 3
        mom_score = (mom_score + 1) / 2   # shift from (-1,1) to (0,1)
        trend_components["momentum_score"]   = round(mom_score, 2)
        trend_components["momentum_1m_pct"]  = round(mom_1m * 100, 2)
        trend_components["momentum_3m_pct"]  = round(mom_3m * 100, 2)
        trend_components["momentum_6m_pct"]  = round(mom_6m * 100, 2)

        # 3c. Kalman velocity (from institutional models)
        kalman_vel = inst_models.get("kalman", {}).get("velocity", 0) or 0
        kal_score  = (math.tanh(kalman_vel * 50) + 1) / 2
        trend_components["kalman_velocity"] = round(float(kalman_vel), 6)
        trend_components["kalman_score"]    = round(kal_score, 2)

        # 3d. MACD direction
        macd_hist_val = indicators.get("macd_hist", 0) or 0
        macd_score    = 0.75 if macd_hist_val > 0 else 0.25
        trend_components["macd_score"] = macd_score

        # 3e. SPY trend alignment (reduces trend signal in bear market)
        spy_trend = spy_data.get("spy_trend", "MIXED")
        spy_ts = {"BULL MARKET":1.0,"UPTREND":0.8,"MIXED":0.5,"DOWNTREND":0.2,"BEAR MARKET":0.0}.get(spy_trend, 0.5)
        trend_components["spy_alignment"] = spy_ts

        # Blend with weights — momentum is king for CTAs
        trend_signal = round(
            ema_score  * 0.20 +
            mom_score  * 0.35 +
            kal_score  * 0.20 +
            macd_score * 0.10 +
            spy_ts     * 0.15,
            3
        )
        result["trend_signal"]    = trend_signal
        result["trend_breakdown"] = trend_components
        result["trend_direction"] = (
            "STRONG LONG"  if trend_signal >= 0.75 else
            "LONG"         if trend_signal >= 0.60 else
            "WEAK LONG"    if trend_signal >= 0.50 else
            "FLAT"         if trend_signal >= 0.40 else
            "WEAK SHORT"   if trend_signal >= 0.25 else
            "SHORT"
        )

        # ══════════════════════════════════════════════════
        # STEP 4 — CORRELATION ADJUSTMENT (0.5 to 1.0)
        # When TSLA is highly correlated with SPY, you're
        # already long the market. Reduce size to avoid
        # doubling up on the same risk.
        # ══════════════════════════════════════════════════
        corr_60d = spy_data.get("correlation_60d", 0.7) or 0.7
        corr_60d = abs(corr_60d)
        # Corr=1.0 → factor=0.5 (heavily penalised, same risk as SPY)
        # Corr=0.0 → factor=1.0 (uncorrelated, full size)
        corr_factor = round(1.0 - (corr_60d * 0.5), 3)
        result["correlation_factor"] = corr_factor
        result["corr_60d"]           = round(corr_60d, 3)

        # ══════════════════════════════════════════════════
        # STEP 5 — REGIME MULTIPLIER (0.2 to 1.2)
        # Combines: HMM regime + VIX level + GEX signal
        # + News sentiment + Pre-market activity
        # This is the "environment awareness" layer
        # ══════════════════════════════════════════════════
        reg_components = {}

        # 5a. HMM regime
        hmm_regime = hmm_result.get("regime", "NEUTRAL")
        hmm_conf   = hmm_result.get("confidence", 0.5) or 0.5
        hmm_mult   = {"BULLISH": 1.0, "NEUTRAL": 0.7, "BEARISH": 0.3}.get(hmm_regime, 0.7)
        hmm_mult   = hmm_mult * (0.5 + hmm_conf * 0.5)  # scale by confidence
        reg_components["hmm"] = {"regime": hmm_regime, "confidence": round(hmm_conf, 2), "multiplier": round(hmm_mult, 2)}

        # 5b. VIX regime
        vix = spy_data.get("vix", 20) or 20
        vix_mult = (
            0.20 if vix >= 40 else
            0.35 if vix >= 30 else
            0.55 if vix >= 25 else
            0.75 if vix >= 20 else
            0.90 if vix >= 15 else
            1.10        # low VIX = calm = more exposure
        )
        reg_components["vix"] = {"level": vix, "multiplier": round(vix_mult, 2)}

        # 5c. GEX environment
        gex = mm_data.get("gex_total", 0) or 0
        # Negative GEX = trending market = CTA loves it
        # Positive GEX = pinned market = reduce size (less opportunity)
        gex_mult = (
            1.15 if gex < -500 else   # strong trend environment
            1.05 if gex < -100 else
            0.90 if gex > 500  else   # pinned, range-bound
            0.95 if gex > 100  else
            1.0
        )
        reg_components["gex"] = {"value": round(gex, 0), "multiplier": round(gex_mult, 2)}

        # 5d. News sentiment weight
        news_sig  = news_data.get("signal", "NEUTRAL")
        news_mult = {
            "VERY BULLISH": 1.10,
            "BULLISH":      1.05,
            "NEUTRAL":      1.00,
            "BEARISH":      0.85,
            "VERY BEARISH": 0.70,
        }.get(news_sig, 1.0)
        reg_components["news"] = {"signal": news_sig, "multiplier": round(news_mult, 2)}

        # 5e. Pre-market activity
        pm_pct   = ext_data.get("premarket_change_pct", 0) or 0
        pm_mult  = min(max(1.0 + (pm_pct / 20), 0.75), 1.15)  # ±5% PM → ±0.25 multiplier
        reg_components["premarket"] = {"change_pct": round(pm_pct, 2), "multiplier": round(pm_mult, 2)}

        # Blend regime components
        regime_mult = round(
            hmm_mult  * 0.30 +
            vix_mult  * 0.30 +
            gex_mult  * 0.15 +
            news_mult * 0.15 +
            pm_mult   * 0.10,
            3
        )
        regime_mult = min(max(regime_mult, 0.10), 1.20)  # hard floor/ceiling
        result["regime_multiplier"] = regime_mult
        result["regime_breakdown"]  = reg_components
        result["regime_label"] = (
            "RISK-ON"     if regime_mult >= 0.90 else
            "CAUTIOUS"    if regime_mult >= 0.65 else
            "DEFENSIVE"   if regime_mult >= 0.40 else
            "RISK-OFF"
        )

        # ══════════════════════════════════════════════════
        # STEP 6 — FINAL POSITION
        # Base × TrendSignal × CorrFactor × RegimeMultiplier
        # ══════════════════════════════════════════════════
        final_exposure = round(
            base_exposure * trend_signal * corr_factor * regime_mult, 2
        )
        final_exposure = max(0, min(final_exposure, portfolio_value * 2.0))  # 2x max leverage
        final_pct      = round(final_exposure / portfolio_value * 100, 1)
        share_count    = int(final_exposure / price) if price > 0 else 0

        # Conservative (×0.7) and Aggressive (×1.3) bands
        conservative   = round(final_exposure * 0.70, 2)
        aggressive     = round(min(final_exposure * 1.30, portfolio_value * 2.0), 2)
        cons_shares    = int(conservative / price) if price > 0 else 0
        agg_shares     = int(aggressive   / price) if price > 0 else 0

        result["final_exposure"]      = final_exposure
        result["final_exposure_pct"]  = final_pct
        result["share_count"]         = share_count
        result["conservative_shares"] = cons_shares
        result["aggressive_shares"]   = agg_shares
        result["conservative_exposure"] = conservative
        result["aggressive_exposure"]   = aggressive

        # ── Risk metrics ──
        beta   = spy_data.get("beta_20d", 2.0) or 2.0
        dollar_at_risk  = round(final_exposure * vol_blend / (252 ** 0.5), 2)  # 1-day 1σ
        spy_1pct_impact = round(final_exposure * beta * 0.01, 2)               # SPY drops 1%
        result["dollar_at_risk"]    = dollar_at_risk    # daily 1σ P&L swing
        result["max_loss_1pct_spy"] = spy_1pct_impact   # expected TSLA $ loss if SPY -1%

        # ── Sizing signal ──
        if trend_signal >= 0.65 and regime_mult >= 0.80:
            sizing_signal = "FULL SIZE"
        elif trend_signal >= 0.55 and regime_mult >= 0.60:
            sizing_signal = "NORMAL SIZE"
        elif trend_signal >= 0.40 and regime_mult >= 0.45:
            sizing_signal = "HALF SIZE"
        elif trend_signal >= 0.25 or regime_mult >= 0.30:
            sizing_signal = "QUARTER SIZE"
        else:
            sizing_signal = "STAY OUT"
        result["sizing_signal"] = sizing_signal

        # ── Factor table for UI display ──
        result["factor_table"] = [
            {"factor": "Portfolio Value",      "value": f"${portfolio_value:,.0f}", "impact": "—"},
            {"factor": "Target Volatility",    "value": f"{target_vol*100:.0f}%",   "impact": "—"},
            {"factor": "Asset Vol (20d)",      "value": f"{vol_20d*100:.1f}%",      "impact": "—"},
            {"factor": "Asset Vol (60d)",      "value": f"{vol_60d*100:.1f}%",      "impact": "—"},
            {"factor": "Vol-Scaled Base",      "value": f"${base_exposure:,.0f}",   "impact": f"{base_pct:.1f}% of portfolio"},
            {"factor": "Trend Signal",         "value": f"{trend_signal:.3f}",      "impact": f"×{trend_signal:.3f} — {result.get("trend_direction","")}"},
            {"factor": "Correlation Factor",   "value": f"{corr_factor:.3f}",       "impact": f"×{corr_factor:.3f} (corr={corr_60d:.2f})"},
            {"factor": "Regime Multiplier",    "value": f"{regime_mult:.3f}",       "impact": f"×{regime_mult:.3f} — {result.get("regime_label","")}"},
            {"factor": "⟹  Final Exposure",   "value": f"${final_exposure:,.0f}",  "impact": f"{final_pct:.1f}% of portfolio"},
            {"factor": "Share Count",          "value": f"{share_count:,}",         "impact": f"@ ${price:.2f}"},
            {"factor": "Daily 1σ P&L Risk",    "value": f"${dollar_at_risk:,.0f}",  "impact": "expected daily swing"},
            {"factor": "SPY -1% Impact",       "value": f"-${spy_1pct_impact:,.0f}","impact": f"beta={beta}x"},
        ]

        # ── Reasons ──
        reasons = []
        if vol_20d > vol_60d * 1.2:
            reasons.append(f"⚠️ Volatility rising ({vol_20d*100:.1f}% vs {vol_60d*100:.1f}% LT) — base exposure auto-reduced")
        elif vol_20d < vol_60d * 0.8:
            reasons.append(f"✅ Volatility contracting ({vol_20d*100:.1f}%) — base exposure auto-increased")
        reasons.append(f"Trend signal {trend_signal:.2f} ({result.get("trend_direction","")}) — momentum {mom_1m*100:+.1f}% 1m / {mom_3m*100:+.1f}% 3m")
        reasons.append(f"Regime {result.get("regime_label","")} (mult={regime_mult:.2f}) — HMM:{hmm_regime} VIX:{vix} GEX:{gex:+.0f}M")
        reasons.append(f"Corr adjustment ×{corr_factor:.2f} — TSLA/SPY 60d correlation = {corr_60d:.2f}")
        result["sizing_reasons"] = reasons

        print(f"  📐 CTA: Base ${base_exposure:,.0f} → Trend×{trend_signal:.2f} × Regime×{regime_mult:.2f} → Final ${final_exposure:,.0f} ({share_count} shares) [{sizing_signal}]")

    except Exception as e:
        print(f"  ❌ CTA sizing error: {e}")
        import traceback; traceback.print_exc()
        result["sizing_signal"] = "ERROR"

    return result


# ═══════════════════════════════════════════════════════════════
#  PRECISION TOP ENGINE
# ═══════════════════════════════════════════════════════════════


# ═══════════════════════════════════════════════════════════════
#  PRECISION ENTRY ENGINE — When to Buy & How Much
#
#  Mirror of the Peak Detection engine but for BOTTOMS.
#  9 leading signals that fire BEFORE the reversal up,
#  not after. Tells you exactly:
#    • When to buy (entry score 0–100)
#    • Where to buy (support levels, Fibonacci retrace)
#    • How to stage the entry (3 tranches with % of capital)
#    • Hard invalidation level (where the thesis is wrong)
#
#  The 3-tranche approach is how professional traders buy:
#    Tranche 1 — Initial position on signal (35% of allocation)
#    Tranche 2 — Add on pullback to support (40% of allocation)
#    Tranche 3 — Confirm on breakout above entry (25% of allocation)
# ═══════════════════════════════════════════════════════════════

def calculate_entry_signals(closes, highs, lows, volumes, opens,
                             mm_data=None, indicators=None,
                             spy_data=None, portfolio_value=100_000):
    """
    Returns:
    - entry_score:     0–100 (how strong is the buy setup)
    - entry_urgency:   WAIT / WATCH / ACCUMULATE / BUY NOW
    - signals:         list of active bottom signals with scores
    - tranche_plan:    3-tranche staged entry with prices + % of capital
    - support_levels:  key price floors below current price
    - invalidation:    price that proves the thesis wrong
    - total_deploy_pct: what % of portfolio to deploy now
    """
    mm_data    = mm_data    or {}
    indicators = indicators or {}
    spy_data   = spy_data   or {}

    result = {
        "signals":          [],
        "entry_score":      0,
        "entry_urgency":    "WAIT",
        "entry_color":      "var(--text-dim)",
        "tranche_plan":     [],
        "support_levels":   [],
        "fib_retrace":      {},
        "invalidation":     None,
        "total_deploy_pct": 0,
        "total_deploy_$":   0,
        "entry_reasons":    [],
        "candle_patterns":  [],
        "divergence_days":  0,
        "vol_dry_up_ratio": None,
        "fear_extreme":     False,
    }

    try:
        price = float(closes.iloc[-1])
        n     = len(closes)
        entry_score = 0
        signals     = []

        # ══════════════════════════════════════════════
        # 1. SELLING CLIMAX — massive volume at new low
        #    Mirror of buying climax — last sellers out
        #    Wyckoff: selling climax → accumulation begins
        # ══════════════════════════════════════════════
        try:
            avg_vol_20  = float(volumes.iloc[-20:].mean())
            today_vol   = float(volumes.iloc[-1])
            vol_ratio   = round(today_vol / (avg_vol_20 + 1), 2)
            is_new_low  = float(lows.iloc[-1]) <= float(lows.iloc[-20:].min()) * 1.002
            result["vol_dry_up_ratio"] = vol_ratio

            if vol_ratio >= 3.0 and is_new_low:
                entry_score += 30
                signals.append({
                    "name":   "🟢 SELLING CLIMAX",
                    "detail": f"Volume {vol_ratio}× avg at 20-day low — last sellers panicking out, Wyckoff bottom signal",
                    "score":  30, "severity": "CRITICAL"
                })
            elif vol_ratio >= 2.0 and is_new_low:
                entry_score += 15
                signals.append({
                    "name":   "⚡ Elevated Volume at Low",
                    "detail": f"Volume {vol_ratio}× avg near recent low — selling pressure peaking, watch for reversal",
                    "score":  15, "severity": "WARNING"
                })
        except Exception: pass

        # ══════════════════════════════════════════════
        # 2. BULLISH CANDLE PATTERNS at support
        #    Hammer, Bullish Engulfing, Morning Doji Star
        # ══════════════════════════════════════════════
        try:
            candle_patterns = []
            for i in [-1, -2, -3]:
                o = float(opens.iloc[i]);  h = float(highs.iloc[i])
                l = float(lows.iloc[i]);   c = float(closes.iloc[i])
                body        = abs(c - o)
                range_      = h - l
                if range_ < 1e-9: continue
                lower_wick  = min(o, c) - l
                upper_wick  = h - max(o, c)
                near_low_20 = float(lows.iloc[i]) <= float(lows.iloc[-20:].min()) * 1.03

                # Hammer: small body at top, long lower wick (≥2× body), near low
                if lower_wick >= 2 * body and body <= 0.35 * range_ and upper_wick < body and near_low_20:
                    candle_patterns.append({"bar": i, "pattern": "Hammer", "severity": "HIGH"})
                    if i == -1:
                        entry_score += 22
                        signals.append({
                            "name":   "🔨 HAMMER CANDLE",
                            "detail": f"Buyers rejected sellers at ${round(l,2)} — strong support found, reversal signal",
                            "score":  22, "severity": "HIGH"
                        })

                # Bullish Engulfing: today bullish, fully engulfs yesterday bearish
                if i == -1 and c > o:
                    prev_o = float(opens.iloc[-2]); prev_c = float(closes.iloc[-2])
                    if prev_c < prev_o and o <= prev_c and c >= prev_o:
                        candle_patterns.append({"bar": -1, "pattern": "Bullish Engulfing", "severity": "HIGH"})
                        entry_score += 25
                        signals.append({
                            "name":   "🟢 BULLISH ENGULFING",
                            "detail": "Today's buyers completely overwhelmed yesterday's sellers in one candle — strong reversal",
                            "score":  25, "severity": "CRITICAL"
                        })

                # Doji at low: indecision at support = potential bottom
                if body <= 0.05 * range_ and near_low_20 and i == -1:
                    candle_patterns.append({"bar": i, "pattern": "Doji at Low", "severity": "MEDIUM"})
                    entry_score += 12
                    signals.append({
                        "name":   "⚖ DOJI AT SUPPORT",
                        "detail": "Indecision candle at support — buyers and sellers in balance, breakout imminent",
                        "score":  12, "severity": "MEDIUM"
                    })

            result["candle_patterns"] = candle_patterns
        except Exception: pass

        # ══════════════════════════════════════════════
        # 3. PRICE DECELERATION (falling but slowing)
        #    Rate-of-change shrinking = momentum exhausted
        #    The move is dying → reversal incoming
        # ══════════════════════════════════════════════
        try:
            if n >= 11:
                ret_5d  = (float(closes.iloc[-1]) / float(closes.iloc[-6])  - 1) * 100
                ret_10d = (float(closes.iloc[-1]) / float(closes.iloc[-11]) - 1) * 100
                # Deceleration: 5d drop less than first half of 10d drop
                first_half = (float(closes.iloc[-6]) / float(closes.iloc[-11]) - 1) * 100
                is_falling = ret_10d < -3
                is_slowing = is_falling and abs(ret_5d) < abs(first_half) * 0.5

                if is_slowing and ret_10d < -5:
                    entry_score += 18
                    signals.append({
                        "name":   "🛑 SELLOFF DECELERATING",
                        "detail": f"Down {ret_10d:.1f}% in 10 days but only {ret_5d:.1f}% in last 5 — selling exhausting, buyers absorbing",
                        "score":  18, "severity": "HIGH"
                    })
                elif is_slowing:
                    entry_score += 10
                    signals.append({
                        "name":   "⚡ Momentum Slowing",
                        "detail": f"Down {ret_10d:.1f}% overall, pace decelerating — watch for reversal",
                        "score":  10, "severity": "MEDIUM"
                    })
        except Exception: pass

        # ══════════════════════════════════════════════
        # 4. RSI BULLISH DIVERGENCE TIMELINE
        #    Price making lower lows but RSI rising
        #    = buyers stepping in quietly at the bottom
        # ══════════════════════════════════════════════
        try:
            rsi_series = _calc_rsi_series(closes)
            div_days   = 0
            for lookback in range(5, min(30, n)):
                price_lower = float(closes.iloc[-1]) < float(closes.iloc[-lookback])
                rsi_higher  = float(rsi_series.iloc[-1]) > float(rsi_series.iloc[-lookback])
                if price_lower and rsi_higher:
                    div_days = lookback
                else:
                    break
            result["divergence_days"] = div_days
            if div_days >= 10:
                entry_score += 25
                signals.append({
                    "name":   f"📈 RSI BULLISH DIVERGENCE × {div_days} DAYS",
                    "detail": f"Price making lower lows but RSI rising for {div_days} days — smart money accumulating quietly",
                    "score":  25, "severity": "CRITICAL"
                })
            elif div_days >= 5:
                entry_score += 15
                signals.append({
                    "name":   f"📈 RSI Divergence × {div_days} days",
                    "detail": f"RSI not confirming price lows for {div_days} days — accumulation building",
                    "score":  15, "severity": "HIGH"
                })
        except Exception: pass

        # ══════════════════════════════════════════════
        # 5. VOLUME DRY-UP AT LOWS
        #    Sellers running out of ammo
        #    Low volume on down days = distribution over
        # ══════════════════════════════════════════════
        try:
            if n >= 10:
                recent_avg  = float(volumes.iloc[-3:].mean())
                prior_avg   = float(volumes.iloc[-10:-3].mean())
                price_down  = float(closes.iloc[-1]) < float(closes.iloc[-10])
                vol_drying  = recent_avg < prior_avg * 0.65

                if price_down and vol_drying:
                    entry_score += 16
                    signals.append({
                        "name":   "💧 VOLUME DRY-UP",
                        "detail": f"Price still falling but volume dropped {round((1-recent_avg/prior_avg)*100)}% — sellers exhausted, supply drying up",
                        "score":  16, "severity": "HIGH"
                    })
        except Exception: pass

        # ══════════════════════════════════════════════
        # 6. EXTREME FEAR / VIX SPIKE REVERSAL
        #    VIX ≥ 30 = near-term contrarian BUY signal
        #    Markets bottom when fear is maximum
        # ══════════════════════════════════════════════
        try:
            vix = spy_data.get("vix", 20) or 20
            if vix >= 35:
                entry_score += 20
                result["fear_extreme"] = True
                signals.append({
                    "name":   "😱 EXTREME FEAR — CONTRARIAN BUY",
                    "detail": f"VIX={vix} — historically, VIX ≥ 35 marks near-term bottoms. Fear is maximum = opportunity",
                    "score":  20, "severity": "HIGH"
                })
            elif vix >= 28:
                entry_score += 12
                signals.append({
                    "name":   f"⚠️ High Fear (VIX={vix})",
                    "detail": "Elevated fear often precedes recovery. Begin accumulation plan.",
                    "score":  12, "severity": "MEDIUM"
                })
        except Exception: pass

        # ══════════════════════════════════════════════
        # 7. AT KEY FIBONACCI SUPPORT
        #    38.2%, 50%, 61.8% retrace = institutional buy zones
        #    These are the levels where smart money places orders
        # ══════════════════════════════════════════════
        try:
            window     = min(60, n)
            swing_high = float(closes.iloc[-window:].max())
            swing_low  = float(closes.iloc[-window:].min())
            diff       = swing_high - swing_low
            fib_levels = {
                "61.8% Retrace": round(swing_high - 0.618 * diff, 2),
                "50.0% Retrace": round(swing_high - 0.500 * diff, 2),
                "38.2% Retrace": round(swing_high - 0.382 * diff, 2),
                "23.6% Retrace": round(swing_high - 0.236 * diff, 2),
            }
            result["fib_retrace"] = fib_levels
            for label, level in fib_levels.items():
                if abs(price - level) / price <= 0.015:
                    entry_score += 18
                    signals.append({
                        "name":   f"📐 AT FIB {label}",
                        "detail": f"Price ${round(price,2)} within 1.5% of {label} at ${level} — institutional buy zone",
                        "score":  18, "severity": "HIGH"
                    })
                    break
        except Exception: pass

        # ══════════════════════════════════════════════
        # 8. BELOW LOWER BOLLINGER / Z-SCORE OVERSOLD
        #    Statistically stretched = mean reversion due
        # ══════════════════════════════════════════════
        try:
            bb_lower = indicators.get("bb_lower", price * 0.95) or price * 0.95
            zscore   = indicators.get("zscore", 0) or 0
            if price <= bb_lower * 1.001:
                entry_score += 14
                signals.append({
                    "name":   "📉 BELOW LOWER BOLLINGER",
                    "detail": f"Price ${round(price,2)} at/below lower BB ${round(bb_lower,2)} — statistically oversold, mean reversion likely",
                    "score":  14, "severity": "MEDIUM"
                })
            if zscore <= -2:
                entry_score += 12
                signals.append({
                    "name":   f"📊 Z-SCORE OVERSOLD ({zscore:.1f}σ)",
                    "detail": f"Price {abs(zscore):.1f} standard deviations below mean — historically low probability of further decline",
                    "score":  12, "severity": "MEDIUM"
                })
        except Exception: pass

        # ══════════════════════════════════════════════
        # 9. OPTIONS PUT/CALL EXTREME + GEX POSITIVE
        #    P/C > 1.5 at lows = max pessimism = contrarian buy
        #    Positive GEX = MMs will stabilise price
        # ══════════════════════════════════════════════
        try:
            pc_ratio = mm_data.get("pc_ratio", 1.0) or 1.0
            gex      = mm_data.get("gex_total", 0) or 0
            near_low = float(closes.iloc[-1]) <= float(closes.iloc[-20:].min()) * 1.03

            if pc_ratio >= 1.5 and near_low:
                entry_score += 18
                signals.append({
                    "name":   "🔴 EXTREME PUT BUYING (Contrarian)",
                    "detail": f"P/C Ratio {pc_ratio:.2f} at lows — extreme pessimism historically precedes bounces",
                    "score":  18, "severity": "HIGH"
                })
            if gex > 300 and near_low:
                entry_score += 10
                signals.append({
                    "name":   "🟢 POSITIVE GEX — MM Support",
                    "detail": f"GEX +{gex:.0f}M — market makers will buy dips to hedge, creates a floor",
                    "score":  10, "severity": "MEDIUM"
                })
        except Exception: pass

        # ══════════════════════════════════════════════════════════
        # SUPPORT LEVELS — where the floor is
        # Cluster historical lows + Fibonacci + Put walls
        # ══════════════════════════════════════════════════════════
        try:
            support_candidates = []
            # Historical local lows
            for i in range(5, n - 5):
                if lows.iloc[i] == lows.iloc[max(0,i-5):i+6].min():
                    support_candidates.append(round(float(lows.iloc[i]), 2))
            # Cluster within 1%
            clustered_support = []
            for s in sorted(set(support_candidates)):
                if not clustered_support or s > clustered_support[-1] * 1.01:
                    clustered_support.append(s)
            # Levels below current price
            support_below = [s for s in clustered_support if s < price * 0.998][-4:]
            # Add put walls from options
            put_walls = mm_data.get("put_walls", [])
            for pw in (put_walls or []):
                if isinstance(pw, dict):
                    lv = pw.get("strike") or pw.get("level")
                    if lv and lv < price:
                        support_below.append(round(float(lv), 2))
            result["support_levels"] = sorted(set(support_below))[-4:]
        except Exception: pass

        # ══════════════════════════════════════════════════════════
        # INVALIDATION LEVEL — where thesis is proven wrong
        # Set below the lowest recent support
        # ══════════════════════════════════════════════════════════
        try:
            recent_low = float(lows.iloc[-20:].min())
            result["invalidation"] = round(recent_low * 0.97, 2)  # 3% below 20-day low
        except Exception:
            result["invalidation"] = round(price * 0.93, 2)

        # ══════════════════════════════════════════════════════════
        # ENTRY SCORE → URGENCY
        # ══════════════════════════════════════════════════════════
        entry_score = min(entry_score, 100)
        result["entry_score"] = entry_score

        if   entry_score >= 70:
            result.update({"entry_urgency": "🟢 BUY NOW",    "entry_color": "#00ff88"})
        elif entry_score >= 50:
            result.update({"entry_urgency": "📈 ACCUMULATE", "entry_color": "#69f0ae"})
        elif entry_score >= 30:
            result.update({"entry_urgency": "👁 WATCH",      "entry_color": "var(--gold)"})
        else:
            result.update({"entry_urgency": "⏳ WAIT",       "entry_color": "var(--text-dim)"})

        # ══════════════════════════════════════════════════════════
        # 3-TRANCHE STAGED ENTRY PLAN
        # Based on score + support levels + CTA allocation
        # ══════════════════════════════════════════════════════════
        try:
            # Base deploy % from CTA vol-scaling (already computed in sizing)
            # We'll compute independently here so entry engine is self-contained

            # Asset vol for sizing reference
            returns   = closes.pct_change().dropna()
            vol_20d   = float(returns.iloc[-20:].std()) * (252 ** 0.5)
            target_vol = 0.12
            base_ratio = min(target_vol / (vol_20d + 1e-9), 2.0)

            # Scale deploy % by entry score — don't go all-in on weak signals
            score_factor = entry_score / 100.0
            if   entry_score >= 70: max_deploy_pct = min(base_ratio * 100 * 0.9, 80)   # Up to 80%
            elif entry_score >= 50: max_deploy_pct = min(base_ratio * 100 * 0.65, 55)  # Up to 55%
            elif entry_score >= 30: max_deploy_pct = min(base_ratio * 100 * 0.35, 30)  # Up to 30%
            else:                   max_deploy_pct = 0

            # Support levels for tranche prices
            supports = result["support_levels"]
            s1 = supports[-1] if len(supports) >= 1 else round(price * 0.97, 2)
            s2 = supports[-2] if len(supports) >= 2 else round(price * 0.94, 2)

            # Tranche 1 — Buy now (signal confirmed) — 35% of allocation
            t1_pct    = round(max_deploy_pct * 0.35, 1)
            t1_price  = round(price, 2)
            t1_shares = int((portfolio_value * t1_pct / 100) / price) if price > 0 else 0
            t1_dollar = round(portfolio_value * t1_pct / 100, 2)

            # Tranche 2 — Add on pullback to first support — 40% of allocation
            t2_pct    = round(max_deploy_pct * 0.40, 1)
            t2_price  = s1
            t2_shares = int((portfolio_value * t2_pct / 100) / t2_price) if t2_price > 0 else 0
            t2_dollar = round(portfolio_value * t2_pct / 100, 2)

            # Tranche 3 — Add on confirmation breakout — 25% of allocation
            t3_pct    = round(max_deploy_pct * 0.25, 1)
            t3_price  = round(price * 1.025, 2)   # Confirmed: price breaks above entry +2.5%
            t3_shares = int((portfolio_value * t3_pct / 100) / t3_price) if t3_price > 0 else 0
            t3_dollar = round(portfolio_value * t3_pct / 100, 2)

            result["tranche_plan"] = [
                {
                    "number":    1,
                    "label":     "BUY NOW",
                    "trigger":   f"Signal confirmed at ${t1_price}",
                    "price":     t1_price,
                    "pct_cap":   t1_pct,
                    "dollars":   t1_dollar,
                    "shares":    t1_shares,
                    "color":     "#00ff88",
                    "rationale": "Initial position — signal firing, enter with 35% of allocation"
                },
                {
                    "number":    2,
                    "label":     "ADD ON DIP",
                    "trigger":   f"Price pulls back to ${t2_price} (support)",
                    "price":     t2_price,
                    "pct_cap":   t2_pct,
                    "dollars":   t2_dollar,
                    "shares":    t2_shares,
                    "color":     "#69f0ae",
                    "rationale": "Add on pullback to key support — best average cost, 40% of allocation"
                },
                {
                    "number":    3,
                    "label":     "CONFIRM BREAKOUT",
                    "trigger":   f"Price reclaims ${t3_price} (+2.5% above entry)",
                    "price":     t3_price,
                    "pct_cap":   t3_pct,
                    "dollars":   t3_dollar,
                    "shares":    t3_shares,
                    "color":     "var(--gold)",
                    "rationale": "Confirmation tranche — breakout confirms the bottom is in, 25% of allocation"
                },
            ]

            result["total_deploy_pct"] = round(max_deploy_pct, 1)
            result["total_deploy_$"]   = round(portfolio_value * max_deploy_pct / 100, 2)

        except Exception as e:
            print(f"  ⚠️ Tranche calc error: {e}")

        # Reasons summary
        result["entry_reasons"] = [s["detail"] for s in signals[:4]]
        result["signals"]       = sorted(signals, key=lambda x: -x["score"])

        print(f"  🟢 Entry: {entry_score}/100 | {result.get("entry_urgency","")} | Deploy: {result.get("total_deploy_pct","")}% | {len(signals)} signals")

    except Exception as e:
        print(f"  ❌ Entry signals error: {e}")
        import traceback; traceback.print_exc()

    return result



def calculate_peak_signals(closes, highs, lows, volumes, opens,
                            mm_data=None, indicators=None):
    mm_data    = mm_data or {}
    indicators = indicators or {}
    result = {
        "signals": [], "peak_score": 0, "peak_urgency": "CLEAR",
        "peak_color": "#00ff88", "countdown_bars": None,
        "optimal_exit_window": "—", "top_price_target": None,
        "hard_stop": None, "candle_patterns": [],
        "vol_climax_ratio": None, "divergence_days": 0,
        "acceleration_pct": None,
    }
    try:
        price = float(closes.iloc[-1])
        n     = len(closes)
        peak_score = 0
        signals    = []

        # 1. BUYING CLIMAX
        try:
            avg_vol_20 = float(volumes.iloc[-20:].mean())
            today_vol  = float(volumes.iloc[-1])
            vol_ratio  = round(today_vol / (avg_vol_20 + 1), 2)
            is_new_high_20 = float(highs.iloc[-1]) >= float(highs.iloc[-20:].max()) * 0.998
            result["vol_climax_ratio"] = vol_ratio
            if vol_ratio >= 3.0 and is_new_high_20:
                peak_score += 30
                signals.append({"name": "🚨 BUYING CLIMAX", "detail": f"Volume {vol_ratio}× avg at 20-day high — last buyers in, Wyckoff top signal", "score": 30, "severity": "CRITICAL"})
            elif vol_ratio >= 2.0 and is_new_high_20:
                peak_score += 18
                signals.append({"name": "⚠️ Elevated Volume at High", "detail": f"Volume {vol_ratio}× avg near recent high — watch for reversal", "score": 18, "severity": "WARNING"})
        except Exception: pass

        # 2. CANDLE PATTERNS
        try:
            candle_patterns = []
            for i in [-1, -2, -3]:
                o = float(opens.iloc[i]); h = float(highs.iloc[i])
                l = float(lows.iloc[i]);  c = float(closes.iloc[i])
                body = abs(c - o); range_ = h - l
                if range_ < 1e-9: continue
                upper_wick = h - max(o, c); lower_wick = min(o, c) - l
                if upper_wick >= 2 * body and body <= 0.3 * range_ and lower_wick < body:
                    candle_patterns.append({"bar": i, "pattern": "Shooting Star", "severity": "HIGH"})
                    if i == -1:
                        peak_score += 22
                        signals.append({"name": "🕯 SHOOTING STAR", "detail": f"Rejection candle at ${round(h,2)} — buyers pushed up then sellers slammed it back", "score": 22, "severity": "HIGH"})
                elif body <= 0.05 * range_ and float(highs.iloc[i]) >= float(highs.iloc[-20:].max()) * 0.98:
                    candle_patterns.append({"bar": i, "pattern": "Doji at High", "severity": "MEDIUM"})
                    if i == -1:
                        peak_score += 14
                        signals.append({"name": "⚖ DOJI AT HIGH", "detail": "Indecision candle near resistance — equilibrium at top", "score": 14, "severity": "MEDIUM"})
                if i == -1 and c < o:
                    prev_o = float(opens.iloc[-2]); prev_c = float(closes.iloc[-2])
                    if prev_c > prev_o and o >= prev_c and c <= prev_o:
                        candle_patterns.append({"bar": -1, "pattern": "Bearish Engulfing", "severity": "HIGH"})
                        peak_score += 25
                        signals.append({"name": "🐻 BEARISH ENGULFING", "detail": "Today completely swallowed yesterday's bullish bar — aggressive reversal", "score": 25, "severity": "CRITICAL"})
            result["candle_patterns"] = candle_patterns
        except Exception: pass

        # 3. PRICE ACCELERATION
        try:
            if n >= 11:
                ret_5d  = (float(closes.iloc[-1]) / float(closes.iloc[-6])  - 1) * 100
                ret_10d = (float(closes.iloc[-1]) / float(closes.iloc[-11]) - 1) * 100
                result["acceleration_pct"] = round(ret_5d, 2)
                if ret_5d > 8 and ret_5d > ret_10d * 0.7:
                    peak_score += 20
                    signals.append({"name": "🚀 PARABOLIC ACCELERATION", "detail": f"Up {ret_5d:.1f}% in 5 days vs {ret_10d:.1f}% in 10 — unsustainable velocity", "score": 20, "severity": "HIGH"})
                elif ret_5d > 5:
                    peak_score += 10
                    signals.append({"name": "⚡ Rapid Move", "detail": f"Up {ret_5d:.1f}% in 5 days — watch for exhaustion", "score": 10, "severity": "MEDIUM"})
        except Exception: pass

        # 4. RSI DIVERGENCE TIMELINE
        try:
            rsi_series = _calc_rsi_series(closes)
            div_days = 0
            for lookback in range(5, min(30, n)):
                if float(closes.iloc[-1]) > float(closes.iloc[-lookback]) and float(rsi_series.iloc[-1]) < float(rsi_series.iloc[-lookback]):
                    div_days = lookback
                else:
                    break
            result["divergence_days"] = div_days
            if div_days >= 10:
                peak_score += 25
                signals.append({"name": f"📉 RSI DIVERGENCE × {div_days} DAYS", "detail": f"Price higher highs but RSI declining {div_days} days — textbook distribution", "score": 25, "severity": "CRITICAL"})
            elif div_days >= 5:
                peak_score += 15
                signals.append({"name": f"📉 RSI Divergence × {div_days} days", "detail": f"RSI not confirming price highs for {div_days} days", "score": 15, "severity": "HIGH"})
        except Exception: pass

        # 5. PUT/CALL AT HIGH
        try:
            pc_ratio = mm_data.get("pc_ratio", 1.0) or 1.0
            max_pain = mm_data.get("max_pain", price) or price
            if pc_ratio > 1.3 and float(closes.iloc[-1]) >= float(closes.iloc[-20:].max()) * 0.97:
                peak_score += 18
                signals.append({"name": "🔴 PUT BUYING AT HIGH", "detail": f"P/C Ratio {pc_ratio:.2f} while near 20-day high — smart money hedging", "score": 18, "severity": "HIGH"})
            if abs(price - max_pain) / price < 0.03:
                peak_score += 8
                signals.append({"name": "📌 Near Max Pain", "detail": f"Price within 3% of Max Pain ${max_pain} — options expiry magnetic zone", "score": 8, "severity": "LOW"})
        except Exception: pass

        # 6. VOLUME DISTRIBUTION
        try:
            if n >= 10:
                recent_avg = float(volumes.iloc[-5:].mean())
                prior_avg  = float(volumes.iloc[-10:-5].mean())
                if float(closes.iloc[-1]) > float(closes.iloc[-6]) and recent_avg < prior_avg * 0.75:
                    peak_score += 16
                    signals.append({"name": "📊 VOLUME DISTRIBUTION", "detail": f"Price rising but volume down {round((1-recent_avg/prior_avg)*100)}% — professionals selling into retail", "score": 16, "severity": "HIGH"})
        except Exception: pass

        # 7. GEX FLIP
        try:
            gex = mm_data.get("gex_total", 0) or 0
            if gex < -200:
                peak_score += 12
                signals.append({"name": "⚡ NEGATIVE GEX", "detail": f"GEX {gex:+.0f}M — market makers not pinning price, free to fall", "score": 12, "severity": "MEDIUM"})
        except Exception: pass

        # 8. BOLLINGER UPPER BAND
        try:
            bb_upper = indicators.get("bb_upper", price * 1.05) or price * 1.05
            if price >= bb_upper * 0.999:
                peak_score += 14
                signals.append({"name": "📈 AT UPPER BOLLINGER", "detail": f"${round(price,2)} touching upper BB ${round(bb_upper,2)} — statistically extended", "score": 14, "severity": "MEDIUM"})
        except Exception: pass

        # 9. OVERBOUGHT CLUSTER
        try:
            rsi_val  = indicators.get("rsi", 50) or 50
            ob_count = sum([rsi_val > 70, (indicators.get("zscore",0) or 0) > 2, indicators.get("macd_hist",0) < 0 and rsi_val > 60])
            if ob_count >= 2:
                peak_score += 15
                signals.append({"name": "🔴 OVERBOUGHT CLUSTER", "detail": f"{ob_count}/3 overbought indicators simultaneously — high confluence top", "score": 15, "severity": "HIGH"})
        except Exception: pass

        # URGENCY
        peak_score = min(peak_score, 100)
        result["peak_score"] = peak_score
        if   peak_score >= 70: result.update({"peak_urgency":"🚨 SELL NOW",   "peak_color":"#ff1744", "countdown_bars":1, "optimal_exit_window":"Exit immediately — reversal imminent"})
        elif peak_score >= 50: result.update({"peak_urgency":"⚠️ NEAR TOP",   "peak_color":"#ff6d00", "countdown_bars":3, "optimal_exit_window":"Sell into next 1–3 day bounce — do not wait"})
        elif peak_score >= 30: result.update({"peak_urgency":"👁 WATCH",      "peak_color":"#ffd600", "countdown_bars":7, "optimal_exit_window":"Reduce 25–50% at next resistance, trail stop"})
        else:                  result.update({"peak_urgency":"✅ CLEAR",      "peak_color":"#00ff88", "countdown_bars":None, "optimal_exit_window":"No topping signals — hold with stop below SAR"})

        try:
            res_above = [r for r in [float(highs.iloc[-20:].max()), indicators.get("bb_upper")] if r and r > price]
            result["top_price_target"] = round(min(res_above), 2) if res_above else round(price * 1.02, 2)
            result["hard_stop"] = round(float(lows.iloc[-3:].min()) * 0.995, 2)
        except Exception: pass

        result["signals"] = sorted(signals, key=lambda x: -x["score"])
        print(f"  🎯 Peak: {peak_score}/100 | {result.get("peak_urgency","")} | {len(signals)} signals")
    except Exception as e:
        print(f"  ❌ Peak error: {e}")
    return result

# ═══════════════════════════════════════════════════════════════
#  SEC EDGAR — 13F INSTITUTIONAL DATA
# ═══════════════════════════════════════════════════════════════

def fetch_institutional_data():
    institutions = [
        {"name": "Vanguard Group",  "cik": "0000102909"},
        {"name": "BlackRock",       "cik": "0001364742"},
        {"name": "State Street",    "cik": "0000093751"},
        {"name": "ARK Invest",      "cik": "0001579982"},
        {"name": "Geode Capital",   "cik": "0001484544"},
    ]
    results = []
    for inst in institutions:
        try:
            # SEC EDGAR requires exactly 10-digit CIK with leading zeros
            cik_padded = inst["cik"].zfill(10)
            url  = f"https://data.sec.gov/submissions/CIK{cik_padded}.json"
            resp = requests.get(url, headers=SEC_HEADERS, timeout=15)
            print(f"  EDGAR {inst.get("name","")}: HTTP {resp.status_code} → {url}")
            if resp.status_code != 200: continue
            data     = resp.json()
            filings  = data.get("filings", {}).get("recent", {})
            forms    = filings.get("form", [])
            dates    = filings.get("filingDate", [])
            for i, form in enumerate(forms):
                if form in ("13F-HR", "13F-HR/A"):
                    days_ago = (datetime.now() - datetime.strptime(dates[i], "%Y-%m-%d")).days
                    action   = "RECENT FILING" if days_ago < 45 else "QUARTERLY UPDATE" if days_ago < 90 else "OLDER FILING"
                    results.append({"institution": inst["name"], "form": form, "date": dates[i], "action": action})
                    break
        except Exception as e:
            print(f"⚠️  EDGAR error {inst.get("name","")}: {e}")
    return sorted(results, key=lambda x: x["date"], reverse=True)


# ═══════════════════════════════════════════════════════════════
#  SMS ALERT
# ═══════════════════════════════════════════════════════════════

# Track last WhatsApp send time for throttling
_last_wa_send = {}   # key → datetime

def send_whatsapp(message, alert_key="default"):
    """
    Send WhatsApp message via Green API (free tier).
    https://green-api.com — scan QR code to connect your WhatsApp.
    Throttled per alert_key to avoid spam.
    """
    global _last_wa_send
    if not WA_ENABLED:
        print(f"🔔 ALERT (WhatsApp off): {message[:80]}...")
        return False
    # Throttle: don't resend same alert type within WA_THROTTLE_MIN minutes
    # Track alert for quality scoring
    _cur_price = state.get("price", 0) or 0
    _cur_signal = state.get("signal", "HOLD")
    _alert_outcomes.append({
        "alert_key":  alert_key,
        "signal":     _cur_signal,
        "price":      _cur_price,
        "timestamp":  time.time(),
        "ticker":     TICKER,
    })
    # Keep last 500 alerts
    if len(_alert_outcomes) > 500:
        _alert_outcomes.pop(0)
    # Check outcomes of past alerts
    for _past in _alert_outcomes[-50:]:
        _check_alert_outcome(_past, _cur_price)

    last = _last_wa_send.get(alert_key)
    if last and (datetime.now() - last).total_seconds() < WA_THROTTLE_MIN * 60:
        print(f"⏳ WhatsApp throttled ({alert_key}) — {WA_THROTTLE_MIN}min cooldown")
        return False
    try:
        # Green API endpoint
        url = (
            f"https://api.green-api.com"
            f"/waInstance{GREEN_INSTANCE}"
            f"/sendMessage"
            f"/{GREEN_TOKEN}"
        )
        # chatId format: phonenumber@c.us
        payload = {
            "chatId":  f"{GREEN_PHONE}@c.us",
            "message": message
        }
        resp = requests.post(url, json=payload, timeout=15)
        data = resp.json() if resp.content else {}
        if resp.status_code == 200 and data.get("idMessage"):
            _last_wa_send[alert_key] = datetime.now()
            print(f"✅ WhatsApp sent via Green API ({alert_key}): {message[:60]}...")
            return True
        else:
            print(f"⚠️ Green API response: {resp.status_code} — {resp.text[:120]}")
            return False
    except Exception as e:
        print(f"❌ WhatsApp error: {e}")
        return False


def _check_alert_outcome(alert_entry, current_price):
    """Check if a past alert was profitable. Called on each analysis cycle."""
    try:
        import time as _t
        alert_time  = alert_entry.get("timestamp", 0)
        alert_price = float(alert_entry.get("price", current_price) or current_price)
        signal      = alert_entry.get("signal", "HOLD")
        elapsed_h   = (time.time() - alert_time) / 3600

        if signal == "HOLD" or alert_price <= 0:
            return

        price_chg = (current_price - alert_price) / alert_price * 100

        # 1-hour outcome
        if elapsed_h >= 1.0 and not alert_entry.get("outcome_1h"):
            profitable = (signal == "BUY" and price_chg > 0) or (signal == "SELL" and price_chg < 0)
            alert_entry["outcome_1h"]   = round(price_chg, 2)
            alert_entry["profit_1h"]    = profitable
            alert_entry["price_1h"]     = round(current_price, 2)

        # 1-day outcome
        if elapsed_h >= 24.0 and not alert_entry.get("outcome_1d"):
            profitable = (signal == "BUY" and price_chg > 0) or (signal == "SELL" and price_chg < 0)
            alert_entry["outcome_1d"]   = round(price_chg, 2)
            alert_entry["profit_1d"]    = profitable
            alert_entry["price_1d"]     = round(current_price, 2)
    except Exception:
        pass


def _get_alert_scorecard():
    """Compute win rates for each alert type."""
    scorecard = {}
    for entry in _alert_outcomes[-200:]:   # last 200 alerts
        key    = entry.get("alert_key", "unknown")
        signal = entry.get("signal", "?")
        label  = f"{key}_{signal}" if signal not in key else key

        if label not in scorecard:
            scorecard[label] = {"total": 0, "win_1h": 0, "win_1d": 0, "avg_chg_1h": [], "avg_chg_1d": []}

        scorecard[label]["total"] += 1
        if entry.get("outcome_1h") is not None:
            if entry.get("profit_1h"):
                scorecard[label]["win_1h"] += 1
            scorecard[label]["avg_chg_1h"].append(entry["outcome_1h"])
        if entry.get("outcome_1d") is not None:
            if entry.get("profit_1d"):
                scorecard[label]["win_1d"] += 1
            scorecard[label]["avg_chg_1d"].append(entry["outcome_1d"])

    # Compute averages
    result = {}
    for label, s in scorecard.items():
        n1h = len(s["avg_chg_1h"]); n1d = len(s["avg_chg_1d"])
        result[label] = {
            "total":       s["total"],
            "win_rate_1h": round(s["win_1h"] / max(n1h, 1) * 100, 1) if n1h > 0 else None,
            "win_rate_1d": round(s["win_1d"] / max(n1d, 1) * 100, 1) if n1d > 0 else None,
            "avg_chg_1h":  round(sum(s["avg_chg_1h"]) / max(n1h, 1), 2) if n1h > 0 else None,
            "avg_chg_1d":  round(sum(s["avg_chg_1d"]) / max(n1d, 1), 2) if n1d > 0 else None,
        }
    return result


def log_alert(message, alert_key="default"):
    """Log to dashboard and send WhatsApp if configured."""
    print(f"🔔 ALERT: {message[:80]}...")
    send_whatsapp(message, alert_key)


# ═══════════════════════════════════════════════════════════════
#  CORE MONITOR LOOP
# ═══════════════════════════════════════════════════════════════

last_signal = None


def calculate_master_signal(signal, strength, ml_signal, mm_data, uoa_data,
                             dv_result, entry_data, peak_data, exit_score,
                             spy_data, cap_result, ichi, hmm_result,
                             news_data, indicators, price):
    """
    Master Signal — synthesizes ALL models into one clear decision.
    
    Returns dict:
        action:      STRONG BUY / BUY / HOLD / SELL / STRONG SELL
        score:       -100 to +100
        conviction:  0-100% (% of models agreeing)
        reasons:     top 3 drivers
        risk:        LOW / MEDIUM / HIGH / EXTREME
        color:       hex color for UI
    """
    score   = 0
    reasons = []
    votes   = {"bull": 0, "bear": 0, "neutral": 0}

    # ── TIER 1: HIGH CONVICTION (±30 pts each) ──────────────────────────────

    # 1. UOA Net Flow — smart money options activity
    uoa_flow   = uoa_data.get("net_flow", "NEUTRAL")
    uoa_prem   = uoa_data.get("total_call_premium", 0) - uoa_data.get("total_put_premium", 0)
    uoa_whales = len(uoa_data.get("whale_alerts", []))
    if "STRONGLY BULLISH" in uoa_flow:
        score += 30; reasons.append(f"Smart money STRONGLY BULLISH (${abs(uoa_prem/1e6):.0f}M calls)")
        votes["bull"] += 1
    elif "BULLISH" in uoa_flow:
        score += 18; reasons.append(f"Smart money BULLISH (${abs(uoa_prem/1e6):.0f}M call heavy)")
        votes["bull"] += 1
    elif "STRONGLY BEARISH" in uoa_flow:
        score -= 30; reasons.append(f"Smart money STRONGLY BEARISH (${abs(uoa_prem/1e6):.0f}M puts)")
        votes["bear"] += 1
    elif "BEARISH" in uoa_flow:
        score -= 18; reasons.append(f"Smart money BEARISH (${abs(uoa_prem/1e6):.0f}M put heavy)")
        votes["bear"] += 1
    else:
        votes["neutral"] += 1

    # 2. ML Ensemble (67 features + SPY/QQQ context)
    ml_sig  = ml_signal.get("signal", "HOLD")
    ml_conf = ml_signal.get("confidence", 0) or 0
    ml_prob = ml_signal.get("probability", 0.5) or 0.5
    if ml_sig == "BUY" and ml_conf >= 30:
        pts = min(30, int(ml_conf * 0.4))
        score += pts; reasons.append(f"ML ensemble BUY (conf {ml_conf}%, prob {ml_prob:.0%})")
        votes["bull"] += 1
    elif ml_sig == "SELL" and ml_conf >= 30:
        pts = min(30, int(ml_conf * 0.4))
        score -= pts; reasons.append(f"ML ensemble SELL (conf {ml_conf}%, prob {ml_prob:.0%})")
        votes["bear"] += 1
    else:
        votes["neutral"] += 1

    # ── TIER 2: MARKET STRUCTURE (±20 pts each) ─────────────────────────────

    # 3. GEX + Max Pain gravity
    gex      = float(mm_data.get("gex_total", 0) or 0)
    max_pain = float(mm_data.get("max_pain", price) or price)
    pain_pull = (max_pain - price) / max(price, 1) * 100  # % to max pain
    if gex > 100:
        score += 12; reasons.append(f"GEX +{gex:.0f}M: dealers long gamma → stabilizing")
        votes["bull"] += 1
    elif gex < -100:
        score -= 12; reasons.append(f"GEX {gex:.0f}M: dealers short gamma → amplifying moves")
        votes["bear"] += 1
    else:
        votes["neutral"] += 1
    if pain_pull > 3:
        score += 8; reasons.append(f"Max Pain ${max_pain:.0f} is {pain_pull:.1f}% above — magnetic pull UP")
        votes["bull"] += 1
    elif pain_pull < -3:
        score -= 8; reasons.append(f"Max Pain ${max_pain:.0f} is {abs(pain_pull):.1f}% below — pull DOWN")
        votes["bear"] += 1

    # 4. DarthVader institutional intelligence
    dv_state = dv_result.get("tsla_state", {}).get("state", "") if dv_result else ""
    dv_risk  = dv_result.get("risk_mode", "NORMAL") if dv_result else "NORMAL"
    dv_conf  = float(dv_result.get("tsla_state", {}).get("confidence", 0) or 0) if dv_result else 0
    if "CAPITULATION_BOUNCE" in dv_state and dv_conf > 0.5:
        score += 20; reasons.append(f"DarthVader: CAPITULATION BOUNCE ({dv_conf:.0%} conf)")
        votes["bull"] += 1
    elif "ACCUMULATION" in dv_state:
        score += 15; votes["bull"] += 1
    elif "LIQUIDITY_VACUUM" in dv_state and dv_risk == "DEFENSIVE":
        score -= 15; reasons.append("DarthVader: DEFENSIVE — institutional caution")
        votes["bear"] += 1
    elif "DISTRIBUTION" in dv_state or "MEAN_REVERSION" in dv_state:
        score -= 10; votes["bear"] += 1
    else:
        votes["neutral"] += 1

    # ── TIER 3: TECHNICAL (±10 pts each) ────────────────────────────────────

    # 5. Main multi-factor signal
    if signal == "BUY":
        pts = min(10, max(3, strength // 10))
        score += pts; votes["bull"] += 1
    elif signal == "SELL":
        pts = min(10, max(3, strength // 10))
        score -= pts; votes["bear"] += 1
    else:
        votes["neutral"] += 1

    # 6. Entry/Exit score composite
    entry_score = entry_data.get("entry_score", 0) or 0
    if entry_score >= 70:
        score += 10; reasons.append(f"Entry score STRONG ({entry_score}/100)")
        votes["bull"] += 1
    elif entry_score >= 50:
        score += 5; votes["bull"] += 1
    if exit_score >= 70:
        score -= 10; reasons.append(f"Exit score HIGH ({exit_score}/100) — overbought")
        votes["bear"] += 1
    elif exit_score >= 55:
        score -= 5; votes["bear"] += 1

    # 7. HMM regime
    hmm_reg = hmm_result.get("regime", "NEUTRAL") if hmm_result else "NEUTRAL"
    if "BULL" in hmm_reg:
        score += 8; votes["bull"] += 1
    elif "BEAR" in hmm_reg:
        score -= 8; votes["bear"] += 1
    else:
        votes["neutral"] += 1

    # 8. SPY/QQQ macro backdrop
    macro_score = float(spy_data.get("macro_score", 0) or 0)
    spy_ob = spy_data.get("spy_ob", False)
    spy_os = spy_data.get("spy_os", False)
    qqq_ob = spy_data.get("qqq_ob", False)
    qqq_os = spy_data.get("qqq_os", False)
    if spy_ob and qqq_ob:
        score -= 10; reasons.append("SPY + QQQ both overbought — market stretched")
        votes["bear"] += 1
    elif spy_os and qqq_os:
        score += 10; reasons.append("SPY + QQQ both oversold — market washed out")
        votes["bull"] += 1
    elif macro_score >= 20:
        score += 6; votes["bull"] += 1
    elif macro_score <= -20:
        score -= 6; votes["bear"] += 1
    else:
        votes["neutral"] += 1

    # ── TIER 4: CONFIRMING (±5 pts each) ────────────────────────────────────

    # 9. Capitulation bounce
    if cap_result and cap_result.get("detected"):
        cap_conv = cap_result.get("conviction", 0) or 0
        if cap_conv >= 60:
            score += 5; votes["bull"] += 1
        else:
            votes["neutral"] += 1

    # 10. Ichimoku cloud
    cloud = ichi.get("cloud_signal", "NEUTRAL") if ichi else "NEUTRAL"
    if "BULL" in cloud.upper():
        score += 5; votes["bull"] += 1
    elif "BEAR" in cloud.upper():
        score -= 5; votes["bear"] += 1
    else:
        votes["neutral"] += 1

    # 11. News sentiment
    news_score = float(news_data.get("score", 0) or 0) if news_data else 0
    if news_score >= 20:
        score += 5; votes["bull"] += 1
    elif news_score <= -20:
        score -= 5; votes["bear"] += 1
    else:
        votes["neutral"] += 1

    # 12. Momentum (price action confirmation)
    ret_1b = float(indicators.get("ret_1b", 0) or 0)
    ret_3b = float(indicators.get("ret_3b", 0) or 0)
    if ret_1b > 0.003 and ret_3b > 0.005:
        score += 5; votes["bull"] += 1
    elif ret_1b < -0.003 and ret_3b < -0.005:
        score -= 5; votes["bear"] += 1
    else:
        votes["neutral"] += 1

    # ── FINAL DECISION ───────────────────────────────────────────────────────
    score = max(-100, min(100, score))

    total_votes = votes["bull"] + votes["bear"] + votes["neutral"]
    bull_pct    = round(votes["bull"] / max(total_votes, 1) * 100)
    bear_pct    = round(votes["bear"] / max(total_votes, 1) * 100)
    conviction  = max(bull_pct, bear_pct)

    # Require BOTH score threshold AND minimum conviction
    min_conv_buy  = 55   # at least 55% of models must agree for BUY
    min_conv_sell = 55   # at least 55% of models must agree for SELL

    if score >= 65 and conviction >= min_conv_buy:
        action = "STRONG BUY";  color = "#00ff88"
    elif score >= 40 and conviction >= min_conv_buy:
        action = "BUY";         color = "#69f0ae"
    elif score <= -65 and conviction >= min_conv_sell:
        action = "STRONG SELL"; color = "#ff1744"
    elif score <= -40 and conviction >= min_conv_sell:
        action = "SELL";        color = "#ff6d00"
    else:
        action = "HOLD";        color = "#00e5ff"
        # Show WHY it's HOLD if score was close
        if score >= 40 and conviction < min_conv_buy:
            action = "HOLD — LOW CONVICTION"; color = "#ffb300"
        elif score <= -40 and conviction < min_conv_sell:
            action = "HOLD — LOW CONVICTION"; color = "#ffb300"

    # Risk level
    vix = float(spy_data.get("vix", 20) or 20)
    abs_gex = abs(gex)
    if vix >= 35 or abs_gex >= 500:
        risk = "EXTREME"
    elif vix >= 25 or abs_gex >= 200:
        risk = "HIGH"
    elif vix >= 18 or abs_gex >= 100:
        risk = "MEDIUM"
    else:
        risk = "LOW"

    # Top 3 reasons (deduplicated)
    top_reasons = reasons[:3] if reasons else ["Insufficient signal confluence"]

    return {
        "action":        action,
        "score":         score,
        "conviction":    conviction,
        "bull_votes":    votes["bull"],
        "bear_votes":    votes["bear"],
        "neutral_votes": votes["neutral"],
        "total_models":  total_votes,
        "reasons":       top_reasons,
        "risk":          risk,
        "color":         color,
        "vix":           round(vix, 1),
        "gex":           round(gex, 0),
    }

def run_analysis():
    global last_signal
    print(f"\n[ANALYSIS] {TICKER} @ {datetime.now().strftime('%H:%M:%S')}...", flush=True)
    try:
        # ── Fetch price history — Schwab first, yfinance fallback ──
        hist = None
        if sc.is_configured() and sc.get_client():
            try:
                print(f"  📡 Fetching {TICKER} via Schwab API (5-min bars, 2yr)...", flush=True)
                hist = sc.get_price_history(TICKER, period_years=2, freq_minutes=5)
                if hist is not None and not hist.empty:
                    print(f"  📡 Schwab: {len(hist)} bars loaded", flush=True)
                else:
                    hist = None
            except Exception as _se:
                print(f"  ⚠️ Schwab history failed: {_se} — falling back to yfinance", flush=True)
                hist = None

        if hist is None or (hasattr(hist, 'empty') and hist.empty):
            for _attempt in range(3):
                try:
                    hist = yf.Ticker(TICKER).history(period="6mo", interval="1d")
                    if not hist.empty:
                        break
                    print(f"  ⚠️ yfinance returned empty data (attempt {_attempt+1}/3)")
                    time.sleep(2)
                except Exception as _ye:
                    print(f"  ⚠️ yfinance fetch error (attempt {_attempt+1}/3): {_ye}")
                    time.sleep(2)

        if hist is None or hist.empty:
            print(f"[FATAL] Could not fetch {TICKER} data — retrying next cycle",flush=True)
            state.update({"signal":"WAIT","price":state.get("price",0),"market_state":"DATA UNAVAILABLE","last_updated":datetime.now().strftime("%H:%M:%S"),"signal_strength":0})
            return
        closes  = hist["Close"]
        volumes = hist["Volume"]
        price   = round(float(closes.iloc[-1]), 2)

        # ── Real-time quote from Schwab (no 15-min delay) ──
        if sc.is_configured() and sc.get_client():
            try:
                _rt = sc.get_quote(TICKER)
                if _rt.get("price", 0) > 0:
                    price = round(float(_rt["price"]), 2)
                    print(f"  📡 Schwab real-time: ${price} ({_rt.get('change_pct',0):+.2f}%)", flush=True)
            except Exception as _qe:
                pass  # silently fall back to hist price

        rsi                    = calculate_rsi(closes)
        macd_val, macd_sig, macd_hist = calculate_macd(closes)
        bb_upper, bb_mid, bb_lower    = calculate_bollinger(closes)
        ema50                  = calculate_ema(closes, 50)
        ema200                 = calculate_ema(closes, 200)
        avg_vol                = volumes.iloc[-20:].mean()
        vol_ratio              = round(volumes.iloc[-1] / avg_vol, 2) if avg_vol > 0 else 1.0

        # ── Ichimoku Cloud ──
        highs  = hist["High"]
        lows   = hist["Low"]
        ichi   = calculate_ichimoku(highs, lows, closes)

        # ── Hidden Markov Model ──
        hmm_result = calculate_hmm(closes)

        # ══ INSTITUTIONAL / WALL STREET MODELS ══
        opens_s  = hist["Open"]
        vwap_r   = calculate_vwap(highs, lows, closes, volumes)
        kalman_r = calculate_kalman_filter(closes)
        zscore_r = calculate_zscore(closes)
        kelly_r  = calculate_kelly(closes)
        mc_r     = calculate_monte_carlo_var(closes, simulations=3000, horizon=10)
        factor_r = calculate_factor_model(closes, volumes)
        smi_r    = calculate_smart_money_index(opens_s, closes, volumes)

        inst_models = {
            "vwap":        vwap_r,
            "kalman":      kalman_r,
            "zscore":      zscore_r,
            "kelly":       kelly_r,
            "monte_carlo": mc_r,
            "factor":      factor_r,
            "smart_money": smi_r,
        }

        # ══ SPY / MACRO ENGINE ══
        try:
            spy_data = calculate_spy_analysis(closes, price)
        except Exception as _e:
            print(f"  ⚠️ SPY analysis error: {_e}")
            spy_data = {"macro_score":0,"macro_signal":"ERROR","spy_trend":"UNKNOWN","spy_change_pct":0,"beta_20d":2.0,"vix":20,"vix_regime":"UNKNOWN","rs_signal":"NEUTRAL","divergence_warning":False,"expected_tsla_move":0,"tsla_spy_deviation":0}

        # ══ NEWS ENGINE ══
        print("  📰 Fetching real-time news...")
        try:
            raw_articles = fetch_news()
            news_data    = calculate_news_sentiment(raw_articles)
        except Exception as _e:
            print(f"  ⚠️ News error: {_e}")
            raw_articles = []
            news_data    = {"score":0,"signal":"ERROR","bull_count":0,"bear_count":0,"articles":[]}

        # ══ EXTENDED HOURS ENGINE ══
        print("  ⏰ Fetching extended hours data...")
        try:
            ext_data = calculate_extended_hours(TICKER)
        except Exception as _e:
            print(f"  ⚠️ Extended hours error: {_e}")
            ext_data = {"session":"UNKNOWN","ext_score":0,"ext_signal":"ERROR","premarket_change_pct":0,"afterhours_change_pct":0,"overnight_gap_pct":0,"gap_direction":"NONE"}

        # ══ MARKET MAKER ENGINE ══
        print("  🎰 Running Market Maker analysis...")
        _schwab_opts = {}  # Schwab options data shared with UOA + ML
        try:
            # Fetch Schwab options chain if available (gets real Greeks)
            if sc.is_configured() and sc.get_client():
                try:
                    _schwab_opts = sc.get_option_chain(TICKER, current_price=price)
                    if _schwab_opts.get("calls"):
                        print(f"  📡 Schwab options: {len(_schwab_opts['calls'])} calls, "
                              f"{len(_schwab_opts['puts'])} puts, "
                              f"GEX={_schwab_opts.get('gex_total',0):.0f}M "
                              f"PC={_schwab_opts.get('pc_ratio',0):.2f}", flush=True)
                except Exception as _soe:
                    print(f"  ⚠️ Schwab options failed: {_soe}", flush=True)
                    _schwab_opts = {}

            mm_data   = calculate_market_maker_data(TICKER, price)
            dark_pool = calculate_dark_pool_levels(closes, volumes, highs, lows)

            # Enhance mm_data with Schwab values where better
            # Always override GEX with Schwab value (more accurate than approximation)
            if _schwab_opts.get("gex_total") is not None:
                mm_data["gex_total"]    = float(_schwab_opts["gex_total"])
                gex_v = float(_schwab_opts["gex_total"])
                mm_data["gex_signal"] = "POSITIVE" if gex_v > 50 else "NEGATIVE" if gex_v < -50 else "NEUTRAL"
            if _schwab_opts.get("max_pain"):
                mm_data["max_pain"]     = _schwab_opts["max_pain"]
            if _schwab_opts.get("pc_ratio") and float(_schwab_opts["pc_ratio"]) > 0.01:
                mm_data["pc_ratio"]     = _schwab_opts["pc_ratio"]
            if _schwab_opts.get("front_iv"):
                mm_data["iv_front"]     = _schwab_opts["front_iv"]
                mm_data["iv_back"]      = _schwab_opts.get("back_iv", _schwab_opts["front_iv"])
                mm_data["iv_term_spread"] = _schwab_opts.get("iv_term_spread", 0)

            # Rebuild summary string with Schwab-corrected values
            _gex_s  = mm_data.get("gex_total", 0)
            _pc_s   = mm_data.get("pc_ratio", "?")
            _mp_s   = mm_data.get("max_pain", "?")
            _ivr_s  = mm_data.get("iv_rank", "?")
            _hed_s  = mm_data.get("hedging_pressure", "")
            mm_data["summary"] = (
                f"GEX: {_gex_s:+.0f}M ({mm_data.get('gex_signal','')}) | "
                f"Max Pain: ${_mp_s} | "
                f"P/C: {_pc_s} | "
                f"IV Rank: {_ivr_s}% | "
                f"Hedging: {_hed_s}"
            )
            print(f"  🎰 MM: {mm_data['summary'][:90]}", flush=True)

        except Exception as _e:
            print(f"  ⚠️ Market maker error: {_e}")
            mm_data   = {"gex_total":0,"gex_signal":"ERROR","max_pain":None,"pc_ratio":None,"iv_rank":50,"iv_signal":"ERROR","hedging_pressure":"NEUTRAL","call_walls":[],"put_walls":[],"pin_risk":False,"zero_dte_risk":False}
            dark_pool = {"above":[],"below":[],"gaps":[]}

        # ══ UNUSUAL OPTIONS ACTIVITY ENGINE ══
        print("  🔍 Scanning for unusual options activity...")
        try:
            uoa_data = calculate_unusual_options_activity(TICKER, price)
        except Exception as _e:
            print(f"  ⚠️ UOA error: {_e}")
            uoa_data = {"net_flow":"ERROR","flow_score":0,"whale_alerts":[],"unusual_calls":[],"unusual_puts":[],"total_call_premium":0,"total_put_premium":0,"uoa_reasons":["Options data unavailable"]}

        # ── Derived values needed for indicators dict ──
        prev_macd_hist = state.get("indicators", {}).get("macd_hist", macd_hist)
        obv = 0
        for i in range(1, len(closes)):
            if closes.iloc[i] > closes.iloc[i-1]:
                obv += volumes.iloc[i]
            elif closes.iloc[i] < closes.iloc[i-1]:
                obv -= volumes.iloc[i]
        obv_series = []
        _obv = 0
        for i in range(1, min(11, len(closes))):
            if closes.iloc[-i] > closes.iloc[-i-1]:  _obv += volumes.iloc[-i]
            elif closes.iloc[-i] < closes.iloc[-i-1]: _obv -= volumes.iloc[-i]
            obv_series.append(_obv)
        obv_trend = 1 if len(obv_series) >= 2 and obv_series[0] > obv_series[-1] else                    -1 if len(obv_series) >= 2 and obv_series[0] < obv_series[-1] else 0

        indicators = {
            "rsi": rsi, "macd": macd_val, "macd_signal": macd_sig, "macd_hist": macd_hist,
            "prev_macd_hist": prev_macd_hist,
            "vix":   float(spy_data.get("vix", 20) or 20),
            "ret_1b": float(closes.pct_change(1).iloc[-1] or 0),
            "ret_3b": float(closes.pct_change(3).iloc[-1] or 0),
            "bb_upper": bb_upper, "bb_mid": bb_mid, "bb_lower": bb_lower,
            "ema50": ema50, "ema200": ema200,
            "volume_ratio": vol_ratio,
            "volume_today": int(volumes.iloc[-1]),
            "volume_avg":   int(avg_vol),
            "obv_trend":    obv_trend,
            # Ichimoku
            "ichimoku_signal": ichi["cloud_signal"],
            "tenkan":          ichi["tenkan"],
            "kijun":           ichi["kijun"],
            # HMM
            "hmm_regime":      hmm_result["regime"],
            "hmm_confidence":  hmm_result["confidence"],
            # Institutional models (for scoring)
            "vwap":            vwap_r["vwap"],
            "kalman_signal":   kalman_r["signal"],
            "zscore":          zscore_r["zscore"],
            "kelly_signal":    kelly_r["signal"],
            "mc_prob_up":      mc_r["prob_up"],
            "factor_signal":   factor_r["signal"],
            "smi_signal":      smi_r["signal"],
            # SPY / Macro signals (for scoring)
            "macro_score":        spy_data.get("macro_score", 0),
            "macro_signal":       spy_data.get("macro_signal", "NEUTRAL"),
            "spy_trend":          spy_data.get("spy_trend", "UNKNOWN"),
            "spy_change_pct":     spy_data.get("spy_change_pct", 0),
            "spy_beta":           spy_data.get("beta_20d", 2.0),
            "vix":                spy_data.get("vix", 20),
            "vix_regime":         spy_data.get("vix_regime", "NORMAL"),
            "rs_signal":          spy_data.get("rs_signal", "INLINE"),
            "divergence_warning": spy_data.get("divergence_warning", False),
            # Market Maker signals (for scoring)
            "mm_gex_total":       mm_data.get("gex_total", 0),
            "mm_gex_signal":      mm_data.get("gex_signal", "UNKNOWN"),
            "mm_max_pain":        mm_data.get("max_pain"),
            "mm_pc_ratio":        mm_data.get("pc_ratio"),
            "mm_hedging":         mm_data.get("hedging_pressure", "NEUTRAL"),
            "mm_iv_rank":         mm_data.get("iv_rank", 50),
            "mm_iv_signal":       mm_data.get("iv_signal", "NORMAL IV"),
            "mm_pin_risk":        mm_data.get("pin_risk", False),
            "mm_zero_dte":        mm_data.get("zero_dte_risk", False),
            "mm_call_walls":      mm_data.get("call_walls", []),
            "mm_put_walls":       mm_data.get("put_walls", []),
            # SPY / Macro
            "spy_macro_score":    spy_data.get("macro_score", 0),
            "spy_macro_signal":   spy_data.get("macro_signal", "NEUTRAL"),
            "spy_trend":          spy_data.get("spy_trend", "UNKNOWN"),
            "spy_change_pct":     spy_data.get("spy_change_pct", 0),
            "vix":                spy_data.get("vix", 20),
            "vix_regime":         spy_data.get("vix_regime", "NORMAL"),
            "beta_20d":           spy_data.get("beta_20d", 2.0),
            "expected_tsla_move": spy_data.get("expected_tsla_move", 0),
            "tsla_spy_deviation": spy_data.get("tsla_spy_deviation", 0),
            "rs_signal":          spy_data.get("rs_signal", "INLINE"),
            "divergence_warning": spy_data.get("divergence_warning", False),
            # News sentiment
            "news_score":    news_data.get("score", 0),
            "news_signal":   news_data.get("signal", "NEUTRAL"),
            "news_bull_ct":  news_data.get("bull_count", 0),
            "news_bear_ct":  news_data.get("bear_count", 0),
            # Extended hours
            "ext_score":          ext_data.get("ext_score", 0),
            "ext_signal":         ext_data.get("ext_signal", "NEUTRAL"),
            "session":            ext_data.get("session", "UNKNOWN"),
            "premarket_change_pct": ext_data.get("premarket_change_pct", 0),
            "afterhours_change_pct":ext_data.get("afterhours_change_pct", 0),
            "overnight_gap_pct":  ext_data.get("overnight_gap_pct", 0),
            "gap_direction":      ext_data.get("gap_direction", "NONE"),
        }

        # ══ CTA POSITION SIZING ENGINE ══
        portfolio_val = state.get("_portfolio_value", 100_000)
        target_vol    = state.get("_target_vol", 0.12)
        print("  📐 Computing CTA position sizing...")
        try:
            sizing = calculate_cta_sizing(
            closes, volumes, indicators, spy_data, hmm_result,
            inst_models, mm_data, news_data, ext_data,
            portfolio_value=portfolio_val,
            target_vol=target_vol,
        )
        except Exception as _e:
            print(f"  ⚠️ CTA sizing error: {_e}")
            sizing = {"sizing_signal":"ERROR","final_exposure_pct":0,"final_exposure_dollar":0,"share_count":0,"vol_history":[]}

        signal, strength, reasons = generate_signal(indicators, price)

        # ── EXIT / PEAK DETECTION ENGINE ──
        try:
            exit_data = calculate_exit_analysis(closes, highs, lows, volumes, indicators, inst_models)
        except Exception as _e:
            print(f"  ⚠️ Exit analysis error: {_e}")
            exit_data = {"exit_analysis": {"urgency":"ERROR","exit_score":0,"optimal_sell_low":None,"optimal_sell_high":None,"stop_loss":None,"sell_tranches":[],"exit_reasons":[]}}
        exit_analysis = exit_data.get("exit_analysis", {})
        exit_urgency  = exit_analysis.get("urgency", "HOLD — NO TOP YET")
        exit_score    = exit_analysis.get("exit_score", 0)

        # ── PRECISION TOP ENGINE (9 leading signals) ──
        print("  🎯 Running precision top detection...")
        try:
            peak_data = calculate_peak_signals(
            closes, highs, lows, volumes, opens_s,
            mm_data=mm_data, indicators=indicators
        )
        except Exception as _e:
            print(f"  ⚠️ Peak signals error: {_e}")
            peak_data = {"peak_score":0,"peak_urgency":"✅ CLEAR","signals":[],"top_price_target":None,"hard_stop":None}

        # ── PRECISION ENTRY ENGINE (when + how much to buy) ──
        print("  🟢 Running precision entry detection...")
        portfolio_val = state.get("_portfolio_value", 100_000)
        try:
            entry_data = calculate_entry_signals(
            closes, highs, lows, volumes, opens_s,
            mm_data=mm_data, indicators=indicators,
            spy_data=spy_data, portfolio_value=portfolio_val
        )
        except Exception as _e:
            print(f"  ⚠️ Entry signals error: {_e}")
            entry_data = {"entry_score":0,"entry_urgency":"⏳ WAIT","tranche_plan":[],"signals":[],"total_deploy_pct":0,"invalidation":None}

        # ── Build chart history data ──
        # vol_history comes from sizing (CTA engine computes rolling vol)
        vol_history = sizing.get("vol_history", [])

        # vol_profile — Volume Profile with POC, VAH, VAL (last 60 days)
        vol_profile = []
        poc_data    = {}
        try:
            price_bins = {}
            _bin_size  = 1.0   # $1 price buckets
            for i in range(-60, 0):
                _h = float(highs.iloc[i])
                _l = float(lows.iloc[i])
                _v = float(volumes.iloc[i])
                # Distribute volume proportionally across the bar's range
                _steps = max(int((_h - _l) / _bin_size), 1)
                _v_per_step = _v / _steps
                for _s in range(_steps):
                    _bucket = round(_l + (_s + 0.5) * (_h - _l) / _steps, 0)
                    price_bins[_bucket] = price_bins.get(_bucket, 0) + _v_per_step

            # Sort by price for chart display
            _sorted_bins = sorted(price_bins.items(), key=lambda x: x[0])
            _total_vol   = sum(v for _, v in _sorted_bins)

            # POC = highest volume price level
            _poc_price   = max(price_bins, key=price_bins.get) if price_bins else 0
            _poc_vol     = price_bins.get(_poc_price, 0)

            # Value Area = 70% of total volume centered around POC
            # Walk outward from POC adding bins until 70% is captured
            _va_target   = _total_vol * 0.70
            _va_vol      = _poc_vol
            _bins_sorted_by_price = [p for p, _ in _sorted_bins]
            _poc_idx     = _bins_sorted_by_price.index(_poc_price) if _poc_price in _bins_sorted_by_price else len(_bins_sorted_by_price) // 2
            _lo_idx      = _poc_idx
            _hi_idx      = _poc_idx
            while _va_vol < _va_target and (_lo_idx > 0 or _hi_idx < len(_bins_sorted_by_price) - 1):
                _add_lo = price_bins.get(_bins_sorted_by_price[_lo_idx - 1], 0) if _lo_idx > 0 else 0
                _add_hi = price_bins.get(_bins_sorted_by_price[_hi_idx + 1], 0) if _hi_idx < len(_bins_sorted_by_price) - 1 else 0
                if _add_hi >= _add_lo and _hi_idx < len(_bins_sorted_by_price) - 1:
                    _hi_idx += 1; _va_vol += _add_hi
                elif _lo_idx > 0:
                    _lo_idx -= 1; _va_vol += _add_lo
                else:
                    break
            _vah = _bins_sorted_by_price[_hi_idx] if _bins_sorted_by_price else 0
            _val = _bins_sorted_by_price[_lo_idx] if _bins_sorted_by_price else 0

            vol_profile = sorted(
                [{"price_mid": k, "volume": round(v)} for k, v in price_bins.items()],
                key=lambda x: x["price_mid"]
            )

            poc_data = {
                "poc":        float(_poc_price),
                "poc_vol":    round(_poc_vol),
                "vah":        float(_vah),
                "val":        float(_val),
                "total_vol":  round(_total_vol),
                "va_pct":     70,
                "price_vs_poc": round((price - _poc_price) / (_poc_price + 1e-9) * 100, 2) if _poc_price else 0,
                "above_poc":  price > _poc_price,
                "in_va":      _val <= price <= _vah,
            }
            print(f"  📊 Volume Profile: POC=${_poc_price} | VAH=${_vah} | VAL=${_val} | Price {'above' if poc_data['above_poc'] else 'below'} POC", flush=True)
        except Exception as _vpe:
            print(f"  ⚠️ vol_profile error: {_vpe}")
            vol_profile = []
            poc_data    = {}

        # macd_history — last 60 days of MACD line, signal, histogram
        macd_history = []
        try:
            exp12 = closes.ewm(span=12, adjust=False).mean()
            exp26 = closes.ewm(span=26, adjust=False).mean()
            macd_line   = exp12 - exp26
            signal_line = macd_line.ewm(span=9, adjust=False).mean()
            histogram   = macd_line - signal_line
            for i in range(-60, 0):
                h = float(histogram.iloc[i])
                macd_history.append({
                    "date":   str(closes.index[i].date()),
                    "macd":   round(float(macd_line.iloc[i]), 4),
                    "signal": round(float(signal_line.iloc[i]), 4),
                    "hist":   round(h, 4),
                    "color":  "#00ff88" if h >= 0 else "#ff3355",
                })
        except Exception:
            macd_history = []

        state.update({
            "price": price, "signal": signal, "signal_strength": strength,
            "indicators":         indicators,
            "ichimoku":           ichi,
            "hmm":                hmm_result,
            "institutional_models": inst_models,
            "exit_data":          exit_data,
            "peak_data":          peak_data,
            "entry_data":         entry_data,
            "spy_data":           spy_data,
            "news_data":          news_data,
            "ext_data":           ext_data,
            "sizing":             sizing,
            "mm_data":            mm_data,
            "uoa_data":           uoa_data,
            "dark_pool":          dark_pool,
            "spy_data":           spy_data,
            "vol_history":        vol_history,
            "vol_profile":        vol_profile,
            "poc_data":           poc_data,
            "macd_history":       macd_history,
            "signal_reasons":     reasons,
            "last_updated": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "price_history": [{"date": str(d.date()), "price": round(v, 2)}
                               for d, v in zip(hist.index[-90:], closes.iloc[-90:])],
            "ichimoku_history": ichi.get("history", []),
        })

        # ── Capitulation Bounce Detector ─────────────────────────
        cap_result = {}
        try:
            cap_result = calculate_capitulation_bounce(TICKER, price, closes, highs, lows)
            state["capitulation"] = _sanitize(cap_result)
            if cap_result.get("detected"):
                print(f"  CAPITULATION BOUNCE DETECTED! Conv:{cap_result.get('conviction',0)} Phase:{cap_result.get("phase","?")}", flush=True)
        except Exception as _cap_e:
            print(f"  Capitulation detector error: {_cap_e}", flush=True)
            state["capitulation"] = {}

        # ── DarthVader 1.0 — Institutional Intelligence ──────────
        dv_result = {}  # default if calculate_darthvader throws
        try:
            dv_result = calculate_darthvader(
                closes, highs, lows, volumes, opens_s,
                mm_data, spy_data, indicators,
                cap_data=cap_result,
            )
            state["darthvader"] = _sanitize(dv_result)
            dv_state = dv_result.get("tsla_state", {}).get("state", "?")
            dv_risk  = dv_result.get("risk_mode", "?")
            dv_conf  = dv_result.get("tsla_state", {}).get("confidence", 0)
            print(f"  ⚔️  DarthVader: {dv_state} | {dv_risk} | conf:{dv_conf:.0%}")
        except Exception as _dv_e:
            print(f"  ⚠️ DarthVader error: {_dv_e}")

        regime_str = hmm_result.get("regime", "?")
        cloud_str  = ichi.get("cloud_signal", "?")
        kelly_str  = kelly_r.get("signal", "?")
        mc_str     = f"{mc_r.get("prob_up","?")}% up"
        smi_str    = smi_r.get("signal", "?")
        mm_gex_str = f"GEX:{mm_data.get('gex_total',0):+.0f}M"
        mm_mp_str  = f"MaxPain:${mm_data.get("max_pain","?")}"
        mm_pc_str  = f"P/C:{mm_data.get("pc_ratio","?")}"
        print(f"  💰 ${price} | {signal}({strength}) | EXIT:{exit_urgency}(score:{exit_score}) | {mm_gex_str} {mm_mp_str} {mm_pc_str} | HMM:{regime_str}")

        # ── Dashboard alert: BUY/SELL signal change ──
        # Momentum confirmation: don't alert BUY if price trend is down
        _recent_momentum = float(closes.pct_change(3).iloc[-1] or 0)
        _above_vwap_now  = price >= float(indicators.get("vwap", price) or price)
        _momentum_ok_buy  = _recent_momentum >= -0.003
        _momentum_ok_sell = _recent_momentum <= 0.003

        # SPOCK conviction check — don't alert if SPOCK disagrees
        _spock = state.get("master_signal", {})
        _spock_action    = _spock.get("action", "HOLD")
        _spock_conv      = _spock.get("conviction", 0) or 0
        _spock_ok_buy    = _spock_conv >= 55 and "BUY"  in _spock_action
        _spock_ok_sell   = _spock_conv >= 55 and "SELL" in _spock_action

        if signal != "HOLD" and signal != last_signal:
            # Momentum check
            if signal == "BUY"  and not _momentum_ok_buy:
                print(f"  ⚠️ BUY suppressed — momentum down ({_recent_momentum:.3%})", flush=True)
                signal = "HOLD"
            if signal == "SELL" and not _momentum_ok_sell:
                print(f"  ⚠️ SELL suppressed — momentum up ({_recent_momentum:.3%})", flush=True)
                signal = "HOLD"
            # SPOCK conviction check
            if signal == "BUY"  and not _spock_ok_buy:
                print(f"  ⚠️ BUY suppressed — SPOCK conviction too low ({_spock_conv}% / need 55%)", flush=True)
                signal = "HOLD"
            if signal == "SELL" and not _spock_ok_sell:
                print(f"  ⚠️ SELL suppressed — SPOCK conviction too low ({_spock_conv}% / need 55%)", flush=True)
                signal = "HOLD"

        if signal != "HOLD" and signal != last_signal:
            emoji  = "🟢" if signal == "BUY" else "🔴"
            top3   = " | ".join(reasons[:3])
            gex_s  = f"{mm_data.get('gex_total', 0):+.0f}M"
            vix    = spy_data.get("vix", "?")
            pm_pct = ext_data.get("premarket_change_pct", 0) or 0
            news_s = news_data.get("signal", "NEUTRAL")
            # Build tranche plan for BUY alerts
            tranches_txt = ""
            if signal == "BUY":
                tp = entry_data.get("tranche_plan", [])
                if tp:
                    for t in tp:
                        tranches_txt += f"  T{t.get("number","")}: {t.get("pct_cap","")}% @ ${t.get("price","")} ({t.get("shares","")} shares)\n"
                    tranches_txt = f"\n💰 *Entry Plan ({entry_data.get('total_deploy_pct',0)}% of capital):*\n" + tranches_txt
                    tranches_txt += f"  🛑 Invalidation: ${entry_data.get("invalidation","?")}"

            # Earnings mode warning
            _earn_ctx = state.get("earnings_context", {})
            _earn_warn = ""
            if _earn_ctx.get("earnings_mode"):
                _earn_warn = f"\n⚠️ *EARNINGS IN {_earn_ctx.get('days_away','?')} DAYS* — use tighter stops, expect IV crush after\n"

            _ms = state.get("master_signal", {})
            _ms_line = f"\n🖖 *SPOCK: {_ms.get('action','?')}* | Score: {_ms.get('score',0):+d}/100 | Conviction: {_ms.get('conviction',0)}%"

            wa_msg = (
                f"{emoji} {TICKER} *{signal} SIGNAL*\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"💰 Price: *${price}* | Strength: *{strength}/100*\n"
                f"\n"
                f"📊 *Market Maker*\n"
                f"  GEX: {gex_s} | MaxPain: ${mm_data.get("max_pain","?")}\n"
                f"  P/C: {mm_data.get("pc_ratio","?")} | {mm_data.get("hedging_pressure","?")[:30]}\n"
                f"\n"
                f"🌍 *Macro*\n"
                f"  SPY: {spy_data.get("spy_trend","?")} | VIX: {vix}\n"
                f"  {spy_data.get("macro_signal","?")}\n"
                f"\n"
                f"⏰ Pre-Mkt: {pm_pct:+.1f}% | 📰 News: {news_s}\n"
                f"🧠 HMM: {regime_str} | ☁ Cloud: {cloud_str}\n"
                f"{_ms_line}\n"
                f"{_earn_warn}"
                f"{tranches_txt}\n"
                f"📌 *Why:*\n  {top3}"
            )
            log_alert(wa_msg, alert_key=f"signal_{signal}")
            state["alerts_log"].insert(0, {
                "time": state["last_updated"], "signal": signal,
                "price": price, "strength": strength, "reason": top3,
                "gex": gex_s, "max_pain": mm_data.get("max_pain","?"),
                "hmm": regime_str, "cloud": cloud_str,
            })
            state["alerts_log"] = state["alerts_log"][:50]
            last_signal = signal

        # ── Whale / UOA WhatsApp alert ──
        prev_uoa_whales = state.get("_prev_uoa_whales", 0)
        curr_uoa_whales = len(uoa_data.get("whale_alerts", []))
        if curr_uoa_whales >= 5 and prev_uoa_whales < 5:  # Raised from 2→5 to reduce spam
            top_whale  = uoa_data.get("whale_alerts", [{}])[0]
            net_flow   = uoa_data.get("net_flow", "NEUTRAL")
            call_prem  = uoa_data.get("total_call_premium", 0)
            put_prem   = uoa_data.get("total_put_premium", 0)
            top3_uoa   = " | ".join(uoa_data.get("uoa_reasons", [])[:2])
            wa_msg = (
                f"🐋 TSLA *WHALE ACTIVITY DETECTED*\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"Flow: *{net_flow}* | {curr_uoa_whales} whale trades\n"
                f"💰 Price: *${price}*\n"
                f"\n"
                f"📊 *Premium Flow:*\n"
                f"  Calls: ${call_prem/1e6:.2f}M | Puts: ${put_prem/1e6:.2f}M\n"
                f"  Net: {'CALL' if call_prem>put_prem else 'PUT'} heavy by ${abs(call_prem-put_prem)/1e6:.2f}M\n"
                f"\n"
                f"🎯 *Top whale:* {top_whale.get("type","?")} ${top_whale.get("strike","?")} "
                f"exp {top_whale.get("expiry","?")} → {top_whale.get("premium_fmt","?")} premium\n"
                f"  Vol/OI: {top_whale.get("vol_oi","?")}× | IV: {top_whale.get("iv","?")}%\n"
                f"\n"
                f"📌 {top3_uoa}"
            )
            log_alert(wa_msg, alert_key="uoa_whale")
        state["_prev_uoa_whales"] = curr_uoa_whales
        # Track UOA flow delta (change since last cycle)
        _prev_call_prem = state.get("_prev_call_prem", 0)
        _prev_put_prem  = state.get("_prev_put_prem",  0)
        _curr_call_prem = uoa_data.get("total_call_premium", 0) or 0
        _curr_put_prem  = uoa_data.get("total_put_premium",  0) or 0
        _call_delta = _curr_call_prem - _prev_call_prem
        _put_delta  = _curr_put_prem  - _prev_put_prem
        state["uoa_flow_delta"] = {
            "call_delta": round(_call_delta),
            "put_delta":  round(_put_delta),
            "net_delta":  round(_call_delta - _put_delta),
            "direction":  "BULLISH" if _call_delta > _put_delta else "BEARISH" if _put_delta > _call_delta else "NEUTRAL",
        }
        state["_prev_call_prem"] = _curr_call_prem
        state["_prev_put_prem"]  = _curr_put_prem

        # ── CAPITULATION BOUNCE WhatsApp + SPOCK auto-trigger ────
        prev_cap = state.get("_prev_cap_detected", False)
        curr_cap = cap_result.get("detected", False)
        if curr_cap and not prev_cap:
            cap_conv=cap_result.get("conviction",0); cap_phase=cap_result.get("phase","?")
            cap_drop=cap_result.get("drop_from_high_pct",0)
            cap_lo=cap_result.get("session_low",0); cap_hi=cap_result.get("session_high",0)
            cap_elo=cap_result.get("entry_zone_low",0); cap_ehi=cap_result.get("entry_zone_high",0)
            cap_stop=cap_result.get("stop_loss",0)
            cap_t1=cap_result.get("t1",0); cap_t2=cap_result.get("t2",0); cap_t3=cap_result.get("t3",0)
            cap_vwap=cap_result.get("vwap",0); cap_rs=cap_result.get("reasons",[])
            send_whatsapp(
                f"CAPITULATION BOUNCE DETECTED — {TICKER}\n"
                f"Phase: {cap_phase} | Conviction: {cap_conv}/100\n"
                f"Drop: {cap_drop:.1f}% from ${cap_hi:.2f} to ${cap_lo:.2f}\n"
                f"Current: ${price:.2f} | VWAP: ${cap_vwap:.2f}\n"
                f"MULTI-DAY LONG SETUP:\n"
                f"  Entry: ${cap_elo:.2f} - ${cap_ehi:.2f}\n"
                f"  Stop: ${cap_stop:.2f}\n"
                f"  T1: ${cap_t1:.2f} | T2: ${cap_t2:.2f} | T3: ${cap_t3:.2f}\n"
                f"Signals: {' | '.join(cap_rs[:3])}",
                alert_key="cap_bounce"
            )
            # SPOCK auto-trigger on capitulation disabled to save API costs
        state["_prev_cap_detected"] = curr_cap

        # ── ML Directional Signal ─────────────────────────────
        try:
            _dv_ft = (dv_result if isinstance(dv_result, dict) else {}).get("features", {})
            _now_h = datetime.now().hour + datetime.now().minute / 60
            _vol_ma12 = float(volumes.rolling(12).mean().iloc[-1] + 1)
            _vol_now  = float(volumes.iloc[-1])
            _atr5  = float(_dv_ft.get("atr5",  0.01) or 0.01)
            _atr20 = float(_dv_ft.get("atr20", 0.01) or 0.01)
            _atr_ratio = _atr5 / (_atr20 + 1e-9)
            _ret_std = float(closes.pct_change().iloc[-20:].std() or 0.01)
            _ofi_ratio = float(_dv_ft.get("ofi_ratio", 0) or 0)
            _vwap_val  = float(indicators.get("vwap", price) or price)
            _vwap_dist = (price - _vwap_val) / (_vwap_val + 1e-9) if _vwap_val else 0
            _ema50  = float(indicators.get("ema50",  price) or price)
            _ema200 = float(indicators.get("ema200", price) or price)
            _trend_score = float(_dv_ft.get("trend_score", 0) or 0)
            _bb_upper = float(indicators.get("bb_upper", price*1.05) or price*1.05)
            _bb_lower = float(indicators.get("bb_lower", price*0.95) or price*0.95)
            _bb_pct   = (price - _bb_lower) / (_bb_upper - _bb_lower + 1e-9)
            _high20 = float(closes.iloc[-20:].max() or price)
            _low20  = float(closes.iloc[-20:].min() or price)
            _dist_high = (price - _high20) / (_high20 + 1e-9)
            _dist_low  = (price - _low20)  / (_low20  + 1e-9)
            _open_ref  = float(closes.iloc[-78] if len(closes) > 78 else closes.iloc[0])
            _daily_ret = (price - _open_ref) / (_open_ref + 1e-9)

            # NEW: SPY decoupling regime
            _tsla_spy_corr = float(spy_data.get("correlation_60d", 0) or 0)
            _spy_decouple  = 1 if abs(_tsla_spy_corr) < 0.4 else 0

            # NEW: Earnings proximity — cached, with earnings mode detection
            _earn_proximity = 0.0; _earn_near_5d = 0; _earn_near_10d = 0
            _earn_days_away = 99; _earnings_mode = False
            try:
                _earn_dates = state.get("_ml_earn_dates", [])
                _earn_ticker = state.get("_ml_earn_ticker", "")
                # Refresh earnings if ticker changed or cache empty
                if not _earn_dates or _earn_ticker != TICKER:
                    try:
                        _ec = yf.Ticker(TICKER).get_earnings_dates(limit=10)
                        if _ec is not None and not _ec.empty:
                            _earn_dates = [d.date() if hasattr(d,"date") else d
                                           for d in _ec.index.tolist()]
                            state["_ml_earn_dates"] = _earn_dates
                            state["_ml_earn_ticker"] = TICKER
                    except Exception:
                        pass
                if _earn_dates:
                    import datetime as _dt2
                    _today = _dt2.date.today()
                    _future = [ed for ed in _earn_dates if ed >= _today]
                    if _future:
                        _dte = min(abs((_today - ed).days) for ed in _future)
                    else:
                        _dte = 99
                    _earn_days_away  = _dte
                    _earn_proximity  = 1.0 / (_dte + 1)
                    _earn_near_5d    = 1 if _dte <= 5  else 0
                    _earn_near_10d   = 1 if _dte <= 10 else 0
                    _earnings_mode   = _dte <= 7  # within 1 week of earnings

                    if _earnings_mode:
                        print(f"  ⚠️ EARNINGS MODE: {TICKER} earnings in {_dte} days!", flush=True)

                # Store earnings context in state for dashboard
                state["earnings_context"] = {
                    "days_away":      _earn_days_away,
                    "earnings_mode":  _earnings_mode,
                    "near_5d":        bool(_earn_near_5d),
                    "near_10d":       bool(_earn_near_10d),
                    "next_date":      str(_future[0]) if _earn_dates and _future else "Unknown",
                }
            except Exception: pass

            # NEW: Greeks from Schwab options chain
            _delta_atm = 0.5; _gamma_exp = 0.0; _theta_atm = 0.0; _vega_atm = 0.0; _iv_skew = 0.0
            try:
                if _schwab_opts.get('calls'):
                    _calls = _schwab_opts['calls']
                    _puts  = _schwab_opts['puts']
                    _atm_calls = sorted(_calls, key=lambda x: abs(x['strike']-price))[:5]
                    _atm_puts  = sorted(_puts,  key=lambda x: abs(x['strike']-price))[:5]
                    if _atm_calls:
                        _delta_atm = float(sum(c['delta'] for c in _atm_calls) / len(_atm_calls))
                        _theta_atm = float(sum(c['theta'] for c in _atm_calls) / len(_atm_calls))
                        _vega_atm  = float(sum(c['vega']  for c in _atm_calls) / len(_atm_calls))
                    _gamma_exp = float(_schwab_opts.get('gex_total', 0)) / (price + 1e-9)
                    _call_iv = float(sum(c['iv'] for c in _atm_calls) / max(len(_atm_calls),1)) if _atm_calls else 0.3
                    _put_iv  = float(sum(p['iv'] for p in _atm_puts)  / max(len(_atm_puts), 1)) if _atm_puts  else 0.3
                    _iv_skew = _put_iv - _call_iv
            except Exception: pass

            # NEW: IV term structure + P/C ratio (from mm_data / uoa_data)
            # IV term structure — try Schwab opts first, then mm_data fallback
            _iv_front = 0.4; _iv_back = 0.4
            if _schwab_opts.get("front_iv"):
                _iv_front = float(_schwab_opts["front_iv"] or 0.4)
                _iv_back  = float(_schwab_opts.get("back_iv", _iv_front) or _iv_front)
            else:
                _iv_front = float(mm_data.get("iv_front", 0.4) or 0.4)
                _iv_back  = float(mm_data.get("iv_back",  _iv_front) or _iv_front)
            _iv_term_spd = _iv_back - _iv_front
            _iv_ratio    = _iv_front / (_iv_back + 1e-9)

            # P/C ratio — Schwab opts first (more accurate), then mm_data
            if _schwab_opts.get("pc_ratio"):
                _pc_ratio = float(_schwab_opts["pc_ratio"] or 1.0)
            else:
                _pc_ratio = float(mm_data.get("pc_ratio", 1.0) or 1.0)
            # P/C delta: change vs previous cycle (momentum of sentiment)
            _pc_prev  = float(state.get("_ml_pc_prev", _pc_ratio))
            _pc_delta = _pc_ratio - _pc_prev
            state["_ml_pc_prev"] = _pc_ratio

            _ml_features = {
                # Core returns
                "ret_1b":      float(closes.pct_change(1).iloc[-1] or 0),
                "ret_3b":      float(closes.pct_change(3).iloc[-1] or 0),
                "ret_6b":      float(closes.pct_change(6).iloc[-1] or 0),
                "ret_12b":     float(closes.pct_change(12).iloc[-1] or 0),
                "ret_48b":     float(closes.pct_change(48).iloc[-1] or 0),
                # Momentum
                "rsi_14":      float(indicators.get("rsi", 50)),
                "rsi_6":       float(indicators.get("rsi", 50)),
                "rsi_ob":      1 if indicators.get("rsi", 50) > 70 else 0,
                "rsi_os":      1 if indicators.get("rsi", 50) < 30 else 0,
                "macd_hist":   float(indicators.get("macd_hist", 0) or 0),
                # Macro
                "vix":         float(spy_data.get("vix", 20) or 20),
                "vix_high":    1 if float(spy_data.get("vix", 20) or 20) > 25 else 0,
                # Volume
                "vol_ratio":   _vol_now / _vol_ma12,
                "vol_surge":   1 if _vol_now / _vol_ma12 > 2 else 0,
                # Volatility
                "atr_ratio":   _atr_ratio,
                "realized_vol":_ret_std,
                # OFI
                "ofi_6b":      _ofi_ratio,
                "ofi_zscore":  _ofi_ratio,
                # VWAP
                "vwap_dist":   _vwap_dist,
                "above_vwap":  1 if _vwap_dist > 0 else 0,
                # SPY / correlation
                "tsla_spy_corr":   _tsla_spy_corr,
                "spy_ret_1b":      float((spy_data.get("spy_change_pct", 0) or 0) / 100),
                "spy_decouple":    _spy_decouple,
                # SPY technical state — critical for market-aware signals
                "spy_rsi":         float(spy_data.get("spy_rsi", 50) or 50),
                "spy_ob":          1 if spy_data.get("spy_ob", False) else 0,
                "spy_os":          1 if spy_data.get("spy_os", False) else 0,
                "spy_macd_bull":   1 if spy_data.get("spy_macd_bull", True) else 0,
                "spy_bb_pct":      float(spy_data.get("spy_bb_pct", 0.5) or 0.5),
                "spy_mom_5d":      float(spy_data.get("spy_mom_5d", 0) or 0) / 100,
                "spy_above_200":   1 if spy_data.get("spy_trend", "") in ("BULL MARKET", "UPTREND") else 0,
                # QQQ technical state — tech sector leading indicator
                "qqq_rsi":         float(spy_data.get("qqq_rsi", 50) or 50),
                "qqq_ob":          1 if spy_data.get("qqq_ob", False) else 0,
                "qqq_os":          1 if spy_data.get("qqq_os", False) else 0,
                "qqq_macd_bull":   1 if spy_data.get("qqq_macd_bull", True) else 0,
                "qqq_mom_5d":      float(spy_data.get("qqq_mom_5d", 0) or 0) / 100,
                "qqq_bull":        1 if spy_data.get("qqq_trend", "") == "BULL" else 0,
                # Market breadth composite
                "market_ob":       1 if (spy_data.get("spy_ob") and spy_data.get("qqq_ob")) else 0,
                "market_os":       1 if (spy_data.get("spy_os") and spy_data.get("qqq_os")) else 0,
                # Daily context
                "daily_ret_so_far": _daily_ret,
                # EMA / trend
                "above_daily_ma20": 1 if price > _ema50 else 0,
                "daily_trend_up":   1 if _ema50 > _ema200 else 0,
                "trend_score":  _trend_score,
                "above_ema9":   1 if _trend_score >= 2 else 0,
                "above_ema21":  1 if _trend_score >= 1 else 0,
                # Time
                "time_of_day": _now_h,
                "is_open":     1 if 9.5 <= _now_h < 10.25 else 0,
                "is_close":    1 if 15.25 <= _now_h < 16.0 else 0,
                "is_lunch":    1 if 11.75 <= _now_h < 13.0 else 0,
                "day_of_week": datetime.now().weekday(),
                # BB
                "bb_pct":      _bb_pct,
                # Distance
                "dist_from_high": _dist_high,
                "dist_from_low":  _dist_low,
                # Microstructure
                "absorption":  float(_dv_ft.get("absorption", 0) or 0),
                # NEW: Earnings proximity
                "earn_proximity":  _earn_proximity,
                "earn_near_5d":    _earn_near_5d,
                "earn_near_10d":   _earn_near_10d,
                # NEW: IV term structure
                "iv_front":        _iv_front,
                "iv_back":         _iv_back,
                "iv_term_spread":  _iv_term_spd,
                "iv_ratio":        _iv_ratio,
                # NEW: P/C ratio + delta
                "pc_ratio":        _pc_ratio,
                "pc_delta":        _pc_delta,
                # NEW: Real Greeks from Schwab (0 if not available)
                "delta_atm":       _delta_atm,
                "gamma_exposure":  _gamma_exp,
                "theta_decay":     _theta_atm,
                "vega_exposure":   _vega_atm,
                "iv_skew":         _iv_skew,
            }
            ml_signal = _get_ml_signal(_ml_features)
            state["ml_signal"] = ml_signal

            # ── MASTER SIGNAL — synthesize all models ──────────────────────
            try:
                master = calculate_master_signal(
                    signal      = signal,
                    strength    = strength,
                    ml_signal   = ml_signal,
                    mm_data     = mm_data,
                    uoa_data    = uoa_data,
                    dv_result   = dv_result,
                    entry_data  = entry_data,
                    peak_data   = peak_data,
                    exit_score  = exit_score,
                    spy_data    = spy_data,
                    cap_result  = cap_result,
                    ichi        = ichi,
                    hmm_result  = hmm_result,
                    news_data   = news_data,
                    indicators  = indicators,
                    price       = price,
                )
                state["master_signal"] = master
                print(f"  🖖 SPOCK MASTER: {master['action']} | score={master['score']:+d} | "
                      f"conviction={master['conviction']}% | risk={master['risk']} | "
                      f"bulls={master['bull_votes']} bears={master['bear_votes']}", flush=True)
            except Exception as _me:
                print(f"  ⚠️ Master signal error: {_me}", flush=True)
                state["master_signal"] = {"action":"HOLD","score":0,"conviction":0,
                                          "risk":"MEDIUM","color":"#00e5ff","reasons":[]}
            _regime_str = ml_signal.get('regime', '')
            print(f"  [ML] signal={ml_signal.get('signal')} conf={ml_signal.get('confidence')} "
                  f"regime={_regime_str} matched={ml_signal.get('features_matched','?')}/{ml_signal.get('features_total','?')} "
                  f"avail={ml_signal.get('available')} err={ml_signal.get('error','')}", flush=True)
        except Exception as _ml_e:
            state["ml_signal"] = {"signal":"HOLD","confidence":0,"probability":0.5,"available":False,"error":str(_ml_e)[:60]}
            print(f"  [ML] EXCEPTION: {_ml_e}", flush=True)

        # ── Entry signal WhatsApp alert ──
        prev_entry = state.get("_prev_entry_score", 0)
        curr_entry = entry_data.get("entry_score", 0)
        if curr_entry >= 50 and prev_entry < 50:  # Raised 45→50 to match ACCUMULATE tier
            tp = entry_data.get("tranche_plan", [])
            t1 = tp[0] if tp else {}
            t2 = tp[1] if len(tp) > 1 else {}
            top3_entry = " | ".join(s["name"] for s in entry_data.get("signals", [])[:3])
            wa_msg = (
                f"🟢 TSLA *ENTRY OPPORTUNITY*\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"Entry Score: *{curr_entry}/100* — {entry_data.get("entry_urgency","?")}\n"
                f"💰 Price: *${price}* | Deploy: *{entry_data.get('total_deploy_pct',0)}% of capital*\n"
                f"\n"
                f"📋 *Staged Entry Plan:*\n"
                f"  T1: {t1.get('pct_cap',0)}% now @ ${t1.get("price","?")} ({t1.get('shares',0)} shares)\n"
                f"  T2: {t2.get('pct_cap',0)}% on dip to ${t2.get("price","?")}\n"
                f"  🛑 Invalidation: ${entry_data.get("invalidation","?")}\n"
                f"\n"
                f"🔍 *Signals:* {top3_entry}\n"
                f"🌍 SPY: {spy_data.get("spy_trend","?")} | VIX: {spy_data.get("vix","?")}"
            )
            log_alert(wa_msg, alert_key="entry_signal")
        state["_prev_entry_score"] = curr_entry

        # ── Peak signal WhatsApp alert ──
        prev_peak = state.get("_prev_peak_score", 0)
        curr_peak = peak_data.get("peak_score", 0)
        if curr_peak >= 70 and prev_peak < 70:  # Raised 65→70
            top_tgt = peak_data.get("top_price_target", "?")
            hard_stop = peak_data.get("hard_stop", "?")
            top3_sigs = " | ".join(s["name"] for s in peak_data.get("signals", [])[:3])
            # Include sell tranches in peak alert
            peak_tp  = exit_analysis.get("sell_tranches", [])
            peak_t_txt = ""
            if peak_tp:
                for t in peak_tp[:2]:  # just T1+T2 to keep message concise
                    peak_t_txt += f"  T{t.get("number","")}: Sell {t.get("pct_holding","")}% @ ${t.get("price","")} (+{t.get("gain_pct","")}%)\n"
                peak_t_txt = "\n📋 *Sell Plan:*\n" + peak_t_txt

            wa_msg = (
                f"🎯 TSLA *PRECISION TOP ALERT*\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"Peak Score: *{curr_peak}/100* — {peak_data.get("peak_urgency","?")}\n"
                f"💰 Current Price: *${price}*\n"
                f"🎯 Top Target: ${top_tgt} | Stop: ${hard_stop}\n"
                f"⏰ Exit Window: {peak_data.get("optimal_exit_window","?")}\n"
                f"{peak_t_txt}\n"
                f"🔍 Signals: {top3_sigs}\n"
                f"CTA: {sizing.get("sizing_signal","?")} | {sizing.get("final_exposure_pct","?")}% deployed"
            )
            log_alert(wa_msg, alert_key="peak_top")
        state["_prev_peak_score"] = curr_peak

        # ── Dashboard alert: exit urgency escalation ──
        prev_exit_score = state.get("_prev_exit_score", 0)
        if exit_score >= 55 and prev_exit_score < 55:  # Raised from 45→55 to reduce noise
            sell_low  = exit_analysis.get("optimal_sell_low", price)
            sell_high = exit_analysis.get("optimal_sell_high", price * 1.02)
            stop      = exit_analysis.get("stop_loss", price * 0.97)
            top_exit  = exit_analysis.get("exit_reasons", [])[:3]
            urgency   = exit_analysis.get("urgency", "PREPARE TO SELL")
            # Build sell tranche text
            sell_tp = exit_analysis.get("sell_tranches", [])
            tranches_sell_txt = ""
            if sell_tp:
                for t in sell_tp:
                    tranches_sell_txt += f"  T{t.get("number","")} ({t.get("pct_holding","")}%): ${t.get("price","")} (+{t.get("gain_pct","")}%) → stop ${t.get("trailing_stop","")}\n"
                avg_ex  = exit_analysis.get("avg_exit_price", sell_high)
                avg_gn  = exit_analysis.get("avg_gain_pct",   0)
                tranches_sell_txt = f"\n📋 *Staged Exit Plan:*\n" + tranches_sell_txt
                tranches_sell_txt += f"  📊 Blended avg exit: ${avg_ex} (+{avg_gn}%)"

            wa_msg = (
                f"🚨 TSLA *SELL ZONE ALERT*\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"💰 Price: *${price}* | Exit Score: *{exit_score}/100*\n"
                f"⚡ Urgency: *{urgency}*\n"
                f"{tranches_sell_txt}\n"
                f"\n"
                f"🛑 Hard Stop: ${stop}\n"
                f"📊 GEX: {mm_data.get('gex_total',0):+.0f}M | MaxPain: ${mm_data.get("max_pain","?")}\n"
                f"🌍 SPY: {spy_data.get("spy_trend","?")} | VIX: {spy_data.get("vix","?")}\n"
                f"\n"
                f"📌 *Exit Reasons:*\n" +
                "\n".join(f"  • {r}" for r in top_exit)
            )
            log_alert(wa_msg, alert_key="exit_alert")
            state["alerts_log"].insert(0, {
                "time":     state["last_updated"],
                "signal":   "🚨 EXIT ALERT",
                "price":    price,
                "strength": exit_score,
                "reason":   f"Optimal sell ${sell_low}–${sell_high} | Stop ${stop}",
                "gex":      f"{mm_data.get('gex_total',0):+.0f}M",
                "max_pain": mm_data.get("max_pain","?"),
                "hmm":      regime_str,
                "cloud":    cloud_str,
            })
            state["alerts_log"] = state["alerts_log"][:50]

        # ── High VIX spike alert (new) ──
        prev_vix = state.get("_prev_vix", 20)
        curr_vix = spy_data.get("vix", 20) or 20
        if curr_vix >= 30 and prev_vix < 30:
            wa_msg = (
                f"⚠️ *VIX SPIKE ALERT*\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"VIX just crossed *{curr_vix}* (was {prev_vix})\n"
                f"📉 TSLA expected move: {spy_data.get("expected_tsla_move","?")}%\n"
                f"🌍 SPY Trend: {spy_data.get("spy_trend","?")}\n"
                f"Risk-off mode — consider reducing exposure"
            )
            log_alert(wa_msg, alert_key="vix_spike")
        state["_prev_vix"] = curr_vix

        # ── Large pre-market move alert (new) ──
        prev_pm = state.get("_prev_pm_pct", 0)
        curr_pm = ext_data.get("premarket_change_pct", 0) or 0
        if abs(curr_pm) >= 3 and abs(prev_pm) < 3:
            direction = "surging" if curr_pm > 0 else "crashing"
            wa_msg = (
                f"{'🚀' if curr_pm > 0 else '🔻'} *TSLA Pre-Market {direction.upper()}*\n"
                f"━━━━━━━━━━━━━━━━━━━━━━\n"
                f"Pre-mkt: *{curr_pm:+.1f}%* | Price: ${ext_data.get("premarket_price","?")}\n"
                f"📊 Trend: {ext_data.get("premarket_trend","?")}\n"
                f"📰 News: {news_data.get("signal","?")}\n"
                f"Expected open move based on beta: {spy_data.get("expected_tsla_move","?")}%"
            )
            log_alert(wa_msg, alert_key="premarket_move")
        state["_prev_pm_pct"] = curr_pm

        state["_prev_exit_score"] = exit_score

        # ── Spock auto-trigger check ──
        try:
            algo_alert = detect_algo_activity()
            state["algo_alert"] = algo_alert
            state["algo_history"] = _algo_state.get("alert_history", [])
            check_spock_triggers(algo_alert=algo_alert)
        except Exception as _se:
            print(f"  ⚠️ Spock trigger error: {_se}")

    except Exception as e:
        print(f"❌ Analysis error: {e}")


def fetch_institutional_periodically():
    while True:
        print("\n🏦 Fetching SEC EDGAR 13F data...")
        try:
            data = fetch_institutional_data()
            state["institutional"] = data
            print(f"  ✅ {len(data)} institutions loaded.")
        except Exception as e:
            print(f"❌ Institutional fetch error: {e}")
        time.sleep(6 * 3600)


def monitor_loop():
    cycle = 0
    while True:
        cycle += 1
        print(f"[LOOP] cycle {cycle} starting", flush=True)
        run_analysis()
        print(f"[LOOP] cycle {cycle} done, sleeping {CHECK_INTERVAL}s", flush=True)
        time.sleep(CHECK_INTERVAL)


# ═══════════════════════════════════════════════════════════════
#  FLASK ROUTES
# ═══════════════════════════════════════════════════════════════

def _sanitize(obj, _depth=0):
    """
    Recursively convert numpy/pandas types → native Python so Flask jsonify
    never raises TypeError. Caps recursion at depth 20 to be safe.
    """
    if _depth > 20:
        return str(obj)
    import math
    try:
        import numpy as np
        if isinstance(obj, (np.integer,)):           return int(obj)
        if isinstance(obj, (np.floating,)):
            v = float(obj)
            return None if (math.isnan(v) or math.isinf(v)) else v
        if isinstance(obj, (np.bool_,)):             return bool(obj)
        if isinstance(obj, np.ndarray):              return [_sanitize(x, _depth+1) for x in obj.tolist()]
    except ImportError:
        pass
    if isinstance(obj, dict):
        return {k: _sanitize(v, _depth+1) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [_sanitize(x, _depth+1) for x in obj]
    try:
        import math
        if isinstance(obj, float) and (math.isnan(obj) or math.isinf(obj)):
            return None
    except Exception:
        pass
    return obj


@app.route("/api/state")
def api_state():
    try:
        payload = _sanitize({
            **state,
            "wa_enabled":    WA_ENABLED,
            "wa_phone_tail": GREEN_PHONE[-4:] if GREEN_PHONE else "",
        })
        return jsonify(payload)
    except Exception as e:
        print(f"  ❌ api_state serialization error: {e}")
        # Return state without darthvader as fallback
        safe = {k: v for k, v in state.items() if k != "darthvader"}
        safe["wa_enabled"]    = WA_ENABLED
        safe["wa_phone_tail"] = GREEN_PHONE[-4:] if GREEN_PHONE else ""
        # Include darthvader features for algo radar gauges (strip heavy data)
        dv_full = state.get("darthvader", {})
        safe["darthvader"]    = {
            "features":           dv_full.get("features", {}),
            "tsla_state":         dv_full.get("tsla_state", {}),
            "risk_mode":          dv_full.get("risk_mode", "NORMAL"),
            "probabilistic_signals": dv_full.get("probabilistic_signals", {}),
            "market_intent":      dv_full.get("market_intent", ""),
        }
        return jsonify(safe)

@app.route("/api/switch_ticker")
def api_switch_ticker():
    global TICKER
    sym = request.args.get("ticker","TSLA").upper().strip()
    if sym and sym.isalpha() and len(sym) <= 6:
        TICKER = sym
        # Clear DV cache so it recalculates for new ticker
        global _DV_CACHE
        _DV_CACHE = {"ts": 0, "data": None}
        # Reset state
        state.clear()
        state.update({"ticker": TICKER, "darthvader": {}, "last_updated": None})
        print(f"  🔄 Ticker switched to {TICKER}", flush=True)
        # Clear ML cache so new ticker gets its own model
        global _ml_model_cache, _ml_load_errors
        _ml_model_cache = None
        _ml_load_errors = []
        # Trigger retrain for new ticker in background
        threading.Thread(target=_run_ml_retrain, daemon=True).start()
        print(f"  🤖 ML retrain queued for {TICKER}", flush=True)
        # Trigger async analysis
        import threading
        threading.Thread(target=run_analysis, daemon=True).start()
        return jsonify({"status": "switched", "ticker": TICKER})
    return jsonify({"status": "error", "msg": "invalid ticker"}), 400




@app.route("/api/debug")
def api_debug():
    """Diagnostic endpoint — shows exactly what is failing."""
    import traceback, sys
    results = {}

    # 1. Test yfinance
    try:
        import yfinance as yf
        h = yf.Ticker("TSLA").history(period="5d", interval="1d")
        results["yfinance"] = {
            "ok": not h.empty,
            "rows": len(h),
            "latest_close": float(h["Close"].iloc[-1]) if not h.empty else None,
            "columns": list(h.columns),
        }
    except Exception as e:
        results["yfinance"] = {"ok": False, "error": str(e), "trace": traceback.format_exc()[-500:]}

    # 2. Test state
    results["state_price"] = state.get("price")
    results["state_keys_populated"] = {k: bool(v) for k, v in state.items() if isinstance(v, dict)}
    results["last_updated"] = state.get("last_updated", "NEVER")

    # 3. Try running a mini-analysis inline
    try:
        import yfinance as yf
        hist = yf.Ticker("TSLA").history(period="6mo", interval="1d")
        if hist.empty:
            results["mini_analysis"] = "FAIL - hist.empty"
        else:
            results["mini_analysis"] = f"OK - {len(hist)} rows, close={float(hist.get("Close","").iloc[-1]):.2f}"
            # Try each major sub-function
            closes  = hist["Close"]
            volumes = hist["Volume"]
            highs   = hist["High"]
            lows    = hist["Low"]
            opens_s = hist["Open"]
            for fn_name, fn_call in [
                ("rsi",        lambda: calculate_rsi(closes)),
                ("macd",       lambda: calculate_macd(closes)),
                ("bollinger",  lambda: calculate_bollinger(closes)),
                ("ichimoku",   lambda: calculate_ichimoku(highs, lows, closes)),
                ("spy",        lambda: calculate_spy_analysis(closes, float(closes.iloc[-1]))),
                ("mm_data",    lambda: calculate_market_maker_data("TSLA", float(closes.iloc[-1]))),
                ("uoa",        lambda: calculate_unusual_options_activity("TSLA", float(closes.iloc[-1]))),
                ("exit",       lambda: calculate_exit_analysis(closes, highs, lows, volumes, {}, {})),
                ("darthvader", lambda: calculate_darthvader(closes, highs, lows, volumes, opens_s, {}, {}, {})),
            ]:
                try:
                    r = fn_call()
                    results[f"fn_{fn_name}"] = f"OK ({type(r).__name__})"
                except Exception as fe:
                    results[f"fn_{fn_name}"] = f"FAIL: {str(fe)[:200]}"

    except Exception as e:
        results["mini_analysis"] = f"FAIL: {str(e)}"
        results["mini_trace"] = traceback.format_exc()[-800:]

    return jsonify(results)

@app.route("/api/spock", methods=["GET", "POST"])
def api_spock():
    """Spock AI — fires background thread, returns immediately."""
    from flask import request as freq
    import threading as _thr
    data        = freq.get_json(silent=True) or {}
    trigger     = data.get("trigger", "manual")
    portfolio   = int(data.get("portfolio", 100000))
    shares      = float(data.get("shares", 0))
    entry_price = float(data.get("entry_price", 0))
    ticker_req  = data.get("ticker", state.get("ticker","TSLA")).upper()
    if _spock_cache["running"]:
        return jsonify({"status":"running","message":"Spock is already analyzing..."})
    _thr.Thread(target=call_spock,
        kwargs={"trigger":trigger,"portfolio":portfolio,
                "shares":shares,"entry_price":entry_price,"ticker":ticker_req},
        daemon=True).start()
    return jsonify({"status":"started","message":"Spock is analyzing..."})


@app.route("/api/algo_alerts")
def api_algo_alerts():
    """Returns current algo detection state."""
    return jsonify({
        "last_alert":   _algo_state.get("last_alert"),
        "alert_history": _algo_state.get("alert_history", [])[:10],
        "signal_counts": {
            "ofi_ratio":   _algo_state.get("prev_ofi_ratio", 0),
            "aggression":  _algo_state.get("prev_aggression", 0),
        }
    })


@app.route("/api/spock/status")
def api_spock_status():
    cached=_spock_cache.get("last_analysis")
    return jsonify({"has_analysis":cached is not None,"analysis":cached,
                    "running":_spock_cache["running"],"last_trigger":_spock_cache["last_trigger"]})

@app.route("/api/spock/reset")
def api_spock_reset():
    _spock_cache["running"]=False
    return jsonify({"status":"reset"})

def call_spock_quickread(ticker=None):
    """One-line ACTION — sentence header read."""
    if _spock_cache.get("quick_running"): return
    _spock_cache["quick_running"]=True
    ticker_name=(ticker or state.get("ticker","TSLA")).upper()
    try:
        s=state; price=s.get("price",0); dv=s.get("darthvader",{})
        dv_state=dv.get("tsla_state",{}); risk=dv.get("risk_mode","NORMAL")
        probs=dv.get("probabilistic_signals",{}); rsi=s.get("indicators",{}).get("rsi",50)
        vix=s.get("spy_data",{}).get("vix",0)
        ext=s.get("ext_data",{}); session=ext.get("session","REGULAR")
        from datetime import datetime as _dt
        now=_dt.now(); month_name=now.strftime("%B"); day_of_week=now.strftime("%A")
        is_opex=(now.weekday()==4 and 15<=now.day<=21)
        system_prompt=(
            "You are SPOCK - a ruthlessly logical AI trading co-pilot.\n"
            "Task: ONE LINE ONLY in this exact format:\n"
            "ACTION - one sentence explanation (max 12 words)\n\n"
            "ACTION must be one of: BUY | SELL | HOLD | WAIT | CAUTION | AVOID\n\n"
            "Rules:\n"
            "- Total response: ONE LINE, NO newlines, NO bullets, NO extra text.\n"
            "- Apply 100 years of market wisdom:\n"
            "  * Momentum/mean-reversion base rates (RSI extremes, vol expansion)\n"
            "  * Macro regime (rate cycle phase, inflation regime, yield curve)\n"
            "  * Seasonality (OpEx vol, Fed week bias, Jan effect, sell-in-May)\n"
            "  * Crash pattern analogs (1987, 2000, 2008, 2020)\n\n"
            "Examples:\n"
            "HOLD - RSI overbought near resistance, mean-reversion likely within 3 sessions\n"
            "CAUTION - OpEx week historically volatile, wait for Friday resolution\n"
            "BUY - momentum breakout confirmed, 1995-style melt-up regime, add on dips\n"
            "AVOID - VIX spike matches 2018 vol unwind, stay flat until sub-20"
        )
        brk=probs.get("breakout_30m",{}).get("probability",0)
        brd=probs.get("breakdown_30m",{}).get("probability",0)
        user_msg=(
            f"Ticker: {ticker_name} | Price: ${price} | Session: {session}\n"
            f"DV State: {dv_state.get("state","?")} ({round(dv_state.get('confidence',0)*100)}% conf) | Risk: {risk}\n"
            f"RSI: {round(rsi,1)} | VIX: {vix} | Month: {month_name} | Day: {day_of_week} | OpEx: {is_opex}\n"
            f"Breakout: {brk:.0%} | Breakdown: {brd:.0%} | Intent: {dv.get("market_intent","?")}\n"
            f"Generate the one-line header read now:"
        )
        import urllib.request as _u, json as _j
        api_key=os.environ.get("ANTHROPIC_API_KEY","")
        if not api_key:
            _spock_cache["quick_read"]={"action":"WAIT","sentence":"API key not configured","ticker":ticker_name,"timestamp":"--"}
            return
        payload=_j.dumps({"model":"claude-haiku-4-5-20251001","max_tokens":80,
            "system":system_prompt,"messages":[{"role":"user","content":user_msg}]}).encode()
        req=_u.Request("https://api.anthropic.com/v1/messages",data=payload,
            headers={"Content-Type":"application/json","x-api-key":api_key,"anthropic-version":"2023-06-01"})
        with _u.urlopen(req,timeout=15) as resp: result=_j.loads(resp.read())
        raw=result.get("content",[{}])[0].get("text","HOLD - analyzing").strip()
        import re as _re
        m=_re.match(r'^(BUY|SELL|HOLD|WAIT|CAUTION|AVOID)\s*[-:\u2014]+\s*(.+)$',raw,_re.IGNORECASE)
        action,sentence=(m.group(1).upper(),m.group(2).strip()[:120]) if m else ("HOLD",raw[:120])
        _spock_cache["quick_read"]={"action":action,"sentence":sentence,"ticker":ticker_name,"timestamp":_dt.now().strftime("%H:%M")}
        print(f"[SPOCK-QR] {ticker_name}: {action} - {sentence[:60]}",flush=True)
    except Exception as e:
        print(f"[SPOCK-QR] Error: {e}",flush=True)
        _spock_cache["quick_read"]={"action":"HOLD","sentence":"Analysis temporarily unavailable","ticker":ticker_name,"timestamp":"--"}
    finally:
        _spock_cache["quick_running"]=False

@app.route("/api/spock/quickread",methods=["POST"])
def api_spock_quickread():
    import threading as _thr
    from flask import request as freq
    data=freq.get_json(silent=True) or {}
    ticker_req=data.get("ticker",state.get("ticker","TSLA")).upper()
    if _spock_cache.get("quick_running"): return jsonify({"status":"running"})
    _thr.Thread(target=call_spock_quickread,kwargs={"ticker":ticker_req},daemon=True).start()
    return jsonify({"status":"started"})

@app.route("/api/spock/quickread/status")
def api_spock_quickread_status():
    qr=_spock_cache.get("quick_read")
    return jsonify({"running":_spock_cache.get("quick_running",False),"has_read":qr is not None,"quick_read":qr})

@app.route("/api/refresh")
def api_refresh():
    threading.Thread(target=run_analysis).start()
    return jsonify({"status": "refreshing"})



def _save_regime_models(X_df, y, feat_cols, scaler, models_trained, base_pkg):
    """Save regime-specific models trained on regime-filtered data."""
    import pickle, numpy as np

    # Regime columns in feature set
    vix_col    = "vix"       if "vix"          in feat_cols else None
    earn_col   = "earn_near_5d" if "earn_near_5d" in feat_cols else None
    trend_col  = "trend_score"  if "trend_score"  in feat_cols else None

    regimes = {}
    if vix_col:
        regimes["high_vix"] = X_df[vix_col] >= 30
        regimes["low_vix"]  = X_df[vix_col] <= 15
    if earn_col:
        regimes["earnings"] = X_df[earn_col] == 1
    if trend_col:
        regimes["trending"] = X_df[trend_col].abs() >= 7

    for regime_name, mask in regimes.items():
        try:
            n = mask.sum()
            if n < 100:
                print(f"[REGIME] {regime_name}: only {n} samples, skipping", flush=True)
                continue
            Xr = X_df[mask]; yr = y[mask]
            regime_models = []
            for m in models_trained:
                try:
                    import copy
                    rm = copy.deepcopy(m)
                    rm.fit(Xr, yr)
                    regime_models.append(rm)
                except Exception: pass
            if not regime_models: continue
            pkg = {**base_pkg, "models": regime_models, "model": regime_models[0],
                   "n_samples": int(n), "regime": regime_name}
            path = f"/app/{TICKER.lower()}_model_{regime_name}.pkl"
            with open(path, "wb") as f: pickle.dump(pkg, f)
            print(f"[REGIME] Saved {regime_name} model ({n} samples)", flush=True)
        except Exception as e:
            print(f"[REGIME] {regime_name} failed: {e}", flush=True)


def _run_ml_retrain():
    """
    Enhanced ML retrain:
    - 5-minute intraday bars (~18,000 samples vs 104 daily)
    - New features: earnings proximity, IV term structure, dark pool %, SPY regime, P/C delta
    - Ensemble: LightGBM + XGBoost + LogisticRegression (majority vote)
    Feature names MUST match _ml_features keys in run_analysis.
    """
    global _ml_model_cache, _ml_load_errors
    print("[ML-RETRAIN] Starting enhanced retrain (5min bars + ensemble)...", flush=True)
    try:
        import numpy as np, pickle, os
        import pandas as _pd_rt
        from sklearn.preprocessing import StandardScaler
        from sklearn.model_selection import TimeSeriesSplit
        from sklearn.linear_model import LogisticRegression
        from sklearn.metrics import roc_auc_score
        # Import schwab_client locally so sc is always defined in this scope
        try:
            import schwab_client as sc
        except ImportError:
            sc = None

        # 1. Fetch 6 months of 5-minute TSLA bars
        # Fetch price history — Schwab first (2yr 5-min), yfinance fallback
        print("[ML-RETRAIN] Fetching price history...", flush=True)
        hist5 = _pd_rt.DataFrame()
        use_intraday = False

        # Try Schwab (2 years of 5-min = ~58,000 bars)
        if sc and sc.is_configured() and sc.get_client():
            try:
                hist5 = sc.get_price_history(TICKER, period_years=2, freq_minutes=5)
                if hist5 is not None and not hist5.empty and len(hist5) >= 500:
                    use_intraday = True
                    print(f"[ML-RETRAIN] Schwab: {len(hist5)} 5-min bars (2yr)", flush=True)
                else:
                    hist5 = _pd_rt.DataFrame()
            except Exception as _sch_e:
                print(f"[ML-RETRAIN] Schwab failed: {_sch_e}", flush=True)
                hist5 = _pd_rt.DataFrame()

        # Fallback: Yahoo 60d 5-min
        if hist5.empty:
            print("[ML-RETRAIN] Trying Yahoo 60d 5-min...", flush=True)
            try:
                hist5 = yf.download(TICKER, period="60d", interval="5m",
                                    progress=False, auto_adjust=True)
                if hasattr(hist5.columns, "levels"):
                    hist5.columns = hist5.columns.get_level_values(0)
                use_intraday = not hist5.empty and len(hist5) >= 500
            except Exception:
                hist5 = yf.Ticker("TSLA").history(period="60d", interval="5m")
                use_intraday = not hist5.empty and len(hist5) >= 500
        if not use_intraday:
            print("[ML-RETRAIN] Trying 1h bars (730 day limit)...", flush=True)
            try:
                hist5 = yf.download("TSLA", period="730d", interval="1h",
                                    progress=False, auto_adjust=True)
                if hist5.empty or len(hist5) < 200:
                    raise ValueError(f"only {len(hist5)} 1h bars")
                # yf.download returns MultiIndex columns sometimes - flatten
                if hasattr(hist5.columns, "levels"):
                    hist5.columns = hist5.columns.get_level_values(0)
                print(f"[ML-RETRAIN] Got {len(hist5)} 1h bars", flush=True)
            except Exception as _1he:
                print(f"[ML-RETRAIN] 1h failed ({_1he}), using 2y daily...", flush=True)
                hist5 = yf.download("TSLA", period="2y", interval="1d",
                                    progress=False, auto_adjust=True)
                if hasattr(hist5.columns, "levels"):
                    hist5.columns = hist5.columns.get_level_values(0)
                use_intraday = False
        print(f"[ML-RETRAIN] Got {len(hist5)} bars (interval={'5m' if use_intraday else 'fallback'})", flush=True)

        closes  = hist5["Close"].astype(float).reset_index(drop=True)
        highs   = hist5["High"].astype(float).reset_index(drop=True)
        lows    = hist5["Low"].astype(float).reset_index(drop=True)
        volumes = hist5["Volume"].astype(float).reset_index(drop=True)
        idx     = hist5.index

        # 2. Fetch SPY + QQQ daily data for market context features
        print("[ML-RETRAIN] Fetching SPY + QQQ daily for market features...", flush=True)
        # Fetch SPY daily for RSI/MACD/BB features aligned to bar dates
        try:
            spy_daily = yf.download("SPY", period="2y", interval="1d",
                                    progress=False, auto_adjust=True)
            if hasattr(spy_daily.columns, "levels"):
                spy_daily.columns = spy_daily.columns.get_level_values(0)
            spy_daily_closes = spy_daily["Close"].astype(float) if not spy_daily.empty else _pd_rt.Series()
        except Exception: spy_daily_closes = _pd_rt.Series()

        try:
            qqq_daily = yf.download("QQQ", period="2y", interval="1d",
                                    progress=False, auto_adjust=True)
            if hasattr(qqq_daily.columns, "levels"):
                qqq_daily.columns = qqq_daily.columns.get_level_values(0)
            qqq_daily_closes = qqq_daily["Close"].astype(float) if not qqq_daily.empty else _pd_rt.Series()
        except Exception: qqq_daily_closes = _pd_rt.Series()

        # Pre-compute daily SPY/QQQ indicators
        def _rsi14(s):
            d = s.diff(); g = d.where(d>0,0).rolling(14).mean()
            l = -d.where(d<0,0).rolling(14).mean()
            return 100 - 100/(1 + g/(l+1e-9))
        def _macd_hist(s):
            m = s.ewm(span=12,adjust=False).mean() - s.ewm(span=26,adjust=False).mean()
            return m - m.ewm(span=9,adjust=False).mean()
        def _bb_pct(s):
            ma = s.rolling(20).mean(); sd = s.rolling(20).std().replace(0,1)
            return (s - (ma - 2*sd)) / (4*sd + 1e-9)

        spy_rsi_s  = _rsi14(spy_daily_closes)   if len(spy_daily_closes) > 14 else _pd_rt.Series()
        spy_macd_s = _macd_hist(spy_daily_closes) if len(spy_daily_closes) > 26 else _pd_rt.Series()
        spy_bb_s   = _bb_pct(spy_daily_closes)   if len(spy_daily_closes) > 20 else _pd_rt.Series()
        spy_ema200 = spy_daily_closes.ewm(span=200,adjust=False).mean() if len(spy_daily_closes) > 50 else _pd_rt.Series()

        qqq_rsi_s  = _rsi14(qqq_daily_closes)    if len(qqq_daily_closes) > 14 else _pd_rt.Series()
        qqq_macd_s = _macd_hist(qqq_daily_closes) if len(qqq_daily_closes) > 26 else _pd_rt.Series()
        qqq_ema50  = qqq_daily_closes.ewm(span=50,adjust=False).mean()  if len(qqq_daily_closes) > 50 else _pd_rt.Series()
        qqq_ema200 = qqq_daily_closes.ewm(span=200,adjust=False).mean() if len(qqq_daily_closes) > 50 else _pd_rt.Series()

        print(f"[ML-RETRAIN] SPY daily: {len(spy_daily_closes)} bars, QQQ: {len(qqq_daily_closes)} bars", flush=True)

        # 2. Fetch SPY for correlation regime
        print("[ML-RETRAIN] Fetching SPY intraday...", flush=True)
        try:
            spy5 = _pd_rt.DataFrame()
            # Try Schwab SPY (matches TSLA bar count)
            if sc and sc.is_configured() and sc.get_client() and use_intraday:
                try:
                    spy5 = sc.get_price_history("SPY", period_years=2, freq_minutes=5)
                    if spy5 is None or spy5.empty: spy5 = _pd_rt.DataFrame()
                    else: print(f"[ML-RETRAIN] Schwab SPY: {len(spy5)} bars", flush=True)
                except Exception: spy5 = _pd_rt.DataFrame()
            # Yahoo fallback
            if spy5.empty:
                try:
                    spy5 = yf.download("SPY", period="60d", interval="5m",
                                       progress=False, auto_adjust=True)
                    if hasattr(spy5.columns, "levels"): spy5.columns = spy5.columns.get_level_values(0)
                except Exception: spy5 = yf.Ticker("SPY").history(period="60d", interval="5m")
            if spy5.empty or len(spy5) < 500:
                try:
                    spy5 = yf.download("SPY", period="730d", interval="1h",
                                       progress=False, auto_adjust=True)
                    if hasattr(spy5.columns, "levels"): spy5.columns = spy5.columns.get_level_values(0)
                except Exception: spy5 = yf.Ticker("SPY").history(period="2y", interval="1h")
            spy_closes = spy5["Close"].astype(float).reset_index(drop=True)
            min_len    = min(len(closes), len(spy_closes))
            closes     = closes.iloc[:min_len]
            highs      = highs.iloc[:min_len]
            lows       = lows.iloc[:min_len]
            volumes    = volumes.iloc[:min_len]
            spy_closes = spy_closes.iloc[:min_len]
            idx        = hist5.index[:min_len]
            spy_ok     = True
        except Exception as _spy_e:
            print(f"[ML-RETRAIN] SPY failed: {_spy_e}", flush=True)
            spy_closes = _pd_rt.Series(0.0, index=closes.index)
            spy_ok     = False

        # 3. Fetch real VIX (daily)
        try:
            vix_daily = yf.Ticker("^VIX").history(period="6mo", interval="1d")["Close"].astype(float)
            vix_ok = True
        except Exception:
            vix_ok = False

        # 4. Options: IV term structure + P/C ratio
        print("[ML-RETRAIN] Fetching options data...", flush=True)
        front_iv, back_iv, iv_term_spread, pc_ratio_now = 0.4, 0.4, 0.0, 1.0
        try:
            tkr = yf.Ticker("TSLA")
            exps = tkr.options
            if exps and len(exps) >= 2:
                c1 = tkr.option_chain(exps[0])
                c2 = tkr.option_chain(exps[1])
                front_iv = float(c1.calls["impliedVolatility"].median() or 0.4)
                back_iv  = float(c2.calls["impliedVolatility"].median() or 0.4)
                call_v   = float(c1.calls["volume"].sum() or 1)
                put_v    = float(c1.puts["volume"].sum() or 1)
                pc_ratio_now  = put_v / (call_v + 1e-9)
            iv_term_spread = back_iv - front_iv
        except Exception as _oe:
            print(f"[ML-RETRAIN] Options failed: {_oe}", flush=True)

        # 5. Earnings dates
        earnings_dates = []
        try:
            import subprocess as _subp, sys as _sys
            # Install lxml if missing (needed for earnings calendar)
            try:
                import lxml
            except ImportError:
                _subp.check_call([_sys.executable, "-m", "pip", "install", "lxml", "--quiet"])
            cal = yf.Ticker(TICKER).get_earnings_dates(limit=20)
            if cal is not None and not cal.empty:
                earnings_dates = [d.date() if hasattr(d,"date") else d for d in cal.index.tolist()]
            print(f"[ML-RETRAIN] Earnings: {len(earnings_dates)} dates loaded", flush=True)
        except Exception as _ee:
            print(f"[ML-RETRAIN] Earnings skipped: {str(_ee)[:60]}", flush=True)

        # 6. Pre-compute series
        delta     = closes.diff()
        gain14    = delta.where(delta>0,0).rolling(14).mean()
        loss14    = (-delta.where(delta<0,0)).rolling(14).mean()
        rsi14_s   = 100 - 100/(1 + gain14/loss14.replace(0,1e-9))
        gain6     = delta.where(delta>0,0).rolling(6).mean()
        loss6     = (-delta.where(delta<0,0)).rolling(6).mean()
        rsi6_s    = 100 - 100/(1 + gain6/loss6.replace(0,1e-9))
        ema12_s   = closes.ewm(span=12, adjust=False).mean()
        ema26_s   = closes.ewm(span=26, adjust=False).mean()
        macd_s    = ema12_s - ema26_s
        macd_h_s  = macd_s - macd_s.ewm(span=9, adjust=False).mean()
        ema50_s   = closes.ewm(span=50,  adjust=False).mean()
        ema200_s  = closes.ewm(span=200, adjust=False).mean()
        bb_ma20_s = closes.rolling(20).mean()
        bb_std_s  = closes.rolling(20).std().replace(0, 1e-9)
        if spy_ok and spy_closes.std() > 0:
            tsla_ret_s = closes.pct_change()
            spy_ret_s  = spy_closes.pct_change()
            corr_s     = tsla_ret_s.rolling(20).corr(spy_ret_s)
        else:
            corr_s = _pd_rt.Series(0.75, index=closes.index)

        # 7. Build feature rows — LOOKBACK scales with bar interval
        n = len(closes)
        if n >= 5000:
            LOOKBACK = 78   # 5-min: 78 bars ~ 1 trading day
            MIN_START = 200
            FORWARD   = 6   # predict 30min ahead (6x5min)
        elif n >= 1000:
            LOOKBACK = 7    # 1h: 7 bars ~ 1 trading day
            MIN_START = 50
            FORWARD   = 2   # predict 2h ahead
        else:
            LOOKBACK = 5    # daily: 5 bars ~ 1 week
            MIN_START = 30
            FORWARD   = 1   # predict next day
        print(f"[ML-RETRAIN] Using LOOKBACK={LOOKBACK} FORWARD={FORWARD}", flush=True)
        X_rows, y_rows = [], []
        import numpy as np

        skipped_errors = 0
        for i in range(MIN_START, n - FORWARD - 1):
            try:
                price = float(closes.iloc[i])
                if price <= 0: continue

                ts       = idx[i]
                bar_date = ts.date() if hasattr(ts,"date") else None
                bar_hour = float(ts.hour + ts.minute/60.0) if hasattr(ts,"hour") else 12.0
                bar_dow  = int(ts.weekday()) if hasattr(ts,"weekday") else 2

                def sc(j): return float(closes.iloc[j]) if float(closes.iloc[j])>0 else price
                ret_1b  = price/sc(i-1)-1;  ret_3b  = price/sc(i-3)-1
                ret_6b  = price/sc(i-6)-1;  ret_12b = price/sc(i-12)-1
                ret_48b = price/sc(max(0,i-48))-1

                rsi_14 = float(rsi14_s.iloc[i]) if not np.isnan(rsi14_s.iloc[i]) else 50.0
                rsi_6  = float(rsi6_s.iloc[i])  if not np.isnan(rsi6_s.iloc[i])  else rsi_14
                rsi_ob = 1 if rsi_14>70 else 0;  rsi_os = 1 if rsi_14<30 else 0

                macd_hist = float(macd_h_s.iloc[i]) if not np.isnan(macd_h_s.iloc[i]) else 0.0

                if vix_ok and bar_date is not None:
                    try:   vix_val = float(vix_daily.asof(str(bar_date)) or 20)
                    except: vix_val = 20.0
                else:
                    rets20  = [float(closes.iloc[j])/float(closes.iloc[j-1])-1
                               for j in range(max(1,i-19),i+1) if float(closes.iloc[j-1])>0]
                    vix_val = float(np.std(rets20)*(252**0.5)*100) if rets20 else 20.0
                vix_high = 1 if vix_val>25 else 0

                vol_ma    = float(volumes.iloc[max(0,i-12):i].mean() or 1)
                vol_ratio = float(volumes.iloc[i]) / vol_ma
                vol_surge = 1 if vol_ratio>2 else 0

                def tr(j): return max(float(highs.iloc[j])-float(lows.iloc[j]),
                abs(float(highs.iloc[j])-float(closes.iloc[j-1])),
                abs(float(lows.iloc[j])-float(closes.iloc[j-1])))
                tr5       = float(np.mean([tr(j) for j in range(max(1,i-5),i+1)]))
                tr20      = float(np.mean([tr(j) for j in range(max(1,i-20),i+1)]))
                atr_ratio = tr5/(tr20+1e-9)
                realized_vol = float(closes.pct_change().iloc[max(0,i-20):i].std() or 0.01)

                ma20  = float(bb_ma20_s.iloc[i]) if not np.isnan(bb_ma20_s.iloc[i]) else price
                std20 = float(bb_std_s.iloc[i])  if not np.isnan(bb_std_s.iloc[i])  else price*0.02
                bb_pct = (price-(ma20-2*std20))/(4*std20+1e-9)

                ofi_6b     = ret_6b
                ofi_zscore = ret_6b/(realized_vol/(252**0.5)+1e-9)

                vwap_proxy = float(closes.iloc[max(0,i-LOOKBACK):i+1].mean())
                vwap_dist  = (price-vwap_proxy)/(vwap_proxy+1e-9)
                above_vwap = 1 if vwap_dist>0 else 0

                tsla_spy_corr = float(corr_s.iloc[i]) if not np.isnan(corr_s.iloc[i]) else 0.75
                spy_ret_1b    = float(spy_closes.pct_change().iloc[i]) if spy_ok and not np.isnan(spy_closes.pct_change().iloc[i]) else ret_1b*0.5
                spy_decouple  = 1 if abs(tsla_spy_corr)<0.4 else 0

                open_ref         = float(closes.iloc[max(0,i-LOOKBACK)])
                daily_ret_so_far = (price-open_ref)/(open_ref+1e-9)

                ema50_v  = float(ema50_s.iloc[i]);  ema200_v = float(ema200_s.iloc[i])
                above_daily_ma20 = 1 if price>ema50_v  else 0
                daily_trend_up   = 1 if ema50_v>ema200_v else 0
                trend_score = sum(1 if float(closes.iloc[j])>float(closes.iloc[j-1]) else -1
                for j in range(max(1,i-10),i+1))
                above_ema9  = 1 if trend_score>=2 else 0
                above_ema21 = 1 if trend_score>=1 else 0

                is_open  = 1 if 9.5<=bar_hour<10.25  else 0
                is_close = 1 if 15.25<=bar_hour<16.0 else 0
                is_lunch = 1 if 11.75<=bar_hour<13.0 else 0

                h20 = float(highs.iloc[max(0,i-20):i].max() or price)
                l20 = float(lows.iloc[max(0,i-20):i].min()  or price)
                dist_from_high = (price-h20)/(h20+1e-9)
                dist_from_low  = (price-l20)/(l20+1e-9)
                absorption     = abs(float(highs.iloc[i])-float(lows.iloc[i]))/(price+1e-9)

                # SPY/QQQ market context for this bar date
                _spy_rsi_r=50.0;_spy_ob_r=0;_spy_os_r=0;_spy_mbull_r=1;_spy_bb_r=0.5;_spy_mom_r=0.0;_spy_a200_r=1
                _qqq_rsi_r=50.0;_qqq_ob_r=0;_qqq_os_r=0;_qqq_mbull_r=1;_qqq_mom_r=0.0;_qqq_bull_r=1;_mkt_ob_r=0;_mkt_os_r=0
                if bar_date is not None:
                  try:
                    _bd = str(bar_date)
                    if len(spy_rsi_s)>0: _sr=float(spy_rsi_s.asof(_bd) or 50); _spy_rsi_r=_sr; _spy_ob_r=1 if _sr>70 else 0; _spy_os_r=1 if _sr<30 else 0
                    if len(spy_macd_s)>0: _spy_mbull_r=1 if float(spy_macd_s.asof(_bd) or 0)>0 else 0
                    if len(spy_bb_s)>0: _spy_bb_r=float(spy_bb_s.asof(_bd) or 0.5)
                    if len(spy_ema200)>0 and len(spy_daily_closes)>0:
                      _sp=float(spy_daily_closes.asof(_bd) or 0); _s2=float(spy_ema200.asof(_bd) or _sp); _spy_a200_r=1 if _sp>_s2 else 0
                    if len(spy_daily_closes)>5:
                      _spn=float(spy_daily_closes.asof(_bd) or 0); _sp5=float(spy_daily_closes.shift(5).asof(_bd) or _spn)
                      _spy_mom_r=(_spn/_sp5-1) if _sp5>0 else 0
                    if len(qqq_rsi_s)>0: _qr=float(qqq_rsi_s.asof(_bd) or 50); _qqq_rsi_r=_qr; _qqq_ob_r=1 if _qr>70 else 0; _qqq_os_r=1 if _qr<30 else 0
                    if len(qqq_macd_s)>0: _qqq_mbull_r=1 if float(qqq_macd_s.asof(_bd) or 0)>0 else 0
                    if len(qqq_ema50)>0 and len(qqq_daily_closes)>0:
                      _qp=float(qqq_daily_closes.asof(_bd) or 0); _q50=float(qqq_ema50.asof(_bd) or _qp); _q200=float(qqq_ema200.asof(_bd) or _qp) if len(qqq_ema200)>0 else _qp
                      _qqq_bull_r=1 if _qp>_q50 and _qp>_q200 else 0
                    if len(qqq_daily_closes)>5:
                      _qpn=float(qqq_daily_closes.asof(_bd) or 0); _qp5=float(qqq_daily_closes.shift(5).asof(_bd) or _qpn)
                      _qqq_mom_r=(_qpn/_qp5-1) if _qp5>0 else 0
                    _mkt_ob_r=1 if _spy_ob_r and _qqq_ob_r else 0; _mkt_os_r=1 if _spy_os_r and _qqq_os_r else 0
                  except Exception: pass

                # Earnings proximity
                if earnings_dates and bar_date is not None:
                    days_to_earn  = min(abs((bar_date-ed).days) for ed in earnings_dates)
                    earn_near_5d  = 1 if days_to_earn<=5  else 0
                    earn_near_10d = 1 if days_to_earn<=10 else 0
                    earn_proximity = 1.0/(days_to_earn+1)
                else:
                    days_to_earn=30; earn_near_5d=0; earn_near_10d=0; earn_proximity=0.0

                # IV term structure (static from latest options fetch)
                iv_front     = front_iv
                iv_back      = back_iv
                iv_term_sprd = iv_term_spread
                iv_ratio     = front_iv/(back_iv+1e-9)

                # P/C
                pc_ratio      = pc_ratio_now
                pc_delta_feat = 0.0  # live value used in inference

                row = [
                ret_1b, ret_3b, ret_6b, ret_12b, ret_48b,
                rsi_14, rsi_6, rsi_ob, rsi_os, macd_hist,
                vix_val, vix_high,
                vol_ratio, vol_surge,
                atr_ratio, realized_vol,
                ofi_6b, ofi_zscore,
                vwap_dist, above_vwap,
                tsla_spy_corr, spy_ret_1b, spy_decouple,
                daily_ret_so_far,
                above_daily_ma20, daily_trend_up,
                trend_score, above_ema9, above_ema21,
                bar_hour, is_open, is_close, is_lunch, bar_dow,
                bb_pct,
                dist_from_high, dist_from_low,
                absorption,
                earn_proximity, earn_near_5d, earn_near_10d,
                iv_front, iv_back, iv_term_sprd, iv_ratio,
                pc_ratio, pc_delta_feat,
                # Greeks placeholders
                0.5, 0.0, 0.0, 0.0, 0.0,
                # SPY/QQQ market features
                _spy_rsi_r, _spy_ob_r, _spy_os_r, _spy_mbull_r, _spy_bb_r,
                _spy_mom_r, _spy_a200_r,
                _qqq_rsi_r, _qqq_ob_r, _qqq_os_r, _qqq_mbull_r, _qqq_mom_r, _qqq_bull_r,
                _mkt_ob_r, _mkt_os_r,
                ]
                X_rows.append(row)
                future = float(closes.iloc[min(i+FORWARD, n-1)])
                threshold = 1.0005 if FORWARD <= 2 else 1.001
                y_rows.append(1 if future > price*threshold else 0)
            except Exception as _le:
                skipped_errors += 1
                if skipped_errors <= 3: print(f"[ML-RETRAIN] bar {i} err: {_le}", flush=True)
        print(f"[ML-RETRAIN] {len(X_rows)} samples ({skipped_errors} errors), pos_rate={sum(y_rows)/max(len(y_rows),1):.2f}", flush=True)
        min_samples = 50 if FORWARD == 1 else 200   # daily bars need fewer samples
        if len(X_rows) < min_samples:
            print(f"[ML-RETRAIN] Not enough samples ({len(X_rows)} < {min_samples})", flush=True); return

        X  = _pd_rt.DataFrame(X_rows).replace([np.inf,-np.inf],0).fillna(0).values
        y  = np.array(y_rows)

        feat_cols = [
            "ret_1b","ret_3b","ret_6b","ret_12b","ret_48b",
            "rsi_14","rsi_6","rsi_ob","rsi_os","macd_hist",
            "vix","vix_high",
            "vol_ratio","vol_surge",
            "atr_ratio","realized_vol",
            "ofi_6b","ofi_zscore",
            "vwap_dist","above_vwap",
            "tsla_spy_corr","spy_ret_1b","spy_decouple",
            "daily_ret_so_far",
            "above_daily_ma20","daily_trend_up",
            "trend_score","above_ema9","above_ema21",
            "time_of_day","is_open","is_close","is_lunch","day_of_week",
            "bb_pct",
            "dist_from_high","dist_from_low",
            "absorption",
            "earn_proximity","earn_near_5d","earn_near_10d",
            "iv_front","iv_back","iv_term_spread","iv_ratio",
            "pc_ratio","pc_delta",
            # Schwab Greeks
            "delta_atm","gamma_exposure","theta_decay","vega_exposure","iv_skew",
            # SPY/QQQ market context (NEW)
            "spy_rsi","spy_ob","spy_os","spy_macd_bull","spy_bb_pct",
            "spy_mom_5d","spy_above_200",
            "qqq_rsi","qqq_ob","qqq_os","qqq_macd_bull","qqq_mom_5d","qqq_bull",
            "market_ob","market_os",
        ]

        assert len(feat_cols)==X.shape[1], f"Mismatch {len(feat_cols)} vs {X.shape[1]}"

        X_df   = _pd_rt.DataFrame(X, columns=feat_cols)
        scaler = StandardScaler()
        X_s    = scaler.fit_transform(X_df)
        X_s_df = _pd_rt.DataFrame(X_s, columns=feat_cols)

        # 9. Train ensemble
        print("[ML-RETRAIN] Training ensemble...", flush=True)
        models_trained = []
        model_names    = []

        try:
            from lightgbm import LGBMClassifier
            lgbm = LGBMClassifier(n_estimators=300, learning_rate=0.03, max_depth=5,
                                  num_leaves=31, subsample=0.8, colsample_bytree=0.8,
                                  random_state=42, verbose=-1)
            lgbm.fit(X_s_df, y); models_trained.append(lgbm); model_names.append("LightGBM")
            print("[ML-RETRAIN]   LightGBM OK", flush=True)
        except Exception as _le: print(f"[ML-RETRAIN]   LGBM fail: {_le}", flush=True)

        try:
            from xgboost import XGBClassifier
            xgb = XGBClassifier(n_estimators=300, learning_rate=0.03, max_depth=5,
                                subsample=0.8, colsample_bytree=0.8,
                                eval_metric="logloss", random_state=42, verbosity=0)
            xgb.fit(X_s_df, y); models_trained.append(xgb); model_names.append("XGBoost")
            print("[ML-RETRAIN]   XGBoost OK", flush=True)
        except Exception as _xe: print(f"[ML-RETRAIN]   XGB fail: {_xe}", flush=True)

        try:
            lr = LogisticRegression(C=0.1, max_iter=500, random_state=42)
            lr.fit(X_s_df, y); models_trained.append(lr); model_names.append("LogReg")
            print("[ML-RETRAIN]   LogReg OK", flush=True)
        except Exception as _lre: print(f"[ML-RETRAIN]   LR fail: {_lre}", flush=True)

        if not models_trained:
            print("[ML-RETRAIN] All models failed", flush=True); return

        # 10. TimeSeriesSplit CV
        tscv = TimeSeriesSplit(n_splits=5)
        fold_aucs = []
        for tr_idx, val_idx in tscv.split(X_s_df):
            X_tr,X_val = X_s_df.iloc[tr_idx],X_s_df.iloc[val_idx]
            y_tr,y_val = y[tr_idx],y[val_idx]
            fold_probs = []
            for m in models_trained:
                try: m.fit(X_tr,y_tr); fold_probs.append(m.predict_proba(X_val)[:,1])
                except: pass
            if fold_probs:
                try: fold_aucs.append(roc_auc_score(y_val, np.mean(fold_probs,axis=0)))
                except: pass
        # Re-fit on full data
        for m in models_trained:
            try: m.fit(X_s_df, y)
            except: pass

        auc = float(np.mean(fold_aucs)) if fold_aucs else 0.5
        print(f"[ML-RETRAIN] CV AUC={auc:.3f}", flush=True)

        # 11. Best threshold
        ens_prob = np.mean([m.predict_proba(X_s_df)[:,1] for m in models_trained], axis=0)
        best_thresh, best_f1 = 0.55, 0.0
        for thr in [0.52,0.55,0.58,0.60,0.62,0.65]:
            preds = (ens_prob>=thr).astype(int)
            tp=np.sum((preds==1)&(y==1)); fp=np.sum((preds==1)&(y==0)); fn=np.sum((preds==0)&(y==1))
            prec=tp/(tp+fp+1e-9); rec=tp/(tp+fn+1e-9); f1=2*prec*rec/(prec+rec+1e-9)
            if f1>best_f1: best_f1=f1; best_thresh=thr

        pkg = {
            "models":       models_trained,
            "model":        models_trained[0],
            "scaler":       scaler,
            "feature_cols": feat_cols,
            "model_name":   "+".join(model_names),
            "auc":          round(auc,3),
            "n_samples":    len(X),
            "entry_thresh": best_thresh,
            "trained_on":   datetime.now().strftime("%Y-%m-%d %H:%M"),
            "bar_interval": "5m",
            "n_models":     len(models_trained),
            "iv_front_ref": front_iv,
            "iv_back_ref":  back_iv,
            "pc_ratio_ref": pc_ratio_now,
        }
        pkl_path = f"/app/{TICKER.lower()}_model.pkl"
        with open(pkl_path,"wb") as f: pickle.dump(pkg,f)

        # Also save regime-specific models by splitting training data
        try:
            _save_regime_models(X_df, y, feat_cols, scaler, models_trained, pkg)
        except Exception as _re: print(f"[ML-RETRAIN] Regime models: {_re}", flush=True)
        _ml_model_cache = pkg
        _ml_load_errors = []
        print(f"[ML-RETRAIN] Saved — {pkg['model_name']} AUC={auc:.3f} on {len(X)} bars, {len(feat_cols)} features.", flush=True)

        try:
            print("[ML-RETRAIN] Triggering re-analysis...", flush=True)
            run_analysis()
            print("[ML-RETRAIN] Done.", flush=True)
        except Exception as _ra_e:
            print(f"[ML-RETRAIN] Re-analysis error: {_ra_e}", flush=True)

    except Exception as e:
        import traceback
        print(f"[ML-RETRAIN] Error: {e}", flush=True)
        traceback.print_exc()


@app.route("/api/ml/retrain")
def api_ml_retrain():
    """Retrain ML model directly on Railway using live yfinance data."""
    import threading as _thr
    _thr.Thread(target=_run_ml_retrain, daemon=True).start()
    return jsonify({"status": "started", "message": "Retraining ML model on Railway... check /api/debug/ml in ~60s"})

@app.route("/api/debug/ml")
def api_debug_ml():
    """Show exactly why ML model is or isn't working."""
    import os, pickle
    result = {}
    # 1. Check all candidate paths
    _script_dir = os.path.dirname(os.path.abspath(__file__))
    _paths = [
        f"{TICKER.lower()}_model.pkl", f"./{TICKER.lower()}_model.pkl",
        f"/app/{TICKER.lower()}_model.pkl",
        os.path.join(_script_dir, f"{TICKER.lower()}_model.pkl"),
        os.path.join(os.getcwd(), f"{TICKER.lower()}_model.pkl"),
        # fallback to tsla model for backward compat
        "tsla_model.pkl", "./tsla_model.pkl", "/app/tsla_model.pkl",
    ]
    result["cwd"]         = os.getcwd()
    result["script_dir"]  = _script_dir
    result["paths_checked"] = {}
    for p in _paths:
        result["paths_checked"][p] = os.path.exists(p)
    # 2. List files in cwd and /app
    try: result["cwd_files"]  = [f for f in os.listdir(os.getcwd()) if f.endswith('.pkl') or 'model' in f.lower()]
    except: result["cwd_files"] = []
    try: result["app_files"]  = [f for f in os.listdir("/app") if f.endswith('.pkl') or 'model' in f.lower()]
    except: result["app_files"] = []
    # 3. Try loading and report
    result["model_loaded"]  = _ml_model_cache is not None
    result["load_errors"]   = _ml_load_errors
    if _ml_model_cache:
        result["model_keys"]  = list(_ml_model_cache.keys()) if isinstance(_ml_model_cache, dict) else str(type(_ml_model_cache))
        result["feature_cols"] = _ml_model_cache.get("feature_cols", [])
        result["auc"]          = _ml_model_cache.get("auc", 0)
    # 4. Show last ML signal from state
    result["ml_signal"]     = state.get("ml_signal", {})
    result["master_signal"] = state.get("master_signal", {})
    result["earnings_context"] = state.get("earnings_context", {})
    result["alert_scorecard"]  = _get_alert_scorecard()
    return jsonify(result)

@app.route("/api/debug/options")
def api_debug_options():
    ticker_sym=request.args.get("ticker",TICKER)
    result={"ticker":ticker_sym,"steps":[]}
    try:
        tkr=yf.Ticker(ticker_sym); result["steps"].append("yf.Ticker() OK")
        expiries=tkr.options; result["expiries"]=list(expiries) if expiries else []
        result["steps"].append(f"tkr.options: {len(expiries) if expiries else 0} expiries")
        if expiries:
            chain=tkr.option_chain(expiries[0]); result["steps"].append(f"option_chain({expiries[0]}) OK")
            result["calls_rows"]=len(chain.calls); result["puts_rows"]=len(chain.puts)
        result["uoa_in_state"]={"net_flow":state.get("uoa_data",{}).get("net_flow","MISSING"),
            "signal":state.get("uoa_data",{}).get("uoa_signal","MISSING"),
            "whales":len(state.get("uoa_data",{}).get("whale_alerts",[])),
            "reasons":state.get("uoa_data",{}).get("uoa_reasons",[])}
    except Exception as e:
        import traceback; result["error"]=str(e); result["tb"]=traceback.format_exc()[-600:]
    return jsonify(result)

@app.route("/api/institutions/refresh")
def api_inst_refresh():
    def _fetch():
        state["institutional"] = fetch_institutional_data()
    threading.Thread(target=_fetch).start()
    return jsonify({"status": "fetching institutional data"})


@app.route("/api/set_portfolio", methods=["POST"])
def set_portfolio():
    """User sets their portfolio value from the dashboard."""
    from flask import request
    data = request.get_json() or {}
    try:
        pv = float(data.get("portfolio_value", 100_000))
        tv = float(data.get("target_vol", 0.12))
        state["_portfolio_value"] = max(1_000, pv)
        state["_target_vol"]      = max(0.05, min(tv, 0.30))
        return jsonify({"status": "ok", "portfolio_value": state["_portfolio_value"], "target_vol": state["_target_vol"]})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 400

@app.route("/api/darthvader")
def api_darthvader():
    """DarthVader 1.0 institutional intelligence API endpoint."""
    dv = state.get("darthvader", {})
    if not dv:
        return jsonify({
            "error": "DarthVader not yet computed",
            "tsla_state": {"state":"ANALYZING","confidence":0,"action":"Waiting for first analysis..."},
            "prob_signals": {"prob_breakout":0,"prob_breakdown":0,"prob_revert":50},
            "risk_mode": "NORMAL",
            "risk_color": "#00ff88",
            "risk_bg": "rgba(0,255,136,0.08)",
            "features": {"ofi_ratio":0,"aggression":0,"absorption":0,"vol_ratio":1,"trend_score":5,"momentum_5":0,"vacuum":0},
            "market_intent": "Initializing analysis...",
            "updated": "—",
        })
    return jsonify(_sanitize(dv))




# ── Schwab API Routes ─────────────────────────────────────────────────────────

@app.route("/api/schwab/status")
def api_schwab_status():
    """Check Schwab connection status."""
    configured = sc.is_configured()
    client     = sc.get_client() if configured else None
    connected  = client is not None
    result = {
        "configured": configured,
        "connected":  connected,
        "app_key_set":  bool(sc.SCHWAB_APP_KEY),
        "secret_set":   bool(sc.SCHWAB_APP_SECRET),
        "token_set":    bool(sc.SCHWAB_TOKEN_JSON and sc.SCHWAB_TOKEN_JSON != "PENDING"),
        "source":       "schwab" if connected else "yfinance",
    }
    if connected:
        try:
            q = sc.get_quote(TICKER)
            result["live_price"]   = q.get("price")
            result["change_pct"]   = q.get("change_pct")
            result["quote_source"] = q.get("source")
        except Exception as e:
            result["test_error"] = str(e)
    return jsonify(result)


@app.route("/api/schwab/auth_url")
def api_schwab_auth_url():
    """Step 1 of OAuth: get the Schwab login URL."""
    url, err = sc.get_auth_url()
    if err:
        return jsonify({"error": err}), 400
    return jsonify({
        "auth_url": url,
        "instructions": [
            "1. Open auth_url in your browser",
            "2. Log in with your Schwab credentials",
            "3. You will be redirected to https://127.0.0.1?code=... (browser shows error — this is normal)",
            "4. Copy the FULL URL from your browser address bar",
            "5. Call /api/schwab/complete_auth?url=PASTE_URL_HERE",
        ]
    })


@app.route("/api/schwab/complete_auth")
def api_schwab_complete_auth():
    """Step 2 of OAuth: complete with the redirect URL from browser."""
    redirect_url = request.args.get("url", "")
    if not redirect_url:
        return jsonify({"error": "Missing ?url= parameter — paste the full redirect URL"}), 400
    success, msg, token_json = sc.complete_auth_from_url(redirect_url)
    if not success:
        return jsonify({"error": msg}), 400
    return jsonify({
        "success":   True,
        "message":   msg,
        "next_step": "Add this as SCHWAB_TOKEN_JSON in Railway Variables, then redeploy",
        "token_json": token_json,
    })


@app.route("/api/schwab/test")
def api_schwab_test():
    """Test all Schwab data endpoints."""
    results = {"configured": sc.is_configured(), "connected": sc.get_client() is not None}
    try:
        q = sc.get_quote(TICKER)
        results["quote"] = {"price": q.get("price"), "change_pct": q.get("change_pct"), "source": q.get("source")}
    except Exception as e:
        results["quote"] = {"error": str(e)}
    try:
        df = sc.get_price_history(TICKER, period_years=0.1, freq_minutes=5)
        results["price_history"] = {"bars": len(df), "ok": len(df) > 0}
    except Exception as e:
        results["price_history"] = {"error": str(e)}
    try:
        opts = sc.get_option_chain(TICKER)
        results["options"] = {
            "calls": len(opts.get("calls", [])), "puts": len(opts.get("puts", [])),
            "front_iv": opts.get("front_iv"), "pc_ratio": opts.get("pc_ratio"),
            "gex": opts.get("gex_total"), "max_pain": opts.get("max_pain"),
            "source": opts.get("source"),
        }
    except Exception as e:
        results["options"] = {"error": str(e)}
    try:
        pos = sc.get_positions()
        tsla = [p for p in pos if p.get("symbol") == TICKER]
        results["positions"] = {"total": len(pos), "tsla": tsla[0] if tsla else None}
    except Exception as e:
        results["positions"] = {"error": str(e)}
    try:
        acct = sc.get_account_summary()
        results["account"] = acct
    except Exception as e:
        results["account"] = {"error": str(e)}
    return jsonify(results)


@app.route("/schwab-setup")
def schwab_setup_page():
    """Simple HTML page for Schwab OAuth setup — no URL encoding headaches."""
    import schwab_client as sc
    auth_url, err = sc.get_auth_url()
    status = "connected" if (sc.is_configured() and sc.get_client()) else ("configured" if sc.is_configured() else "not configured")
    html = """<!DOCTYPE html>
<html>
<head>
<title>Schwab Setup</title>
<style>
body{font-family:monospace;background:#0a0e1a;color:#00e5ff;padding:40px;max-width:800px;margin:0 auto;}
h1{color:#00ff88;}
h2{color:#ffb300;margin-top:30px;}
input{width:100%;padding:10px;background:#1a2030;border:1px solid #00e5ff;color:#fff;font-family:monospace;font-size:13px;border-radius:4px;box-sizing:border-box;}
button{background:#00ff88;color:#000;border:none;padding:12px 24px;font-family:monospace;font-size:14px;font-weight:700;cursor:pointer;border-radius:4px;margin-top:10px;}
button:hover{background:#00cc66;}
.status{padding:10px;border-radius:4px;margin:10px 0;}
.ok{background:rgba(0,255,136,0.1);border:1px solid #00ff88;color:#00ff88;}
.warn{background:rgba(255,179,0,0.1);border:1px solid #ffb300;color:#ffb300;}
.err{background:rgba(255,51,85,0.1);border:1px solid #ff3355;color:#ff3355;}
pre{background:#1a2030;padding:15px;border-radius:4px;overflow-x:auto;font-size:12px;color:#69f0ae;white-space:pre-wrap;word-break:break-all;}
a{color:#00e5ff;}
</style>
</head>
<body>
<h1>🔐 Schwab API Setup</h1>
<div class="status STATUSCLASS">Status: STATUS</div>

<h2>Step 1 — Open Schwab Login</h2>
<p>Click the button below to open the Schwab login page in a new tab:</p>
AUTH_BUTTON

<h2>Step 2 — Paste Redirect URL</h2>
<p>After logging in, your browser will redirect to <code>https://127.0.0.1/?code=...</code> and show an error. 
Copy the <b>full URL</b> from your address bar and paste it below:</p>
<input type="text" id="redirectUrl" placeholder="https://127.0.0.1/?code=C0.xxx&session=xxx&state=xxx" />
<br>
<button onclick="completeAuth()">Complete Auth</button>
<div id="result"></div>

<h2>Step 3 — Save Token</h2>
<p>After completing auth above, copy the <code>token_json</code> value and add it as <code>SCHWAB_TOKEN_JSON</code> in Railway Variables.</p>

<script>
async function completeAuth() {
    var url = document.getElementById('redirectUrl').value.trim();
    if (!url) { alert('Paste the redirect URL first'); return; }
    document.getElementById('result').innerHTML = '<p style="color:#ffb300">Completing auth...</p>';
    try {
        var resp = await fetch('/api/schwab/complete_auth_post', {
            method: 'POST',
            headers: {'Content-Type': 'application/json'},
            body: JSON.stringify({url: url})
        });
        var data = await resp.json();
        if (data.success) {
            document.getElementById('result').innerHTML = 
                '<div class="status ok">✅ Auth complete!</div>' +
                '<p>Copy this entire value and set it as <b>SCHWAB_TOKEN_JSON</b> in Railway:</p>' +
                '<pre>' + JSON.stringify(JSON.parse(data.token_json), null, 2) + '</pre>';
        } else {
            document.getElementById('result').innerHTML = 
                '<div class="status err">❌ Error: ' + (data.error || 'Unknown error') + '</div>';
        }
    } catch(e) {
        document.getElementById('result').innerHTML = '<div class="status err">❌ ' + e.message + '</div>';
    }
}
</script>
</body>
</html>""".replace("STATUS", status).replace("STATUSCLASS", "ok" if status=="connected" else "warn" if status=="configured" else "err")
    
    if auth_url:
        btn = f'<a href="{auth_url}" target="_blank"><button>🔑 Open Schwab Login (new tab)</button></a>'
    else:
        btn = f'<div class="status err">Error: {err}</div>'
    html = html.replace("AUTH_BUTTON", btn)
    return html


@app.route("/api/schwab/complete_auth_post", methods=["POST"])
def api_schwab_complete_auth_post():
    """POST version of complete_auth — accepts JSON body so URL encoding is not an issue."""
    import schwab_client as sc
    data = request.get_json() or {}
    redirect_url = data.get("url", "").strip()
    if not redirect_url:
        return jsonify({"error": "Missing url in request body"}), 400
    success, msg, token_json = sc.complete_auth_from_url(redirect_url)
    if not success:
        return jsonify({"error": msg}), 400
    return jsonify({
        "success":   True,
        "message":   msg,
        "next_step": "Copy token_json and set as SCHWAB_TOKEN_JSON in Railway Variables",
        "token_json": token_json,
    })

@app.route("/api/alert_scorecard")
def api_alert_scorecard():
    """Alert quality scorecard — win rates for each alert type."""
    scorecard = _get_alert_scorecard()
    return jsonify({
        "scorecard": scorecard,
        "total_tracked": len(_alert_outcomes),
        "recent": _alert_outcomes[-10:][::-1],
    })


@app.route("/health")
def health(): return jsonify({"status": "ok"}), 200

# ═══════════════════════════════════════════════════════════════
#  SPOCK 2.0 — AI TRADING CO-PILOT (Claude-powered, server-side)
# ═══════════════════════════════════════════════════════════════

def _build_cap_context(s):
    cap=s.get("capitulation",{})
    if not cap or not cap.get("detected"): return ""
    return (
        f"\nCAPITULATION BOUNCE ALERT:\n"
        f"  Drop: {cap.get('drop_from_high_pct',0):.1f}% | Phase: {cap.get("phase","?")} | Recovery: {cap.get('recovery_pct',0):.0f}%\n"
        f"  OFI Flip: {cap.get('ofi_flip',False)} | Vol Exhaustion: {cap.get('vol_exhaustion',False)} | VWAP Reclaim: {cap.get('vwap_reclaim',False)}\n"
        f"  Entry: ${cap.get('entry_zone_low',0):.2f}-${cap.get('entry_zone_high',0):.2f} | Stop: ${cap.get('stop_loss',0):.2f}\n"
        f"  T1: ${cap.get('t1',0):.2f} | T2: ${cap.get('t2',0):.2f} | T3: ${cap.get('t3',0):.2f}\n"
        f"  Daily Trend Intact: {cap.get('daily_trend_intact',True)} | Conviction: {cap.get('conviction',0)}/100"
    )


def build_spock_prompt(portfolio=100000, shares=0, entry_price=0, ticker_override=None):
    """Assembles full market snapshot into Spock's prompt."""
    s         = state
    if ticker_override: s = dict(s); s["ticker"] = ticker_override.upper()
    dv        = s.get("darthvader", {})
    dv_state  = dv.get("tsla_state", {})
    risk      = dv.get("risk_mode", "UNKNOWN")
    probs     = dv.get("probabilistic_signals", {})
    uoa       = s.get("uoa_data", {})
    ind       = s.get("indicators", {})
    ichi      = s.get("ichimoku", {})
    hmm       = s.get("hmm", {})
    news      = s.get("news_data", {})
    ext       = s.get("ext_data", {})
    exit_data = s.get("exit_data", {})
    entry_data= s.get("entry_data", {})
    mm        = s.get("mm_data", {})
    price     = float(s.get("price", 0) or 0)

    # Position calculations
    has_position   = shares > 0 and entry_price > 0
    position_value = round(shares * price, 2)
    cost_basis     = round(shares * entry_price, 2)
    pnl_usd        = round((price - entry_price) * shares, 2)
    pnl_pct        = round((price / entry_price - 1) * 100, 2) if entry_price else 0
    position_pct   = round((position_value / portfolio) * 100, 1) if portfolio else 0
    risk_per_share = round(price - entry_price, 2) if entry_price else 0

    # Key price levels from exit engine
    targets    = exit_data.get("targets", [])
    stop_level = exit_data.get("stop_loss", None)
    t1 = targets[0].get("price") if len(targets) > 0 else None
    t2 = targets[1].get("price") if len(targets) > 1 else None
    t3 = targets[2].get("price") if len(targets) > 2 else None

    # Risk/reward if in position
    if has_position and t1 and stop_level:
        reward    = round(t1 - entry_price, 2)
        risk_amt  = round(entry_price - stop_level, 2)
        rr_ratio  = round(reward / risk_amt, 2) if risk_amt > 0 else 0
    else:
        rr_ratio  = 0
        risk_amt  = 0

    # Max Pain / GEX levels
    max_pain  = mm.get("max_pain", "—")
    gex_level = mm.get("gex_flip", "—")

    # State probabilities
    state_dist = dv_state.get("state_distribution", {})
    probs_str  = "\n".join(
        f"  {k}: {round(v*100)}%" for k, v in
        sorted(state_dist.items(), key=lambda x: -x[1])
    ) if state_dist else "  No distribution data"

    # Top 3 news
    articles  = news.get("articles", [])[:3]
    news_str  = "\n".join(
        f"  [{a.get("sentiment","?").upper()}] {a.get("headline","")[:90]}"
        for a in articles
    ) if articles else "  No recent news"

    # Top whale
    whales    = uoa.get("whale_alerts", [])
    if whales:
        w = whales[0]
        whale_str = f"{w.get("premium_fmt","")} {w.get("type","")} ${w.get("strike","")} exp {w.get("expiry","")} ({w.get("severity","")})"
    else:
        whale_str = "None detected"

    # BB position
    bb_upper  = ind.get("bb_upper", 0) or 0
    bb_lower  = ind.get("bb_lower", 0) or 0
    if price > bb_upper:     bb_pos = f"ABOVE UPPER BAND (${bb_upper}) — stretched"
    elif price < bb_lower:   bb_pos = f"BELOW LOWER BAND (${bb_lower}) — oversold"
    else:                    bb_pos = f"Inside bands (${bb_lower} - ${bb_upper})"

    # Position context block
    if has_position:
        position_block = f"""
TRADER'S ACTIVE POSITION — THIS IS THE CORE OF YOUR ANALYSIS:
==============================================================
Shares Held:      {shares} shares
Entry Price:      ${entry_price}
Current Price:    ${price}
Cost Basis:       ${cost_basis:,}
Current Value:    ${position_value:,}
Unrealized P&L:   ${pnl_usd:+,} ({pnl_pct:+.2f}%)
Portfolio Alloc:  {position_pct}% of ${portfolio:,}
Risk Per Share:   ${risk_per_share:+.2f}

EXIT TARGETS FROM SYSTEM:
  T1 (first target):  ${t1 or "—"} → sell 40% of position
  T2 (main target):   ${t2 or "—"} → sell 40% of position
  T3 (extension):     ${t3 or "—"} → sell remaining 20%
  Stop Loss:          ${stop_level or "—"}
  Risk/Reward:        {rr_ratio}:1

YOUR SPECIFIC QUESTIONS TO ANSWER:
1. Is it safe to hold this position RIGHT NOW given current market state?
2. At what exact price should I start selling? Which tranche first?
3. How much should I sell at each level? (give % of position)
4. What is the stop loss level where I should cut losses?
5. What is the biggest risk to this position in the next 24-48 hours?"""
    else:
        position_block = f"""
TRADER HAS NO CURRENT POSITION:
Portfolio: ${portfolio:,}
Watching for entry. Assess whether current conditions warrant opening a position.
If yes: what price, how many shares, what stop loss."""

    ticker_name = s.get("ticker","TSLA")
    prompt = f"""You are SPOCK — a ruthlessly logical AI trading co-pilot for an active {ticker_name} trader.
You have access to a sophisticated multi-layer quant system (DarthVader 2.0).
Be precise. Be direct. Give exact prices and percentages. No vague answers.
The trader is relying on you for actionable guidance.

CURRENT MARKET SNAPSHOT:
========================
Ticker: {s.get("ticker", "TSLA")} | Price: ${price} | Session: {ext.get("session", "UNKNOWN")}
{_build_cap_context(s)}
Time: {ext.get("current_et_time", "—")} | Pre-mkt change: {ext.get("premarket_change_pct", "—")}%

DARTHVADER BEHAVIORAL STATE ENGINE:
- Current State:  {dv_state.get("state", "UNKNOWN")} ({round((dv_state.get("confidence",0))*100)}% confidence)
- Risk Mode:      {risk}
- Market Intent:  {dv.get("market_intent", "—")}
- Description:    {dv_state.get("description", "—")}
- Detection:      {" | ".join(dv_state.get("detection_signals", [])[:3])}

STATE PROBABILITY DISTRIBUTION:
{probs_str}

PROBABILISTIC SIGNALS (30-minute horizon):
- Breakout probability:  {round(probs.get("prob_breakout",0)*100)}%
- Breakdown probability: {round(probs.get("prob_breakdown",0)*100)}%
- Mean reversion:        {round(probs.get("prob_revert",0)*100)}%
- Expected move range:   {probs.get("expected_move_low","—")}% to {probs.get("expected_move_high","—")}%
- Model reliability:     {round(probs.get("model_reliability",0)*100)}%

OPTIONS FLOW (UOA):
- Net Flow Direction: {uoa.get("net_flow","—")} | Signal: {uoa.get("uoa_signal","—")}
- Whale Trades:       {len(uoa.get("whale_alerts",[]))} detected
- Call Premium:       ${round(uoa.get("total_call_premium",0)/1e6,2)}M
- Put Premium:        ${round(uoa.get("total_put_premium",0)/1e6,2)}M
- Call/Put Ratio:     {uoa.get("call_put_premium_ratio","—")}%
- Top Whale Alert:    {whale_str}
- Unusual Strikes:    {uoa.get("total_unusual",0)}

PRICE ACTION & TECHNICALS:
- EMA50:    ${ind.get("ema50","—")} | EMA200: ${ind.get("ema200","—")}
- RSI:      {ind.get("rsi","—")} | MACD Hist: {ind.get("macd_hist","—")}
- Bollinger: {bb_pos}
- Ichimoku: {ichi.get("cloud_signal","—")} — {" | ".join(ichi.get("cloud_details",[])[:2])}
- HMM Regime: {hmm.get("regime","—")} ({hmm.get("confidence","—")}% confidence)
- Volume Ratio: {ind.get("volume_ratio","—")}x avg

MARKET STRUCTURE:
- Max Pain:   ${max_pain}
- GEX Flip:   ${gex_level}

RECENT NEWS SENTIMENT ({news.get("signal","--")} | score: {news.get("score","--")}):
{news_str}

ALGO DETECTION ENGINE (real-time order flow signals):
{get_spock_algo_context()}

{position_block}

RESPOND IN THIS EXACT FORMAT:
================================================================
ACTION: [HOLD / REDUCE / EXIT / ADD / WAIT — pick ONE]
CONFIDENCE: [HIGH / MEDIUM / LOW]

POSITION SAFETY:
[Is this position safe to hold? Yes/No and why in 2 sentences max]

SELL PLAN:
• T1 SELL: [exact price] — sell [X]% of position — reason: [why this level]
• T2 SELL: [exact price] — sell [X]% of position — reason: [why this level]  
• T3 SELL: [exact price] — sell [X]% of position — reason: [why this level]

STOP LOSS:
[Exact price to cut losses. No negotiation.]

BIGGEST RISK RIGHT NOW:
[Single most dangerous thing that could hurt this position in next 48hrs]

MARKET READ:
[2 sentences — what is the market telling us RIGHT NOW]

WATCH FOR:
• [Most important trigger/level to monitor]
• [Second key thing]"""

    return prompt

def call_spock(trigger="manual", portfolio=100000, shares=0, entry_price=0, ticker=None):
    """Call Claude API server-side and cache the result."""
    import time, urllib.request, json as _json

    global _spock_cache

    if not ANTHROPIC_KEY:
        return {"error": "ANTHROPIC_API_KEY not set in Railway environment variables"}

    if _spock_cache["running"]:
        return {"error": "Spock is already thinking..."}

    # Cooldown check for auto-triggers
    if trigger != "manual":
        elapsed = time.time() - _spock_cache["last_ts"]
        if elapsed < SPOCK_COOLDOWN:
            return {"error": f"Cooldown: {int(SPOCK_COOLDOWN - elapsed)}s remaining"}

    _spock_cache["running"] = True
    try:
        prompt = build_spock_prompt(portfolio, shares, entry_price)

        payload = _json.dumps({
            "model": "claude-sonnet-4-6",
            "max_tokens": 400,
            "messages": [{"role": "user", "content": prompt}]
        }).encode("utf-8")

        req = urllib.request.Request(
            "https://api.anthropic.com/v1/messages",
            data=payload,
            headers={
                "Content-Type":      "application/json",
                "x-api-key":         ANTHROPIC_KEY,
                "anthropic-version": "2023-06-01",
            },
            method="POST"
        )

        with urllib.request.urlopen(req, timeout=25) as resp:
            data = _json.loads(resp.read())

        text = data["content"][0]["text"].strip()

        # Parse structured response
        def extract(label, txt):
            for line in txt.split("\n"):
                if line.strip().startswith(label + ":"):
                    return line.split(":", 1)[1].strip()
            return "—"

        result = {
            "action":     extract("ACTION", text),
            "size":       extract("SIZE", text),
            "confidence": extract("CONFIDENCE", text),
            "full_text":  text,
            "trigger":    trigger,
            "timestamp":  datetime.now().strftime("%H:%M:%S ET"),
            "price":      state.get("price", 0),
            "dv_state":   state.get("darthvader", {}).get("tsla_state", {}).get("state", "—"),
        }

        _spock_cache.update({
            "last_analysis":    result,
            "last_trigger":     trigger,
            "last_ts":          time.time(),
            "last_dv_state":    result["dv_state"],
            "last_risk_mode":   state.get("darthvader", {}).get("risk_mode", "—"),
            "last_whale_count": len(state.get("uoa_data", {}).get("whale_alerts", [])),
        })

        print(f"  🖖 Spock: {result.get("action","")} | {result.get("confidence","")} | triggered by {trigger}")
        return result

    except Exception as e:
        err_msg = str(e)
        try:
            if hasattr(e, 'read'):
                body = e.read().decode('utf-8', errors='replace')
                err_msg = str(e) + " | " + body[:300]
        except Exception:
            pass
        print(f"  Spock error: {err_msg}")
        return {"error": err_msg}
    finally:
        _spock_cache["running"] = False



# ═══════════════════════════════════════════════════════════════
#  ALGO DETECTION ENGINE — 5-Signal Real-Time Scanner
# ═══════════════════════════════════════════════════════════════

# Rolling history for velocity detection (last 10 price snapshots)
_price_history_rt = []   # [(timestamp, price, volume)]
_algo_state = {
    "last_alert":       None,   # last fired AlgoAlert dict
    "last_alert_ts":    0,      # unix time of last alert
    "alert_history":    [],     # last 20 alerts for display
    "prev_ofi_ratio":   0,
    "prev_aggression":  0,
    "prev_volume":      0,
    "consecutive_up":   0,
    "consecutive_down": 0,
    "baseline_volume":  0,
}
ALGO_COOLDOWN = 45   # min seconds between same-type alerts


def detect_algo_activity():
    """
    Runs every analysis cycle. Checks 5 signals against current
    order flow features. Returns AlgoAlert dict or None.
    """
    import time as _time

    dv       = state.get("darthvader", {})
    features = dv.get("features", {})
    price    = float(state.get("price", 0) or 0)
    if not features or not price:
        return None


# ── ML Directional Signal (trained LightGBM model) ───────────────
_ml_model_cache = None
_ml_load_errors = []

def _load_ml_model():
    global _ml_model_cache
    if _ml_model_cache is not None: return _ml_model_cache
    import pickle, os, subprocess, sys


    # Fix missing libgomp.so.1 (required by LightGBM on Railway/Debian containers)
    try:
        import ctypes
        ctypes.CDLL("libgomp.so.1")
    except OSError:
        print("  [ML] libgomp.so.1 missing -- installing libgomp1 via apt...", flush=True)
        try:
            subprocess.check_call(["apt-get", "install", "-y", "-q", "libgomp1"],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            print("  [ML] libgomp1 installed", flush=True)
        except Exception as _ae:
            print("  [ML] apt install libgomp1 failed: " + str(_ae), flush=True)

    # Auto-install schwab-py and lightgbm if not present
    for _pkg in ['schwab-py', 'lightgbm']:
        try:
            __import__(_pkg.replace('-','_'))
        except ImportError:
            try:
                import subprocess as _sp, sys as _sys
                _sp.check_call([_sys.executable, '-m', 'pip', 'install', _pkg, '--quiet'])
                print(f'  [ML] {_pkg} installed', flush=True)
            except Exception as _ie:
                print(f'  [ML] Could not install {_pkg}: {_ie}', flush=True)
    try:
        import lightgbm as _lgbm_test  # noqa
    except (ImportError, OSError):
        print("  [ML] Installing lightgbm...", flush=True)
        try:
            subprocess.check_call([sys.executable, "-m", "pip", "install", "lightgbm", "--quiet"])
            print("  [ML] lightgbm installed", flush=True)
        except Exception as _ie:
            print("  [ML] Could not install lightgbm: " + str(_ie), flush=True)

    # Railway deploys to /app by default; also check cwd and script dir
    _script_dir = os.path.dirname(os.path.abspath(__file__))
    _paths = [
        f"{TICKER.lower()}_model.pkl",
        f"./{TICKER.lower()}_model.pkl",
        f"/app/{TICKER.lower()}_model.pkl",
        os.path.join(_script_dir, f"{TICKER.lower()}_model.pkl"),
        os.path.join(os.getcwd(), f"{TICKER.lower()}_model.pkl"),
        "tsla_model.pkl", "./tsla_model.pkl", "/app/tsla_model.pkl",
    ]
    _load_errors = []
    for path in _paths:
        try:
            with open(path, "rb") as f:
                _ml_model_cache = pickle.load(f)
            print(f"  ✅ ML model loaded from {path} (AUC={_ml_model_cache.get('auc',0):.3f})", flush=True)
            return _ml_model_cache
        except FileNotFoundError:
            continue
        except Exception as e:
            _err = f"{path}: {type(e).__name__}: {str(e)[:200]}"
            _load_errors.append(_err)
            print(f"  ⚠️ ML model load error — {_err}", flush=True)
            break  # same file at all paths, no point retrying
    # Store errors for debug endpoint
    global _ml_load_errors
    _ml_load_errors = _load_errors
    print(f"  ❌ {TICKER.lower()}_model.pkl failed to load. Errors: {_load_errors}", flush=True)
    return None

def _detect_regime(features_dict):
    """Detect current market regime for regime-aware model selection."""
    vix     = float(features_dict.get("vix", 20) or 20)
    earn_5d = int(features_dict.get("earn_near_5d", 0) or 0)
    ts      = float(features_dict.get("trend_score", 0) or 0)

    if earn_5d:
        return "earnings"
    elif vix >= 30:
        return "high_vix"
    elif vix <= 15:
        return "low_vix"
    elif abs(ts) >= 7:
        return "trending"
    else:
        return "normal"


def _load_regime_model(regime):
    """Load regime-specific model if available, fall back to base model."""
    import os, pickle
    ticker_lower = TICKER.lower()
    regime_path  = f"/app/{ticker_lower}_model_{regime}.pkl"
    if os.path.exists(regime_path):
        try:
            with open(regime_path, "rb") as f:
                pkg = pickle.load(f)
            return pkg, regime
        except Exception:
            pass
    return _load_ml_model(), "base"


def _get_ml_signal(features_dict):
    """Run regime-aware ensemble ML model on current features."""
    empty = {"signal":"HOLD","confidence":0,"probability":0.5,"available":False}
    try:
        import numpy as np
        import pandas as pd

        # Detect regime and load appropriate model
        regime = _detect_regime(features_dict)
        pkg, used_regime = _load_regime_model(regime)

        if pkg is None: return empty
        cols = pkg["feature_cols"]
        row_data = {c: float(features_dict.get(c, 0) or 0) for c in cols}
        _is_stale = len(cols) != 67
        X_df   = pd.DataFrame([row_data], columns=cols)
        X_s    = pkg["scaler"].transform(X_df)
        X_s_df = pd.DataFrame(X_s, columns=cols)

        # Ensemble: average probabilities from all models
        models = pkg.get("models", [pkg.get("model")])
        models = [m for m in models if m is not None]
        if not models: return {**empty, "error": "no models in pkg"}

        probs = []
        for m in models:
            try: probs.append(float(m.predict_proba(X_s_df)[0][1]))
            except Exception: pass
        if not probs: return {**empty, "error": "all models failed"}

        prob   = float(np.mean(probs))
        agree  = sum(1 for p in probs if p >= 0.5) / len(probs)
        thresh = pkg.get("entry_thresh", 0.60)  # Tightened default 0.58→0.60
        min_confidence = 30  # Ignore ML signals below this — too noisy

        if prob >= thresh:         signal = "BUY"
        elif prob <= (1 - thresh): signal = "SELL"
        else:                      signal = "HOLD"

        # Compute confidence FIRST then apply noise filter
        base_conf        = round(abs(prob - 0.5) * 200)
        agreement_bonus  = round((abs(agree - 0.5) * 2) * 20)
        confidence       = min(100, base_conf + agreement_bonus)

        # Force HOLD if confidence too low — below 30% is noise
        if confidence < min_confidence:
            signal = "HOLD"

        matched = sum(1 for c in cols if c in features_dict)  # count all present features
        return {
            "signal":           signal,
            "confidence":       confidence,
            "probability":      round(prob, 3),
            "available":        True,
            "model":            pkg.get("model_name", "Ensemble"),
            "auc":              round(pkg.get("auc", 0), 3),
            "n_models":         len(probs),
            "model_agreement":  round(agree, 2),
            "features_matched": matched,
            "features_total":   len(cols),
            "stale":            _is_stale,
            "regime":           used_regime,
        }
    except Exception as e:
        return {**empty, "error": str(e)[:60]}

    ofi_ratio   = float(features.get("ofi_ratio",   0) or 0)
    aggression  = float(features.get("aggression",  0) or 0)
    absorption  = float(features.get("absorption",  0) or 0)
    vacuum      = float(features.get("vacuum",      0) or 0)
    vol_ratio   = float(features.get("vol_ratio",   0) or 0)
    trend_score = float(features.get("trend_score", 0) or 0)
    momentum_5  = float(features.get("momentum_5",  0) or 0)
    volume_now  = float(features.get("volume_now",  0) or 0)

    now         = _time.time()
    alerts      = []   # collect all firing signals this cycle

    # ── SIGNAL 1: OFI SPIKE ──────────────────────────────────────
    # ofi_ratio > 2.0  = buy programs dominating last 5 bars
    # ofi_ratio < -2.0 = sell programs dominating last 5 bars
    ofi_prev = _algo_state["prev_ofi_ratio"]
    if ofi_ratio > 2.0:
        intensity = "STRONG" if ofi_ratio > 4.0 else "MODERATE"
        alerts.append({
            "signal":    "OFI_BUY_SPIKE",
            "direction": "BUY",
            "intensity": intensity,
            "value":     round(ofi_ratio, 2),
            "label":     "OFI BUY SPIKE",
            "detail":    f"Buy imbalance {round(ofi_ratio,1)}x baseline — algo accumulation detected",
            "urgency":   "HIGH" if ofi_ratio > 4.0 else "MEDIUM",
        })
    elif ofi_ratio < -2.0:
        intensity = "STRONG" if ofi_ratio < -4.0 else "MODERATE"
        alerts.append({
            "signal":    "OFI_SELL_SPIKE",
            "direction": "SELL",
            "intensity": intensity,
            "value":     round(ofi_ratio, 2),
            "label":     "OFI SELL SPIKE",
            "detail":    f"Sell imbalance {round(abs(ofi_ratio),1)}x baseline — algo distribution detected",
            "urgency":   "HIGH" if ofi_ratio < -4.0 else "MEDIUM",
        })

    # ── SIGNAL 2: AGGRESSION SURGE ───────────────────────────────
    # Closes pinned near high (>0.25) = buying aggression
    # Closes pinned near low (<-0.25) = selling aggression
    if aggression > 0.25 and vol_ratio > 1.2:
        alerts.append({
            "signal":    "AGGRESSION_BUY",
            "direction": "BUY",
            "intensity": "STRONG" if aggression > 0.4 else "MODERATE",
            "value":     round(aggression, 3),
            "label":     "BUY AGGRESSION",
            "detail":    f"Bars closing near highs (aggr={round(aggression,2)}) on {round(vol_ratio,1)}x volume — aggressive buyers",
            "urgency":   "HIGH" if aggression > 0.4 else "MEDIUM",
        })
    elif aggression < -0.25 and vol_ratio > 1.2:
        alerts.append({
            "signal":    "AGGRESSION_SELL",
            "direction": "SELL",
            "intensity": "STRONG" if aggression < -0.4 else "MODERATE",
            "value":     round(aggression, 3),
            "label":     "SELL AGGRESSION",
            "detail":    f"Bars closing near lows (aggr={round(aggression,2)}) on {round(vol_ratio,1)}x volume — aggressive sellers",
            "urgency":   "HIGH" if aggression < -0.4 else "MEDIUM",
        })

    # ── SIGNAL 3: VOLUME VACUUM ───────────────────────────────────
    # vacuum > 3.0 AND ofi near zero = bids/offers pulled, gap risk
    prev_vol = _algo_state["prev_volume"]
    vol_collapse = (prev_vol > 0 and volume_now < prev_vol * 0.35 and volume_now > 0)
    if (vacuum > 3.0 or vol_collapse) and abs(ofi_ratio) < 1.0:
        direction = "SELL" if momentum_5 < 0 else "BUY"
        alerts.append({
            "signal":    "VOLUME_VACUUM",
            "direction": direction,
            "intensity": "STRONG",
            "value":     round(vacuum, 2),
            "label":     "VOLUME VACUUM",
            "detail":    f"Liquidity evaporating — bids/offers pulled. Vacuum={round(vacuum,1)}. Fast move imminent.",
            "urgency":   "HIGH",
        })

    # ── SIGNAL 4: ABSORPTION WALL ────────────────────────────────
    # High volume + tiny range = institution defending a level
    if absorption > 2.0 and vol_ratio > 1.5:
        # Determine if defending support (price near low of range) or resistance
        direction = "BUY" if momentum_5 >= 0 else "SELL"
        label = "BUY ABSORPTION" if direction == "BUY" else "SELL ABSORPTION"
        alerts.append({
            "signal":    "ABSORPTION_WALL",
            "direction": direction,
            "intensity": "STRONG" if absorption > 3.0 else "MODERATE",
            "value":     round(absorption, 2),
            "label":     label,
            "detail":    f"Institution absorbing {'supply' if direction=='BUY' else 'demand'} at ${round(price,2)} — {round(vol_ratio,1)}x vol, tiny range",
            "urgency":   "MEDIUM",
        })

    # ── SIGNAL 5: PRICE VELOCITY ─────────────────────────────────
    # trend_score counts how many of last 10 bars closed in same direction
    # +7 or better = momentum ignition (BUY), -7 or worse = momentum collapse
    if trend_score >= 7:
        alerts.append({
            "signal":    "VELOCITY_UP",
            "direction": "BUY",
            "intensity": "STRONG" if trend_score >= 9 else "MODERATE",
            "value":     round(trend_score, 0),
            "label":     "PRICE VELOCITY UP",
            "detail":    f"{int(trend_score)}/10 bars closing up — momentum ignition, algo buy program running",
            "urgency":   "HIGH" if trend_score >= 9 else "MEDIUM",
        })
    elif trend_score <= -7:
        alerts.append({
            "signal":    "VELOCITY_DOWN",
            "direction": "SELL",
            "intensity": "STRONG" if trend_score <= -9 else "MODERATE",
            "value":     round(trend_score, 0),
            "label":     "PRICE VELOCITY DOWN",
            "detail":    f"{abs(int(trend_score))}/10 bars closing down — momentum collapse, algo sell program running",
            "urgency":   "HIGH" if trend_score <= -9 else "MEDIUM",
        })

    # Update rolling state
    _algo_state["prev_ofi_ratio"]  = ofi_ratio
    _algo_state["prev_aggression"] = aggression
    _algo_state["prev_volume"]     = volume_now

    if not alerts:
        return None

    # Pick highest urgency alert
    priority = {"HIGH": 3, "MEDIUM": 2, "LOW": 1}
    top = max(alerts, key=lambda a: (priority.get(a["urgency"], 0),
                                     abs(float(a["value"]))))

    # Cooldown — don't repeat same signal within 45s
    last = _algo_state["last_alert"]
    if last and last.get("signal") == top["signal"]:
        if now - _algo_state["last_alert_ts"] < ALGO_COOLDOWN:
            return None

    # Build full alert
    alert = {
        **top,
        "price":       round(price, 2),
        "timestamp":   __import__("datetime").datetime.now().strftime("%H:%M:%S"),
        "all_signals": [a["signal"] for a in alerts],
        "signal_count": len(alerts),
        "ofi_ratio":   round(ofi_ratio, 2),
        "aggression":  round(aggression, 3),
        "absorption":  round(absorption, 2),
        "vacuum":      round(vacuum, 2),
        "vol_ratio":   round(vol_ratio, 2),
        "trend_score": round(trend_score, 0),
    }

    _algo_state["last_alert"]    = alert
    _algo_state["last_alert_ts"] = now
    _algo_state["alert_history"].insert(0, alert)
    _algo_state["alert_history"] = _algo_state["alert_history"][:20]  # keep last 20

    print(f"  [ALGO] {alert.get("label","")} | {alert.get("direction","")} | {alert.get("urgency","")} | ${alert.get("price","")}")
    return alert


def get_spock_algo_context():
    """Returns algo state summary string for Spock prompt."""
    last  = _algo_state.get("last_alert")
    hist  = _algo_state.get("alert_history", [])
    if not last:
        return "No algo signals detected in recent bars."

    recent_dirs = [a["direction"] for a in hist[:5]]
    buy_count   = recent_dirs.count("BUY")
    sell_count  = recent_dirs.count("SELL")
    bias        = "BUY BIAS" if buy_count > sell_count else "SELL BIAS" if sell_count > buy_count else "MIXED"

    return (
        f"LATEST ALGO SIGNAL: {last.get("label","")} ({last.get("direction","")}) at ${last.get("price","")} @ {last.get("timestamp","")}\n"
        f"  Detail: {last.get("detail","")}\n"
        f"  OFI={last.get("ofi_ratio","")} | Aggression={last.get("aggression","")} | Absorption={last.get("absorption","")} | Vol={last.get("vol_ratio","")}x\n"
        f"  Last 5 signals: {', '.join(recent_dirs)} => {bias}"
    )

def check_spock_triggers(algo_alert=None):
    """Called every analysis cycle — fires Spock if something changed meaningfully."""
    import threading, time

    dv       = state.get("darthvader", {})
    cur_state = dv.get("tsla_state", {}).get("state", "")
    cur_risk  = dv.get("risk_mode", "")
    cur_whales= len(state.get("uoa_data", {}).get("whale_alerts", []))

    trigger = None

    if cur_state and cur_state != _spock_cache["last_dv_state"] and _spock_cache["last_dv_state"]:
        trigger = f"STATE CHANGE: {_spock_cache.get("last_dv_state","")} → {cur_state}"

    elif cur_risk in ("DEFENSIVE",) and cur_risk != _spock_cache["last_risk_mode"]:
        trigger = f"RISK ESCALATED to {cur_risk}"

    elif cur_whales > _spock_cache["last_whale_count"] and cur_whales > 0:
        trigger = f"NEW WHALE TRADE DETECTED ({cur_whales} total)"

    if not trigger and algo_alert and algo_alert.get("urgency") == "HIGH":
        trigger = f"ALGO: {algo_alert.get("label","?")} @ ${algo_alert.get("price","?")}"

    if trigger:
        print(f"  🖖 Spock auto-trigger: {trigger}")
        threading.Thread(
            target=call_spock,
            kwargs={"trigger": trigger, "ticker": state.get("ticker","TSLA")},
            daemon=True
        ).start()


@app.route("/")
def dashboard():
    from flask import Response
    return Response(DASHBOARD_HTML, mimetype='text/html')


# ───────────────────────────────────────────────────────────────
# NEW HIGHS / NEW LOWS SCANNER
# ───────────────────────────────────────────────────────────────
_NH_NL_CACHE    = {"ts": 0, "data": None}
_NH_NL_INTERVAL = 30   # seconds — fast enough to catch breakouts

NH_NL_UNIVERSE = [
    # Mega-cap / NASDAQ
    "AAPL","MSFT","NVDA","AMZN","META","GOOGL","TSLA","AVGO","NFLX","AMD",
    "ADBE","QCOM","INTC","TXN","CSCO","INTU","AMAT","MU","LRCX","KLAC",
    "MRVL","PANW","CRWD","FTNT","ORCL","CRM","NOW","SNOW","DDOG","ZS",
    "ARM","ABNB","BKNG","PYPL","MELI","ISRG","REGN","VRTX","GILD","AMGN",
    "PLTR","COIN","HOOD","RBLX","RIVN","LYFT","UBER","ABNB","SPOT","RBLX",
    # Financials
    "JPM","BAC","WFC","GS","MS","V","MA","AXP","BLK","C","SCHW","COF",
    # Energy
    "XOM","CVX","COP","EOG","SLB","OXY","MPC","VLO",
    # Healthcare
    "JNJ","UNH","LLY","PFE","ABT","TMO","DHR","MRNA",
    # Consumer / Retail
    "HD","WMT","TGT","MCD","SBUX","NKE","CMG","COST","AMZN","TSLA",
    # Industrials
    "BA","CAT","HON","UPS","FDX","GE","RTX","LMT","DE",
    # ETFs
    "SPY","QQQ","IWM","DIA","XLK","XLF","XLE","XLV","GLD","SLV","TLT",
]
# Deduplicate
NH_NL_UNIVERSE = list(dict.fromkeys(NH_NL_UNIVERSE))


def calculate_new_highs_lows():
    """
    Scan universe for stocks making TRUE NEW INTRADAY HIGHS/LOWS.
    Uses 1-minute bars. Detects the MOMENT a stock exceeds all prior bars.
    """
    global _NH_NL_CACHE
    now = time.time()
    if _NH_NL_CACHE["data"] and (now - _NH_NL_CACHE["ts"]) < _NH_NL_INTERVAL:
        return _NH_NL_CACHE["data"]

    new_highs, new_lows = [], []

    def _scan_one(tkr):
        try:
            import yfinance as yf
            df = yf.Ticker(tkr).history(period="1d", interval="1m")
            if df is None or df.empty or len(df) < 5:
                df = yf.Ticker(tkr).history(period="1d", interval="5m")
            if df is None or df.empty or len(df) < 3:
                return None

            if hasattr(df.columns, 'levels'):
                df.columns = df.columns.get_level_values(-1)

            # Filter to regular session only
            try:
                import pytz
                et = pytz.timezone("America/New_York")
                df.index = df.index.tz_convert(et) if df.index.tzinfo else df.index.tz_localize("UTC").tz_convert(et)
                df = df.between_time("09:30", "16:00")
            except Exception:
                pass

            if df.empty or len(df) < 3:
                return None

            day_high   = float(df["High"].max())
            day_low    = float(df["Low"].min())
            day_open   = float(df["Open"].iloc[0])
            price      = float(df["Close"].iloc[-1])
            last_bar_h = float(df["High"].iloc[-1])
            last_bar_l = float(df["Low"].iloc[-1])
            prev_high  = float(df["High"].iloc[:-1].max())
            prev_low   = float(df["Low"].iloc[:-1].min())
            vol_today  = int(df["Volume"].sum()) if "Volume" in df.columns else 0
            vol_last3  = int(df["Volume"].iloc[-3:].sum()) if len(df) >= 3 else 0
            avg_bar_vol= max(vol_today / len(df), 1)

            if day_open <= 0 or price <= 0:
                return None

            chg_pct       = round((price / day_open - 1) * 100, 2)
            pct_from_high = round((price / day_high  - 1) * 100, 2)
            pct_from_low  = round((price / day_low   - 1) * 100, 2)

            # TRUE new high: last bar's HIGH exceeds ALL previous bars' highs
            is_new_high = last_bar_h >= prev_high
            # TRUE new low: last bar's LOW is below ALL previous bars' lows
            is_new_low  = last_bar_l <= prev_low
            vol_surge   = round(vol_last3 / (avg_bar_vol * 3), 1)

            return {
                "symbol":        tkr,
                "price":         round(price, 2),
                "day_high":      round(day_high, 2),
                "day_low":       round(day_low, 2),
                "day_open":      round(day_open, 2),
                "chg_pct":       chg_pct,
                "pct_from_high": pct_from_high,
                "pct_from_low":  pct_from_low,
                "vol":           vol_today,
                "vol_surge":     vol_surge,
                "is_new_high":   is_new_high,
                "is_new_low":    is_new_low,
            }
        except Exception:
            return None

    try:
        from concurrent.futures import ThreadPoolExecutor, as_completed
        results = {}
        with ThreadPoolExecutor(max_workers=25) as pool:
            futs = {pool.submit(_scan_one, tkr): tkr for tkr in NH_NL_UNIVERSE}
            for fut in as_completed(futs, timeout=45):
                r = fut.result()
                if r:
                    results[r["symbol"]] = r

        for entry in results.values():
            # New high: broke above all prior bars OR within 0.1% of day high
            if entry["is_new_high"] or entry["pct_from_high"] >= -0.1:
                new_highs.append(entry)
            # New low: broke below all prior bars OR within 0.1% of day low
            if entry["is_new_low"] or entry["pct_from_low"] <= 0.1:
                new_lows.append(entry)

        new_highs.sort(key=lambda x: x["chg_pct"], reverse=True)
        new_lows.sort(key=lambda x: x["chg_pct"])
        print(f"  📊 NHL: {len(new_highs)} highs, {len(new_lows)} lows from {len(results)} scanned")

    except Exception as e:
        print(f"  ⚠️ NHL scan error: {e}")

    result = {
        "new_highs": new_highs[:40],
        "new_lows":  new_lows[:40],
        "nh_count":  len(new_highs),
        "nl_count":  len(new_lows),
        "updated":   datetime.now().strftime("%H:%M:%S"),
        "universe":  len(NH_NL_UNIVERSE),
    }
    _NH_NL_CACHE = {"ts": now, "data": result}
    return result


@app.route("/api/new_highs_lows")
def api_new_highs_lows():
    try:
        return jsonify(calculate_new_highs_lows())
    except Exception as e:
        return jsonify({"error": str(e), "new_highs": [], "new_lows": [], "nh_count": 0, "nl_count": 0})



# ═══════════════════════════════════════════════════════════════
#  DARTHVADER 2.0 — INSTITUTIONAL INTELLIGENCE LAYER
# ═══════════════════════════════════════════════════════════════
# ═══════════════════════════════════════════════════════════════════
#  DARTHVADER 2.0 — INSTITUTIONAL INTELLIGENCE LAYER
#  Layer 2: Feature Engineering
#  Layer 3: Probabilistic Models  
#  Layer 4: Risk & State Engine
#  Layer 6: Meta Controller
# ═══════════════════════════════════════════════════════════════════

# ── Global state cache ──────────────────────────────────────────
_DV_CACHE = {"ts": 0, "data": None}
_DV_INTERVAL = 60  # seconds between full re-runs

# ── Prediction tracking for model reliability ───────────────────
_PREDICTION_LOG = []   # [{ts, state, prob_breakout, actual_outcome, correct}]
_MAX_PRED_LOG   = 200


# ─────────────────────────────────────────────────────────────────
# LAYER 2: ORDER FLOW FEATURE ENGINEERING
# Derives institutional-grade features from price/volume/options data
# ─────────────────────────────────────────────────────────────────
def calculate_order_flow_features(closes, highs, lows, volumes, opens):
    """
    Extracts order-flow imbalance, liquidity absorption, and
    volatility expansion/contraction features from OHLCV data.
    Returns a feature dict consumed by the state engine.
    """
    import numpy as np
    try:
        n = min(len(closes), 60)
        c = closes.iloc[-n:].values.astype(float)
        h = highs.iloc[-n:].values.astype(float)
        l = lows.iloc[-n:].values.astype(float)
        v = volumes.iloc[-n:].values.astype(float)
        o = opens.iloc[-n:].values.astype(float)

        price = float(c[-1])

        # ── Order Flow Imbalance ──────────────────────────────────
        # Positive = buyers in control, negative = sellers
        # Proxy: (close - open) / range * volume
        bar_range = h - l
        bar_range = np.where(bar_range < 0.01, 0.01, bar_range)
        ofi_bars  = (c - o) / bar_range * v
        ofi_5     = float(np.sum(ofi_bars[-5:]))
        ofi_20    = float(np.sum(ofi_bars[-20:])) if n >= 20 else ofi_5
        ofi_ratio = round(ofi_5 / (abs(ofi_20) + 1e-9), 2)  # recent vs longer

        # ── Aggressive vs Passive Flow ────────────────────────────
        # Large bars closing near high = aggressive buying
        # Large bars closing near low = aggressive selling
        close_position = (c - l) / bar_range  # 0=closed at low, 1=at high
        vol_weight     = v / (np.mean(v) + 1e-9)
        aggression     = float(np.mean((close_position[-5:] - 0.5) * vol_weight[-5:]))

        # ── Liquidity Absorption ──────────────────────────────────
        # High volume + small range = absorption (institutions absorbing)
        # Low volume + large range = vacuum (thin liquidity)
        range_pct  = bar_range / (c + 1e-9)
        vol_norm   = v / (np.mean(v) + 1e-9)
        absorption = float(np.mean(vol_norm[-5:] / (range_pct[-5:] * 1000 + 1)))
        vacuum     = float(np.mean(range_pct[-3:] * 1000 / (vol_norm[-3:] + 0.1)))

        # ── Volatility Expansion / Contraction ───────────────────
        # Compare recent ATR to longer-term ATR
        tr     = np.maximum(h - l, np.maximum(abs(h - np.roll(c, 1)), abs(l - np.roll(c, 1))))
        atr5   = float(np.mean(tr[-5:]))
        atr20  = float(np.mean(tr[-20:])) if n >= 20 else atr5
        vol_ratio = round(atr5 / (atr20 + 1e-9), 2)

        # ── Trend Persistence ─────────────────────────────────────
        # How many of last 10 bars closed in the same direction as the move?
        directions = np.sign(c[1:] - c[:-1])
        trend_score = float(np.sum(directions[-10:]))  # +10 = perfect up, -10 = perfect down
        momentum_5  = round((float(c[-1]) - float(c[-5])) / float(c[-5]) * 100, 2) if n >= 5 else 0
        momentum_20 = round((float(c[-1]) - float(c[-20])) / float(c[-20]) * 100, 2) if n >= 20 else 0

        # ── Smart Money Index (refined) ───────────────────────────
        # Early = dumb money (first 30min), late = smart money (last 30min)
        # Use first/last bar as proxy
        first_bar_move = float(c[0] - o[0]) if len(o) > 0 else 0
        last_bar_move  = float(c[-1] - o[-1]) if len(o) > 0 else 0
        smi = round(last_bar_move - first_bar_move, 3)

        # ── Gap Analysis ──────────────────────────────────────────
        gap_today = round((float(o[0]) - float(c[-2 if n > 1 else -1])) / float(c[-2 if n > 1 else -1]) * 100, 2) if n > 1 else 0

        return {
            "ofi_5":         round(ofi_5 / 1e6, 2),         # $ millions
            "ofi_ratio":     ofi_ratio,                       # recent vs baseline
            "aggression":    round(aggression, 3),            # buy/sell pressure
            "absorption":    round(absorption, 2),            # institutional absorption
            "vacuum":        round(vacuum, 2),                # liquidity vacuum score
            "vol_ratio":     vol_ratio,                       # expanding vs contracting
            "atr5":          round(atr5, 2),
            "atr20":         round(atr20, 2),
            "trend_score":   round(trend_score, 1),
            "momentum_5":    momentum_5,
            "momentum_20":   momentum_20,
            "smi":           smi,
            "gap_today":     gap_today,
            "price":         round(price, 2),
        }
    except Exception as e:
        print(f"  ⚠️ order_flow_features error: {e}")
        return {}


# ─────────────────────────────────────────────────────────────────
# LAYER 6 SHORTCUT: TSLA BEHAVIORAL STATE ENGINE
# The master variable — determines HOW the market is behaving
# ─────────────────────────────────────────────────────────────────
TSLA_STATES = {
    "TREND_EXPANSION":  {
        "color": "#00ff88", "icon": "📈",
        "desc": "Momentum works. Ride the trend.",
        "action": "Follow breakouts. Hold winners. Reduce counter-trend trades.",
        "risk": "NORMAL"
    },
    "MEAN_REVERSION":   {
        "color": "#40c4ff", "icon": "↩️",
        "desc": "Extended moves snap back. Fade.",
        "action": "Sell rips, buy dips. Tight stops. Avoid breakout chasing.",
        "risk": "NORMAL"
    },
    "DEALER_GAMMA_PIN": {
        "color": "#ffd600", "icon": "📌",
        "desc": "Dealer hedging pins price to strikes. Range-bound.",
        "action": "Sell options. Expect chop. Wait for pin break before trending.",
        "risk": "CAUTIOUS"
    },
    "GAMMA_EXPANSION":  {
        "color": "#ff9800", "icon": "💥",
        "desc": "Gamma pin broken. Dealers forced to buy/sell hard.",
        "action": "Direction determined by break. Size up. Fast moves incoming.",
        "risk": "NORMAL"
    },
    "LIQUIDITY_VACUUM": {
        "color": "#ff3355", "icon": "🌀",
        "desc": "Thin book. Fast impulsive moves on small volume.",
        "action": "Reduce size dramatically. Widen stops. Expect whipsaws.",
        "risk": "DEFENSIVE"
    },
    "CAPITULATION_BOUNCE": {
        "color": "#00ff88", "icon": "🎯",
        "desc": "Sharp drop exhausted. Buyers absorbing. Multi-day long setup forming.",
        "action": "Look to enter on first green 5m bar after low. Stop below session low. Target prior high.",
        "risk": "NORMAL"
    },
    "MACRO_RISK_OFF":   {
        "color": "#b388ff", "icon": "🌍",
        "desc": "TSLA correlated with broad selloff. Macro drives.",
        "action": "Don't fight the tape. Hedge. Wait for SPY stabilization.",
        "risk": "DEFENSIVE"
    },
}


def calculate_tsla_state(features, mm_data, spy_data, indicators):
    """
    Determine the current TSLA behavioral state from feature inputs.
    Returns state name, confidence, key signals, and next state probability.
    Implements the Level-6 meta-layer shortcut from the blueprint.
    """
    import numpy as np

    scores = {state: 0.0 for state in TSLA_STATES}
    signals = []

    vol_ratio    = features.get("vol_ratio", 1.0)
    trend_score  = features.get("trend_score", 0)
    absorption   = features.get("absorption", 1.0)
    vacuum       = features.get("vacuum", 1.0)
    momentum_5   = features.get("momentum_5", 0)
    momentum_20  = features.get("momentum_20", 0)
    aggression   = features.get("aggression", 0)
    ofi_ratio    = features.get("ofi_ratio", 0)

    # GEX from MM data
    net_gex      = mm_data.get("net_gex", 0) if mm_data else 0
    gamma_flip   = mm_data.get("gamma_flip", 0) if mm_data else 0
    price        = features.get("price", 0)
    price_vs_flip= (price - gamma_flip) / (abs(gamma_flip) + 1) if gamma_flip else 0

    # SPY correlation
    spy_chg      = spy_data.get("spy_change", 0) if spy_data else 0
    tsla_spy_corr= spy_data.get("tsla_spy_correlation", 0) if spy_data else 0

    # ── TREND_EXPANSION scoring ──────────────────────────────────
    if abs(trend_score) >= 6:
        scores["TREND_EXPANSION"] += 2.0
        signals.append(f"Strong trend: {trend_score:+.0f}/10 bars in direction")
    if abs(momentum_5) > 2.0:
        scores["TREND_EXPANSION"] += 1.5
        signals.append(f"5-bar momentum: {momentum_5:+.1f}%")
    if vol_ratio > 1.3 and abs(trend_score) > 4:
        scores["TREND_EXPANSION"] += 1.0
        signals.append("Volatility expanding with trend")
    if abs(aggression) > 0.2:
        scores["TREND_EXPANSION"] += 1.0

    # ── MEAN_REVERSION scoring ───────────────────────────────────
    rsi = indicators.get("rsi", 50) if indicators else 50
    bb_pct = indicators.get("bb_pct", 0.5) if indicators else 0.5
    if rsi > 72 or rsi < 28:
        scores["MEAN_REVERSION"] += 2.5
        signals.append(f"RSI extreme: {rsi:.0f} → mean-reversion setup")
    if bb_pct > 0.95 or bb_pct < 0.05:
        scores["MEAN_REVERSION"] += 2.0
        signals.append(f"Bollinger extreme: {bb_pct:.0%} of band")
    if vol_ratio < 0.8 and abs(momentum_5) > 1.5:
        scores["MEAN_REVERSION"] += 1.0  # extended on declining vol = reversal
        signals.append("Extended move with vol contraction")

    # ── DEALER_GAMMA_PIN scoring ─────────────────────────────────
    if net_gex > 0 and abs(price_vs_flip) < 0.01:
        scores["DEALER_GAMMA_PIN"] += 2.5
        signals.append(f"Positive GEX near gamma flip — dealer pinning")
    if vol_ratio < 0.85 and abs(trend_score) < 4:
        scores["DEALER_GAMMA_PIN"] += 1.5
        signals.append("Low vol + choppy → gamma pin likely")
    if absorption > 1.5:
        scores["DEALER_GAMMA_PIN"] += 1.0
        signals.append("High absorption — institutions defending levels")

    # ── GAMMA_EXPANSION scoring ──────────────────────────────────
    if net_gex < 0:
        scores["GAMMA_EXPANSION"] += 2.0
        signals.append("Negative GEX → dealers amplify moves")
    if vol_ratio > 1.4 and abs(price_vs_flip) > 0.02:
        scores["GAMMA_EXPANSION"] += 1.5
        signals.append("Vol expanding after pin break → gamma expansion")
    if net_gex < 0 and abs(momentum_5) > 1.5:
        scores["GAMMA_EXPANSION"] += 1.5
        signals.append("Negative gamma + momentum = acceleration")

    # ── LIQUIDITY_VACUUM scoring ─────────────────────────────────
    if vacuum > 2.0:
        scores["LIQUIDITY_VACUUM"] += 2.5
        signals.append(f"Liquidity vacuum score: {vacuum:.1f} — thin book")
    if vol_ratio > 2.0 and absorption < 0.5:
        scores["LIQUIDITY_VACUUM"] += 2.0
        signals.append("High vol expansion + low absorption = vacuum")
    if abs(momentum_5) > 4.0:
        scores["LIQUIDITY_VACUUM"] += 1.0
        signals.append("Extreme 5-bar momentum → possible vacuum")

    # ── MACRO_RISK_OFF scoring ───────────────────────────────────
    if tsla_spy_corr > 0.7 and spy_chg < -1.0:
        scores["MACRO_RISK_OFF"] += 3.0
        signals.append(f"High SPY correlation ({tsla_spy_corr:.0%}) + SPY down {spy_chg:.1f}%")
    if spy_chg < -2.0:
        scores["MACRO_RISK_OFF"] += 2.0
        signals.append(f"SPY macro selloff: {spy_chg:.1f}%")
    if tsla_spy_corr > 0.8:
        scores["MACRO_RISK_OFF"] += 1.0

    # ── CAPITULATION_BOUNCE scoring ──────────────────────────────
    cap_data = features.get("capitulation", {})
    drop_pct       = cap_data.get("drop_from_high_pct", 0)
    ofi_flip       = cap_data.get("ofi_flip", False)
    vol_exhaust    = cap_data.get("vol_exhaustion", False)
    vwap_reclaim   = cap_data.get("vwap_reclaim", False)
    support_bounce = cap_data.get("support_bounce", False)
    daily_trend_ok = cap_data.get("daily_trend_intact", True)
    if drop_pct > 3.0 and daily_trend_ok:
        scores["CAPITULATION_BOUNCE"] += 2.5
        signals.append(f"Intraday drop {drop_pct:.1f}% — potential capitulation")
    if ofi_flip:
        scores["CAPITULATION_BOUNCE"] += 2.0
        signals.append("OFI flipped positive — buyers absorbing after drop")
    if vol_exhaust:
        scores["CAPITULATION_BOUNCE"] += 1.5
        signals.append("Volume exhaustion on sell side — sellers drying up")
    if vwap_reclaim:
        scores["CAPITULATION_BOUNCE"] += 2.0
        signals.append("Price reclaimed VWAP — institutional buyers defending")
    if support_bounce:
        scores["CAPITULATION_BOUNCE"] += 1.5
        signals.append("Bounced off key support level — structure intact")
    if drop_pct > 5.0 and ofi_flip and daily_trend_ok:
        scores["CAPITULATION_BOUNCE"] += 1.5
        signals.append(f"Large drop ({drop_pct:.1f}%) + buyer absorption = high-conviction setup")

    # ── ML-validated regime multipliers (from SHAP analysis) ────
    # ATR regime: high vol = trend signals stronger, low vol = mean-revert
    atr_ratio   = features.get("atr_ratio", 0.01)
    realized_vol= features.get("realized_vol", 0.5)
    high_vol    = atr_ratio > 0.012 or realized_vol > 0.6
    low_vol     = atr_ratio < 0.006 and realized_vol < 0.3

    # Time-of-day multiplier (SHAP #2 predictor)
    from datetime import datetime as _dt2
    _now_h = _dt2.now().hour + _dt2.now().minute / 60
    is_open_window  = 9.5  <= _now_h < 10.25   # first 45min: highest edge
    is_close_window = 15.25 <= _now_h < 16.0   # last 45min: second highest
    is_lunch_chop   = 11.75 <= _now_h < 13.0   # lunch: weakest signals
    is_power_hour   = 15.0  <= _now_h < 16.0

    tod_mult = 1.0
    if is_open_window:  tod_mult = 1.3   # boost open signals
    if is_close_window: tod_mult = 1.2   # boost close signals
    if is_lunch_chop:   tod_mult = 0.7   # reduce lunch signals

    # ATR multiplier
    atr_mult = 1.2 if high_vol else (0.8 if low_vol else 1.0)

    # Apply multipliers to trend-following states
    trend_states = ["MARKUP","MOMENTUM_SURGE","BREAKOUT_IMMINENT",
                    "CAPITULATION_BOUNCE","DISTRIBUTION","MARKDOWN"]
    mean_rev_states = ["RANGE_BOUND","CONSOLIDATION","CHOP"]

    for st in trend_states:
        if st in scores:
            scores[st] *= tod_mult * atr_mult
    for st in mean_rev_states:
        if st in scores:
            scores[st] *= tod_mult * (1.2 if low_vol else 0.9)

    # ── Determine winner ─────────────────────────────────────────
    total = sum(scores.values()) or 1.0
    probs = {k: round(v / total, 3) for k, v in scores.items()}
    best_state = max(scores, key=scores.get)
    confidence = round(probs[best_state], 2)

    # ── Confidence floor: need > 25% to claim a state ────────────
    if confidence < 0.25:
        best_state = "MEAN_REVERSION"  # neutral fallback
        confidence = round(confidence, 2)

    state_meta = TSLA_STATES[best_state]
    risk_mode  = state_meta["risk"]

    return {
        "state":        best_state,
        "confidence":   confidence,
        "color":        state_meta["color"],
        "icon":         state_meta["icon"],
        "desc":         state_meta["desc"],
        "action":       state_meta["action"],
        "risk_mode":    risk_mode,
        "state_probs":  probs,
        "signals":      signals[:6],
        "pilot_mode":   confidence < 0.45,  # autopilot only if confident
    }


# ─────────────────────────────────────────────────────────────────
# LAYER 3: PROBABILISTIC SIGNAL ENGINE
# Replaces binary buy/sell with actual probabilities
# ─────────────────────────────────────────────────────────────────
def calculate_probabilistic_signals(closes, highs, lows, volumes,
                                    features, tsla_state, indicators):
    """
    Generates institutional-style probability outputs:
      - prob_breakout_30m:  probability price breaks above current range in 30min
      - prob_breakdown_30m: probability price breaks below current range in 30min
      - prob_mean_revert:   probability price reverts toward mean
      - expected_move_1h:   mean ± stdev of expected move in next hour
      - model_reliability:  how trustworthy are current signals
    """
    import numpy as np

    try:
        n = min(len(closes), 60)
        c = closes.iloc[-n:].values.astype(float)
        price = float(c[-1])

        # ── Base probabilities from state ───────────────────────
        state = tsla_state.get("state", "MEAN_REVERSION")
        conf  = tsla_state.get("confidence", 0.5)

        # Prior probabilities by state
        state_priors = {
            "TREND_EXPANSION":  {"breakout": 0.65, "breakdown": 0.15, "revert": 0.20},
            "MEAN_REVERSION":   {"breakout": 0.20, "breakdown": 0.20, "revert": 0.60},
            "DEALER_GAMMA_PIN": {"breakout": 0.25, "breakdown": 0.25, "revert": 0.50},
            "GAMMA_EXPANSION":  {"breakout": 0.55, "breakdown": 0.30, "revert": 0.15},
            "LIQUIDITY_VACUUM": {"breakout": 0.40, "breakdown": 0.40, "revert": 0.20},
            "MACRO_RISK_OFF":   {"breakout": 0.15, "breakdown": 0.65, "revert": 0.20},
        }
        priors = state_priors.get(state, {"breakout": 0.33, "breakdown": 0.33, "revert": 0.34})

        # ── Adjust based on directional features ────────────────
        momentum_5   = features.get("momentum_5", 0)
        trend_score  = features.get("trend_score", 0)
        ofi_ratio    = features.get("ofi_ratio", 0)
        vol_ratio    = features.get("vol_ratio", 1.0)
        rsi          = indicators.get("rsi", 50) if indicators else 50

        # Momentum adjustment
        mom_adj = min(0.20, abs(momentum_5) * 0.04)
        if momentum_5 > 0:
            p_break = priors["breakout"] + mom_adj * conf
            p_down  = priors["breakdown"] - mom_adj * conf * 0.5
        else:
            p_break = priors["breakout"] - mom_adj * conf * 0.5
            p_down  = priors["breakdown"] + mom_adj * conf

        # OFI adjustment
        ofi_adj = min(0.10, abs(ofi_ratio) * 0.05)
        if ofi_ratio > 0:
            p_break += ofi_adj
        else:
            p_down  += ofi_adj

        # Vol expansion increases breakout/breakdown, reduces reversion
        if vol_ratio > 1.3:
            p_break += 0.05; p_down += 0.05

        # RSI extremes boost reversion
        if rsi > 70 or rsi < 30:
            p_revert = min(0.80, priors["revert"] + 0.15)
        else:
            p_revert = priors["revert"]

        # Normalize to sum to 1
        total = p_break + p_down + p_revert
        p_break  = round(p_break / total, 2)
        p_down   = round(p_down / total, 2)
        p_revert = round(1 - p_break - p_down, 2)

        # ── Expected Move Calculation ────────────────────────────
        # Use recent ATR as volatility estimate
        tr = np.maximum(
            highs.iloc[-20:].values - lows.iloc[-20:].values,
            np.abs(closes.iloc[-20:].values - closes.iloc[-21:-1].values)
        ) if len(closes) > 21 else highs.iloc[-5:].values - lows.iloc[-5:].values
        atr  = float(np.mean(tr))
        # 1h expected move = ~25% of daily ATR (assuming 6.5hr day)
        expected_move_mean = round(momentum_5 * 0.02 * price / 100, 2)
        expected_move_std  = round(atr * 0.3, 2)
        expected_move_pct  = round(expected_move_mean / price * 100, 2)
        expected_std_pct   = round(expected_move_std / price * 100, 2)

        # ── Model Reliability Score ──────────────────────────────
        # Based on: signal consistency, regime stability, recent accuracy
        consistency = 1.0 - abs(p_break - p_down)  # higher = more directional conviction
        regime_stab = conf  # higher state confidence = more reliable model
        # Historical accuracy from prediction log
        if _PREDICTION_LOG:
            recent = _PREDICTION_LOG[-20:]
            correct = sum(1 for p in recent if p.get("correct"))
            hist_acc = correct / len(recent)
        else:
            hist_acc = 0.55  # assume baseline 55% when no history

        model_reliability = round((consistency * 0.4 + regime_stab * 0.4 + hist_acc * 0.2), 2)

        # ── Pilot vs Autopilot ───────────────────────────────────
        # Autopilot = system drives decisions (high reliability, clear state)
        # Pilot = human oversight needed (low reliability, ambiguous state)
        autopilot = model_reliability >= 0.65 and conf >= 0.45

        # ── Signal quality rating ────────────────────────────────
        if model_reliability >= 0.75:
            quality = "HIGH"; q_color = "#00ff88"
        elif model_reliability >= 0.55:
            quality = "MEDIUM"; q_color = "#ffd600"
        else:
            quality = "LOW"; q_color = "#ff3355"

        return {
            "prob_breakout_30m":   p_break,
            "prob_breakdown_30m":  p_down,
            "prob_mean_revert":    p_revert,
            "expected_move_mean":  expected_move_mean,
            "expected_move_std":   expected_move_std,
            "expected_move_pct":   expected_move_pct,
            "expected_std_pct":    expected_std_pct,
            "model_reliability":   model_reliability,
            "autopilot":           autopilot,
            "signal_quality":      quality,
            "quality_color":       q_color,
            "hist_accuracy":       round(hist_acc, 2),
        }

    except Exception as e:
        print(f"  ⚠️ probabilistic_signals error: {e}")
        return {
            "prob_breakout_30m": 0.33, "prob_breakdown_30m": 0.33,
            "prob_mean_revert": 0.34, "model_reliability": 0.5,
            "autopilot": False, "signal_quality": "LOW"
        }


# ─────────────────────────────────────────────────────────────────
# MASTER DARTHVADER FUNCTION — runs all 4 layers, returns JSON
# ─────────────────────────────────────────────────────────────────
def calculate_capitulation_bounce(ticker_symbol, current_price, closes_daily, highs_daily, lows_daily):
    """Detects intraday capitulation + bounce setups on 5m bars for multi-day entries."""
    result = {
        "detected": False, "drop_from_high_pct": 0, "session_high": 0, "session_low": 0,
        "ofi_flip": False, "vol_exhaustion": False, "vwap_reclaim": False,
        "support_bounce": False, "daily_trend_intact": True,
        "entry_zone_low": 0, "entry_zone_high": 0, "stop_loss": 0,
        "t1": 0, "t2": 0, "t3": 0, "conviction": 0,
        "summary": "No capitulation setup", "reasons": [], "phase": "NONE",
        "vwap": 0, "recovery_pct": 0, "risk_per_share": 0,
    }
    try:
        import numpy as np
        tkr = yf.Ticker(ticker_symbol)
        hist5 = tkr.history(period="2d", interval="5m", prepost=False)
        if hist5 is None or hist5.empty or len(hist5) < 20: return result
        from datetime import date as _date
        today = _date.today()
        try: hist5.index = hist5.index.tz_convert("America/New_York")
        except Exception:
            try: hist5.index = hist5.index.tz_localize("America/New_York")
            except Exception: pass
        today_mask = hist5.index.date == today
        h5 = hist5[today_mask]
        if len(h5) < 12: return result
        c5=h5["Close"].values.astype(float); h5h=h5["High"].values.astype(float)
        h5l=h5["Low"].values.astype(float);  v5=h5["Volume"].values.astype(float)
        o5=h5["Open"].values.astype(float)
        session_high=float(np.max(h5h)); session_low=float(np.min(h5l))
        current=float(c5[-1])
        result["session_high"]=round(session_high,2); result["session_low"]=round(session_low,2)
        drop_pct=(session_high-session_low)/session_high*100
        result["drop_from_high_pct"]=round(drop_pct,2)
        if drop_pct < 2.5:
            result["summary"]=f"Normal range ({drop_pct:.1f}%) — no capitulation"; return result
        low_bar_idx=int(np.argmin(h5l)); bars_since_low=len(c5)-1-low_bar_idx
        typical=(h5h+h5l+c5)/3; cum_vol=np.cumsum(v5); cum_tpv=np.cumsum(typical*v5)
        vwap=float(cum_tpv[-1]/(cum_vol[-1]+1e-9))
        bar_range=h5h-h5l; bar_range=np.where(bar_range<0.01,0.01,bar_range)
        ofi_bars=(c5-o5)/bar_range*v5
        low_window=ofi_bars[max(0,low_bar_idx-1):low_bar_idx+2]
        recent_ofi=ofi_bars[-3:]
        ofi_flip=(float(np.sum(low_window))<0)and(float(np.sum(recent_ofi))>0)and bars_since_low>=2
        avg_vol=float(np.mean(v5))
        vol_at_low=float(np.mean(v5[max(0,low_bar_idx-2):low_bar_idx+1]))
        vol_recent=float(np.mean(v5[-4:]))
        vol_exhaustion=(vol_at_low>avg_vol*1.3)and(vol_recent<vol_at_low*0.6)
        below_vwap_at_low=float(h5l[low_bar_idx])<vwap
        vwap_reclaim=below_vwap_at_low and(current>vwap*0.999)
        support_bounce=False; support_level_hit=None
        if closes_daily is not None and len(closes_daily)>=20:
            dc=closes_daily.values.astype(float)
            ma20=float(np.mean(dc[-20:]))
            ma50=float(np.mean(dc[-50:]))if len(dc)>=50 else ma20
            for level,name in[(ma20,"20D MA"),(ma50,"50D MA")]:
                if abs(session_low-level)/level<0.015:
                    support_bounce=True; support_level_hit=f"{name} (${level:.0f})"; break
            nearest_round=round(session_low/5)*5
            if not support_bounce and abs(session_low-nearest_round)<1.5:
                support_bounce=True; support_level_hit=f"Round level ${nearest_round:.0f}"
        daily_trend_intact=True
        if closes_daily is not None and len(closes_daily)>=20:
            dc=closes_daily.values.astype(float)
            ma20d=float(np.mean(dc[-20:]))
            ma50d=float(np.mean(dc[-50:]))if len(dc)>=50 else ma20d
            daily_trend_intact=(current>ma20d*0.97)and(ma20d>=ma50d*0.98)
        recovery_pct=(current-session_low)/(session_high-session_low+0.01)*100
        if bars_since_low<=2: phase="DROPPING"
        elif recovery_pct<30: phase="EXHAUSTING"
        elif recovery_pct<60: phase="BOUNCING"
        else: phase="CONFIRMED"
        conviction=0; reasons=[]
        if drop_pct>=3.0: conviction+=20; reasons.append(f"Dropped {drop_pct:.1f}% from ${session_high:.0f} to ${session_low:.0f}")
        if drop_pct>=5.0: conviction+=10; reasons.append("Large capitulation — increased snap-back potential")
        if ofi_flip: conviction+=25; reasons.append("OFI turned positive — buyers stepping in after drop")
        if vol_exhaustion: conviction+=20; reasons.append("Sell volume exhausted — supply absorbed")
        if vwap_reclaim: conviction+=20; reasons.append(f"Price reclaimed VWAP (${vwap:.2f}) — bullish structure restored")
        if support_bounce: conviction+=15; reasons.append(f"Bounced off {support_level_hit}")
        if not daily_trend_intact: conviction-=30; reasons.append("WARNING: Daily trend degraded — possible real breakdown")
        if phase in("BOUNCING","CONFIRMED"): conviction+=10; reasons.append(f"Recovery underway: {recovery_pct:.0f}% retraced")
        conviction=max(0,min(100,conviction))
        entry_low=round(min(current,vwap)*0.999,2)
        entry_high=round(max(current,vwap)*1.003,2)
        stop_loss=round(session_low*0.992,2)
        risk_ps=entry_high-stop_loss
        t1=round(entry_high+risk_ps*1.5,2); t2=round(entry_high+risk_ps*2.5,2); t3=round(session_high*1.005,2)
        detected=(conviction>=45 and drop_pct>=2.5 and daily_trend_intact
                  and phase in("EXHAUSTING","BOUNCING","CONFIRMED")
                  and(ofi_flip or vwap_reclaim or vol_exhaustion))
        result.update({"detected":detected,"ofi_flip":ofi_flip,"vol_exhaustion":vol_exhaustion,
            "vwap_reclaim":vwap_reclaim,"support_bounce":support_bounce,
            "daily_trend_intact":daily_trend_intact,"entry_zone_low":entry_low,
            "entry_zone_high":entry_high,"stop_loss":stop_loss,"t1":t1,"t2":t2,"t3":t3,
            "conviction":conviction,"reasons":reasons,"phase":phase,"vwap":round(vwap,2),
            "recovery_pct":round(recovery_pct,1),"risk_per_share":round(risk_ps,2)})
        if detected:
            result["summary"]=(f"CAPITULATION BOUNCE — Dropped {drop_pct:.1f}% to ${session_low:.0f}, "
                f"recovering ({phase}). Entry ${entry_low}-${entry_high} | Stop ${stop_loss} | T1 ${t1} T2 ${t2} T3 ${t3}")
        else:
            result["summary"]=f"Monitoring: {drop_pct:.1f}% drop, conviction {conviction}/100"
        print(f"  [CAP] {phase} | drop:{drop_pct:.1f}% | conv:{conviction} | detected:{detected}",flush=True)
    except Exception as e:
        print(f"  [CAP] Error: {e}",flush=True)
    return result


def calculate_darthvader(closes, highs, lows, volumes, opens,
                         mm_data, spy_data, indicators, cap_data=None):
    """
    Orchestrates all DarthVader intelligence layers.
    Returns the full institutional output dict.
    """
    global _DV_CACHE
    now = time.time()
    if _DV_CACHE["data"] and (now - _DV_CACHE["ts"]) < _DV_INTERVAL:
        return _DV_CACHE["data"]

    # L2: Feature Engineering
    features = calculate_order_flow_features(closes, highs, lows, volumes, opens)
    if cap_data: features["capitulation"] = cap_data

    # L6: TSLA State Engine  
    tsla_state = calculate_tsla_state(features, mm_data, spy_data, indicators)

    # L3: Probabilistic Signals
    prob_signals = calculate_probabilistic_signals(
        closes, highs, lows, volumes, features, tsla_state, indicators
    )

    # L4: Risk Mode
    risk_mode = tsla_state.get("risk_mode", "NORMAL")
    risk_colors = {
        "NORMAL":    {"color": "#00ff88", "bg": "rgba(0,255,136,0.08)"},
        "CAUTIOUS":  {"color": "#ffd600", "bg": "rgba(255,214,0,0.08)"},
        "DEFENSIVE": {"color": "#ff3355", "bg": "rgba(255,51,85,0.08)"},
    }
    risk_meta = risk_colors.get(risk_mode, risk_colors["NORMAL"])

    result = {
        # L2 features
        "features":          features,
        # L6 state engine
        "tsla_state":        tsla_state,
        # L3 probabilistic signals
        "prob_signals":      prob_signals,
        # L4 risk
        "risk_mode":         risk_mode,
        "risk_color":        risk_meta["color"],
        "risk_bg":           risk_meta["bg"],
        # Institutional API output (blueprint format)
        "institutional_api": {
            "tsla_state":         tsla_state.get("state"),
            "prob_breakout_30m":  prob_signals.get("prob_breakout_30m"),
            "prob_breakdown_30m": prob_signals.get("prob_breakdown_30m"),
            "expected_move_1h":   {
                "mean":  prob_signals.get("expected_move_pct"),
                "stdev": prob_signals.get("expected_std_pct"),
            },
            "risk_mode":          risk_mode,
            "model_reliability":  prob_signals.get("model_reliability"),
            "autopilot":          prob_signals.get("autopilot"),
        },
        "updated": datetime.now().strftime("%H:%M:%S"),
    }

    _DV_CACHE = {"ts": now, "data": result}
    return result


# ═══════════════════════════════════════════════════════════════
#  DASHBOARD HTML
# ═══════════════════════════════════════════════════════════════

DASHBOARD_HTML = """
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>⚔️ DARTHVADER 2.0 — TSLA Intelligence</title>
<link href="https://fonts.googleapis.com/css2?family=Share+Tech+Mono&family=Barlow+Condensed:wght@300;400;600;700;900&display=swap" rel="stylesheet">
<style>
  :root {
    --bg:#060810; --bg2:#0c0f1a; --bg3:#111520; --border:#1e2540;
    --green:#00ff88; --red:#ff3355; --amber:#ffb300; --blue:#0af;
    --dim:#4a5280; --text:#c8d0f0; --text-dim:#6070a0;
    --font-mono:'Share Tech Mono',monospace; --font-ui:'Barlow Condensed',sans-serif;
  }
  * { margin:0; padding:0; box-sizing:border-box; }
  body { background:var(--bg); color:var(--text); font-family:var(--font-ui); font-size:15px; min-height:100vh; }
  body::before {
    content:''; position:fixed; inset:0; pointer-events:none; z-index:9999;
    background:repeating-linear-gradient(0deg,transparent,transparent 2px,rgba(0,255,136,.015) 2px,rgba(0,255,136,.015) 4px);
  }
  header {
    display:flex; align-items:center; justify-content:space-between;
    padding:12px 24px; background:var(--bg2); border-bottom:1px solid var(--border);
    position:sticky; top:0; z-index:100;
  }
  .logo { font-family:var(--font-ui); font-weight:900; font-size:18px; letter-spacing:4px; color:var(--green); }
  .logo span { color:var(--text-dim); }
  .header-meta { font-family:var(--font-mono); font-size:11px; color:var(--text-dim); text-align:right; line-height:1.6; }
  .live-dot { display:inline-block; width:7px; height:7px; border-radius:50%; background:var(--green); margin-right:6px; animation:pulse 1.5s infinite; }
  @keyframes pulse { 0%,100%{opacity:1;box-shadow:0 0 0 0 rgba(0,255,136,.5)} 50%{opacity:.6;box-shadow:0 0 0 5px rgba(0,255,136,0)} }

  .main-grid { display:grid; grid-template-columns:1fr; gap:1px; background:var(--border); overflow:visible; }
  .panel { background:var(--bg2); padding:16px; }
  .panel-title { font-weight:700; font-size:12px; letter-spacing:3px; text-transform:uppercase; color:var(--text-dim); margin-bottom:12px; padding-bottom:8px; border-bottom:1px solid var(--border); }

  .signal-panel { grid-column:1/-1; display:flex; align-items:center; justify-content:space-between; padding:20px 32px; background:var(--bg3); flex-wrap:wrap; gap:16px; overflow:visible; position:relative; z-index:10; }
  .ticker-name { font-family:var(--font-ui); font-weight:900; font-size:48px; color:#fff; letter-spacing:2px; line-height:1; }
  .ticker-full { font-size:11px; color:var(--text-dim); letter-spacing:2px; margin-top:2px; }
  .price-value { font-family:var(--font-mono); font-size:42px; color:#fff; }
  .price-label { font-size:10px; letter-spacing:3px; color:var(--text-dim); }
  .signal-badge { padding:12px 32px; border-radius:2px; font-weight:900; font-size:36px; letter-spacing:8px; position:relative; overflow:hidden; }
  .signal-badge::before { content:''; position:absolute; inset:0; background:currentColor; opacity:.08; }
  .signal-badge.BUY  { color:var(--green); border:2px solid var(--green); }
  .signal-badge.SELL { color:var(--red);   border:2px solid var(--red); }
  .signal-badge.HOLD { color:var(--amber); border:2px solid var(--amber); }
  .strength-bar-wrap { display:flex; flex-direction:column; gap:6px; flex:1; max-width:200px; }
  .strength-label { font-size:10px; letter-spacing:3px; color:var(--text-dim); text-transform:uppercase; }
  .strength-bar { height:6px; background:var(--bg); border-radius:3px; overflow:hidden; }
  .strength-fill { height:100%; border-radius:3px; transition:width .8s ease; }
  .strength-val { font-family:var(--font-mono); font-size:13px; }

  .indicator-row { display:flex; justify-content:space-between; align-items:center; padding:8px 0; border-bottom:1px solid var(--border); font-size:13px; }
  .indicator-row:last-child { border-bottom:none; }
  .ind-name { font-family:var(--font-mono); color:var(--text-dim); font-size:11px; letter-spacing:1px; }
  .ind-val  { font-family:var(--font-mono); font-size:14px; }
  .ind-dot  { width:6px; height:6px; border-radius:50%; flex-shrink:0; }
  .bullish { color:var(--green); } .bearish { color:var(--red); } .neutral { color:var(--amber); }
  .dot-bull { background:var(--green); } .dot-bear { background:var(--red); } .dot-neut { background:var(--amber); }

  .chart-panel { display:flex; flex-direction:column; height:420px; min-height:420px; }

  /* ── DV 2.0 Ticker Dropdown ── */
  #tickerDropdown { font-family:var(--font-mono); }
  #tickerDropdown .tkr-row { padding:10px 14px; cursor:pointer; font-size:12px;
    display:flex; align-items:center; gap:10px; border-bottom:1px solid rgba(255,255,255,0.05); 
    transition:background 0.1s; }
  #tickerDropdown .tkr-row:hover, #tickerDropdown .tkr-row.active { background:rgba(0,255,136,0.10); }
  #tickerDropdown .tkr-sym { color:var(--green); font-weight:700; min-width:60px; font-size:13px; letter-spacing:1px; }
  #tickerDropdown .tkr-name { color:var(--text); font-size:10px; }
  #tickerDropdown .tkr-price { color:#fff; font-weight:700; margin-left:auto; }
  /* Search box header in dropdown */
  #tickerDropdown::before { content:'SEARCH TICKERS'; display:block; padding:8px 14px 6px;
    font-size:8px; letter-spacing:3px; color:var(--text-dim); border-bottom:1px solid rgba(0,255,136,0.2); }

  /* ── Risk Mode dominant border (injected by JS) ── */
  .risk-normal   { border-left-color:#00ff88 !important; }
  .risk-cautious { border-left-color:#ffd600 !important; }
  .risk-defensive{ border-left-color:#ff3355 !important; }

  /* ── Hide empty panels ── */
  .panel-empty { display:none !important; }

  /* ── Collapsible secondary panels ── */
  .panel-collapsible .panel-body { overflow:hidden; transition:max-height 0.3s ease; }
  .panel-collapsible.collapsed .panel-body { max-height:0 !important; }
  .panel-collapse-btn { cursor:pointer; float:right; color:var(--text-dim); font-size:10px; 
    padding:0 6px; letter-spacing:1px; }
  .panel-collapse-btn:hover { color:var(--text); }
  canvas#priceChart { flex:1; width:100%; height:300px !important; }
  @keyframes pulse { 0%,100%{opacity:1;} 50%{opacity:0.3;} }
  #aiOutputArea .ai-section { margin-bottom:8px; }
  #aiOutputArea .ai-label { color:#b388ff; font-weight:700; letter-spacing:1px; }
  #aiOutputArea .ai-buy  { color:#00ff88; }
  #aiOutputArea .ai-sell { color:#ff3355; }
  #aiOutputArea .ai-hold { color:#ffd600; }
  #aiOutputArea .ai-warn { color:#ff9800; }

  .alert-item { padding:10px 0; border-bottom:1px solid var(--border); line-height:1.5; }
  .alert-item:last-child { border-bottom:none; }
  .alert-time { font-family:var(--font-mono); font-size:10px; color:var(--text-dim); }
  .alert-sig  { font-weight:700; font-size:14px; letter-spacing:2px; }
  .alert-reason { font-family:var(--font-mono); font-size:10px; color:var(--text-dim); margin-top:2px; }
  .no-alerts { font-family:var(--font-mono); font-size:12px; color:var(--text-dim); padding:16px 0; }

  .inst-item { padding:10px 0; border-bottom:1px solid var(--border); }
  .inst-name { font-weight:700; font-size:14px; }
  .inst-meta { font-family:var(--font-mono); font-size:10px; color:var(--text-dim); margin-top:3px; }
  .inst-badge { display:inline-block; padding:1px 8px; font-size:10px; font-weight:700; letter-spacing:1px; border-radius:1px; margin-top:4px; }
  .badge-recent  { background:rgba(0,255,136,.1); color:var(--green); border:1px solid var(--green); }
  .badge-quarter { background:rgba(255,179,0,.1);  color:var(--amber); border:1px solid var(--amber); }
  .badge-old     { background:rgba(74,82,128,.2);  color:var(--dim);   border:1px solid var(--dim); }

  .sms-badge { display:flex; align-items:center; gap:8px; background:rgba(0,255,136,.06); border:1px solid rgba(0,255,136,.2); border-radius:2px; padding:8px 14px; font-family:var(--font-mono); font-size:11px; color:var(--green); }

  .btn-refresh { background:none; border:1px solid var(--border); color:var(--text-dim); font-family:var(--font-mono); font-size:11px; letter-spacing:2px; padding:6px 14px; cursor:pointer; transition:all .2s; text-transform:uppercase; }
  .btn-refresh:hover { border-color:var(--green); color:var(--green); background:rgba(0,255,136,.05); }

  footer { grid-column:1/-1; background:var(--bg2); padding:8px 24px; display:flex; justify-content:space-between; font-family:var(--font-mono); font-size:10px; color:var(--text-dim); border-top:1px solid var(--border); }

  /* ── NHL Scanner ── */
  /* nhlScrollUp removed — using overflow scroll */
  @keyframes nhlFlashGreen {
    0%   { background: rgba(0,255,136,0.35); }
    100% { background: transparent; }
  }
  @keyframes nhlFlashRed {
    0%   { background: rgba(255,51,85,0.35); }
    100% { background: transparent; }
  }
  .nhl-flash-high { animation: nhlFlashGreen 2s ease-out !important; }
  .nhl-flash-low  { animation: nhlFlashRed  2s ease-out !important; }
  .nhl-badge {
    font-size: 7px; letter-spacing: 1px; font-weight: 700;
    padding: 1px 4px; border-radius: 2px; margin-left: 4px;
    vertical-align: middle; display: inline-block;
  }
  .nhl-badge-new   { background: rgba(255,214,0,0.2);   color:#ffd600; border:1px solid rgba(255,214,0,0.5); }
  .nhl-badge-break { background: rgba(0,255,136,0.15);  color:#00ff88; border:1px solid rgba(0,255,136,0.4); }
  .nhl-badge-vol   { background: rgba(255,152,0,0.15);  color:#ff9800; border:1px solid rgba(255,152,0,0.4); }
  #nhlHighScroll:hover, #nhlLowScroll:hover { animation-play-state: paused; }

</style>
<script src="https://cdnjs.cloudflare.com/ajax/libs/Chart.js/4.4.1/chart.umd.min.js"></script>
<script>
function updateClock() { var el=document.getElementById('clock'); if(el) el.textContent = new Date().toLocaleTimeString('en-US',{hour12:false}); }
setInterval(updateClock,1000); updateClock();

// Register ChartAnnotation plugin when available
function registerAnnotationPlugin() {
  try {
    if(typeof ChartAnnotation !== 'undefined') {
      Chart.register(ChartAnnotation);
    } else if(window['chartjs-plugin-annotation']) {
      Chart.register(window['chartjs-plugin-annotation']);
    }
  } catch(e) { console.warn('ChartAnnotation:', e.message); }
}
registerAnnotationPlugin();
document.addEventListener('DOMContentLoaded', registerAnnotationPlugin);

const CHART_DEFAULTS = {
  responsive:true, maintainAspectRatio:false,
  plugins:{legend:{display:false}},
  scales:{
    x:{grid:{color:'#1e2540'},ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:9},maxTicksLimit:10}},
    y:{position:'right',grid:{color:'#1e2540'},ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:9},callback:v=>'$'+v.toFixed(0)}}
  }
};

// -- Price Chart - with annotation support for all buy/sell levels --
let chart = null;
function initChart() {
  if(chart) return;
  if(typeof Chart === 'undefined') { setTimeout(initChart, 100); return; }
  const _prc = document.getElementById('priceChart');
  const ctx = _prc ? _prc.getContext('2d') : null;
  if(!ctx) { setTimeout(initChart, 100); return; }
  try { chart = new Chart(ctx, {
  type:'line',
  data:{labels:[],datasets:[{label:'TSLA',data:[],borderColor:'#00ff88',borderWidth:2,pointRadius:0,fill:true,
    backgroundColor:(c)=>{const g=c.chart.ctx.createLinearGradient(0,0,0,300);g.addColorStop(0,'rgba(0,255,136,0.15)');g.addColorStop(1,'rgba(0,255,136,0)');return g;},tension:0.3}]},
  options:{
    ...CHART_DEFAULTS,
    plugins:{
      legend:{display:false},
      // annotation plugin removedted dynamically by updateChartAnnotations()
    }
  }
});

} catch(e) { console.error('Chart init failed:', e.message); }
}
initChart();
setTimeout(initChart, 500);

var ichimokuChart = null, hmmChart = null;
function initIchiHmm() {
  if(typeof Chart==='undefined'){setTimeout(initIchiHmm,200);return;}
  if(!ichimokuChart){var _ich=document.getElementById('ichimokuChart');if(_ich)try{ichimokuChart=new Chart(_ich.getContext('2d'),{type:'line',data:{labels:[],datasets:[{label:'Close',data:[],borderColor:'#fff',borderWidth:2,pointRadius:0,tension:0.3,fill:false,order:1},{label:'Tenkan',data:[],borderColor:'#ff6688',borderWidth:1,pointRadius:0,tension:0.3,fill:false,order:2},{label:'Kijun',data:[],borderColor:'#4488ff',borderWidth:1,pointRadius:0,tension:0.3,fill:false,order:3},{label:'Span A',data:[],borderColor:'rgba(0,255,136,0.6)',borderWidth:1,pointRadius:0,tension:0.3,fill:'+1',backgroundColor:'rgba(0,255,136,0.08)',order:4},{label:'Span B',data:[],borderColor:'rgba(255,51,85,0.6)',borderWidth:1,pointRadius:0,tension:0.3,fill:false,order:5}]},options:{...CHART_DEFAULTS,plugins:{legend:{display:true,labels:{color:'#6070a0',font:{family:'Share Tech Mono',size:9},boxWidth:20}}}}});}catch(e){console.warn('ichimokuChart:',e.message);}}
  if(!hmmChart){var _hmm=document.getElementById('hmmChart');if(_hmm)try{hmmChart=new Chart(_hmm.getContext('2d'),{type:'bar',data:{labels:[],datasets:[{label:'Daily Return (%)',data:[],backgroundColor:[],borderWidth:0,borderRadius:2}]},options:{responsive:true,maintainAspectRatio:false,plugins:{legend:{display:false},tooltip:{callbacks:{label:function(c){return c.parsed.y.toFixed(2)+'%';}}}},scales:{x:{grid:{color:'#1e2540'},ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},maxTicksLimit:12}},y:{position:'right',grid:{color:'#1e2540'},ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:9},callback:function(v){return v.toFixed(1)+'%';}}}}}})}catch(e){console.warn('hmmChart:',e.message);}}
}
initIchiHmm(); setTimeout(initIchiHmm,600); setTimeout(initIchiHmm,1500);

// -- UOA Heatmap Chart --
const _uoa=document.getElementById('uoaHeatmapChart'); const uoaHeatCtx=_uoa?_uoa.getContext('2d'):null;
let uoaHeatChart = null; if(uoaHeatCtx) uoaHeatChart = new Chart(uoaHeatCtx, {
  type:'bar',
  data:{ labels:[], datasets:[
    { label:'Call Premium ($K)', data:[], backgroundColor:'rgba(0,255,136,0.7)', borderWidth:0, borderRadius:2, stack:'s' },
    { label:'Put Premium ($K)',  data:[], backgroundColor:'rgba(255,51,85,0.7)',  borderWidth:0, borderRadius:2, stack:'s' },
  ]},
  options:{ responsive:true, maintainAspectRatio:false,
    plugins:{ legend:{ display:true, labels:{color:'#6070a0',font:{family:'Share Tech Mono',size:9},boxWidth:12}}},
    scales:{
      x:{ stacked:true, grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},maxTicksLimit:16}},
      y:{ stacked:true, position:'right', grid:{color:'#1e2540'},
          ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},callback:v=>v>=1000?(v/1000).toFixed(0)+'K':'$'+v}}
    }
  }
});

// -- Volatility Chart --
const _vol=document.getElementById('volChart'); const volCtx=_vol?_vol.getContext('2d'):null;
let volChart = null; if(volCtx) volChart = new Chart(volCtx, {
  type:'line',
  data:{ labels:[], datasets:[
    { label:'Realised Vol %', data:[], borderColor:'#00ff88', borderWidth:2,
      backgroundColor:'rgba(0,255,136,0.08)', fill:true, pointRadius:0, tension:0.4 }
  ]},
  options:{ responsive:true, maintainAspectRatio:false,
    plugins:{ legend:{display:false} },
    scales:{
      x:{ grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},maxTicksLimit:10}},
      y:{ position:'right', grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},callback:v=>v.toFixed(0)+'%'}}
    }
  }
});

// -- Intraday Chart --
const _intra=document.getElementById('intradayChart'); const intradayCtx=_intra?_intra.getContext('2d'):null;
let intradayChart = null; if(intradayCtx) intradayChart = new Chart(intradayCtx, {
  type:'line',
  data:{ labels:[], datasets:[
    { label:'Price', data:[], borderColor:'#40c4ff', borderWidth:1.5,
      pointRadius:0, fill:false, tension:0,
      segment:{ borderColor: ctx => {
        const raw = ctx.chart.data.datasets[0]._sessionColors;
        return raw ? raw[ctx.p1DataIndex] : '#40c4ff';
      }}
    }
  ]},
  options:{ responsive:true, maintainAspectRatio:false,
    plugins:{ legend:{display:false},
      annotation:{ annotations:{
        regStart:{ type:'line', scaleID:'x', value:0, borderColor:'rgba(0,255,136,0.3)', borderWidth:1, label:{content:'Open',display:false}},
        regEnd:  { type:'line', scaleID:'x', value:0, borderColor:'rgba(255,193,7,0.3)',  borderWidth:1, label:{content:'Close',display:false}},
      }}
    },
    scales:{
      x:{ grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},maxTicksLimit:12}},
      y:{ position:'right', grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},callback:v=>'$'+v.toFixed(0)}}
    }
  }
});


// -- SPY Price Chart --
const _spy=document.getElementById('spyChart'); const spyCtx=_spy?_spy.getContext('2d'):null;
let spyChart = null; if(spyCtx) spyChart = new Chart(spyCtx, {
  type:'line',
  data:{ labels:[], datasets:[
    { label:'SPY',  data:[], borderColor:'#29b6f6', borderWidth:2, pointRadius:0, fill:false, tension:0.3 },
    { label:'EMA20',data:[], borderColor:'rgba(255,193,7,0.7)', borderWidth:1, pointRadius:0, fill:false, borderDash:[4,4] },
    { label:'EMA50', data:[], borderColor:'rgba(255,100,50,0.7)', borderWidth:1, pointRadius:0, fill:false, borderDash:[4,4] },
  ]},
  options:{ responsive:true, maintainAspectRatio:false,
    plugins:{ legend:{ display:true, labels:{color:'#6070a0',font:{family:'Share Tech Mono',size:9},boxWidth:16}}},
    scales:{
      x:{ grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},maxTicksLimit:10}},
      y:{ position:'right', grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},callback:v=>'$'+v.toFixed(0)}}
    }
  }
});

// -- Relative Strength Chart --
const _rs=document.getElementById('rsChart'); const rsCtx=_rs?_rs.getContext('2d'):null;
let rsChart = null; if(rsCtx) rsChart = new Chart(rsCtx, {
  type:'line',
  data:{ labels:[], datasets:[
    { label:'TSLA', data:[], borderColor:'#00ff88', borderWidth:2, pointRadius:0, fill:false, tension:0.3 },
    { label:'SPY',  data:[], borderColor:'#29b6f6', borderWidth:2, pointRadius:0, fill:false, tension:0.3 },
    { label:'QQQ',  data:[], borderColor:'#ffd600', borderWidth:1.5, pointRadius:0, fill:false, tension:0.3, borderDash:[4,4] },
  ]},
  options:{ responsive:true, maintainAspectRatio:false,
    plugins:{ legend:{ display:true, labels:{color:'#6070a0',font:{family:'Share Tech Mono',size:9},boxWidth:16}},
      annotation:{annotations:[{type:'line',yMin:100,yMax:100,borderColor:'rgba(255,255,255,0.15)',borderWidth:1}]}
    },
    scales:{
      x:{ grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},maxTicksLimit:10}},
      y:{ position:'right', grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},callback:v=>v.toFixed(0)}}
    }
  }
});

// -- GEX by Strike Chart --
const _gex=document.getElementById('gexChart'); const gexCtx=_gex?_gex.getContext('2d'):null;
let gexChart = null; if(gexCtx) gexChart = new Chart(gexCtx, {
  type: 'bar',
  data: { labels:[], datasets:[{ label:'GEX ($M)', data:[], backgroundColor:[], borderWidth:0, borderRadius:2 }]},
  options:{ responsive:true, maintainAspectRatio:false,
    plugins:{ legend:{display:false}, annotation:{} },
    scales:{
      x:{ grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},maxTicksLimit:14} },
      y:{ position:'right', grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},
          callback:v=>v.toFixed(0)+'M'} }
    }
  }
});

// -- OI by Strike Chart --
const _oi=document.getElementById('oiChart'); const oiCtx=_oi?_oi.getContext('2d'):null;
let oiChart = null; if(oiCtx) oiChart = new Chart(oiCtx, {
  type: 'bar',
  data: { labels:[], datasets:[
    { label:'Call OI', data:[], backgroundColor:'rgba(255,51,85,0.6)',  borderWidth:0, borderRadius:2 },
    { label:'Put OI',  data:[], backgroundColor:'rgba(0,255,136,0.6)',  borderWidth:0, borderRadius:2 },
  ]},
  options:{ responsive:true, maintainAspectRatio:false,
    plugins:{ legend:{ display:true, labels:{color:'#6070a0',font:{family:'Share Tech Mono',size:9},boxWidth:16} }},
    scales:{
      x:{ grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},maxTicksLimit:14} },
      y:{ position:'right', grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},
          callback:v=>v>=1e3?(v/1e3).toFixed(0)+'K':v} }
    }
  }
});


// -- VIX Chart --
const _vix=document.getElementById('vixChart'); const vixCtx=_vix?_vix.getContext('2d'):null;
let vixChart = null; if(vixCtx) vixChart = new Chart(vixCtx, {
  type: 'line',
  data: { labels:[], datasets:[
    { label:'VIX', data:[], borderColor:'#ff6d00', backgroundColor:'rgba(255,109,0,0.08)', borderWidth:2, pointRadius:0, tension:0.3, fill:true },
  ]},
  options:{ responsive:true, maintainAspectRatio:false,
    plugins:{ legend:{display:false},
      annotation:{ annotations:{
        fear25:{ type:'line', yMin:25, yMax:25, borderColor:'rgba(255,51,85,0.5)', borderWidth:1, borderDash:[4,4] },
        fear18:{ type:'line', yMin:18, yMax:18, borderColor:'rgba(255,180,0,0.5)', borderWidth:1, borderDash:[4,4] },
      }}
    },
    scales:{
      x:{ grid:{color:'#1e2540'}, ticks:{color:'#4a5280', font:{family:'Share Tech Mono',size:8}, maxTicksLimit:10} },
      y:{ position:'right', grid:{color:'#1e2540'}, ticks:{color:'#4a5280', font:{family:'Share Tech Mono',size:8}} }
    }
  }
});

// -- MACD Line Chart --
const _ml=document.getElementById('macdLineChart'); const macdLineCtx=_ml?_ml.getContext('2d'):null;
let macdLineChart = null; if(macdLineCtx) macdLineChart = new Chart(macdLineCtx, {
  type: 'line',
  data: { labels: [], datasets: [
    { label:'MACD',   data:[], borderColor:'#00aaff', borderWidth:2, pointRadius:0, fill:false, tension:0.3 },
    { label:'Signal', data:[], borderColor:'#ff8800', borderWidth:1, pointRadius:0, fill:false, tension:0.3 },
  ]},
  options: { ...CHART_DEFAULTS,
    plugins:{ legend:{ display:true, labels:{ color:'#6070a0', font:{family:'Share Tech Mono',size:9}, boxWidth:20 }}},
    scales:{ x:{ grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},maxTicksLimit:10} },
             y:{ position:'right', grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8}} }}
  }
});

// -- MACD Histogram --
const _mh=document.getElementById('macdHistChart'); const macdHistCtx=_mh?_mh.getContext('2d'):null;
let macdHistChart = null; if(macdHistCtx) macdHistChart = new Chart(macdHistCtx, {
  type: 'bar',
  data: { labels:[], datasets:[{ label:'Histogram', data:[], backgroundColor:[], borderWidth:0, borderRadius:1 }]},
  options: { responsive:true, maintainAspectRatio:false, plugins:{legend:{display:false}},
    scales:{ x:{ display:false },
             y:{ position:'right', grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8}} }}
  }
});

// -- Volume Bars Chart --
const _vb=document.getElementById('volBarsChart'); const volBarsCtx=_vb?_vb.getContext('2d'):null;
let volBarsChart = null; if(volBarsCtx) volBarsChart = new Chart(volBarsCtx, {
  type: 'bar',
  data: { labels:[], datasets:[{ label:'Volume', data:[], backgroundColor:[], borderWidth:0, borderRadius:1 }]},
  options: { responsive:true, maintainAspectRatio:false, plugins:{legend:{display:false}},
    scales:{ x:{ grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},maxTicksLimit:12} },
             y:{ position:'right', grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8},
               callback:v => v>=1e6?(v/1e6).toFixed(0)+'M':v>=1e3?(v/1e3).toFixed(0)+'K':v }}
    }
  }
});

// -- POC Profile Chart (dedicated panel) --
const _poc2=document.getElementById('pocProfileChart'); const pocProfileCtx=_poc2?_poc2.getContext('2d'):null;
let pocProfileChart = null; if(pocProfileCtx) pocProfileChart = new Chart(pocProfileCtx, {
  type: 'bar',
  data: { labels:[], datasets:[{ label:'Vol @ Price', data:[], backgroundColor:[], borderWidth:0, borderRadius:2 }]},
  options: { responsive:true, maintainAspectRatio:false, indexAxis:'y',
    plugins:{ legend:{display:false}, tooltip:{ callbacks:{ label: ctx=>'Vol: '+(ctx.parsed.x/1e6).toFixed(1)+'M' }}},
    scales:{ x:{ grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:7},
               callback:v => (v/1e6).toFixed(0)+'M'} },
             y:{ grid:{display:false}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:8}} }}
  }
});

// -- Volume Profile (horizontal bar - price vs volume) --
const _vp=document.getElementById('volProfileChart'); const volProfileCtx=_vp?_vp.getContext('2d'):null;
let volProfileChart = null; if(volProfileCtx) volProfileChart = new Chart(volProfileCtx, {
  type: 'bar',
  data: { labels:[], datasets:[
    { label:'Vol @ Price', data:[], backgroundColor:[], borderWidth:0, borderRadius:1 }
  ]},
  options: { responsive:true, maintainAspectRatio:false, indexAxis:'y',
    plugins:{
      legend:{display:false},
      tooltip:{ callbacks:{ label: ctx=>'Vol: '+(ctx.parsed.x/1e6).toFixed(1)+'M' }},
      annotation:{ annotations:{} }
    },
    scales:{
      x:{ grid:{color:'#1e2540'}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:7},
             callback:v => (v/1e6).toFixed(0)+'M'} },
      y:{ grid:{display:false}, ticks:{color:'#4a5280',font:{family:'Share Tech Mono',size:7}} }
    }
  }
});

// -- Chart Tab Switcher --

function showChartTab(tab) {
  const allTabs = ['price','ichimoku','hmm','macd','volume'];
  allTabs.forEach(t => {
    const chartId = 'chart' + t.charAt(0).toUpperCase() + t.slice(1);
    const el = document.getElementById(chartId);
    if(el) el.style.display = t===tab ? 'flex' : 'none';
    const btn = document.getElementById('tab' + t.charAt(0).toUpperCase() + t.slice(1));
    if(btn) {
      btn.style.borderBottomColor = t===tab ? 'var(--green)' : 'transparent';
      btn.style.color = t===tab ? 'var(--green)' : 'var(--text-dim)';
    }
  });
}

function setText(id,v){const e=document.getElementById(id);if(e)e.textContent=v;}

function setDot(id,k){const e=document.getElementById(id);if(e)e.className='ind-dot dot-'+k.slice(0,4);}

function colorClass(s){return s==='BUY'?'bullish':s==='SELL'?'bearish':'neutral';}

function badgeClass(a){return a.includes('RECENT')?'badge-recent':a.includes('QUARTERLY')?'badge-quarter':'badge-old';}

function regimeDot(r){return r==='BULLISH'?'bull':r==='BEARISH'?'bear':'neut';}


// ---------------------------------------------------------------
//  updateChartAnnotations(s)
//  Draws every buy/sell/tranche/support/resistance/stop level
//  directly onto the TSLA price chart as labelled horizontal lines.
//
//  Lines drawn:
//    - BUY TRANCHES    - T1/T2/T3 entry prices (solid green)
//    - SELL TRANCHES   - T1/T2/T3 exit prices  (solid red/orange/gold)
//    - HARD STOP       - invalidation / stop loss (dashed red)
//    - RESISTANCE      - historical ceiling levels (dashed orange)
//    - SUPPORT         - historical floor levels   (dashed green dim)
//    - MAX PAIN        - options max pain level    (dashed purple)
// ---------------------------------------------------------------

function updateChartAnnotations(s) {
  if(!chart?.options?.plugins?.annotation) return;

  const annotations = {};
  let idx = 0;
  const price = s.price || 0;

  // Helper: make a horizontal annotation line + label
  function hLine(key, yVal, color, label, dash, labelPos, labelBg) {
    if(!yVal || isNaN(yVal)) return;
    annotations[key] = {
      type:        'line',
      yMin:        yVal,
      yMax:        yVal,
      borderColor: color,
      borderWidth: dash ? 1.5 : 2,
      borderDash:  dash ? [5,4] : [],
      label: {
        display:         true,
        content:         label,
        position:        labelPos || 'start',
        backgroundColor: labelBg  || color + '22',
        color:           color,
        font:            { family:'Share Tech Mono', size:9, weight:'bold' },
        padding:         { x:6, y:3 },
        borderRadius:    2,
        xAdjust:         6,
      }
    };
  }

  // -- - BUY ENTRY TRANCHES --
  const en = s.entry_data || {};
  const tp = en.tranche_plan || [];
  const entryColors = ['#00ff88','#69f0ae','#b9f6ca'];
  tp.forEach((t,i) => {
    if(t.price) hLine(
      `buyT${i+1}`, t.price,
      entryColors[i] || '#00ff88',
      `- BUY T${i+1} ${t.pct_cap}% @ $${t.price}`,
      false, 'start', '#00ff8811'
    );
  });

  // Entry invalidation (hard stop for longs)
  if(en.invalidation) hLine(
    'entryStop', en.invalidation,
    '#ff1744',
    `- Invalidation $${en.invalidation}`,
    true, 'end', '#ff174411'
  );

  // -- - SELL EXIT TRANCHES --
  const ex = s.exit_data?.exit_analysis || {};
  const st = ex.sell_tranches || [];
  const sellColors = ['#ffd600','#ff6d00','#ff1744'];
  st.forEach((t,i) => {
    if(t.price) hLine(
      `sellT${i+1}`, t.price,
      sellColors[i] || '#ff6d00',
      `- SELL T${i+1} ${t.pct_holding}% @ $${t.price} (+${t.gain_pct}%)`,
      false, 'end', sellColors[i]+'11'
    );
    // Trailing stop for each tranche (dashed)
    if(t.trailing_stop && t.trailing_stop < price) hLine(
      `trailStop${i+1}`, t.trailing_stop,
      '#ff174488',
      `trail $${t.trailing_stop}`,
      true, 'end', '#00000000'
    );
  });

  // Hard stop loss
  if(ex.stop_loss) hLine(
    'hardStop', ex.stop_loss,
    '#ff1744',
    `- Stop $${ex.stop_loss}`,
    true, 'start', '#ff174411'
  );

  // -- - RESISTANCE LEVELS (top 3 above price) --
  const resAbove = (ex.resistance_above || s.exit_data?.resistance?.levels_above || []).slice(0,3);
  resAbove.forEach((r,i) => {
    hLine(
      `res${i}`, r,
      i === 0 ? '#ff9800' : '#ff980055',
      i === 0 ? `- Resistance $${r}` : `$${r}`,
      true, 'end', '#ff980008'
    );
  });

  // -- - SUPPORT LEVELS (nearest 2 below price) --
  const supBelow = (en.support_levels || []).slice(-2);
  supBelow.forEach((s2,i) => {
    hLine(
      `sup${i}`, s2,
      '#00ff8844',
      `- Support $${s2}`,
      true, 'start', '#00ff8808'
    );
  });

  // -- - MAX PAIN --
  const maxPain = s.mm_data?.max_pain;
  if(maxPain) hLine(
    'maxPain', maxPain,
    '#ce93d8',
    `- Max Pain $${maxPain}`,
    true, 'end', '#ce93d811'
  );

  // -- Current price marker (always visible) --
  if(price) hLine(
    'currentPrice', price,
    'rgba(255,255,255,0.3)',
    `NOW $${price.toFixed(2)}`,
    true, 'start', '#00000000'
  );

  // Apply to chart
  chart.options.plugins.annotation.annotations = annotations;
  chart.update('none');
}

// ---------------------------------------------------------------
//  updateTickerBar(s)
//  Updates the sticky top ticker with live buy/sell signal status,
//  tranche prices, entry score, peak score - all at a glance
// ---------------------------------------------------------------

function updateTickerBar(s) {
  try {
  var price  = s.price  || 0;
  var signal = s.signal || 'HOLD';
  var en     = s.entry_data || {};
  var pk     = s.peak_data  || {};
  var exA    = (s.exit_data && s.exit_data.exit_analysis) ? s.exit_data.exit_analysis : {};
  var sz     = s.sizing || {};

  // Price + signal
  var tpEl = document.getElementById('tickerPrice');
  if(tpEl) tpEl.textContent = price ? '$'+price.toLocaleString('en-US',{minimumFractionDigits:2,maximumFractionDigits:2}) : '-';

  var tsEl = document.getElementById('tickerSignal');
  if(tsEl) {
    var sigColors = {BUY:'#00ff88',SELL:'#ff3355',HOLD:'#ffb300'};
    tsEl.textContent  = signal;
    tsEl.style.color  = sigColors[signal]||'#ffb300';
    tsEl.style.border = '1px solid '+(sigColors[signal]||'#ffb300');
  }

  var items = [];

  // Entry signals
  if((en.entry_score||0) >= 25) {
    var ce = (en.entry_score||0)>=65?'#00ff88':(en.entry_score||0)>=45?'#69f0ae':'#ffd600';
    items.push('<span style="color:'+ce+';margin-right:32px;">- ENTRY '+(en.entry_urgency||'')+' - Score '+(en.entry_score||0)+'/100 - Deploy '+(en.total_deploy_pct||0)+'%</span>');
    (en.tranche_plan||[]).forEach(function(t){
      items.push('<span style="color:'+ce+';margin-right:32px;">T'+t.number+' BUY '+t.pct_cap+'% @ $'+t.price+' ('+t.shares+' shares)</span>');
    });
  }

  // Peak signals
  if((pk.peak_score||0) >= 25) {
    var cp = (pk.peak_score||0)>=65?'#ff1744':(pk.peak_score||0)>=45?'#ff6d00':'#ffd600';
    items.push('<span style="color:'+cp+';margin-right:32px;">- PEAK '+(pk.peak_urgency||'')+' - Score '+(pk.peak_score||0)+'/100</span>');
    (exA.sell_tranches||[]).forEach(function(t){
      items.push('<span style="color:'+cp+';margin-right:32px;">T'+t.number+' SELL '+t.pct_holding+'% @ $'+t.price+' (+'+t.gain_pct+'%)</span>');
    });
  }

  // Exit score
  if((exA.exit_score||0) >= 25) {
    items.push('<span style="color:#ff6d00;margin-right:32px;">- EXIT '+(exA.urgency||'')+' - Score '+(exA.exit_score||0)+'/100 - Stop $'+(exA.stop_loss||'-')+'</span>');
  }

  // CTA sizing
  if(sz.sizing_signal && sz.sizing_signal !== 'HOLD') {
    items.push('<span style="color:#40c4ff;margin-right:32px;">- CTA '+sz.sizing_signal+' - '+(sz.final_exposure_pct||0)+'% of capital - '+(sz.share_count||0)+' shares</span>');
  }

  // UOA flow
  var uoa = s.uoa_data || {};
  if((uoa.whale_alerts||[]).length > 0) {
    var wdir = uoa.net_flow || 'NEUTRAL';
    var wc2  = (uoa.whale_alerts||[]).length;
    items.push('<span style="color:#b388ff;margin-right:32px;">- '+wc2+' WHALE TRADE'+(wc2>1?'S':'')+' - '+wdir+' FLOW - '+(uoa.total_unusual||0)+' unusual strikes</span>');
  }

  // Max pain + VIX
  var spyd = s.spy_data || {};
  var vix  = spyd.vix;
  if(vix) items.push('<span style="color:#b388ff;margin-right:32px;">VIX '+vix+' - '+(spyd.vix_regime||'')+'</span>');
  var mmd = s.mm_data || {};
  var mp  = mmd.max_pain;
  if(mp) items.push('<span style="color:#ce93d8;margin-right:32px;">- Max Pain $'+mp+'</span>');

  if(items.length === 0) {
    items.push('<span style="color:var(--text-dim);margin-right:32px;">No active buy or sell signals - monitoring all indicators</span>');
  }

  var tc = document.getElementById('tickerContent');
  if(tc) tc.innerHTML = items.join('<span style="color:var(--border);margin-right:32px;">|</span>');
  } catch(e) { console.warn('tickerBar: '+e.message); }
}

function updateUI(s) {
  // -- Signal Badge --
  var badge=document.getElementById('signalBadge');
  if(badge){badge.textContent=s.signal||'--';badge.className='signal-badge '+(s.signal||'');}
  var _pv=document.getElementById('priceVal');if(_pv)_pv.textContent=s.price?'$'+s.price.toLocaleString('en-US',{minimumFractionDigits:2}):'-';
  var pct=s.signal_strength||0;
  var fill=document.getElementById('strengthFill');
  if(fill){fill.style.width=pct+'%';fill.style.background=s.signal==='BUY'?'#00ff88':s.signal==='SELL'?'#ff3355':'#ffb300';}
  var _sv=document.getElementById('strengthVal');if(_sv)_sv.textContent=pct;
  // WhatsApp status badge
  const waEl = document.getElementById('waStatus');
  if(waEl) {
    if(s.wa_enabled) {
      waEl.textContent = '- WhatsApp ACTIVE - (---' + (s.wa_phone_tail||'') + ')';
      waEl.style.color = 'var(--accent-green)';
      waEl.style.borderColor = 'var(--accent-green)';
    } else {
      waEl.textContent = '- WhatsApp: set GREEN_INSTANCE + GREEN_TOKEN + GREEN_PHONE in Railway - Variables';
      waEl.style.color = '#ff6d00';
      waEl.style.borderColor = '#ff6d00';
    }
  }

  // -- Classic Indicators --
  const ind = s.indicators||{};
  setText('ind-rsi', ind.rsi??'-'); setDot('dot-rsi', ind.rsi<30?'bull':ind.rsi>70?'bear':'neut');
  setText('ind-macd', ind.macd??'-');
  setText('ind-macd-sig', ind.macd_signal??'-');
  setText('ind-macd-hist', ind.macd_hist??'-'); setDot('dot-macd-hist', ind.macd_hist>0?'bull':ind.macd_hist<0?'bear':'neut');
  setText('ind-ema50', ind.ema50??'-'); setText('ind-ema200', ind.ema200??'-');
  const cross = ind.ema50>ind.ema200?'bull':'bear';
  setDot('dot-ema50',cross); setDot('dot-ema200',cross);
  setText('ind-bb-upper', ind.bb_upper??'-'); setText('ind-bb-mid', ind.bb_mid??'-'); setText('ind-bb-lower', ind.bb_lower??'-');
  setText('ind-vol', ind.volume_ratio??'-'); setDot('dot-vol', ind.volume_ratio>1.5?'bull':ind.volume_ratio<0.7?'bear':'neut');

  // -- Ichimoku Indicators --
  const ichi = s.ichimoku||{};
  setText('ind-tenkan', ichi.tenkan??'-');
  setText('ind-kijun',  ichi.kijun??'-');
  setText('ind-span-a', ichi.span_a??'-');
  setText('ind-span-b', ichi.span_b??'-');
  const cs = ichi.cloud_signal||'NEUTRAL';
  setText('ind-cloud', cs + (ichi.cloud_details&&ichi.cloud_details.length ? ' - '+ichi.cloud_details[0] : ''));
  setDot('dot-cloud', cs==='BULLISH'?'bull':cs==='BEARISH'?'bear':'neut');
  setDot('dot-tenkan', ichi.tenkan>ichi.kijun?'bull':'bear');
  setDot('dot-kijun', ichi.tenkan>ichi.kijun?'bull':'bear');

  // -- HMM Indicators --
  const hmm = s.hmm||{};
  setText('ind-hmm-regime', (hmm.regime||'-') + ' (' + (hmm.confidence||0) + '%)');
  setDot('dot-hmm', regimeDot(hmm.regime||''));
  setText('ind-hmm-conf', hmm.confidence ? hmm.confidence+'% certainty' : '-');
  setText('ind-hmm-next', hmm.next_regime ? hmm.next_regime+' ('+hmm.next_prob+'% prob)' : '-');

  // -- Price Chart + Annotations --
  if(s.price_history&&s.price_history.length&&chart){try{chart.data.labels=s.price_history.map(p=>p.date.slice(5));chart.data.datasets[0].data=s.price_history.map(p=>p.price);updateChartAnnotations(s);chart.update('none');}catch(e){console.warn('priceChart:'+e.message);}}

  // -- Live Ticker Bar --
  updateTickerBar(s);

  // -- MACD Charts --
  if(s.macd_history&&s.macd_history.length&&macdLineChart&&macdHistChart){try{var mh=s.macd_history;macdLineChart.data.labels=mh.map(m=>m.date.slice(5));macdLineChart.data.datasets[0].data=mh.map(m=>m.macd);macdLineChart.data.datasets[1].data=mh.map(m=>m.signal);macdLineChart.update('none');macdHistChart.data.labels=mh.map(m=>m.date.slice(5));macdHistChart.data.datasets[0].data=mh.map(m=>m.hist);macdHistChart.data.datasets[0].backgroundColor=mh.map(m=>m.color+'cc');macdHistChart.update('none');}catch(e){console.warn('macdCharts:'+e.message);}}

  // -- Volume Charts --
  if(s.vol_history&&s.vol_history.length&&volBarsChart) {
    var vh = s.vol_history;
    volBarsChart.data.labels = vh.map(function(v){return v.date.slice(5);});
    volBarsChart.data.datasets[0].data = vh.map(function(v){return v.volume;});
    volBarsChart.data.datasets[0].backgroundColor = vh.map(function(v){return v.color+'99';});
    volBarsChart.update('none');
  }
  if(s.vol_profile&&s.vol_profile.length&&volProfileChart) {
    var vp  = s.vol_profile;
    var poc = s.poc_data || {};
    var pocPrice = poc.poc  || 0;
    var vahPrice = poc.vah  || 0;
    var valPrice = poc.val  || 0;
    var curPrice = s.price  || 0;

    volProfileChart.data.labels = vp.map(function(v){ return '$'+v.price_mid; });
    volProfileChart.data.datasets[0].data   = vp.map(function(v){ return v.volume; });

    // Color coding: POC=gold, VAH/VAL zone=teal, above POC=green tint, below=red tint
    volProfileChart.data.datasets[0].backgroundColor = vp.map(function(v) {
      var p = v.price_mid;
      if(Math.abs(p - pocPrice) < 0.6)   return '#c9a84c';           // POC — gold
      if(p >= valPrice && p <= vahPrice)  return 'rgba(0,229,255,0.45)'; // Value Area — teal
      if(p > pocPrice)                    return 'rgba(0,255,136,0.3)'; // above POC — green
      return 'rgba(255,51,85,0.3)';                                    // below POC — red
    });

    // Add POC/VAH/VAL horizontal lines via annotation plugin
    if(volProfileChart.options.plugins && volProfileChart.options.plugins.annotation) {
      var labels = volProfileChart.data.labels;
      function labelIdx(price) {
        var target = '$'+price;
        var closest = 0; var minDist = 9999;
        labels.forEach(function(l, i) {
          var d = Math.abs(parseFloat(l.replace('$','')) - price);
          if(d < minDist) { minDist=d; closest=i; }
        });
        return closest;
      }
      volProfileChart.options.plugins.annotation.annotations = {
        pocLine: { type:'line', yMin:labelIdx(pocPrice), yMax:labelIdx(pocPrice),
          borderColor:'#c9a84c', borderWidth:2, borderDash:[],
          label:{ display:true, content:'POC $'+pocPrice, color:'#c9a84c',
                  font:{family:'Share Tech Mono',size:8}, position:'end',
                  backgroundColor:'rgba(0,0,0,0.7)', padding:{x:4,y:2} }},
        vahLine: { type:'line', yMin:labelIdx(vahPrice), yMax:labelIdx(vahPrice),
          borderColor:'rgba(0,229,255,0.8)', borderWidth:1, borderDash:[4,3],
          label:{ display:true, content:'VAH $'+vahPrice, color:'#00e5ff',
                  font:{family:'Share Tech Mono',size:8}, position:'end',
                  backgroundColor:'rgba(0,0,0,0.7)', padding:{x:4,y:2} }},
        valLine: { type:'line', yMin:labelIdx(valPrice), yMax:labelIdx(valPrice),
          borderColor:'rgba(0,229,255,0.8)', borderWidth:1, borderDash:[4,3],
          label:{ display:true, content:'VAL $'+valPrice, color:'#00e5ff',
                  font:{family:'Share Tech Mono',size:8}, position:'end',
                  backgroundColor:'rgba(0,0,0,0.7)', padding:{x:4,y:2} }},
        curLine: { type:'line', yMin:labelIdx(curPrice), yMax:labelIdx(curPrice),
          borderColor:'rgba(255,255,255,0.5)', borderWidth:1, borderDash:[2,3],
          label:{ display:true, content:'NOW $'+curPrice, color:'#fff',
                  font:{family:'Share Tech Mono',size:8}, position:'start',
                  backgroundColor:'rgba(0,0,0,0.7)', padding:{x:4,y:2} }},
      };
    }
    volProfileChart.update('none');

    // Update POC stats display
    renderPOCStats(poc, s.price||0);
  }

  // -- Volume indicators --
  const ind2 = s.indicators||{};
  setText('ind-vol', ind2.volume_ratio ? ind2.volume_ratio+'x avg' : '-');
  setDot('dot-vol', ind2.volume_ratio>1.5?'bull':ind2.volume_ratio<0.7?'bear':'neut');

  // -- Signal Reasons --
  var reasonsEl = document.getElementById('signalReasons');
  if(reasonsEl && s.signal_reasons && s.signal_reasons.length) {
    reasonsEl.innerHTML = s.signal_reasons.slice(0,5).map(function(r){
      return '<span style="font-family:var(--font-mono);font-size:10px;color:var(--text-dim);background:var(--bg2);border:1px solid var(--border);padding:3px 10px;border-radius:2px;white-space:nowrap;">'+r+'</span>';
    }).join('');
  }

  // -- Ichimoku Cloud Chart --
  if(typeof ichimokuChart!=='undefined' && ichimokuChart && ichi.history && ichi.history.length) {
    try {
      var ih = ichi.history;
      ichimokuChart.data.labels = ih.map(p=>p.date.slice(5));
      ichimokuChart.data.datasets[0].data = ih.map(p=>p.close);
      ichimokuChart.data.datasets[1].data = ih.map(p=>p.tenkan);
      ichimokuChart.data.datasets[2].data = ih.map(p=>p.kijun);
      ichimokuChart.data.datasets[3].data = ih.map(p=>p.span_a);
      ichimokuChart.data.datasets[4].data = ih.map(p=>p.span_b);
      ichimokuChart.update('none');
    } catch(e) { console.warn('ichimokuChart:', e.message); }
  }

  // -- HMM Regime Chart --
  if(typeof hmmChart!=='undefined' && hmmChart && hmm.history && hmm.history.length) {
    try {
      var hh = hmm.history;
      hmmChart.data.labels = hh.map((h,i)=>i%5===0?i:'');
      hmmChart.data.datasets[0].data = hh.map(h=>h.return);
      hmmChart.data.datasets[0].backgroundColor = hh.map(h=>h.color+'99');
      hmmChart.data.datasets[0].regimes = hh.map(h=>h.state);
      hmmChart.update('none');
    } catch(e) { console.warn('hmmChart:', e.message); }
  }

  // -- Alert Log --
  // -- Alert log with richer display --
  var logEl = document.getElementById('alertLog');
  if(logEl) logEl.innerHTML = (s.alerts_log && s.alerts_log.length)
    ? s.alerts_log.map(function(a) {
        var isSell = (a.signal&&(a.signal.indexOf('EXIT')>=0||a.signal.indexOf('SELL')>=0));
        var isBuy  = a.signal === 'BUY';
        var bdr    = isSell ? '#ff3355' : isBuy ? '#00ff88' : 'var(--gold)';
        return '<div class="alert-item" style="border-left:3px solid '+bdr+';padding-left:10px;margin-bottom:8px;">'
          + '<div style="display:flex;justify-content:space-between;align-items:center;">'
          + '<span style="font-family:var(--font-mono);font-size:12px;color:'+bdr+';font-weight:700;">'+a.signal+' @ $'+a.price+'</span>'
          + '<span style="font-size:9px;color:var(--text-dim);">'+a.time+'</span>'
          + '</div>'
          + '<div style="font-size:10px;color:var(--text-dim);margin-top:3px;">'+a.reason+'</div>'
          + '<div style="display:flex;gap:8px;margin-top:4px;flex-wrap:wrap;">'
          + '<span style="font-size:9px;font-family:var(--font-mono);color:var(--gold);">Strength: '+a.strength+'/100</span>'
          + (a.gex ? '<span style="font-size:9px;font-family:var(--font-mono);color:#b388ff;">GEX: '+a.gex+'</span>' : '')
          + (a.max_pain ? '<span style="font-size:9px;font-family:var(--font-mono);color:var(--gold);">MaxPain: $'+a.max_pain+'</span>' : '')
          + (a.hmm ? '<span style="font-size:9px;font-family:var(--font-mono);color:var(--text-dim);">HMM: '+a.hmm+'</span>' : '')
          + '</div></div>';
      }).join('')
    : '<div class="no-alerts">Monitoring... no signals yet.</div>';

  // -- Last alert ticker in header --
  if(s.alerts_log && s.alerts_log.length) {
    var last = s.alerts_log[0];
    var tickerEl = document.getElementById('lastAlertTicker');
    if(tickerEl) tickerEl.textContent = last.signal+' @ $'+last.price+' - '+(last.reason?last.reason.slice(0,50):'');
  }

  // -- Institutional --
  var instListEl = document.getElementById('instList');
  if(instListEl) instListEl.innerHTML = (s.institutional && s.institutional.length)
    ? s.institutional.map(function(i){return '<div class="inst-item"><div class="inst-name">'+i.institution+'</div><div class="inst-meta">Form '+i.form+' - Filed '+i.date+'</div><span class="inst-badge '+badgeClass(i.action)+'">'+i.action+'</span></div>';}).join('')
    : '<div class="no-alerts">Loading 13F data...</div>';

  var luEl = document.getElementById('lastUpdated'); if(luEl) luEl.textContent = s.last_updated ? 'Updated '+s.last_updated : '-';

  [
    function(){renderExitPanel(s.exit_data||{});},
    function(){renderUOAPanel(s.uoa_data||{});},
    function(){var pv=parseFloat((document.getElementById('portfolioInput')||{}).value||'100000')||100000;renderEntryPanel(s.entry_data||{},pv);},
    function(){renderPeakPanel(s.peak_data||{});},
    function(){renderCTAPanel(s.sizing||{},s.price||0);},
    function(){renderExtPanel(s.ext_data||{});},
    function(){updateAlgoRadar(s);},
    function(){renderNewsPanel(s.news_data||{});},
    function(){renderSPYPanel(s.spy_data||{});},
    function(){renderMMPanel(s.mm_data||{},s.dark_pool||{},s.price||0);},
    function(){renderInstModels(s.institutional_models||{},s.indicators||{});},
    function(){if(s.darthvader)renderDarthVader(s.darthvader);},
    function(){window._lastState=s;renderSpockPanel(s.master_signal||{});renderMLPanel(s.ml_signal||{});},
    function(){try{renderCapBounce(s.capitulation||null);}catch(e){}},
    function(){try{renderPOCPanel(s.poc_data||{},s.vol_profile||[],s.price||0);}catch(e){}},
  ].forEach(function(fn,i){try{fn();}catch(e){console.warn('Panel['+i+']: '+e.message);}});
}



function renderCapBounce(cap) {
  var banner=document.getElementById('capBounceAlert');
  if(!banner)return;
  if(!cap||!cap.detected){banner.style.display='none';return;}
  banner.style.display='block';
  var phaseColors={CONFIRMED:'#00ff88',BOUNCING:'#00e5ff',EXHAUSTING:'#ffb300',DROPPING:'#ff3355'};
  var phaseEl=document.getElementById('capPhase');
  if(phaseEl){phaseEl.textContent=cap.phase||'?';phaseEl.style.color=phaseColors[cap.phase]||'#00ff88';}
  var convEl=document.getElementById('capConviction');
  if(convEl)convEl.textContent='Conviction: '+(cap.conviction||0)+'/100';
  var dropEl=document.getElementById('capDropLine');
  if(dropEl)dropEl.textContent='$'+cap.session_high+' to $'+cap.session_low+' ('+cap.drop_from_high_pct+'%)';
  var recEl=document.getElementById('capRecovery');
  if(recEl)recEl.textContent='Recovery: '+(cap.recovery_pct||0)+'% off low';
  var eEl=document.getElementById('capEntry');if(eEl)eEl.textContent='$'+cap.entry_zone_low+' - $'+cap.entry_zone_high;
  var stEl=document.getElementById('capStop');if(stEl)stEl.textContent='$'+cap.stop_loss;
  var t1El=document.getElementById('capT1');if(t1El)t1El.textContent='$'+cap.t1;
  var t2El=document.getElementById('capT2');if(t2El)t2El.textContent='$'+cap.t2;
  var t3El=document.getElementById('capT3');if(t3El)t3El.textContent='$'+cap.t3;
  function setPill(id,active,label){
    var el=document.getElementById(id);if(!el)return;
    if(active){el.textContent=label+' OK';el.style.background='rgba(0,255,136,0.15)';el.style.borderColor='rgba(0,255,136,0.5)';el.style.color='#00ff88';}
    else{el.textContent=label;el.style.background='rgba(255,255,255,0.05)';el.style.borderColor='rgba(255,255,255,0.1)';el.style.color='var(--text-dim)';}
  }
  setPill('capOFI',cap.ofi_flip,'OFI');setPill('capVolX',cap.vol_exhaustion,'VOL EX');
  setPill('capVWAP',cap.vwap_reclaim,'VWAP');setPill('capSupp',cap.support_bounce,'SUPPORT');
  var dEl=document.getElementById('capDaily');
  if(dEl){
    if(cap.daily_trend_intact){dEl.textContent='DAILY TREND OK';dEl.style.background='rgba(0,255,136,0.12)';dEl.style.borderColor='rgba(0,255,136,0.4)';dEl.style.color='#00ff88';}
    else{dEl.textContent='DAILY TREND WARN';dEl.style.background='rgba(255,51,85,0.12)';dEl.style.borderColor='rgba(255,51,85,0.4)';dEl.style.color='#ff3355';}
  }
  var rEl=document.getElementById('capReasons');
  if(rEl){var rs=cap.reasons||[];rEl.innerHTML=rs.slice(0,4).map(function(r){return '<div style="font-size:9px;color:var(--text-primary);padding:2px 0;">- '+r+'</div>';}).join('');}
}

function renderUOAPanel(uoa) {
  if(!uoa) return;
  try {
  var G='#00ff88', R='#ff3355', P='#b388ff', GO='var(--gold)';
  var fmt$ = function(v) {
    if(!v && v!==0) return '-';
    if(Math.abs(v)>=1e6) return '$'+(v/1e6).toFixed(2)+'M';
    if(Math.abs(v)>=1e3) return '$'+(v/1e3).toFixed(0)+'K';
    return '$'+v;
  };
  var sevColor = {EXTREME:'#ff1744',WHALE:'#ff1744','VERY HIGH':'#ff6d00',HIGH:GO,LARGE:'#ff6d00'};

  var flowEl=document.getElementById('uoaFlow');
  if(flowEl){flowEl.textContent=uoa.net_flow||'-';flowEl.style.color=uoa.flow_color||P;}
  var sigEl=document.getElementById('uoaSignal');
  if(sigEl) sigEl.textContent=uoa.uoa_signal||'-';
  var fc=document.getElementById('uoaFlowCard');
  if(fc) fc.style.borderColor=uoa.flow_color||'rgba(180,100,255,0.4)';

  var callPct=uoa.call_put_premium_ratio||50;
  var putPct=100-callPct;
  var cpEl=document.getElementById('uoaCallPct');
  var ppEl=document.getElementById('uoaPutPct');
  if(cpEl){cpEl.textContent=callPct.toFixed(1)+'%';cpEl.style.color=callPct>55?G:callPct<45?'var(--text-dim)':G;}
  if(ppEl){ppEl.textContent=putPct.toFixed(1)+'%';ppEl.style.color=putPct>55?R:putPct<45?'var(--text-dim)':R;}
  var fb=document.getElementById('uoaFlowBar');
  if(fb){fb.style.width=callPct+'%';fb.style.background=callPct>55?G:callPct<45?R:'var(--gold)';}

  var wc=document.getElementById('uoaWhaleCount');
  if(wc){wc.textContent=(uoa.whale_alerts||[]).length;wc.style.color=(uoa.whale_alerts||[]).length>=2?'#ff6d00':P;}
  var uc=document.getElementById('uoaUnusualCount');
  if(uc){uc.textContent=uoa.total_unusual||0;uc.style.color=(uoa.total_unusual||0)>=5?'#ff6d00':GO;}

  var cpremEl=document.getElementById('uoaCallPrem');
  if(cpremEl) cpremEl.textContent=fmt$(uoa.total_call_premium);
  var ppremEl=document.getElementById('uoaPutPrem');
  if(ppremEl) ppremEl.textContent=fmt$(uoa.total_put_premium);

  var wlEl=document.getElementById('uoaWhaleList');
  if(wlEl) {
    var whales=uoa.whale_alerts||[];
    if(whales.length) {
      wlEl.innerHTML=whales.map(function(w){
        var c2=w.type==='CALL'?G:R;
        var sc=sevColor[w.severity]||GO;
        return '<div style="background:var(--bg2);border:1px solid '+c2+'25;border-left:3px solid '+c2+';padding:8px 10px;border-radius:1px;">'
          +'<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:4px;">'
          +'<span style="font-family:var(--font-mono);font-size:11px;font-weight:700;color:'+c2+';">'+w.type+' $'+w.strike+'</span>'
          +'<span style="font-family:var(--font-mono);font-size:13px;font-weight:700;color:'+sc+';">'+w.premium_fmt+'</span>'
          +'</div>'
          +'<div style="display:flex;gap:8px;flex-wrap:wrap;font-size:8px;color:var(--text-dim);">'
          +'<span>Exp: <strong style="color:var(--text-primary);">'+w.expiry+'</strong> ('+w.dte+'DTE)</span>'
          +'<span>Vol: <strong style="color:'+c2+';">'+w.volume.toLocaleString()+'</strong></span>'
          +'<span>OI: '+w.oi.toLocaleString()+'</span>'
          +'<span>Vol/OI: <strong style="color:'+sc+';">'+w.vol_oi+'x</strong></span>'
          +'<span>IV: '+w.iv+'%</span>'
          +'<span style="border:1px solid '+c2+';padding:1px 5px;border-radius:1px;">'+w.moneyness+'</span>'
          +'<span style="border:1px solid '+sc+';color:'+sc+';padding:1px 5px;border-radius:1px;">'+w.severity+'</span>'
          +'</div></div>';
      }).join('');
    } else {
      wlEl.innerHTML='<div style="font-size:10px;color:var(--text-dim);">No whale trades detected this cycle</div>';
    }
  }

  function renderUnusualList(elId, items, typeColor) {
    var el=document.getElementById(elId);
    if(!el) return;
    if(items.length) {
      el.innerHTML=items.map(function(u){
        return '<div style="background:var(--bg2);border-left:2px solid '+typeColor+';padding:6px 8px;border-radius:1px;">'
          +'<div style="display:flex;justify-content:space-between;margin-bottom:2px;">'
          +'<span style="font-family:var(--font-mono);font-size:10px;font-weight:700;color:'+typeColor+';">$'+u.strike+' <span style="font-size:8px;">'+u.expiry+'</span></span>'
          +'<span style="font-family:var(--font-mono);font-size:10px;color:'+(sevColor[u.severity]||GO)+';">'+u.vol_oi+'x Vol/OI</span>'
          +'</div>'
          +'<div style="display:flex;gap:6px;font-size:8px;color:var(--text-dim);">'
          +'<span>Vol: <strong style="color:'+typeColor+';">'+u.volume.toLocaleString()+'</strong></span>'
          +'<span>OI: '+u.oi.toLocaleString()+'</span>'
          +'<span>Prem: <strong style="color:'+(sevColor[u.severity]||GO)+';">'+u.premium_fmt+'</strong></span>'
          +'<span style="border:1px solid '+typeColor+'33;padding:0 4px;">'+u.moneyness+'</span>'
          +'<span style="color:'+(sevColor[u.severity]||GO)+';">'+u.severity+'</span>'
          +'</div></div>';
      }).join('');
    } else {
      el.innerHTML='<div style="font-size:10px;color:var(--text-dim);">No unusual activity</div>';
    }
  }
  renderUnusualList('uoaCallList', uoa.unusual_calls||[], G);
  renderUnusualList('uoaPutList',  uoa.unusual_puts||[], R);

  var rEl=document.getElementById('uoaReasons');
  if(rEl) {
    var reasons=uoa.uoa_reasons||[];
    if(reasons.length) {
      rEl.innerHTML=reasons.map(function(r){
        return '<div style="font-size:10px;color:var(--text-primary);padding:6px 8px;background:rgba(180,100,255,0.08);border-left:2px solid '+P+';border-radius:1px;">'+r+'</div>';
      }).join('');
    } else {
      rEl.innerHTML='<div style="font-size:10px;color:var(--text-dim);">No notable flow signals this cycle</div>';
    }
  }

  if(uoa.strike_heatmap && uoa.strike_heatmap.length && uoaHeatChart) {
    var hm=uoa.strike_heatmap;
    uoaHeatChart.data.labels=hm.map(function(h){return '$'+h.strike;});
    uoaHeatChart.data.datasets[0].data=hm.map(function(h){return Math.round(h.call_premium/1000);});
    uoaHeatChart.data.datasets[1].data=hm.map(function(h){return -Math.round(h.put_premium/1000);});
    uoaHeatChart.update('none');
  }
  } catch(e) {
    console.error('[UOA] renderUOAPanel crash:', e.message, e.stack);
    var wl=document.getElementById('uoaWhaleList');
    if(wl) wl.innerHTML='<div style="color:#ff3355;font-size:9px;">Render error: '+e.message+'</div>';
  }
}

function renderEntryPanel(en, portfolioValue) {
  if(!en) return;
  const G = '#00ff88', R = 'var(--accent-red)', GO = 'var(--gold)', B = '#40c4ff';
  const fmt$ = v => v != null ? '$' + Number(v).toLocaleString('en-US',{maximumFractionDigits:0}) : '-';
  const sevColor = {"CRITICAL":G, "HIGH":"#69f0ae", "MEDIUM":GO, "WARNING":GO, "LOW":"var(--text-dim)"};

  // Urgency + score bar
  const urgEl = document.getElementById('entryUrgency');
  if(urgEl) { urgEl.textContent = en.entry_urgency||'- WAIT'; urgEl.style.color = en.entry_color||'var(--text-dim)'; }
  const card = document.getElementById('entryUrgencyCard');
  if(card) card.style.borderColor = en.entry_color || 'rgba(0,255,136,0.3)';
  const bar = document.getElementById('entryScoreBar');
  if(bar) { bar.style.width = Math.min(en.entry_score||0, 100)+'%'; bar.style.background = en.entry_color||G; }
  const sv = document.getElementById('entryScoreVal');
  if(sv) sv.textContent = (en.entry_score||0)+'/100';

  // Deploy %
  const dpEl = document.getElementById('entryDeployPct');
  if(dpEl) {
    const pct = en.total_deploy_pct || 0;
    dpEl.textContent = pct > 0 ? pct+'%' : '-';
    dpEl.style.color = pct >= 40 ? G : pct >= 20 ? GO : 'var(--text-dim)';
  }
  const ddEl = document.getElementById('entryDeployDollar');
  if(ddEl) ddEl.textContent = en.total_deploy_$ > 0 ? fmt$(en.total_deploy_$) + ' of your capital' : 'No entry yet';

  // RSI divergence days
  const ddvEl = document.getElementById('entryDivDays');
  if(ddvEl) {
    ddvEl.textContent = en.divergence_days || 0;
    ddvEl.style.color = (en.divergence_days||0) >= 10 ? G : (en.divergence_days||0) >= 5 ? GO : 'var(--text-dim)';
  }

  // Invalidation
  const invEl = document.getElementById('entryInvalidation');
  if(invEl) invEl.textContent = en.invalidation ? '$'+en.invalidation : '-';

  // Fear gauge
  const fvEl = document.getElementById('entryFearVal');
  const flEl = document.getElementById('entryFearLabel');
  const vix  = en.fear_extreme ? '-35' : '-';
  if(fvEl) {
    fvEl.textContent = en.fear_extreme ? '- EXTREME' : 'Normal';
    fvEl.style.color = en.fear_extreme ? G : 'var(--text-dim)';
  }
  if(flEl) flEl.textContent = en.fear_extreme ? 'Max fear = max opportunity' : 'No fear signal';

  // 3-Tranche plan
  const trEl = document.getElementById('entryTranches');
  if(trEl) {
    const tp = en.tranche_plan || [];
    if(tp.length === 0) {
      trEl.innerHTML = '<div style="grid-column:1/-1;text-align:center;font-size:11px;color:var(--text-dim);padding:20px;">No entry opportunity yet - waiting for setup to develop</div>';
    } else {
      trEl.innerHTML = tp.map(function(t){
        return '<div style="background:var(--bg3);border:2px solid '+t.color+'40;border-top:3px solid '+t.color+';padding:16px;border-radius:2px;">'
          +'<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px;">'
          +'<span style="font-family:var(--font-mono);font-size:10px;font-weight:700;color:'+t.color+';">T'+t.number+' - '+t.label+'</span>'
          +'<span style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:'+t.color+';">'+t.pct_cap+'%</span>'
          +'</div>'
          +'<div style="font-size:9px;color:var(--text-dim);margin-bottom:8px;line-height:1.5;">'+t.trigger+'</div>'
          +'<div style="display:grid;grid-template-columns:1fr 1fr;gap:6px;margin-bottom:8px;">'
          +'<div style="text-align:center;background:var(--bg2);padding:8px;border-radius:2px;">'
          +'<div style="font-size:8px;color:var(--text-dim);">DOLLARS</div>'
          +'<div style="font-family:var(--font-mono);font-size:13px;color:'+t.color+';">'+fmt$(t.dollars)+'</div>'
          +'</div>'
          +'<div style="text-align:center;background:var(--bg2);padding:8px;border-radius:2px;">'
          +'<div style="font-size:8px;color:var(--text-dim);">SHARES</div>'
          +'<div style="font-family:var(--font-mono);font-size:13px;color:'+t.color+';">'+t.shares.toLocaleString()+'</div>'
          +'</div></div>'
          +'<div style="font-size:8px;color:var(--text-dim);line-height:1.5;border-top:1px solid var(--border);padding-top:6px;">'+t.rationale+'</div>'
          +'</div>';
      }).join('');
    }
  }

  // Signal list
  const slEl = document.getElementById('entrySignalList');
  if(slEl) {
    const sigs = en.signals || [];
    slEl.innerHTML = sigs.length
      ? sigs.map(function(s){
          var c = sevColor[s.severity] || GO;
          return '<div style="background:var(--bg2);border:1px solid '+c+'30;border-left:3px solid '+c+';padding:8px 10px;border-radius:1px;">'
            +'<div style="display:flex;justify-content:space-between;margin-bottom:3px;">'
            +'<span style="font-size:10px;font-weight:700;color:'+c+';">'+s.name+'</span>'
            +'<span style="font-family:var(--font-mono);font-size:9px;color:'+c+';">+'+s.score+'</span>'
            +'</div>'
            +'<div style="font-size:8px;color:var(--text-dim);line-height:1.4;">'+s.detail+'</div>'
            +'</div>';
        }).join('')
      : '<div style="font-size:10px;color:var(--text-dim);">No bottom signals yet - price not at a buy zone</div>';
  }

  // Support levels
  const supEl = document.getElementById('entrySupportLevels');
  if(supEl) {
    const lvls = en.support_levels || [];
    supEl.innerHTML = lvls.length
      ? [...lvls].reverse().map(function(v,i){
          var bc = i===0?G:i===1?'#69f0ae':GO;
          var vc = i===0?G:'var(--text-dim)';
          var lbl = i===0?'- nearest support':i===1?'- 2nd support':'- 3rd support';
          return '<div style="display:flex;justify-content:space-between;align-items:center;padding:5px 8px;background:var(--bg2);border-radius:2px;border-left:3px solid '+bc+';">'
            +'<span style="font-family:var(--font-mono);font-size:12px;color:'+vc+';">$'+v+'</span>'
            +'<span style="font-size:8px;color:var(--text-dim);">'+lbl+'</span>'
            +'</div>';
        }).join('')
      : '<div style="font-size:9px;color:var(--text-dim);">Computing support levels...</div>';
  }

  // Fibonacci retracement
  const fibEl = document.getElementById('entryFibLevels');
  if(fibEl && en.fib_retrace) {
    const currentPrice = en.tranche_plan?.[0]?.price || 0;
    fibEl.innerHTML = Object.entries(en.fib_retrace).map(([label, level]) => {
      const near = currentPrice && Math.abs(currentPrice - level) / currentPrice < 0.02;
      const below = currentPrice && level < currentPrice;
      const c = near ? G : below ? '#69f0ae' : 'var(--text-dim)';
      return '<div style="display:flex;justify-content:space-between;font-size:9px;padding:2px 0;">'
        +'<span style="color:'+c+';">'+label+'</span>'
        +'<span style="font-family:var(--font-mono);color:'+c+';">'+(near?'- NEAR ':'')+'$'+level+'</span>'
        +'</div>';
    }).join('');
  }

  // Entry checklist
  const clEl = document.getElementById('entryChecklist');
  if(clEl) {
    const score = en.entry_score || 0;
    const hasSig = (en.signals||[]).length > 0;
    const hasCandle = (en.candle_patterns||[]).length > 0;
    const items = [
      { check: (en.divergence_days||0) >= 5,   label: "RSI bullish divergence confirmed",         action: "Enter T1 - 35% of allocation" },
      { check: (en.vol_dry_up_ratio||0) >= 2 || (en.signals||[]).some(s=>s.name.includes('CLIMAX')),
                                                 label: "Selling climax or volume dry-up detected",   action: "Signals high conviction bottom" },
      { check: hasCandle,                        label: "Reversal candle at support",                action: "Hammer / engulfing = confirmed low" },
      { check: score >= 45,                      label: "Entry score - 45 (ACCUMULATE)",             action: "Begin T1 entry at current price" },
      { check: score >= 65,                      label: "Entry score - 65 (BUY NOW)",                action: "Execute T1 + set T2 limit order" },
      { check: !!(en.invalidation),              label: "Stop set at invalidation level",             action: "Place stop at $" + (en.invalidation||'-') },
    ];
    clEl.innerHTML = items.map(function(item){
      return '<div style="display:flex;align-items:flex-start;gap:10px;padding:5px 0;border-bottom:1px solid var(--border);">'
        +'<span style="font-size:14px;flex-shrink:0;">-</span>'
        +'<div>'
        +'<div style="font-size:10px;color:'+(item.check?G:'var(--text-dim)')+';">'+item.label+'</div>'
        +'<div style="font-size:8px;color:'+(item.check?'#69f0ae':'var(--text-dim)')+'40;margin-top:2px;">- '+item.action+'</div>'
        +'</div></div>';
    }).join('');
  }
}

function renderPeakPanel(pk) {
  if(!pk) return;
  const R = '#ff1744', O = '#ff6d00', G = '#00ff88', GO = 'var(--gold)';
  const sevColor = {"CRITICAL": R, "HIGH": O, "MEDIUM": GO, "WARNING": O, "LOW": "var(--text-dim)"};

  // Urgency
  const urgEl = document.getElementById('peakUrgency');
  if(urgEl) { urgEl.textContent = pk.peak_urgency || '- CLEAR'; urgEl.style.color = pk.peak_color || G; }
  const card = document.getElementById('peakUrgencyCard');
  if(card) card.style.borderColor = pk.peak_color || G;

  const bar = document.getElementById('peakScoreBar');
  if(bar) { bar.style.width = Math.min(pk.peak_score||0, 100) + '%'; bar.style.background = pk.peak_color || G; }
  const sv = document.getElementById('peakScoreVal');
  if(sv) sv.textContent = (pk.peak_score||0) + '/100';

  // Numbers
  const ttEl = document.getElementById('peakTopTarget');
  if(ttEl) { ttEl.textContent = pk.top_price_target ? '$' + pk.top_price_target : '-'; ttEl.style.color = O; }
  const hsEl = document.getElementById('peakHardStop');
  if(hsEl) { hsEl.textContent = pk.hard_stop ? '$' + pk.hard_stop : '-'; hsEl.style.color = R; }

  const cdEl = document.getElementById('peakCountdown');
  if(cdEl) {
    cdEl.textContent = pk.countdown_bars ? pk.countdown_bars + (pk.countdown_bars === 1 ? ' bar' : ' bars') : '-';
    cdEl.style.color = pk.countdown_bars === 1 ? R : pk.countdown_bars <= 3 ? O : GO;
  }
  const ewEl = document.getElementById('peakExitWindow');
  if(ewEl) ewEl.textContent = pk.optimal_exit_window || '-';

  const ddEl = document.getElementById('peakDivDays');
  if(ddEl) {
    ddEl.textContent = pk.divergence_days || 0;
    ddEl.style.color = pk.divergence_days >= 10 ? R : pk.divergence_days >= 5 ? O : pk.divergence_days > 0 ? GO : G;
  }

  // Signal cards
  const scEl = document.getElementById('peakSignalCards');
  const cmEl = document.getElementById('peakClearMsg');
  if(scEl) {
    const sigs = pk.signals || [];
    if(sigs.length === 0) {
      scEl.innerHTML = '';
      if(cmEl) cmEl.style.display = 'block';
    } else {
      if(cmEl) cmEl.style.display = 'none';
      scEl.innerHTML = sigs.map(function(s){
        var c = sevColor[s.severity] || GO;
        return '<div style="background:var(--bg3);border:1px solid var(--border);border-left:3px solid '+c+';padding:12px;border-radius:1px;">'
          +'<div style="display:flex;justify-content:space-between;margin-bottom:4px;">'
          +'<span style="font-size:11px;font-weight:700;color:'+c+';">'+s.name+'</span>'
          +'<span style="font-family:var(--font-mono);font-size:10px;color:'+c+';">+'+s.score+'</span>'
          +'</div>'
          +'<div style="font-size:9px;color:var(--text-dim);line-height:1.5;">'+s.detail+'</div>'
          +'</div>';
      }).join('');
    }
  }

  // Candle patterns
  const cpEl = document.getElementById('peakCandlePatterns');
  if(cpEl) {
    const patterns = pk.candle_patterns || [];
    const barLabels = {"-1": "Today", "-2": "Yesterday", "-3": "2 days ago"};
    cpEl.innerHTML = patterns.length
      ? patterns.map(function(p){
          var c = p.severity === 'HIGH' ? R : p.severity === 'MEDIUM' ? O : GO;
          return '<div style="display:flex;justify-content:space-between;align-items:center;background:var(--bg2);border:1px solid '+c+'40;padding:8px 10px;border-radius:2px;">'
            +'<span style="font-size:11px;color:'+c+';font-weight:700;">'+p.pattern+'</span>'
            +'<span style="font-size:9px;color:var(--text-dim);">'+(barLabels[String(p.bar)]||'')+'</span>'
            +'<span style="font-size:9px;font-family:var(--font-mono);color:'+c+';border:1px solid '+c+';padding:2px 6px;">'+p.severity+'</span>'
            +'</div>';
        }).join('')
      : '<div style="font-size:10px;color:var(--accent-green);">- No reversal candle patterns</div>';
  }

  // Professional checklist - dynamic based on peak score
  const clEl = document.getElementById('peakChecklist');
  if(clEl) {
    const score = pk.peak_score || 0;
    const items = [
      { check: (pk.divergence_days||0) >= 5,    label: "RSI bearish divergence confirmed",           action: "Exit 25% of position" },
      { check: (pk.vol_climax_ratio||0) >= 2,   label: "Volume climax at high detected",             action: "Exit 25% more, tighten stop" },
      { check: (pk.candle_patterns||[]).length > 0, label: "Reversal candle pattern on chart",      action: "Set limit sell at today's high" },
      { check: score >= 45,                      label: "Peak score - 45 (NEAR TOP zone)",           action: "Move stop to break-even" },
      { check: score >= 65,                      label: "Peak score - 65 (SELL NOW zone)",           action: "Exit remaining position now" },
      { check: !!(pk.hard_stop),                 label: "Hard stop set below 3-day low",             action: "Place stop order at $" + (pk.hard_stop || '-') },
    ];
    clEl.innerHTML = items.map(function(item){
      return '<div style="display:flex;align-items:flex-start;gap:10px;padding:6px 0;border-bottom:1px solid var(--border);">'
        +'<span style="font-size:14px;flex-shrink:0;">-</span>'
        +'<div>'
        +'<div style="font-size:10px;color:'+(item.check?G:'var(--text-dim)')+';">'+item.label+'</div>'
        +'<div style="font-size:9px;color:'+(item.check?O:'var(--text-dim)')+'40;margin-top:2px;">- '+item.action+'</div>'
        +'</div></div>';
    }).join('');
  }
}

function renderCTAPanel(sz, price) {
  if(!sz || !Object.keys(sz).length) return;
  const G = '#00ff88', R = 'var(--accent-red)', GO = 'var(--gold)', B = '#40c4ff', O = '#ff6d00';
  const fmt$ = v => v != null ? '$' + Number(v).toLocaleString('en-US',{maximumFractionDigits:0}) : '-';
  const fmtN = (v,d=2) => v != null ? Number(v).toFixed(d) : '-';

  // Sizing signal
  const sigColors = {'FULL SIZE':G,'NORMAL SIZE':G,'HALF SIZE':GO,'QUARTER SIZE':O,'STAY OUT':R,'ERROR':R};
  const ssEl = document.getElementById('sizingSignalBig');
  if(ssEl) { ssEl.textContent = sz.sizing_signal||'-'; ssEl.style.color = sigColors[sz.sizing_signal]||GO; }

  // Main numbers
  const feEl = document.getElementById('finalExposure');
  if(feEl) { feEl.textContent = fmt$(sz.final_exposure); feEl.style.color = (sz.final_exposure||0) > 0 ? G : R; }
  const fepEl = document.getElementById('finalExposurePct');
  if(fepEl) fepEl.textContent = (sz.final_exposure_pct||0).toFixed(1) + '% of portfolio';

  const scEl = document.getElementById('shareCount');
  if(scEl) scEl.textContent = sz.share_count != null ? sz.share_count.toLocaleString() : '-';
  const spEl = document.getElementById('sharePrice');
  if(spEl) spEl.textContent = price ? '@ $' + price.toFixed(2) + ' per share' : '-';

  const srEl = document.getElementById('shareRange');
  if(srEl) srEl.innerHTML = sz.conservative_shares != null
    ? '<span style="color:'+B+';">'+sz.conservative_shares.toLocaleString()+'</span>'
      +' <span style="color:var(--text-dim);font-size:12px;"> - </span>'
      +' <span style="color:'+O+';">'+sz.aggressive_shares.toLocaleString()+'</span><br>'
      +'<span style="font-size:10px;color:var(--text-dim);">'+fmt$(sz.conservative_exposure)+' - '+fmt$(sz.aggressive_exposure)+'</span>'
    : '-';

  const drEl = document.getElementById('dailyRisk');
  if(drEl) drEl.textContent = fmt$(sz.dollar_at_risk);
  const siEl = document.getElementById('spyImpact');
  if(siEl) siEl.textContent = sz.max_loss_1pct_spy ? '-' + fmt$(sz.max_loss_1pct_spy) : '-';
  const sbEl = document.getElementById('spyBeta');
  if(sbEl) sbEl.textContent = sz.corr_60d != null ? 'beta: '+fmtN(sz.beta_20d||2,1)+'x | corr: '+fmtN(sz.corr_60d,2) : '-';

  // Factor table
  const ftEl = document.getElementById('ctaFactorTable');
  if(ftEl && sz.factor_table) {
    ftEl.innerHTML = sz.factor_table.map(function(row){
      var isResult = row.factor.includes('-');
      var pad = isResult?'6px 0 2px':'3px 0';
      var fsize = isResult?'11':'9';
      var fc = isResult?G:'var(--text-dim)';
      var vsize = isResult?'13':'10';
      var vc = isResult?G:'var(--text-primary)';
      var border = isResult?'border-top:1px solid rgba(0,255,136,0.3);margin-top:4px;':'';
      return '<div style="display:flex;justify-content:space-between;align-items:baseline;padding:'+pad+';border-bottom:1px solid rgba(255,255,255,0.04);'+border+'">'
        +'<span style="font-size:'+fsize+'px;color:'+fc+';">'+row.factor+'</span>'
        +'<div style="text-align:right;">'
        +'<span style="font-family:var(--font-mono);font-size:'+vsize+'px;color:'+vc+';">'+row.value+'</span>'
        +'<div style="font-size:8px;color:var(--text-dim);">'+row.impact+'</div>'
        +'</div></div>';
    }).join('');
  }

  // Multiplier gauges
  const mmEl = document.getElementById('ctaMultipliers');
  if(mmEl) {
    const mults = [
      { label:'Vol-Scaled Base', val: sz.vol_ratio, pct: Math.min((sz.vol_ratio||0)*50,100), color: G,
        sub: ((sz.asset_vol_annual||0)*100).toFixed(1)+'% vol - '+((sz.vol_ratio||0)*100).toFixed(0)+'% of portfolio' },
      { label:'Trend Signal',    val: sz.trend_signal, pct: (sz.trend_signal||0)*100, color: B,
        sub: sz.trend_direction || '-' },
      { label:'Regime Mult',     val: sz.regime_multiplier, pct: (sz.regime_multiplier||0)*100, color: GO,
        sub: sz.regime_label || '-' },
      { label:'Corr Adjustment', val: sz.correlation_factor, pct: (sz.correlation_factor||0)*100, color: '#b388ff',
        sub: 'Corr='+fmtN(sz.corr_60d,2) },
    ];
    mmEl.innerHTML = mults.map(function(m){
      return '<div>'
        +'<div style="display:flex;justify-content:space-between;margin-bottom:4px;">'
        +'<span style="font-size:9px;color:var(--text-dim);">'+m.label+'</span>'
        +'<span style="font-family:var(--font-mono);font-size:10px;color:'+m.color+';">'+fmtN(m.val,3)+'</span>'
        +'</div>'
        +'<div style="background:var(--bg2);border-radius:2px;height:6px;overflow:hidden;">'
        +'<div style="height:100%;width:'+m.pct.toFixed(1)+'%;background:'+m.color+';transition:width 0.6s;border-radius:2px;"></div>'
        +'</div>'
        +'<div style="font-size:8px;color:var(--text-dim);margin-top:2px;">'+m.sub+'</div>'
        +'</div>';
    }).join('');
  }

  // Regime breakdown cards
  const rbEl = document.getElementById('ctaRegimeBreakdown');
  if(rbEl && sz.regime_breakdown) {
    const rb = sz.regime_breakdown;
    const cards = [
      { label:'HMM Regime',    val: (rb.hmm&&rb.hmm.regime)||'-',    mult: rb.hmm&&rb.hmm.multiplier,    sub: 'Conf: '+(((rb.hmm&&rb.hmm.confidence)||0)*100).toFixed(0)+'%', color: B },
      { label:'VIX Level',     val: rb.vix?.level||'-',     mult: rb.vix?.multiplier,    sub: 'Fear gauge',   color: R },
      { label:'GEX Env',       val: ((rb.gex&&rb.gex.value)||0)>0?'+'+((rb.gex&&rb.gex.value)||0).toFixed(0)+'M':((rb.gex&&rb.gex.value)||0).toFixed(0)+'M', mult: rb.gex&&rb.gex.multiplier, sub: 'Dealer flow', color: '#b388ff' },
      { label:'News',          val: rb.news?.signal||'-',   mult: rb.news?.multiplier,   sub: 'Sentiment',    color: GO },
      { label:'Pre-Market',    val: ((rb.premarket&&rb.premarket.change_pct)||0)>0?'+'+((rb.premarket&&rb.premarket.change_pct)||0).toFixed(1)+'%':((rb.premarket&&rb.premarket.change_pct)||0).toFixed(1)+'%', mult: rb.premarket&&rb.premarket.multiplier, sub: 'PM activity', color: '#40c4ff' },
    ];
    rbEl.innerHTML = cards.map(function(c){
      return '<div style="background:var(--bg2);border:1px solid var(--border);padding:10px;border-radius:2px;text-align:center;">'
        +'<div style="font-size:8px;letter-spacing:1px;color:'+c.color+';text-transform:uppercase;margin-bottom:4px;">'+c.label+'</div>'
        +'<div style="font-family:var(--font-mono);font-size:12px;font-weight:700;color:var(--text-primary);">'+c.val+'</div>'
        +'<div style="font-size:10px;color:'+c.color+';margin-top:2px;">×'+fmtN(c.mult,2)+'</div>'
        +'<div style="font-size:8px;color:var(--text-dim);">'+c.sub+'</div>'
        +'</div>';
    }).join('');
  }

  // Reasons
  const rnEl = document.getElementById('ctaReasons');
  if(rnEl) rnEl.innerHTML = (sz.sizing_reasons||[]).map(r =>
    '<div style="font-size:10px;color:var(--text-dim);line-height:1.6;padding:4px 0;border-bottom:1px solid var(--border);">'+r+'</div>'
  ).join('') || '<div style="font-size:10px;color:var(--text-dim);">Computing...</div>';

  // Vol chart
  if(sz.vol_history?.length && volChart) {
    const vh = sz.vol_history;
    volChart.data.labels = vh.map(v => v.date.slice(5));
    volChart.data.datasets[0].data = vh.map(v => v.vol);
    volChart.update('none');
  }
}

function updatePortfolio() {
  const pv = parseFloat(document.getElementById('portfolioInput').value) || 100000;
  const tv = parseInt(document.getElementById('targetVolInput').value) || 12;
  document.getElementById('targetVolDisplay').textContent = tv + '%';
  fetch('/api/set_portfolio', {
    method: 'POST',
    headers: {'Content-Type':'application/json'},
    body: JSON.stringify({portfolio_value: pv, target_vol: tv / 100})
  }).then(r => r.json()).then(d => {
    if(d.status === 'ok') {
      // Trigger immediate refresh
      setTimeout(fetchState, 500);
    }
  }).catch(e => console.error('Portfolio update error:', e));
}

function renderExtPanel(ext) {
  if(!ext || !Object.keys(ext).length) return;
  const G = 'var(--accent-green)', R = 'var(--accent-red)', GO = 'var(--gold)', P = '#ce93d8', C = '#00e5ff';
  const gc = v => (!v || v===0) ? GO : v > 0 ? G : R;
  const fmt = (v, suffix='') => v != null ? (v>0?'+':'')+v+suffix : '-';

  // Session badge
  const sb = document.getElementById('sessionBadge');
  const sessionColors = {'PRE-MARKET':P,'REGULAR':C,'AFTER-HOURS':'#ff9800','OVERNIGHT':'#7e57c2','WEEKEND':'#546e7a'};
  if(sb) { sb.textContent = ext.session||'-'; sb.style.background = (sessionColors[ext.session]||'#555')+'33'; sb.style.color = sessionColors[ext.session]||'#aaa'; }
  const etEl = document.getElementById('etTimeBadge');
  if(etEl) etEl.textContent = ext.current_et_time || '-';

  // Pre-market
  const pmP = document.getElementById('pmPrice');
  if(pmP) pmP.textContent = ext.premarket_price ? '$'+ext.premarket_price : '-';
  const pmC = document.getElementById('pmChange');
  if(pmC) { pmC.textContent = fmt(ext.premarket_change_pct,'%'); pmC.style.color = gc(ext.premarket_change_pct); }
  const pmT = document.getElementById('pmTrend');
  if(pmT) { pmT.textContent = ext.premarket_trend||'-'; pmT.style.color = ext.premarket_trend==='RISING'?G:ext.premarket_trend==='FALLING'?R:GO; }

  // After-hours
  const ahP = document.getElementById('ahPrice');
  if(ahP) ahP.textContent = ext.afterhours_price ? '$'+ext.afterhours_price : '-';
  const ahC = document.getElementById('ahChange');
  if(ahC) { ahC.textContent = fmt(ext.afterhours_change_pct,'%'); ahC.style.color = gc(ext.afterhours_change_pct); }
  const ahV = document.getElementById('ahVol');
  if(ahV) ahV.textContent = ext.afterhours_volume ? (ext.afterhours_volume/1e6).toFixed(2)+'M shares' : '-';

  // Overnight gap
  const gv = document.getElementById('gapVal');
  if(gv) { gv.textContent = fmt(ext.overnight_gap_pct,'%'); gv.style.color = gc(ext.overnight_gap_pct); }
  const gd = document.getElementById('gapDir');
  if(gd) { gd.textContent = ext.gap_direction==='UP'?'- Gap Up':ext.gap_direction==='DOWN'?'- Gap Down':'- Flat'; gd.style.color = ext.gap_direction==='UP'?G:ext.gap_direction==='DOWN'?R:GO; }
  const gf = document.getElementById('gapFill');
  if(gf) gf.textContent = ext.gap_fill_prob!=null ? 'Fill prob: '+ext.gap_fill_prob+'%' : '-';

  // VWAP
  const vwEl = document.getElementById('pmVwap');
  if(vwEl) vwEl.textContent = ext.premarket_vwap ? '$'+ext.premarket_vwap : '-';

  // High / Low / Volume
  const hlEl = document.getElementById('pmHighLow');
  if(hlEl) hlEl.innerHTML = ext.premarket_high
    ? '<span style="color:'+G+';">H: $'+ext.premarket_high+'</span><br><span style="color:'+R+';">L: $'+ext.premarket_low+'</span>'
    : '-';
  const pvEl = document.getElementById('pmVol');
  if(pvEl) pvEl.textContent = ext.premarket_volume ? (ext.premarket_volume/1e6).toFixed(2)+'M vol' : '-';

  // Ext signal
  const esEl = document.getElementById('extSignal');
  if(esEl) { esEl.textContent = ext.ext_signal||'-'; esEl.style.color = (ext.ext_signal||'').includes('BULL')?G:(ext.ext_signal||'').includes('BEAR')?R:GO; }
  const escEl = document.getElementById('extScore');
  if(escEl) escEl.textContent = 'Score: '+(ext.ext_score>0?'+':'')+ext.ext_score;

  // Reasons
  const erEl = document.getElementById('extReasons');
  if(erEl) erEl.innerHTML = (ext.ext_reasons||[]).length
    ? ext.ext_reasons.map(r => {
        const pos = r.includes('-'); const neg = r.includes('-');
        var ic2=pos?G:neg?R:GO; return '<div style="font-size:9px;color:'+ic2+';line-height:1.6;border-left:2px solid '+ic2+';padding-left:6px;">'+r+'</div>';
      }).join('')
    : '<div style="font-size:10px;color:var(--text-dim);">No extended hours signals</div>';

  // Intraday chart
  if(ext.intraday_history?.length) {
    intradayChart.data.labels = ext.intraday_history.map(b => b.dt);
    intradayChart.data.datasets[0].data = ext.intraday_history;
    intradayChart.update('none');
  }
}

// -- News data cache for filtering --
let _newsCache = [];

function renderNewsPanel(nd) {
  if(!nd) return;
  _newsCache = nd.articles || [];
  const G = 'var(--accent-green)', R = 'var(--accent-red)', GO = 'var(--gold)';
  const sigColors = {'VERY BULLISH':G,'BULLISH':G,'NEUTRAL':GO,'BEARISH':R,'VERY BEARISH':R};

  // Summary numbers
  const nsEl = document.getElementById('newsSignal');
  if(nsEl) { nsEl.textContent = nd.signal||'-'; nsEl.style.color = sigColors[nd.signal]||GO; }
  const nscEl = document.getElementById('newsScore');
  if(nscEl) nscEl.textContent = 'Score: ' + (nd.score > 0 ? '+' : '') + (nd.score ?? '-');
  const bcEl = document.getElementById('newsBullCount');  if(bcEl) bcEl.textContent = nd.bull_count ?? 0;
  const brEl = document.getElementById('newsBearCount');  if(brEl) brEl.textContent = nd.bear_count ?? 0;
  const tcEl = document.getElementById('newsTotalCount'); if(tcEl) tcEl.textContent = nd.total ?? 0;
  const upEl = document.getElementById('newsUpdated');    if(upEl) upEl.textContent = nd.last_updated || '-';

  // High impact cards
  const hiEl = document.getElementById('highImpactNews');
  if(hiEl) hiEl.innerHTML = (nd.high_impact||[]).map(a => newsCard(a, true)).join('') ||
    '<div style="font-size:10px;color:var(--text-dim);">No high-impact news in latest cycle</div>';

  // Full feed
  renderNewsFeed(_newsCache);
}

function newsCard(a, large=false) {
  const G = 'var(--accent-green)', R = 'var(--accent-red)', GO = 'var(--gold)';
  const sc = a.sentiment_score || 0;
  const bdr = sc >= 15 ? G : sc <= -15 ? R : 'var(--border)';
  const sentColor = sc >= 15 ? G : sc <= -15 ? R : GO;
  const srcColor  = a.source === 'SEC EDGAR' ? '#b388ff' : 'var(--text-dim)';
  const kw = (a.matched_keywords||[]).slice(0,3).map(k=>
    '<span style="font-size:8px;background:var(--bg2);border:1px solid var(--border);padding:1px 5px;border-radius:2px;color:'+(sc>=0?G:R)+';white-space:nowrap;">'+k+'</span>'
  ).join('');
  return '<div style="background:var(--bg3);border:1px solid var(--border);border-left:3px solid '+bdr+';padding:10px 12px;border-radius:1px;margin-bottom:6px;">'
    +'<div style="display:flex;justify-content:space-between;align-items:flex-start;gap:8px;margin-bottom:5px;">'
    +'<a href="'+a.url+'" target="_blank" rel="noopener" style="font-size:11px;font-weight:600;color:var(--text-primary);text-decoration:none;line-height:1.4;flex:1;">'+a.title+'</a>'
    +'<span style="font-size:8px;color:var(--text-dim);white-space:nowrap;">'+a.source+' &bull; '+(a.time_ago||a.pub||'')+'</span>'
    +'</div>'
    +'<div style="display:flex;gap:6px;flex-wrap:wrap;align-items:center;">'
    +sentChip(a.sentiment_label||'NEUTRAL', a.sentiment)
    +(a.impact_level?'<span style="font-size:9px;color:'+sentColor+';">'+a.impact_level+'</span>':'')
    +((a.tickers&&a.tickers.length)?a.tickers.map(function(t){return chip(t,sentColor);}).join(''):'')
    +'</div>'
    +(a.summary&&large?'<div style="font-size:9px;color:var(--text-dim);margin-top:6px;line-height:1.5;">'+a.summary.slice(0,180)+'...</div>':'')
    +'</div>'
}

function renderNewsFeed(articles) {
  const el = document.getElementById('newsFeed');
  if(!el) return;
  if(!articles || !articles.length) {
    el.innerHTML = '<div style="font-size:10px;color:var(--text-dim);padding:12px;">Fetching news...</div>';
    return;
  }
  el.innerHTML = articles.map(a => newsCard(a, false)).join('');
}

function filterNews(type) {
  // Update button styles
  ['all','bull','bear','sec'].forEach(t => {
    const btn = document.getElementById('filter' + t.charAt(0).toUpperCase() + t.slice(1));
    if(btn) { btn.style.background = t === type ? 'var(--gold)' : 'var(--bg3)'; btn.style.color = t === type ? '#000' : 'var(--text-dim)'; }
  });
  let filtered = _newsCache;
  if(type === 'bull') filtered = _newsCache.filter(a => (a.sentiment_score||0) >= 10);
  if(type === 'bear') filtered = _newsCache.filter(a => (a.sentiment_score||0) <= -10);
  if(type === 'sec')  filtered = _newsCache.filter(a => a.source === 'SEC EDGAR');
  renderNewsFeed(filtered);
}

function renderSPYPanel(spy) {
  if(!spy || !Object.keys(spy).length) return;
  const G = 'var(--accent-green)', R = 'var(--accent-red)', GO = 'var(--gold)', B = '#00b4ff', O = '#ff6d00';
  const gc = v => v > 0 ? G : v < 0 ? R : 'var(--text-dim)';
  function row(label, val, color) {
    return '<div style="display:flex;justify-content:space-between;font-size:10px;padding:2px 0;">'
      +'<span style="color:var(--text-dim);">'+label+'</span>'
      +'<span style="font-family:var(--font-mono);color:'+(color||'var(--text-primary)')+';">'+val+'</span>'
      +'</div>';
  }
  function chip(text, color) {
    return '<span style="font-size:9px;font-family:var(--font-mono);background:var(--bg2);border:1px solid '+color+';color:'+color+';padding:3px 8px;border-radius:2px;white-space:nowrap;">'+text+'</span>';
  }

  // Macro signal
  const ms = document.getElementById('macroSignal');
  const mc = spy.macro_score >= 15 ? G : spy.macro_score <= -15 ? R : GO;
  if(ms) { ms.textContent = spy.macro_signal || '-'; ms.style.color = mc; }
  const msc = document.getElementById('macroScore');
  if(msc) { msc.textContent = 'Score: '+(spy.macro_score > 0 ? '+':'')+''+(spy.macro_score)+''; msc.style.color = mc; }

  // SPY price + change
  const sp = document.getElementById('spyPrice');
  if(sp) sp.textContent = spy.spy_price ? '$' + spy.spy_price : '-';
  const sc = document.getElementById('spyChange');
  const chg = spy.spy_change_pct;
  if(sc) { sc.textContent = chg != null ? (chg > 0 ? '+' : '') + chg + '%' : '-'; sc.style.color = gc(chg); }

  // VIX
  const vv = document.getElementById('vixVal');
  const vr = document.getElementById('vixRegime');
  const vix = spy.vix;
  const vc = vix >= 35 ? R : vix >= 25 ? O : vix < 13 ? G : 'var(--text-dim)';
  if(vv) { vv.textContent = vix || '-'; vv.style.color = vc; }
  if(vr) { vr.textContent = spy.vix_regime || '-'; vr.style.color = vc; }

  // Beta
  const bv = document.getElementById('betaVal');
  if(bv) bv.textContent = spy.beta_20d != null ? spy.beta_20d + 'x' : '-';

  // Expected TSLA move
  const em = document.getElementById('expectedMove');
  const exp = spy.expected_tsla_move;
  if(em) { em.textContent = exp != null ? (exp > 0 ? '+' : '') + exp + '%' : '-'; em.style.color = gc(exp); }
  const am = document.getElementById('actualMove');
  const act = spy.actual_tsla_move;
  if(am) { am.textContent = act != null ? 'Actual: '+(act>0?'+':'')+act+'%' : 'Actual: -'; am.style.color = gc(act); }

  // RS signal
  const rs = document.getElementById('rsSignal');
  const rc = spy.rs_signal === 'LEADING' || spy.rs_signal === 'OUTPERFORM' ? G :
             spy.rs_signal === 'LAGGING' || spy.rs_signal === 'UNDERPERFORM' ? R : GO;
  if(rs) { rs.textContent = spy.rs_signal || '-'; rs.style.color = rc; }
  const rv = document.getElementById('rsVal');
  if(rv && spy.relative_strength != null) rv.textContent = 'TSLA '+(spy.relative_strength > 0 ? '+' : '')+''+(spy.relative_strength)+'% vs SPY (20d)';

  // SPY key levels
  const sd = document.getElementById('spyDetails');
  const kl = spy.key_levels || {};
  if(sd) sd.innerHTML = [
    row('Trend',        spy.spy_trend || '-', spy.spy_trend?.includes('BULL') ? G : spy.spy_trend?.includes('BEAR') ? R : GO),
    row('SPY RSI',      spy.spy_rsi || '-', spy.spy_rsi > 70 ? R : spy.spy_rsi < 30 ? G : 'var(--text-dim)'),
    row('EMA 20',       kl.spy_ema20 ? '$'+kl.spy_ema20 : '-', 'var(--text-dim)'),
    row('EMA 50',       kl.spy_ema50 ? '$'+kl.spy_ema50 : '-', 'var(--text-dim)'),
    row('EMA 200',      kl.spy_ema200 ? '$'+kl.spy_ema200 : '-', 'var(--text-dim)'),
    row('52W High',     kl.spy_52w_high ? '$'+kl.spy_52w_high : '-', 'var(--text-dim)'),
    row('From 52W High',kl.pct_from_52w_high != null ? kl.pct_from_52w_high+'%' : '-', gc(kl.pct_from_52w_high)),
    row('Correlation',  spy.correlation_60d != null ? spy.correlation_60d : '-', 'var(--text-dim)'),
    row('Divergence',   spy.divergence_warning ? '- YES' : 'No', spy.divergence_warning ? R : G),
  ].join('');

  // QQQ
  const qd = document.getElementById('qqqDetails');
  if(qd) qd.innerHTML = [
    row('QQQ Price',  spy.qqq_price ? '$'+spy.qqq_price : '-', 'var(--text-primary)'),
    row('QQQ Change', spy.qqq_change_pct != null ? (spy.qqq_change_pct > 0 ? '+' : '')+spy.qqq_change_pct+'%' : '-', gc(spy.qqq_change_pct)),
  ].join('');

  // TLT
  const td = document.getElementById('tltDetails');
  if(td) {
    const tc = spy.tlt_5d_change;
    td.textContent = tc != null
      ? '5d change: '+(tc>0?'+':'')+tc+'% - '+(spy.bonds_signal||'NEUTRAL')
      : 'No data';
    td.style.color = spy.bonds_signal === 'RISK-OFF ROTATION' ? O : 'var(--text-dim)';
  }

  // RS chart
  if(spy.rs_history?.length && rsChart) {
    const rsh = spy.rs_history;
    rsChart.data.labels = rsh.map(r => r.date?.slice(5));
    rsChart.data.datasets[0].data = rsh.map(r => r.tsla);
    rsChart.data.datasets[1].data = rsh.map(r => r.spy);
    rsChart.data.datasets[2].data = rsh.map(r => r.qqq || null);
    rsChart.update('none');
  }

  // VIX chart
  if(false && spy.vix_history?.length && vixChart) { // vixChart removed
    const vh = spy.vix_history;
    if(vixChart){try{vixChart.data.labels=vh.map(v=>v.date?v.date.slice(5):'');vixChart.data.datasets[0].data=vh.map(v=>v.vix);vixChart.update('none');}catch(e){console.warn('vixChart:'+e.message);}}
  }

  // Macro reasons chips
  const mr = document.getElementById('macroReasons');
  if(mr) mr.innerHTML = spy.macro_reasons?.length
    ? spy.macro_reasons.map(r => {
        const c = r.includes('-') ? G : r.includes('-') ? R : r.includes('-') ? O : B;
        return chip(r, c);
      }).join('')
    : chip('No macro signals', 'var(--text-dim)');
}

function renderMMPanel(mm, dp, price) {
  if(!mm || !Object.keys(mm).length) return;
  var G = 'var(--accent-green)', R = 'var(--accent-red)', GO = 'var(--gold)', P = '#b388ff', O = '#ff6d00';
  function row(label, val, color) {
    return '<div style="display:flex;justify-content:space-between;align-items:center;font-size:10px;padding:3px 0;">'
      + '<span style="color:var(--text-dim);">'+label+'</span>'
      + '<span style="font-family:var(--font-mono);color:'+(color||'var(--text-primary)')+';">'+val+'</span>'
      + '</div>';
  }

  // -- GEX --
  const gex = mm.gex_total || 0;
  const gexEl = document.getElementById('mmGexVal');
  if(gexEl) { gexEl.textContent = (gex >= 0 ? '+' : '') + gex.toFixed(0) + 'M'; gexEl.style.color = gex > 0 ? G : R; }
  const gexSigEl = document.getElementById('mmGexSig');
  if(gexSigEl) { gexSigEl.textContent = mm.gex_signal || '-'; gexSigEl.style.color = gex > 100 ? G : gex < -100 ? R : GO; }

  // -- Max Pain --
  const mpEl = document.getElementById('mmMaxPain');
  if(mpEl) mpEl.textContent = mm.max_pain ? '$' + mm.max_pain : '-';
  const pinEl = document.getElementById('mmPinRisk');
  if(pinEl) { pinEl.textContent = mm.pin_risk ? '- PIN RISK - expiry soon' : (mm.max_pain ? 'Days to expiry: ' + (mm.days_to_expiry||'?') : '-'); pinEl.style.color = mm.pin_risk ? R : 'var(--text-dim)'; }

  // -- P/C Ratio --
  const pcEl = document.getElementById('mmPCRatio');
  const pc = mm.pc_ratio;
  if(pcEl) { pcEl.textContent = pc ? pc.toFixed(2) : '-'; pcEl.style.color = pc > 1.2 ? G : pc < 0.7 ? R : GO; }
  const pcSigEl = document.getElementById('mmPCSignal');
  if(pcSigEl) pcSigEl.textContent = pc > 1.5 ? 'Bearish crowd - Contrarian BUY' : pc > 1.2 ? 'Bearish sentiment' : pc < 0.5 ? 'Complacent - Contrarian SELL' : pc < 0.7 ? 'Bullish crowd' : 'Neutral';

  // -- IV Rank --
  const ivEl = document.getElementById('mmIVRank');
  const ivr = mm.iv_rank;
  if(ivEl) { ivEl.textContent = ivr != null ? ivr + '%' : '-'; ivEl.style.color = ivr > 75 ? R : ivr < 25 ? G : GO; }
  const ivSigEl = document.getElementById('mmIVSig');
  if(ivSigEl) ivSigEl.textContent = mm.iv_signal || '-';

  // -- Hedging --
  const hEl = document.getElementById('mmHedging');
  if(hEl) { hEl.textContent = mm.hedging_pressure || '-'; hEl.style.color = mm.hedging_pressure?.includes('BUYING') ? G : mm.hedging_pressure?.includes('SELLING') ? R : mm.hedging_pressure?.includes('CHASING') ? O : 'var(--text-dim)'; }

  // -- Expiry / 0DTE --
  const expEl = document.getElementById('mmExpiry');
  if(expEl) expEl.textContent = mm.nearest_expiry || '-';
  const zdEl = document.getElementById('mmZeroDte');
  if(zdEl) { zdEl.textContent = mm.zero_dte_risk ? '- 0DTE TODAY - unstable' : (mm.days_to_expiry || '?')+'d to expiry'; zdEl.style.color = mm.zero_dte_risk ? R : 'var(--text-dim)'; }

  // -- Call Walls --
  var cwEl = document.getElementById('mmCallWalls');
  if(cwEl) cwEl.innerHTML = (mm.call_walls&&mm.call_walls.length)
    ? mm.call_walls.map(function(w,i){
        var bg = 'rgba(255,51,85,'+(0.15-i*0.03)+')';
        var bd = 'rgba(255,51,85,'+(0.8-i*0.15)+')';
        return '<div style="display:flex;justify-content:space-between;align-items:center;padding:4px 8px;background:'+bg+';border-left:2px solid '+bd+';border-radius:1px;">'
          +'<span style="font-family:var(--font-mono);font-size:11px;color:#ff6688;">$'+w.strike+'</span>'
          +'<span style="font-size:9px;color:var(--text-dim);">'+(w.oi/1000).toFixed(0)+'K OI</span>'
          +(i===0?'<span style="font-size:8px;color:#ff3355;">- WALL</span>':'')
          +'</div>';
      }).join('')
    : '<div style="font-size:10px;color:var(--text-dim);">Loading...</div>';

  // -- Put Walls --
  var pwEl = document.getElementById('mmPutWalls');
  if(pwEl) pwEl.innerHTML = (mm.put_walls&&mm.put_walls.length)
    ? mm.put_walls.map(function(w,i){
        var bg = 'rgba(0,255,136,'+(0.12-i*0.02)+')';
        var bd = 'rgba(0,255,136,'+(0.7-i*0.15)+')';
        return '<div style="display:flex;justify-content:space-between;align-items:center;padding:4px 8px;background:'+bg+';border-left:2px solid '+bd+';border-radius:1px;">'
          +'<span style="font-family:var(--font-mono);font-size:11px;color:#00ff88;">$'+w.strike+'</span>'
          +'<span style="font-size:9px;color:var(--text-dim);">'+(w.oi/1000).toFixed(0)+'K OI</span>'
          +(i===0?'<span style="font-size:8px;color:#00ff88;">- FLOOR</span>':'')
          +'</div>';
      }).join('')
    : '<div style="font-size:10px;color:var(--text-dim);">Loading...</div>';

  // -- GEX Chart --
  if(mm.gex_by_strike?.length) {
    const gs = mm.gex_by_strike;
    if(gexChart) { gexChart.data.labels = gs.map(g => '$' + g.strike);
    gexChart.data.datasets[0].data = gs.map(g => g.gex);
    gexChart.data.datasets[0].backgroundColor = gs.map(g => g.color + 'bb');
    gexChart.update('none'); }
  }

  // -- OI Chart --
  if(mm.oi_by_strike?.length) {
    const os = mm.oi_by_strike;
    if(oiChart){try{oiChart.data.labels=os.map(o=>'$'+o.strike);oiChart.data.datasets[0].data=os.map(o=>o.call_oi);oiChart.data.datasets[1].data=os.map(o=>o.put_oi);oiChart.update('none');}catch(e){console.warn('oiChart:'+e.message);}}
  }

  // -- Dark Pool Levels --
  function fmtDP(arr) {
    if(!arr||!arr.length) return '<div style="font-size:10px;color:var(--text-dim);">None detected</div>';
    return arr.map(function(l){
      return '<div style="display:flex;justify-content:space-between;font-size:10px;padding:3px 0;border-bottom:1px solid var(--border);">'
        +'<span style="font-family:var(--font-mono);color:'+GO+';">$'+l.price+'</span>'
        +'<span style="font-size:9px;color:var(--text-dim);">'+(l.volume/1e6).toFixed(1)+'M vol - '+l.strength+'x avg</span>'
        +'</div>';
    }).join('');
  }
  const daEl = document.getElementById('dpAbove'); if(daEl) daEl.innerHTML = fmtDP(dp.nearest_above);
  const dbEl = document.getElementById('dpBelow'); if(dbEl) dbEl.innerHTML = fmtDP(dp.nearest_below);

  var dgEl = document.getElementById('dpGaps');
  if(dgEl) dgEl.innerHTML = (dp.volume_gaps&&dp.volume_gaps.length)
    ? dp.volume_gaps.map(function(g){
        return '<div style="font-size:10px;padding:3px 0;border-bottom:1px solid var(--border);">'
          +'<span style="font-family:var(--font-mono);color:'+P+';">$'+g.price+'</span>'
          +'<span style="font-size:9px;color:var(--text-dim);"> '+g.date+' - '+g.vol_mult+'x vol - '+g.gap_pct+'% gap</span>'
          +'</div>';
      }).join('')
    : '<div style="font-size:10px;color:var(--text-dim);">None detected</div>';
}

function renderExitPanel(ex) {
  if(!ex || !ex.exit_analysis) return;
  const ea  = ex.exit_analysis;
  const G = 'var(--accent-green)', R = 'var(--accent-red)', GO = 'var(--gold)', O = '#ff6d00';
  const gc = v => v > 0 ? G : v < 0 ? R : 'var(--text-dim)';
  function row(label, val, color) {
    return '<div style="display:flex;justify-content:space-between;font-size:10px;">'
      +'<span style="color:var(--text-dim);">'+label+'</span>'
      +'<span style="font-family:var(--font-mono);color:'+(color||'var(--text-primary)')+';">'+val+'</span>'
      +'</div>';
  }
  function chip(text, color) {
    return '<span style="font-size:9px;font-family:var(--font-mono);background:var(--bg2);border:1px solid '+color+';color:'+color+';padding:3px 8px;border-radius:2px;white-space:nowrap;">'+text+'</span>';
  }

  // Urgency
  const urgEl = document.getElementById('exitUrgency');
  if(urgEl) { urgEl.textContent = ea.urgency; urgEl.style.color = ea.urgency_color || G; }

  // Score bar
  const bar = document.getElementById('exitScoreBar');
  if(bar) {
    bar.style.width = Math.min(ea.exit_score, 100) + '%';
    bar.style.background = ea.urgency_color || G;
  }
  const sv = document.getElementById('exitScoreVal');
  if(sv) sv.textContent = 'Exit Score: ' + ea.exit_score + '/100';

  // Sell zone
  const sz = document.getElementById('sellZone');
  if(sz) sz.textContent = ea.optimal_sell_low && ea.optimal_sell_high
    ? '$' + ea.optimal_sell_low + ' - $' + ea.optimal_sell_high : '-';
  const up = document.getElementById('upsideToTarget');
  if(up) up.textContent = ea.upside_to_target ? '+' + ea.upside_to_target + '% to target' : '-';

  // Stop loss
  const sl = document.getElementById('stopLoss');
  if(sl) sl.textContent = ea.stop_loss ? '$' + ea.stop_loss : '-';

  // PSAR
  const psar = ex.parabolic_sar || {};
  const pv = document.getElementById('psarVal');
  if(pv) pv.textContent = psar.sar ? '$' + psar.sar : '-';
  const ps = document.getElementById('psarSignal');
  if(ps) { ps.textContent = psar.signal || '-'; ps.style.color = psar.signal === 'SELL_NOW' ? R : psar.signal === 'NEAR_STOP' ? O : G; }

  // Fibonacci levels
  const fib = ex.fibonacci || {};
  const fl = document.getElementById('fibLevels');
  if(fl && fib.levels) {
    const price = ea.current_price;
    fl.innerHTML = Object.entries(fib.levels).map(([k,v]) => {
      const isAbove = v > price;
      const isNear  = Math.abs(v - price) / price < 0.03;
      const c = isNear ? GO : isAbove ? O : 'var(--text-dim)';
      return row(k, '$'+v + (isNear ? ' - NEAR' : ''), c);
    }).join('');
  }

  // Resistance levels
  const res = ex.resistance || {};
  var ra = document.getElementById('resistanceAbove');
  if(ra) ra.innerHTML = (res.levels_above&&res.levels_above.length)
    ? res.levels_above.map(function(v,i){
        return '<div style="display:flex;justify-content:space-between;font-size:11px;">'
          +'<span style="font-family:var(--font-mono);color:'+(i===0?O:'var(--text-dim)')+';">$'+v+'</span>'
          +'<span style="font-size:9px;color:var(--text-dim);">'+(i===0?'- nearest':'')+'</span>'
          +'</div>';
      }).join('')
    : '<div style="font-size:10px;color:var(--text-dim);">None identified</div>';
  var rb = document.getElementById('resistanceBelow');
  if(rb) rb.innerHTML = (res.levels_below&&res.levels_below.length)
    ? res.levels_below.map(function(v){return '<div style="font-family:var(--font-mono);font-size:11px;color:var(--text-dim);">$'+v+'</div>';}).join('')
    : '<div style="font-size:10px;color:var(--text-dim);">None identified</div>';


  // -- Sell Tranche Plan --
  var ea2  = ex.exit_analysis || {};
  const stp = ea2.sell_tranches || [];
  const fmt$ = v => v != null ? '$' + Number(v).toLocaleString('en-US',{maximumFractionDigits:2,minimumFractionDigits:2}) : '-';
  const trColors = {1:'#ffd600', 2:'#ff6d00', 3:'#ff1744'};

  // Avg exit
  const aeEl = document.getElementById('avgExitPrice');
  if(aeEl) aeEl.textContent = ea2.avg_exit_price ? fmt$(ea2.avg_exit_price) : '-';
  const agEl = document.getElementById('avgGainPct');
  if(agEl) { agEl.textContent = ea.avg_gain_pct != null ? '+'+ea.avg_gain_pct+'% avg gain' : ''; }

  // Tranche cards
  const stEl = document.getElementById('sellTranches');
  if(stEl) {
    if(stp.length === 0) {
      stEl.innerHTML = '<div style="grid-column:1/-1;text-align:center;padding:20px;font-size:11px;color:var(--text-dim);">No sell target yet - waiting for exit score to develop</div>';
    } else {
      stEl.innerHTML = stp.map(function(t){
        return '<div style="background:var(--bg3);border:2px solid '+t.color+'40;border-top:3px solid '+t.color+';padding:14px;border-radius:2px;">'
          +'<div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px;">'
          +'<span style="font-family:var(--font-mono);font-size:9px;font-weight:700;color:'+t.color+';">T'+t.number+' - '+t.label+'</span>'
          +'<span style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:'+t.color+';">'+t.pct_holding+'%</span>'
          +'</div>'
          +'<div style="text-align:center;margin:10px 0;">'
          +'<div style="font-family:var(--font-mono);font-size:22px;font-weight:700;color:'+t.color+';">'+fmt$(t.price)+'</div>'
          +'<div style="font-size:10px;color:var(--accent-green);margin-top:2px;">+'+t.gain_pct+'% from current</div>'
          +'</div>'
          +'<div style="font-size:8px;color:var(--text-dim);margin-bottom:8px;line-height:1.4;">'+t.trigger+'</div>'
          +'<div style="display:grid;grid-template-columns:1fr 1fr;gap:4px;margin-bottom:8px;">'
          +'<div style="background:var(--bg2);padding:6px;border-radius:2px;text-align:center;">'
          +'<div style="font-size:7px;color:var(--text-dim);">SELL % HELD</div>'
          +'<div style="font-family:var(--font-mono);font-size:12px;color:'+t.color+';">'+t.pct_holding+'%</div>'
          +'</div>'
          +'<div style="background:var(--bg2);padding:6px;border-radius:2px;text-align:center;">'
          +'<div style="font-size:7px;color:var(--text-dim);">TRAIL STOP</div>'
          +'<div style="font-family:var(--font-mono);font-size:12px;color:var(--accent-red);">'+fmt$(t.trailing_stop)+'</div>'
          +'</div>'
          +'</div>'
          +'<div style="font-size:8px;color:var(--text-dim);border-top:1px solid var(--border);padding-top:6px;line-height:1.5;">'+t.rationale+'</div>'
          +'</div>';
      }).join('');
    }
  }

  // Trailing stop ladder (horizontal bar)
  const tslEl = document.getElementById('trailStopLadder');
  if(tslEl && stp.length > 0) {
    const allPrices = [ea.current_price||0, ...stp.map(t=>t.price)];
    const minP = Math.min(...allPrices) * 0.97;
    const maxP = Math.max(...allPrices) * 1.01;
    const range = maxP - minP;
    const toX = p => ((p - minP) / range * 100).toFixed(1);

    tslEl.style.position = 'relative';
    tslEl.style.height   = '48px';
    tslEl.style.width    = '100%';

    // Current price marker
    const cp = ea.current_price || 0;
    var html = '<div style="position:absolute;left:'+toX(cp)+'%;top:0;bottom:0;border-left:2px solid #00ff88;transform:translateX(-50%);">'
      +'<div style="font-size:8px;font-family:var(--font-mono);color:#00ff88;white-space:nowrap;margin-top:2px;">NOW<br>'+fmt$(cp)+'</div>'
      +'</div>';

    // Tranche markers
    stp.forEach(function(t) {
      html += '<div style="position:absolute;left:'+toX(t.price)+'%;top:0;bottom:0;border-left:2px dashed '+t.color+';transform:translateX(-50%);">'
        +'<div style="font-size:7px;font-family:var(--font-mono);color:'+t.color+';white-space:nowrap;margin-top:2px;">T'+t.number+'<br>'+fmt$(t.price)+'</div>'
        +'</div>';
    });

    // Baseline
    html = '<div style="position:relative;width:100%;height:48px;background:var(--bg2);border-radius:2px;overflow:hidden;">'
      +'<div style="position:absolute;bottom:0;left:0;right:0;height:2px;background:var(--border);"></div>'
      +html+'</div>';
    tslEl.innerHTML = html;
  }

  // New stop labels
  if(stp.length >= 1) {
    const ns1 = document.getElementById('newStopT1');
    if(ns1) ns1.textContent = stp[0].trailing_stop ? fmt$(stp[0].trailing_stop) : '-';
  }
  if(stp.length >= 2) {
    const ns2 = document.getElementById('newStopT2');
    if(ns2) ns2.textContent = stp[1].trailing_stop ? fmt$(stp[1].trailing_stop) : '-';
  }

  // Divergences
  const divs = (ex.divergences || {}).found || [];
  const dl = document.getElementById('divergenceList');
  if(dl) dl.innerHTML = divs.length
    ? divs.map(function(d){
        return '<div style="font-size:10px;color:'+R+';line-height:1.4;"><strong>'+d.type+'</strong><br>'
          +'<span style="color:var(--text-dim);">'+d.detail+'</span></div>';
      }).join('')
    : '<div style="font-size:10px;color:var(--accent-green);">- No divergences - momentum intact</div>';

  // Distribution
  const dist = ex.distribution || {};
  const ds = document.getElementById('distributionSignal');
  if(ds) {
    const dc = dist.signal === 'TOPPING' ? R : dist.signal === 'WARNING' ? O : G;
    ds.textContent = dist.signal || '-';
    ds.style.color = dc;
  }

  // Stochastic
  const stoch = ex.stochastic || {};
  const sd = document.getElementById('stochDisplay');
  if(sd) sd.innerHTML = [
    row('%K', stoch.k, stoch.k > 80 ? R : stoch.k < 20 ? G : 'var(--text-dim)'),
    row('%D', stoch.d, 'var(--text-dim)'),
    row('Signal', stoch.signal || '-', stoch.signal?.includes('SELL') ? R : stoch.signal?.includes('BUY') ? G : GO),
    row('Bearish Cross', stoch.bearish_cross ? '- YES' : 'No', stoch.bearish_cross ? R : G),
  ].join('');

  // ROC
  const roc = ex.rate_of_change || {};
  const rd = document.getElementById('rocDisplay');
  if(rd) rd.innerHTML = [
    row('5-Day ROC',  (roc.roc_5d > 0 ? '+' : '') + roc.roc_5d + '%', gc(roc.roc_5d)),
    row('10-Day ROC', (roc.roc_10d > 0 ? '+' : '') + roc.roc_10d + '%', gc(roc.roc_10d)),
    row('Momentum',   roc.signal || '-', roc.signal === 'DECELERATING' ? R : roc.signal === 'STRONG' ? G : O),
  ].join('');

  // Exit reasons
  const er = document.getElementById('exitReasons');
  if(er) er.innerHTML = ea.exit_reasons?.length
    ? ea.exit_reasons.map(r => chip(r, O)).join('')
    : chip('No exit signals yet - hold position', G);
}

function sigColor(sig) {
  const bull = ['BULLISH','BUY','STRONG_BUY','ACCUMULATING','SIZE_UP','OVERSOLD'];
  const bear = ['BEARISH','SELL','STRONG_SELL','DISTRIBUTING','AVOID','OVERBOUGHT'];
  if(bull.some(b=>sig?.includes(b))) return 'var(--accent-green)';
  if(bear.some(b=>sig?.includes(b))) return 'var(--accent-red)';
  return 'var(--text-dim)';
}

function sigArrow(sig) {
  const bull = ['BULLISH','BUY','STRONG_BUY','ACCUMULATING','SIZE_UP','OVERSOLD'];
  const bear = ['BEARISH','SELL','STRONG_SELL','DISTRIBUTING','AVOID','OVERBOUGHT'];
  if(bull.some(b=>sig?.includes(b))) return '-';
  if(bear.some(b=>sig?.includes(b))) return '-';
  return '-';
}

function modelCard(title, firm, signal, rows, description) {
  const color = sigColor(signal);
  const arrow = sigArrow(signal);
  return '<div style="background:var(--bg2);border:1px solid var(--border);padding:12px;border-radius:2px;">'
    +'<div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:8px;">'+name+'</div>'
    +rows.map(function(r){return '<div style="display:flex;justify-content:space-between;font-size:10px;"><span style="color:var(--text-dim);">'+r.label+'</span><span style="font-family:var(--font-mono);color:'+(r.color||'var(--text-primary)')+';">'+r.val+'</span></div>';}).join('')
    +'</div>'
}

function renderInstModels(m, ind) {
  const grid = document.getElementById('instModelsGrid');
  if(!grid || !m || !Object.keys(m).length) return;

  const G = 'var(--accent-green)', R = 'var(--accent-red)', D = 'var(--text-dim)', GO = 'var(--gold)';
  const gc = v => v > 0 ? G : v < 0 ? R : D;
  const cards = [];

  // -- 1. VWAP --
  if(m.vwap) {
    const v = m.vwap, px = ind.price||0;
    const vs = px < v.vwap ? 'BELOW VWAP - BUY' : px > v.vwap ? 'ABOVE VWAP - SELL' : 'AT VWAP';
    cards.push(modelCard('VWAP + BANDS','Goldman - Morgan Stanley - All Algo Desks', vs, [
      ['VWAP', '$'+v.vwap, GO],
      ['Price vs VWAP', px < v.vwap ? '- Discount' : '- Premium', gc(px < v.vwap ? 1 : -1)],
      ['+1- Band', '$'+v.upper1, D],
      ['-1- Band', '$'+v.lower1, D],
      ['+2- Band', '$'+v.upper2, D],
      ['-2- Band', '$'+v.lower2, D],
    ], 'Primary institutional execution benchmark. Institutions buy below VWAP and sell above it. Used by every major algo desk for order execution.'));
  }

  // -- 2. Kalman Filter --
  if(m.kalman) {
    const k = m.kalman;
    cards.push(modelCard('KALMAN FILTER','Renaissance Technologies - Two Sigma - DE Shaw', k.signal, [
      ['Filtered Price', '$'+k.filtered_price, GO],
      ['Trend Velocity', k.velocity, gc(k.velocity)],
      ['Acceleration', k.acceleration > 0 ? '+'+k.acceleration : k.acceleration, gc(k.acceleration)],
      ['Trend Direction', k.trend, k.trend==='UP'?G:R],
    ], 'Dynamic noise-filtering model. Separates true price signal from market noise. Used by quant funds for trend following - outperforms simple moving averages in volatile markets.'));
  }

  // -- 3. Z-Score / Mean Reversion --
  if(m.zscore) {
    const z = m.zscore;
    const zc = z.zscore < -1 ? G : z.zscore > 1 ? R : D;
    cards.push(modelCard('MEAN REVERSION Z-SCORE','Citadel - Millennium - Point72 Stat Arb', z.signal, [
      ['Z-Score', z.zscore, zc],
      ['Rolling Mean (20d)', '$'+z.rolling_mean, GO],
      ['Rolling Std Dev', '$'+z.rolling_std, D],
      ['Interpretation', Math.abs(z.zscore) > 2 ? '|Z|>2: HIGH CONVICTION' : Math.abs(z.zscore) > 1 ? '|Z|>1: Moderate' : 'Within normal range', Math.abs(z.zscore)>2?GO:D],
    ], 'Statistical arbitrage model used by quant desks. Z-score > -2 signals mean reversion entry. Citadel runs similar models across thousands of equities simultaneously.'));
  }

  // -- 4. Kelly Criterion --
  if(m.kelly) {
    const k = m.kelly;
    cards.push(modelCard('KELLY CRITERION','Renaissance - Bridgewater - D.E. Shaw', k.signal, [
      ['Kelly % (Half)', k.kelly_pct+'%', gc(k.kelly_pct)],
      ['Win Rate', k.win_rate+'%', k.win_rate>50?G:R],
      ['Avg Win / Avg Loss', k.avg_win+'% / '+k.avg_loss+'%', gc(k.avg_win - k.avg_loss)],
      ['Sharpe Ratio', k.sharpe, gc(k.sharpe)],
      ['Max Drawdown', k.max_drawdown+'%', R],
    ], 'Optimal position sizing formula. Kelly % = mathematically maximum-growth bet size. Renaissance uses Kelly-based sizing. Positive Kelly = edge exists. Half-Kelly used in practice for safety.'));
  }

  // -- 5. Monte Carlo VaR --
  if(m.monte_carlo) {
    const mc = m.monte_carlo;
    cards.push(modelCard('MONTE CARLO VaR','Goldman Sachs - JPMorgan - Morgan Stanley', mc.signal, [
      ['Prob of Upside (10d)', mc.prob_up+'%', mc.prob_up>55?G:mc.prob_up<45?R:D],
      ['Median Price (10d)', '$'+mc.median_price, GO],
      ['VaR 95% (10d)', '$'+mc.var_95, R],
      ['VaR 99% (10d)', '$'+mc.var_99, R],
      ['Upside 95% (10d)', '+$'+mc.upside_95, G],
      ['Expected Shortfall', '$'+mc.cvar_95, R],
    ], 'Monte Carlo simulation ('+mc.simulations.toLocaleString()+' paths, '+mc.horizon+'-day horizon). Every major bank runs daily VaR to measure risk. Prob >55% = bullish edge. VaR tells you worst-case loss at confidence level.'));
  }

  // -- 6. Factor Model --
  if(m.factor) {
    const f = m.factor;
    const fc = f.signal.includes('BUY') ? G : f.signal.includes('SELL') ? R : D;
    cards.push(modelCard('MULTI-FACTOR MOMENTUM','AQR Capital - BlackRock Systematic - DFA', f.signal, [
      ['12-1 Month Momentum', f.momentum_12_1+'%', gc(f.momentum_12_1)],
      ['1-Month Return', f.momentum_1m+'%', gc(f.momentum_1m)],
      ['Annualized Volatility', f.volatility_ann+'%', f.volatility_ann<30?G:R],
      ['Volume Momentum', f.volume_momentum+'%', gc(f.volume_momentum)],
      ['Risk-Adj Momentum', f.sharpe_momentum, gc(f.sharpe_momentum)],
    ], 'Fama-French & AQR factor model. Combines price momentum (12-1 month), short-term reversal, and volume momentum. AQR manages $100B+ using momentum factors. Sharpe momentum > 0.5 = strong signal.'));
  }

  // -- 7. Smart Money Index --
  if(m.smart_money) {
    const smi = m.smart_money;
    const sc = smi.signal === 'ACCUMULATING' ? G : smi.signal === 'DISTRIBUTING' ? R : D;
    cards.push(modelCard('SMART MONEY INDEX','Macro Hedge Funds - CTA Strategies', smi.signal, [
      ['SMI Z-Score', smi.smi_zscore, gc(smi.smi_zscore)],
      ['5-Day Trend', smi.trend_5d > 0 ? '- Rising' : '- Falling', gc(smi.trend_5d)],
      ['Interpretation', smi.signal === 'ACCUMULATING' ? '- Institutions buying' : smi.signal === 'DISTRIBUTING' ? '- Institutions selling' : '- Neutral activity', sc],
    ], 'Separates institutional (smart) money from retail (dumb) money. Theory: retail panics at open, institutions execute strategically at close. Rising SMI = institutions accumulating quietly.'));
  }

  grid.innerHTML = cards.join('');

  // -- Confluence Meter --
  const votes = [
    { label:'VWAP',    bull: m.vwap && ind.price < m.vwap?.vwap },
    { label:'Kalman',  bull: m.kalman?.signal === 'BULLISH' },
    { label:'Z-Score', bull: m.zscore?.zscore < -1 },
    { label:'Monte Carlo', bull: m.monte_carlo?.prob_up > 55 },
    { label:'Factor',  bull: ['BUY','STRONG_BUY'].includes(m.factor?.signal) },
    { label:'Smart $', bull: m.smart_money?.signal === 'ACCUMULATING' },
  ];
  const bullCount = votes.filter(v=>v.bull).length;
  const bearCount = votes.filter(v=>!v.bull).length;
  const needle    = bullCount / votes.length;           // 0=all bear, 1=all bull
  document.getElementById('confluenceNeedle').style.left = (needle * 100) + '%';
  document.getElementById('confluenceLabel').textContent =
    bullCount + '/6 BULLISH - ' + bearCount + '/6 BEARISH';
  document.getElementById('modelVotes').innerHTML = votes.map(v=>
    '<span style="font-size:9px;font-family:var(--font-mono);color:'+(v.bull?'var(--accent-green)':'var(--accent-red)')+';">'+(v.bull?'+':'-')+v.val+'%</span>'
  ).join('');
}

var _sqPoll = null;
var SQ_COLORS = {
  BUY:    {bg:'rgba(0,255,136,0.15)',border:'rgba(0,255,136,0.5)',text:'#00ff88'},
  SELL:   {bg:'rgba(255,51,85,0.15)',border:'rgba(255,51,85,0.5)',text:'#ff3355'},
  HOLD:   {bg:'rgba(0,229,255,0.12)',border:'rgba(0,229,255,0.35)',text:'#00e5ff'},
  WAIT:   {bg:'rgba(255,179,0,0.12)',border:'rgba(255,179,0,0.35)',text:'#ffb300'},
  CAUTION:{bg:'rgba(255,152,0,0.15)',border:'rgba(255,152,0,0.45)',text:'#ff9800'},
  AVOID:  {bg:'rgba(255,51,85,0.12)',border:'rgba(255,51,85,0.4)',text:'#ff3355'},
};
function triggerQuickRead() {
  var btn=document.getElementById('sqBtn'),spinner=document.getElementById('sqSpinner'),
      sentence=document.getElementById('sqSentence');
  if(btn){btn.disabled=true;btn.textContent='READING...';}
  if(spinner)spinner.style.display='inline';
  if(sentence)sentence.textContent='Consulting 100 years of market data...';
  fetch('/api/spock/quickread',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({ticker:_currentTicker})})
  .then(function(r){return r.json();})
  .then(function(){_pollQuickRead(0);})
  .catch(function(e){
    if(sentence)sentence.textContent='Error: '+e.message;
    if(btn){btn.disabled=false;btn.textContent='READ';}
    if(spinner)spinner.style.display='none';
  });
}
function _pollQuickRead(n) {
  if(_sqPoll)clearTimeout(_sqPoll);
  if(n>15){
    var s2=document.getElementById('sqSentence'),b=document.getElementById('sqBtn'),sp=document.getElementById('sqSpinner');
    if(s2)s2.textContent='Timed out - press READ to retry';
    if(b){b.disabled=false;b.textContent='READ';}if(sp)sp.style.display='none';return;
  }
  fetch('/api/spock/quickread/status').then(function(r){return r.json();}).then(function(d){
    if(d.running){_sqPoll=setTimeout(function(){_pollQuickRead(n+1);},1500);}
    else if(d.has_read&&d.quick_read){renderQuickRead(d.quick_read);}
    else if(n<3){_sqPoll=setTimeout(function(){_pollQuickRead(n+1);},1500);}
    else{var b=document.getElementById('sqBtn'),sp=document.getElementById('sqSpinner');
      if(b){b.disabled=false;b.textContent='READ';}if(sp)sp.style.display='none';}
  }).catch(function(){_sqPoll=setTimeout(function(){_pollQuickRead(n+1);},1500);});
}
function renderQuickRead(qr) {
  var action=(qr.action||'HOLD').toUpperCase(),col=SQ_COLORS[action]||SQ_COLORS.HOLD;
  var aEl=document.getElementById('sqAction'),sEl=document.getElementById('sqSentence'),
      tEl=document.getElementById('sqTime'),tkEl=document.getElementById('sqTicker'),
      btn=document.getElementById('sqBtn'),sp=document.getElementById('sqSpinner'),
      bar=document.getElementById('spockQuickBar');
  if(aEl){aEl.textContent=action;aEl.style.background=col.bg;aEl.style.borderColor=col.border;aEl.style.color=col.text;}
  if(sEl){sEl.textContent=qr.sentence||'';sEl.style.color=col.text;}
  if(tEl)tEl.textContent=qr.timestamp||'';
  if(tkEl)tkEl.textContent=qr.ticker||_currentTicker;
  if(bar)bar.style.borderTopColor=col.border;
  if(btn){btn.disabled=false;btn.textContent='READ';}
  if(sp)sp.style.display='none';
}
function _resetQuickReadBar(){
  var sEl=document.getElementById('sqSentence'),aEl=document.getElementById('sqAction'),tEl=document.getElementById('sqTime');
  if(sEl)sEl.textContent='Press READ to get SPOCK analysis for '+_currentTicker;
  if(aEl){aEl.textContent='—';aEl.style.color='#00e5ff';aEl.style.background='rgba(0,229,255,0.12)';aEl.style.borderColor='rgba(0,229,255,0.3)';}
  if(tEl)tEl.textContent='—';
}


function renderSpockPanel(ms) {
  if (!ms || typeof ms !== 'object') return;
  var action = ms.action || 'HOLD';
  var score  = ms.score  || 0;
  var conv   = ms.conviction || 0;
  var risk   = ms.risk   || 'MEDIUM';
  var color  = ms.color  || '#00e5ff';
  var reasons = ms.reasons || [];

  // Action text
  var actEl = document.getElementById('masterAction');
  if (actEl) {
    if (action && action.includes(' — ')) {
      var parts = action.split(' — ');
      actEl.innerHTML = '<span>' + parts[0] + '</span><div style="font-size:11px;letter-spacing:1px;margin-top:3px;opacity:0.7;">' + parts[1] + '</div>';
    } else {
      actEl.textContent = action || 'ANALYZING';
    }
    actEl.style.color = color;
  }

  // Score
  var scoreEl = document.getElementById('masterScore');
  if (scoreEl) { scoreEl.textContent = (score >= 0 ? '+' : '') + score; scoreEl.style.color = color; }

  // Conviction bar
  var convEl = document.getElementById('masterConv');
  if (convEl) { convEl.textContent = conv + '%'; convEl.style.color = color; }
  var barEl = document.getElementById('masterConvBar');
  if (barEl) { barEl.style.width = conv + '%'; barEl.style.background = color; }

  // Votes
  var bEl = document.getElementById('masterBulls');
  var nEl = document.getElementById('masterNeutral');
  var beEl = document.getElementById('masterBears');
  if (bEl)  bEl.textContent  = ms.bull_votes    || 0;
  if (nEl)  nEl.textContent  = ms.neutral_votes  || 0;
  if (beEl) beEl.textContent = ms.bear_votes     || 0;

  // Risk
  var riskEl = document.getElementById('masterRisk');
  if (riskEl) {
    riskEl.textContent = risk;
    riskEl.style.color = risk==='EXTREME'?'#ff1744':risk==='HIGH'?'#ff6d00':risk==='MEDIUM'?'#ffb300':'#00ff88';
  }

  // Reasons
  var reasonEl = document.getElementById('masterReasons');
  if (reasonEl && reasons.length) {
    reasonEl.innerHTML = reasons.slice(0,3).map(function(r){
      return '<div>▸ ' + r + '</div>';
    }).join('');
  }

  // Background glow
  var bg = document.getElementById('masterBg');
  if (bg) {
    var glow = action.includes('BUY')  ? 'rgba(0,255,136,0.05)'  :
               action.includes('SELL') ? 'rgba(255,23,68,0.05)'  :
                                         'rgba(0,10,20,0.95)';
    bg.style.background = glow;
  }
}

function renderMLPanel(ml) {
  if(!ml || typeof ml !== 'object') return;
  var G='#00ff88', R='#ff3355', C='#00e5ff', GO='var(--gold)';
  var sigColors={BUY:G, SELL:R, HOLD:C};
  var col = sigColors[ml.signal] || C;

  var sigEl=document.getElementById('mlSignal');
  if(sigEl){sigEl.textContent=ml.signal||'—';sigEl.style.color=col;}

  var confEl=document.getElementById('mlConf');
  if(confEl){confEl.textContent=(ml.confidence||0)+'%';confEl.style.color=col;}

  var prob=ml.probability||0.5;
  var probEl=document.getElementById('mlProb');
  if(probEl){probEl.textContent=Math.round(prob*100)+'%';probEl.style.color=prob>0.6?G:prob<0.4?R:C;}

  var barEl=document.getElementById('mlProbBar');
  if(barEl){
    barEl.style.width=Math.round(prob*100)+'%';
    barEl.style.background=prob>0.6?G:prob<0.4?R:C;
  }

  var aucEl=document.getElementById('mlAuc');
  if(aucEl&&ml.auc) aucEl.textContent=ml.auc;
  var hdrEl=document.getElementById('mlPanelHeader');
  if(hdrEl&&ml.auc&&ml.available) {
    hdrEl.textContent = (ml.model||'ENSEMBLE').toUpperCase()
      +' ('+(ml.n_models||1)+' models) - '+(ml.features_total||47)+' FEATURES - AUC '+ml.auc
      +(ml.model_agreement!==undefined?' - AGREE '+Math.round(ml.model_agreement*100)+'%':'');
  }

  var statusEl=document.getElementById('mlStatus');
  if(statusEl){
    if(ml.available){statusEl.textContent='ACTIVE';statusEl.style.color=G;}
    else if(ml.error){statusEl.textContent='ERROR: '+ml.error.slice(0,30);statusEl.style.color=R;}
    else{statusEl.textContent='RETRAINING...';statusEl.style.color='#ffb300';}
  }

  // Regime context from state
  var s2=window._lastState||{};
  var dv=s2.darthvader||{};
  var feat=dv.features||{};
  var atr=feat.atr_ratio||0;
  var vol=feat.realized_vol||0;
  var volRegEl=document.getElementById('mlVolRegime');
  if(volRegEl){
    var regime=atr>0.012||vol>0.6?'HIGH VOL':atr<0.006&&vol<0.3?'LOW VOL':'NORMAL';
    var rc=atr>0.012?G:atr<0.006?'#ff9800':C;
    volRegEl.textContent=regime;volRegEl.style.color=rc;
  }

  var now=new Date();
  var h=now.getHours()+now.getMinutes()/60;
  var timeEl=document.getElementById('mlTimeWindow');
  if(timeEl){
    var twin=h>=9.5&&h<10.25?'OPEN (HIGH EDGE)':h>=15.25&&h<16?'CLOSE (HIGH EDGE)':h>=11.75&&h<13?'LUNCH (LOW EDGE)':'MID SESSION';
    var tc=h>=9.5&&h<10.25||h>=15.25&&h<16?G:h>=11.75&&h<13?R:C;
    timeEl.textContent=twin;timeEl.style.color=tc;
  }

  var qualEl=document.getElementById('mlQuality');
  if(qualEl){
    var conf=ml.confidence||0;
    var q=conf>=60?'HIGH':conf>=40?'MEDIUM':'LOW';
    var qc=conf>=60?G:conf>=40?GO:R;
    qualEl.textContent=q+' ('+conf+'%)';qualEl.style.color=qc;
  }

  // Active factors
  var factEl=document.getElementById('mlFactors');
  if(factEl){
    var factors=[];
    var vix=(s2.spy_data||{}).vix||0;
    var rsi=(s2.indicators||{}).rsi||50;
    if(feat.ofi_zscore>1.5) factors.push({label:'OFI surge',col:G});
    if(rsi>70) factors.push({label:'RSI overbought ('+Math.round(rsi)+')',col:R});
    if(rsi<30) factors.push({label:'RSI oversold ('+Math.round(rsi)+')',col:G});
    if(vix>25) factors.push({label:'VIX elevated ('+vix+')',col:'#ff9800'});
    if(feat.vwap_dist>0.01) factors.push({label:'Above VWAP +'+((feat.vwap_dist||0)*100).toFixed(1)+'%',col:G});
    if(feat.vwap_dist<-0.01) factors.push({label:'Below VWAP '+((feat.vwap_dist||0)*100).toFixed(1)+'%',col:R});
    if(feat.vol_ratio>2) factors.push({label:'Vol surge '+((feat.vol_ratio||1)).toFixed(1)+'x',col:G});
    if(factors.length===0) factors.push({label:'No extreme signals',col:'var(--text-dim)'});
    factEl.innerHTML=factors.slice(0,5).map(function(f){
      return '<div style="font-size:9px;color:'+f.col+';padding:2px 0;">● '+f.label+'</div>';
    }).join('');
  }
}

function renderPOCStats(poc, price) {
  if(!poc || !poc.poc) return;
  var G='#00ff88', R='#ff3355', C='#00e5ff', GO='#c9a84c';

  var pocEl=document.getElementById('pocPrice');
  if(pocEl){pocEl.textContent='$'+poc.poc; pocEl.style.color=GO;}

  var vahEl=document.getElementById('pocVAH');
  if(vahEl){vahEl.textContent='$'+poc.vah; vahEl.style.color=C;}

  var valEl=document.getElementById('pocVAL');
  if(valEl){valEl.textContent='$'+poc.val; valEl.style.color=C;}

  var relEl=document.getElementById('pocRelative');
  if(relEl){
    var abv=price>poc.poc;
    relEl.textContent=(abv?'ABOVE':'BELOW')+' POC ('+Math.abs(poc.price_vs_poc).toFixed(1)+'%)';
    relEl.style.color=abv?G:R;
  }

  var vaEl=document.getElementById('pocInVA');
  if(vaEl){
    var inva=poc.in_va;
    vaEl.textContent=inva?'INSIDE VALUE AREA':'OUTSIDE VALUE AREA';
    vaEl.style.color=inva?G:GO;
  }

  var structEl=document.getElementById('pocStructure');
  if(structEl){
    var txt, col;
    if(price>poc.vah){txt='BULLISH — Price accepted above value';col=G;}
    else if(price<poc.val){txt='BEARISH — Price rejected below value';col=R;}
    else if(price>poc.poc){txt='NEUTRAL/BULL — Inside VA, above POC';col='#69f0ae';}
    else{txt='NEUTRAL/BEAR — Inside VA, below POC';col='#ff8a65';}
    structEl.textContent=txt; structEl.style.color=col;
  }
}

async function fetchState() {
  try {
    var resp = await fetch('/api/state');
    if(!resp.ok){ console.warn('fetchState HTTP ' + resp.status); return; }
    var data = await resp.json();
    try { updateUI(data); } catch(e) { console.error('updateUI: ' + e.message); }
  } catch(e) { console.warn('fetchState: ' + e.message); }
}
async function manualRefresh() { await fetch('/api/refresh'); setTimeout(fetchState,2000); }
showChartTab('price');
fetchState();
setInterval(fetchState,10000);
setTimeout(fetchState, 5000);
setTimeout(fetchState, 15000);
setTimeout(function(){ if(chart){ chart.resize(); chart.update(); } }, 300);
setTimeout(function(){ if(chart){ chart.resize(); chart.update(); } }, 2000);


// --------------------------------------------------------------
// DARTHVADER 2.0 - INSTITUTIONAL INTELLIGENCE FRONTEND
// --------------------------------------------------------------

var _dvCache = null;

function renderDarthVader(dv) {
  if(!dv) return;
  _dvCache = dv;

  var ts = dv.tsla_state   || {};
  var ps = dv.prob_signals || {};
  var ft = dv.features     || {};

  // -- State Engine ------------------------------------------
  var stateColor = ts.color || '#b388ff';

  var iconEl = document.getElementById('dvStateIcon');
  if(iconEl) iconEl.textContent = ts.icon || '-';

  var nameEl = document.getElementById('dvStateName');
  if(nameEl) { nameEl.textContent = (ts.state||'-').replace(/_/g,' '); nameEl.style.color = stateColor; }

  var descEl = document.getElementById('dvStateDesc');
  if(descEl) descEl.textContent = ts.desc || '-';

  var actEl = document.getElementById('dvStateAction');
  if(actEl) actEl.textContent = ts.action || '-';

  var confEl = document.getElementById('dvConfidence');
  if(confEl) { confEl.textContent = Math.round((ts.confidence||0)*100) + '%'; confEl.style.color = stateColor; }

  var pilotEl = document.getElementById('dvPilotMode');
  if(pilotEl) {
    var isAuto = ps.autopilot;
    pilotEl.textContent  = isAuto ? '- AUTOPILOT' : '---- PILOT MODE';
    pilotEl.style.background = isAuto ? 'rgba(0,255,136,0.15)' : 'rgba(255,214,0,0.15)';
    pilotEl.style.color      = isAuto ? '#00ff88' : '#ffd600';
    pilotEl.style.border     = '1px solid ' + (isAuto ? 'rgba(0,255,136,0.4)' : 'rgba(255,214,0,0.4)');
  }

  // State probability bars
  var barsEl = document.getElementById('dvStateBars');
  if(barsEl && ts.state_probs) {
    var stateColors = {
      TREND_EXPANSION:'#00ff88', MEAN_REVERSION:'#40c4ff', DEALER_GAMMA_PIN:'#ffd600',
      GAMMA_EXPANSION:'#ff9800', LIQUIDITY_VACUUM:'#ff3355', MACRO_RISK_OFF:'#b388ff'
    };
    var sorted = Object.entries(ts.state_probs).sort(function(a,b){ return b[1]-a[1]; });
    barsEl.innerHTML = sorted.map(function(entry) {
      var s = entry[0], p = entry[1];
      var col = stateColors[s] || '#888';
      var isActive = s === ts.state;
      return '<div style="display:flex;align-items:center;gap:8px;">'
           + '<div style="font-size:9px;color:'+(isActive?col:'var(--text-dim)')+';min-width:130px;letter-spacing:1px;">'
           + (isActive?'- ':'  ') + s.replace(/_/g,' ') + '</div>'
           + '<div style="flex:1;background:var(--bg2);height:5px;border-radius:2px;overflow:hidden;">'
           + '<div style="height:100%;background:'+col+';width:'+(p*100).toFixed(0)+'%;transition:width 0.8s;'
           + (isActive?'box-shadow:0 0 6px '+col+';':'') + '"></div></div>'
           + '<div style="font-family:var(--font-mono);font-size:9px;color:'+(isActive?col:'var(--text-dim)')+';min-width:30px;text-align:right;">'
           + Math.round(p*100)+'%</div>'
           + '</div>';
    }).join('');
  }

  // Detection signals
  var sigEl = document.getElementById('dvSignals');
  if(sigEl && ts.signals) {
    sigEl.innerHTML = ts.signals.map(function(s) {
      return '<div style="font-size:10px;color:var(--text-dim);padding:2px 0;border-left:2px solid '+stateColor+'44;padding-left:6px;">'
           + '- ' + s + '</div>';
    }).join('');
  }

  // -- Probabilistic Signals ---------------------------------
  var pBreak  = ps.prob_breakout_30m  || 0;
  var pDown   = ps.prob_breakdown_30m || 0;
  var pRevert = ps.prob_mean_revert   || 0;

  var pb = document.getElementById('dvPBreak');
  var pbBar = document.getElementById('dvPBreakBar');
  if(pb)    pb.textContent    = Math.round(pBreak*100) + '%';
  if(pbBar) pbBar.style.width = Math.round(pBreak*100) + '%';

  var pd = document.getElementById('dvPDown');
  var pdBar = document.getElementById('dvPDownBar');
  if(pd)    pd.textContent    = Math.round(pDown*100) + '%';
  if(pdBar) pdBar.style.width = Math.round(pDown*100) + '%';

  var pr = document.getElementById('dvPRevert');
  var prBar = document.getElementById('dvPRevertBar');
  if(pr)    pr.textContent    = Math.round(pRevert*100) + '%';
  if(prBar) prBar.style.width = Math.round(pRevert*100) + '%';

  // Expected move
  var emMean = document.getElementById('dvExpMean');
  var emStd  = document.getElementById('dvExpStd');
  if(emMean) {
    var m = ps.expected_move_pct || 0;
    emMean.textContent = (m >= 0 ? '+' : '') + m.toFixed(2) + '%';
    emMean.style.color = m >= 0 ? '#00ff88' : '#ff3355';
  }
  if(emStd) emStd.textContent = '-' + (ps.expected_std_pct || 0).toFixed(2) + '%';

  // Model reliability
  var relEl    = document.getElementById('dvReliability');
  var relBar   = document.getElementById('dvReliabilityBar');
  var qualEl   = document.getElementById('dvQuality');
  var rel      = ps.model_reliability || 0;
  var qCol     = ps.quality_color || '#ffd600';
  if(relEl)  { relEl.textContent = Math.round(rel*100) + '%'; relEl.style.color = qCol; }
  if(relBar) { relBar.style.width = Math.round(rel*100) + '%'; relBar.style.background = qCol; }
  if(qualEl) {
    qualEl.textContent = (ps.signal_quality || '-') + ' SIGNAL';
    qualEl.style.color = qCol;
    qualEl.style.background = qCol.replace(')', ',0.12)').replace('rgb', 'rgba').replace('#','').length > 6
      ? 'rgba(255,214,0,0.12)' : qCol + '22';
    qualEl.style.border = '1px solid ' + qCol + '55';
  }

  // -- Risk Intelligence / L2 Features ----------------------
  var rm = dv.risk_mode || 'NORMAL';
  var rmColor = dv.risk_color || '#00ff88';
  var rmBadge = document.getElementById('dvRiskModeBadge');
  var rmText  = document.getElementById('dvRiskMode');
  if(rmBadge) { rmBadge.style.borderColor = rmColor; rmBadge.style.background = dv.risk_bg||'rgba(0,255,136,0.08)'; }
  if(rmText)  { rmText.textContent = rm; rmText.style.color = rmColor; }

  // L2 feature cards
  function setFeature(id, val, unit, thresholds) {
    var el = document.getElementById(id);
    if(!el) return;
    el.textContent = val !== undefined && val !== null
      ? (typeof val === 'number' ? (val >= 0 && unit!=='%' ? '' : '') + val.toFixed(2) : val) + (unit||'')
      : '-';
    if(thresholds && typeof val === 'number') {
      el.style.color = val > thresholds.good ? '#00ff88'
                     : val < thresholds.bad  ? '#ff3355'
                     : '#ffd600';
    }
  }

  setFeature('dvOFI',       ft.ofi_ratio,   '', {good:0.5, bad:-0.5});
  setFeature('dvAggression',ft.aggression,  '', {good:0.15, bad:-0.15});
  setFeature('dvAbsorption',ft.absorption,  '', {good:1.5, bad:0.5});
  setFeature('dvVolRatio',  ft.vol_ratio,   'x', {good:1.3, bad:0.8});
  setFeature('dvTrend',     ft.trend_score, '', {good:5, bad:-5});
  setFeature('dvMom5',      ft.momentum_5,  '%', {good:1.0, bad:-1.0});
  setFeature('dvVacuum',    ft.vacuum,      '', {good:0.5, bad:2.0});

  var upd = document.getElementById('dvUpdated');
  if(upd) upd.textContent = dv.updated || '-';

  // -- DV 2.0 Master Intelligence Bar --------------------------

  // Market State cell
  var qIcon  = document.getElementById('dvQuickIcon');
  var qState = document.getElementById('dvQuickState');
  var qDesc2 = document.getElementById('dvStateDesc2');
  if(qIcon)  qIcon.textContent = ts.icon || 'ANALYZING';
  if(qState) { qState.textContent = (ts.state||'ANALYZING').replace(/_/g,' '); qState.style.color = stateColor; }
  if(qDesc2) qDesc2.textContent = ts.desc ? ts.desc.split('.')[0] + '.' : '';

  // System Confidence cell
  var qConf    = document.getElementById('dvQuickConf');
  var qConfBar = document.getElementById('dvQuickConfBar');
  var qPilot   = document.getElementById('dvQuickPilot');
  var confPct  = Math.round((ts.confidence||0)*100);
  if(qConf) { qConf.textContent = confPct + '%'; qConf.style.color = stateColor; }
  if(qConfBar) { qConfBar.style.width = confPct + '%'; qConfBar.style.background = stateColor; }
  if(qPilot) {
    var isAuto = ps.autopilot;
    qPilot.textContent = isAuto ? 'AUTO' : 'PILOT';
    qPilot.style.color = isAuto ? '#00ff88' : '#ffd600';
    qPilot.style.borderColor = isAuto ? 'rgba(0,255,136,0.4)' : 'rgba(255,214,0,0.4)';
  }

  // Risk Mode cell - dominant color signal (Change #5)
  var rm       = dv.risk_mode  || 'NORMAL';
  var rmColor  = dv.risk_color || '#00ff88';
  var rmBar    = document.getElementById('dvRiskModeBar');
  var qRisk    = document.getElementById('dvQuickRisk');
  var qRiskDesc= document.getElementById('dvRiskDesc');
  var rmDescs  = { NORMAL:'Standard positioning. Full size.',
                   CAUTIOUS:'Reduce size 25-50%. Tighter stops.',
                   DEFENSIVE:'Minimum size only. Protect capital.' };
  if(qRisk)    { qRisk.textContent = rm; qRisk.style.color = rmColor; }
  if(qRiskDesc){ qRiskDesc.textContent = rmDescs[rm]||''; qRiskDesc.style.color = rmColor+'aa'; }
  if(rmBar)    { rmBar.style.borderLeftColor = rmColor; }

  // Market Intent cell
  var pBreak  = ps.prob_breakout_30m  || 0;
  var pDown   = ps.prob_breakdown_30m || 0;
  var pRevert = ps.prob_mean_revert   || 0;
  var dominant = pBreak > pDown && pBreak > pRevert ? 'EXPANSION'
               : pDown  > pBreak && pDown  > pRevert ? 'CONTRACTION'
               : 'MEAN REVERSION';
  var intentMap = { EXPANSION:'Price seeks expansion above liquidity zone.',
                    CONTRACTION:'Distribution likely. Range compressing.',
                    'MEAN REVERSION':'Stretch condition. Reversion expected.' };
  var qIntent   = document.getElementById('dvMarketIntent');
  var qBreakPct = document.getElementById('dvBreakPct');
  if(qIntent)   { qIntent.textContent = intentMap[dominant]; qIntent.style.color = pBreak>pDown ? '#00ff88':'#ff3355'; }
  if(qBreakPct) qBreakPct.textContent = Math.round(pBreak*100) + '%';

  // Model reliability corner
  var qRel = document.getElementById('dvQuickRel');
  var rel  = ps.model_reliability || 0;
  if(qRel) { qRel.textContent = Math.round(rel*100)+'%'; qRel.style.color = rel>0.7?'#00ff88':rel>0.5?'#ffd600':'#ff3355'; }

  // -- Intent Narrative Bar --------------------------------------------------
  var narrative = document.getElementById('intentNarrative');
  var trendPers = document.getElementById('trendPersistence');
  var flowDisl  = document.getElementById('flowDislocation');
  var stretchC  = document.getElementById('stretchCondition');

  var sentence = (ts.state||'').replace(/_/g,' ') + ': '
    + (intentMap[dominant]||'-')
    + (rm !== 'NORMAL' ? ' Risk mode: '+rm+'.' : '')
    + (rel < 0.5 ? ' Low model confidence - use caution.' : '');
  if(narrative) narrative.textContent = sentence||'-';

  var mom5 = ft.momentum_5 || 0;
  if(trendPers) {
    trendPers.textContent = mom5 > 1 ? 'PERSISTING' : mom5 < -1 ? 'FADING' : 'NEUTRAL';
    trendPers.style.color = mom5 > 1 ? '#00ff88' : mom5 < -1 ? '#ff3355' : '#ffd600';
  }
  var ofi = ft.ofi_ratio || 0;
  if(flowDisl) {
    flowDisl.textContent = Math.abs(ofi) > 0.5 ? (ofi>0?'BUY DISLOC':'SELL DISLOC') : 'BALANCED';
    flowDisl.style.color = Math.abs(ofi) > 0.5 ? (ofi>0?'#00ff88':'#ff3355') : '#40c4ff';
  }
  var vac = ft.vacuum || 0;
  if(stretchC) {
    stretchC.textContent = vac > 2 ? 'EXTENDED' : vac > 1 ? 'MILD STRETCH' : 'NORMAL';
    stretchC.style.color = vac > 2 ? '#ff3355' : vac > 1 ? '#ff9800' : '#00ff88';
  }

  // Market Intent in DV state panel detail block
  var dvIF = document.getElementById('dvMarketIntentFull');
  if(dvIF) {
    dvIF.innerHTML = [
      '- ' + (intentMap[dominant]||ts.desc||'-'),
      '- Dealer positioning: ' + (rm==='NORMAL'?'supporting trend':rm==='CAUTIOUS'?'hedging exposure':'risk-off'),
      '- Expected behavior: ' + (dominant==='EXPANSION'?'directional move, elevated vol.':dominant==='CONTRACTION'?'range compression, reversion.':'choppy mean-revert, reduce size.'),
    ].map(function(l){ return '<div style="color:var(--text-dim);padding:2px 0;">'+l+'</div>'; }).join('');
  }
}

async function loadDarthVader() {
  try {
    var r = await fetch('/api/darthvader');
    var d = await r.json();
    renderDarthVader(d);
  } catch(e) {
    console.warn('DarthVader API error:', e);
  }
}

// Load with main state, and refresh independently every 60s
setInterval(loadDarthVader, 60000);
setTimeout(loadDarthVader, 3000);

// --------------------------------------------------------------
// DARTHVADER 2.0 - TICKER SEARCH - TOGGLE - AUTO-HIDE
// --------------------------------------------------------------

// Popular tickers list for dropdown
var TICKER_LIST = [
  {sym:'TSLA',name:'Tesla Inc',sector:'EV/Auto'},
  {sym:'NVDA',name:'NVIDIA Corp',sector:'Semiconductors'},
  {sym:'AAPL',name:'Apple Inc',sector:'Technology'},
  {sym:'MSFT',name:'Microsoft Corp',sector:'Technology'},
  {sym:'META',name:'Meta Platforms',sector:'Social Media'},
  {sym:'GOOGL',name:'Alphabet Inc',sector:'Technology'},
  {sym:'AMZN',name:'Amazon.com',sector:'E-Commerce'},
  {sym:'AMD',name:'Advanced Micro Devices',sector:'Semiconductors'},
  {sym:'PLTR',name:'Palantir Technologies',sector:'Data/AI'},
  {sym:'SPY',name:'S&P 500 ETF',sector:'ETF'},
  {sym:'QQQ',name:'Nasdaq 100 ETF',sector:'ETF'},
  {sym:'MSTR',name:'MicroStrategy',sector:'Bitcoin/Tech'},
  {sym:'COIN',name:'Coinbase Global',sector:'Crypto'},
  {sym:'NFLX',name:'Netflix Inc',sector:'Streaming'},
  {sym:'UBER',name:'Uber Technologies',sector:'Mobility'},
  {sym:'HOOD',name:'Robinhood Markets',sector:'Fintech'},
  {sym:'SOFI',name:'SoFi Technologies',sector:'Fintech'},
  {sym:'IONQ',name:'IonQ Inc',sector:'Quantum'},
  {sym:'RKLB',name:'Rocket Lab',sector:'Space'},
  {sym:'SMCI',name:'Super Micro Computer',sector:'AI/Servers'},
];
var _currentTicker   = 'TSLA';
var _filteredTickers = TICKER_LIST.slice();
var _ddHighlight     = -1;

function populateDropdown(filter) {
  var dd = document.getElementById('tickerDropdown');
  if(!dd) return;
  filter = (filter||'').toUpperCase().trim();
  _filteredTickers = filter
    ? TICKER_LIST.filter(function(t){ return t.sym.includes(filter) || t.name.toUpperCase().includes(filter); })
    : TICKER_LIST;
  _ddHighlight = -1;
  if(!_filteredTickers.length) {
    _filteredTickers = [{sym:filter, name:'Custom symbol', sector:''}];
  }
  // Build rows WITHOUT inline onclick - use data-sym + event delegation
  dd.innerHTML = _filteredTickers.map(function(t,i) {
    return '<div class="tkr-row" data-sym="' + t.sym + '" data-idx="' + i + '">'
         + '<span class="tkr-sym">' + t.sym + '</span>'
         + '<div style="display:flex;flex-direction:column;flex:1;overflow:hidden;min-width:0;">'
         + '<span class="tkr-name">' + t.name + '</span>'
         + '<span style="font-size:9px;color:#4a5280;letter-spacing:1px;">' + t.sector + '</span>'
         + '</div>'
         + '</div>';
  }).join('');
  // Wire clicks via event delegation (avoids any escaping issues)
  dd.querySelectorAll('.tkr-row').forEach(function(row) {
    row.addEventListener('mouseenter', function() { highlightRow(parseInt(this.dataset.idx)); });
    row.addEventListener('click', function() { selectTicker(this.dataset.sym); });
  });
}

function highlightRow(idx) {
  _ddHighlight = idx;
  var rows = document.querySelectorAll('#tickerDropdown .tkr-row');
  rows.forEach(function(r,i){
    r.classList.toggle('active', i===idx);
    r.style.background = i===idx ? 'rgba(0,255,136,0.12)' : '';
  });
}

function showTickerDropdown() {
  populateDropdown(document.getElementById('tickerSearchInput').value);
  var dd  = document.getElementById('tickerDropdown');
  var inp = document.getElementById('tickerSearchInput');
  if(!dd || !inp) return;
  var rect = inp.getBoundingClientRect();
  dd.style.left  = rect.left + 'px';
  dd.style.top   = (rect.bottom + 6) + 'px';
  dd.style.width = Math.max(300, rect.width) + 'px';
  dd.style.display = 'block';
}
function hideTickerDropdown() {
  var dd = document.getElementById('tickerDropdown');
  if(dd) dd.style.display = 'none';
}
function repositionDropdown() {
  var dd  = document.getElementById('tickerDropdown');
  var inp = document.getElementById('tickerSearchInput');
  if(!dd || dd.style.display === 'none' || !inp) return;
  var rect = inp.getBoundingClientRect();
  dd.style.left = rect.left + 'px';
  dd.style.top  = (rect.bottom + 6) + 'px';
}
window.addEventListener('scroll', repositionDropdown, true);
window.addEventListener('resize', repositionDropdown);
function filterTickerDropdown(val) { populateDropdown(val); showTickerDropdown(); repositionDropdown(); }

function handleTickerKey(e) {
  var rows = _filteredTickers;
  if(e.key === 'ArrowDown') { _ddHighlight = Math.min(_ddHighlight+1, rows.length-1); highlightRow(_ddHighlight); }
  else if(e.key === 'ArrowUp') { _ddHighlight = Math.max(_ddHighlight-1, 0); highlightRow(_ddHighlight); }
  else if(e.key === 'Enter') {
    if(_ddHighlight >= 0 && rows[_ddHighlight]) selectTicker(rows[_ddHighlight].sym);
    else if(rows.length) selectTicker(rows[0].sym);
  }
  else if(e.key === 'Escape') hideTickerDropdown();
}

function selectTicker(sym) {
  sym = sym.toUpperCase().trim();
  if(!sym) return;
  _currentTicker = sym;
  if(typeof _resetQuickReadBar==='function') _resetQuickReadBar();
  // Clear search box so it shows placeholder again
  var inp = document.getElementById('tickerSearchInput');
  if(inp) { inp.value = ''; inp.placeholder = 'Search symbol...'; }
  hideTickerDropdown();
  // Update the big display label
  var disp = document.getElementById('tickerDisplay');
  if(disp) disp.textContent = sym;
  // Update header logo
  var ht = document.getElementById('headerTicker');
  if(ht) ht.textContent = sym;
  // Update full name + sector
  var tn = document.getElementById('tickerFullName');
  var found = TICKER_LIST.find(function(t){ return t.sym===sym; });
  if(tn) tn.textContent = found ? found.name.toUpperCase() + ' - ' + found.sector : sym + ' - CUSTOM';
  // Trigger backend reload
  switchTicker(sym);
}

async function switchTicker(sym) {
  // Tell the backend to switch the active ticker
  try {
    var r = await fetch('/api/switch_ticker?ticker=' + sym);
    var d = await r.json();
    console.log('Ticker switched to', sym, d);
  } catch(e) {
    console.warn('switchTicker error:', e);
  }
  // Refresh all data panels
  manualRefresh();
  setTimeout(function(){ loadDarthVader(); }, 2000);
}

// -- Toggle panel collapse (Change #2) ----------------------------------------
var _collapsedPanels = {};
function togglePanel(panelId) {
  var panel = document.getElementById(panelId);
  if(!panel) return;
  var btn   = document.getElementById('btn-' + panelId);
  _collapsedPanels[panelId] = !_collapsedPanels[panelId];
  var collapsed = _collapsedPanels[panelId];

  // Find everything after the first child (the title)
  var children = Array.from(panel.children).slice(1);
  children.forEach(function(ch) {
    ch.style.display = collapsed ? 'none' : '';
  });
  if(btn) btn.textContent = collapsed ? '-' : '-';
  panel.style.paddingBottom = collapsed ? '0' : '';
}

// -- Auto-hide empty panels (Change #6) --------------------------------------
function autoHideEmptyPanels() {
  var panels = document.querySelectorAll('.panel[id]');
  panels.forEach(function(panel) {
    // Skip the primary DV blocks - always show
    var alwaysShow = ['dv-state-panel','dv-prob-panel','dv-risk-panel','nhl-panel'];
    if(alwaysShow.indexOf(panel.id) >= 0) return;

    // Check if panel has any non-dash, non-empty text content in data elements
    var dataEls = panel.querySelectorAll('[id]');
    var hasData = false;
    dataEls.forEach(function(el) {
      var txt = (el.textContent||'').trim();
      if(txt && txt !== '-' && txt !== '-%' && txt !== '0' && txt.length > 1) hasData = true;
    });
    // Only hide if no data at all
    if(!hasData && panel.style.display !== 'none') {
      panel.classList.add('panel-empty');
    } else {
      panel.classList.remove('panel-empty');
    }
  });
}

// --------------------------------------------------------------
// NEW HIGHS / NEW LOWS SCANNER
// --------------------------------------------------------------
var _nhlCache       = null;
var _nhlLoading     = false;
var _prevNHSymbols  = new Set();
var _prevNLSymbols  = new Set();

function renderNHL() {
  if(!_nhlCache) return;
  var highs = _nhlCache.new_highs || [];
  var lows  = _nhlCache.new_lows  || [];

  // Track which symbols are NEW this scan (just appeared)
  var curNH   = new Set(highs.map(function(h){ return h.symbol; }));
  var curNL   = new Set(lows.map(function(l){ return l.symbol; }));
  var newNH   = new Set([...curNH].filter(function(s){ return !_prevNHSymbols.has(s); }));
  var newNL   = new Set([...curNL].filter(function(s){ return !_prevNLSymbols.has(s); }));
  _prevNHSymbols = curNH;
  _prevNLSymbols = curNL;

  function makeRows(items, isHigh) {
    if(!items.length) {
      return '<div style="padding:12px 10px;color:var(--text-dim);font-size:10px;text-align:center;">'
           + (isHigh ? 'No new highs detected yet' : 'No new lows detected yet') + '</div>';
    }
    return items.map(function(r) {
      var mainColor  = isHigh ? '#00ff88' : '#ff3355';
      var isBreakout = r.is_new_high || r.is_new_low;
      var isNew      = isHigh ? newNH.has(r.symbol) : newNL.has(r.symbol);
      var flashClass = isNew ? (isHigh ? 'nhl-flash-high' : 'nhl-flash-low') : '';
      var newBadge   = isNew      ? '<span class="nhl-badge nhl-badge-new">NEW</span>'   : '';
      var brBadge    = isBreakout ? '<span class="nhl-badge nhl-badge-break">BREAK</span>': '';
      var volBadge   = (r.vol_surge && r.vol_surge > 2)
                       ? '<span class="nhl-badge nhl-badge-vol">VOL-'+r.vol_surge+'</span>' : '';
      return '<div class="'+flashClass+'" data-tkr="'+r.symbol+'"'
           + ' style="display:flex;align-items:center;justify-content:space-between;'
           + 'padding:6px 10px;border-bottom:1px solid rgba(255,255,255,0.04);cursor:pointer;'
           + 'border-left:3px solid '+(isHigh?'rgba(0,255,136,0.5)':'rgba(255,51,85,0.5)')+';"'
           + ''
           + '>'
           + '<div style="display:flex;align-items:center;gap:2px;">'
           + '<span style="font-family:var(--font-mono);font-size:12px;font-weight:700;color:'+mainColor+';min-width:52px;">'+r.symbol+'</span>'
           + newBadge + brBadge + volBadge
           + '</div>'
           + '<div style="font-family:var(--font-mono);font-size:11px;font-weight:700;color:'+mainColor+';">$'+r.price+'</div>'
           + '<div style="font-family:var(--font-mono);font-size:11px;color:'+mainColor+';min-width:46px;text-align:right;">'
           + (r.chg_pct >= 0 ? '+' : '') + r.chg_pct + '%</div>'
           + '</div>';
    }).join('');
  }

  var nhHTML = makeRows(highs, true);
  var nlHTML = makeRows(lows,  false);

  // Populate both scroll copies (for seamless loop)
  // Populate scrollable lists (no CSS animation cloning needed)
  var nhI1 = document.getElementById('nhlHighInner');
  var nlI1 = document.getElementById('nhlLowInner');
  if(nhI1) nhI1.innerHTML = nhHTML;
  if(nlI1) nlI1.innerHTML = nlHTML;

  // Wire click - switch ticker
  document.querySelectorAll('[data-tkr]').forEach(function(el) {
    el.addEventListener('click', function() {
      if(typeof switchTicker === 'function') switchTicker(this.getAttribute('data-tkr'));
    });
  });

  // Flash count badges gold if new entries appeared
  if(newNH.size > 0) {
    var el = document.getElementById('nhCount');
    if(el) { el.style.color = '#ffd600'; setTimeout(function(){ el.style.color = '#00ff88'; }, 2500); }
  }
  if(newNL.size > 0) {
    var el = document.getElementById('nlCount');
    if(el) { el.style.color = '#ffd600'; setTimeout(function(){ el.style.color = '#ff3355'; }, 2500); }
  }
}

async function loadNHL(force) {
  if(_nhlLoading) return;
  _nhlLoading = true;
  try {
    var r = await fetch('/api/new_highs_lows');
    var d = await r.json();
    _nhlCache = d;
    renderNHL();
    var upd = document.getElementById('nhlUpdated');
    if(upd) upd.textContent = d.updated || '-';
    var nhc = document.getElementById('nhCount');
    var nlc = document.getElementById('nlCount');
    var uni = document.getElementById('nhlUniverse');
    if(nhc) nhc.textContent = d.nh_count || 0;
    if(nlc) nlc.textContent = d.nl_count || 0;
    if(uni) uni.textContent = d.universe  || '-';
  } catch(e) {
    console.warn('loadNHL error:', e);
  }
  _nhlLoading = false;
}

// Poll every 20 seconds
setInterval(function(){ loadNHL(true); }, 20000);
// Initial load after 5s (let main data load first)
setTimeout(function(){ loadNHL(false); }, 5000);
// removed duplicate: setTimeout loadNHL(setInterval(function(){ loadNHL(true); }, 20000);
// Initial load after 5s (let main data load first)
setTimeout(function(){ loadNHL(false); }, 5000);



// ------------------------------------------------------------------------------
// ------------------------------------------------------------------------------

var _aiIntervalHandle = null;
var _aiRunning = false;








setInterval(function(){ loadNHL(true); }, 20000);
// Initial load after 5s (let main data load first)
setTimeout(function(){ loadNHL(false); }, 5000);
// -------------------------------------------------------
// SPOCK 2.0 -- Frontend JS

// =========================================================
// ALGO RADAR + SPOCK 2.0  --  Frontend JS
// Clean rewrite: no template literals, no regex ambiguity
// =========================================================

// ---- ALGO RADAR ------------------------------------------

function updateAlgoRadar(s) {
  var ft  = (s && s.darthvader && s.darthvader.features) ? s.darthvader.features : {};
  var ofi = parseFloat(ft.ofi_ratio   || 0);
  var agg = parseFloat(ft.aggression  || 0);
  var ab  = parseFloat(ft.absorption  || 0);
  var vac = parseFloat(ft.vacuum      || 0);
  var vel = parseFloat(ft.trend_score || 0);

  var G = '#00ff88', R = '#ff3355', A = '#ffb300', P = '#b388ff';

  // OFI gauge
  var ofiColor  = ofi > 2 ? G : ofi < -2 ? R : '#555555';
  var ofiFill   = Math.min(100, Math.max(0, 50 + ofi * 8));
  var ofiLabel  = ofi > 2 ? 'BUY PROGRAM' : ofi < -2 ? 'SELL PROGRAM' :
                  ofi > 0.5 ? 'BUY LEAN' : ofi < -0.5 ? 'SELL LEAN' : 'NEUTRAL';
  setAlgoGauge('algoOfi',   ofi.toFixed(2) + 'x', ofiFill,  ofiColor,  ofiLabel);

  // Aggression gauge
  var aggColor  = agg > 0.25 ? G : agg < -0.25 ? R : '#555555';
  var aggFill   = Math.min(100, Math.max(0, 50 + agg * 150));
  var aggLabel  = agg > 0.4 ? 'STRONG BUYERS' : agg > 0.25 ? 'BUYING AGGR' :
                  agg < -0.4 ? 'STRONG SELLERS' : agg < -0.25 ? 'SELLING AGGR' : 'PASSIVE';
  setAlgoGauge('algoAggr',  agg.toFixed(3),        aggFill,  aggColor,  aggLabel);

  // Absorption gauge
  var abColor   = ab > 2 ? A : ab > 1.5 ? '#ffcc44' : '#555555';
  var abFill    = Math.min(100, ab * 20);
  var abLabel   = ab > 3 ? 'HEAVY ABSORB' : ab > 2 ? 'ABSORBING' : ab > 1.5 ? 'MILD ABSORB' : 'PASSIVE';
  setAlgoGauge('algoAbsor', ab.toFixed(2),          abFill,   abColor,   abLabel);

  // Vacuum gauge
  var vacColor  = vac > 3 ? P : vac > 1.5 ? '#cc88ff' : '#555555';
  var vacFill   = Math.min(100, vac * 15);
  var vacLabel  = vac > 3 ? 'DANGER VACUUM' : vac > 1.5 ? 'THINNING' : 'NORMAL';
  setAlgoGauge('algoVac',   vac.toFixed(2),          vacFill,  vacColor,  vacLabel);

  // Velocity gauge
  var velColor  = vel >= 7 ? G : vel <= -7 ? R : vel > 3 ? '#80ff88' : vel < -3 ? '#ff8090' : '#555555';
  var velFill   = Math.min(100, Math.max(0, 50 + vel * 5));
  var velLabel  = vel >= 9 ? 'IGNITION' : vel >= 7 ? 'MOMENTUM UP' :
                  vel <= -9 ? 'COLLAPSE' : vel <= -7 ? 'MOMENTUM DOWN' :
                  vel > 3 ? 'LEAN UP' : vel < -3 ? 'LEAN DOWN' : 'NEUTRAL';
  setAlgoGauge('algoVel',   Math.round(vel) + '/10', velFill,  velColor,  velLabel);

  // Live dot
  var anyFiring = Math.abs(ofi) > 2 || Math.abs(agg) > 0.25 || ab > 2 || vac > 3 || Math.abs(vel) >= 7;
  var dot = document.getElementById('algoLiveIndicator');
  if (dot) {
    dot.style.background  = anyFiring ? G : '#444444';
    dot.style.boxShadow   = anyFiring ? '0 0 6px ' + G : 'none';
  }
  var stEl = document.getElementById('algoStatusText');
  if (stEl) {
    stEl.textContent = anyFiring ? 'SIGNAL FIRING' : 'Scanning...';
    stEl.style.color = anyFiring ? G : 'var(--text-dim)';
  }

  // Render alert banner from backend
  renderAlgoAlert(s.algo_alert || null);

  // Render history
  if (s.algo_history && s.algo_history.length) {
    renderAlgoHistory(s.algo_history);
  }
}

function setAlgoGauge(prefix, val, fillPct, color, label) {
  var vEl = document.getElementById(prefix + 'Val');
  var fEl = document.getElementById(prefix + 'BarFill');
  var lEl = document.getElementById(prefix + 'Label');
  if (vEl) { vEl.textContent = val;   vEl.style.color = color; }
  if (fEl) { fEl.style.width = fillPct + '%'; fEl.style.background = color; }
  if (lEl) { lEl.textContent = label; lEl.style.color = color; }
}

function renderAlgoAlert(alert) {
  var banner = document.getElementById('algoAlertBanner');
  if (!banner) { return; }
  if (!alert || !alert.label) { banner.style.display = 'none'; return; }

  var isBuy  = (alert.direction === 'BUY');
  var color  = isBuy ? '#00ff88' : '#ff3355';
  var bg     = isBuy ? 'rgba(0,255,136,0.07)' : 'rgba(255,51,85,0.07)';
  var border = isBuy ? 'rgba(0,255,136,0.3)'  : 'rgba(255,51,85,0.3)';

  banner.style.display      = 'block';
  banner.style.background   = bg;
  banner.style.borderTop    = '1px solid ' + border;
  banner.style.borderBottom = '1px solid ' + border;

  var iconEl  = document.getElementById('algoAlertIcon');
  var lblEl   = document.getElementById('algoAlertLabel');
  var detEl   = document.getElementById('algoAlertDetail');
  var priceEl = document.getElementById('algoAlertPrice');
  var timeEl  = document.getElementById('algoAlertTime');

  if (iconEl)  { iconEl.textContent = isBuy ? '\\u25b2' : '\\u25bc'; iconEl.style.color = color; }
  if (lblEl)   { lblEl.textContent  = alert.label   || '--'; lblEl.style.color = color; }
  if (detEl)   { detEl.textContent  = alert.detail  || '--'; }
  if (priceEl) { priceEl.textContent = '$' + (alert.price || '--'); priceEl.style.color = color; }
  if (timeEl)  { timeEl.textContent  = alert.timestamp || '--'; }
}

function renderAlgoHistory(history) {
  var el = document.getElementById('algoHistory');
  if (!el || !history || !history.length) { return; }
  var rows = '';
  var limit = Math.min(history.length, 8);
  for (var i = 0; i < limit; i++) {
    var a     = history[i];
    var isBuy = (a.direction === 'BUY');
    var c     = isBuy ? '#00ff88' : '#ff3355';
    var arrow = isBuy ? '\\u25b2' : '\\u25bc';
    var lbl   = a.label   || '';
    var det   = (a.detail || '').slice(0, 70);
    var px    = '$' + (a.price || '--');
    var ts    = a.timestamp || '';
    rows += '<div style="display:flex;gap:10px;align-items:center;padding:3px 0;border-bottom:1px solid rgba(255,255,255,0.04);">'
          + '<span style="color:' + c + ';font-size:10px;">' + arrow + '</span>'
          + '<span style="font-family:var(--font-mono);font-size:9px;color:' + c + ';min-width:140px;">' + lbl + '</span>'
          + '<span style="font-size:9px;color:var(--text-dim);flex:1;">' + det + '</span>'
          + '<span style="font-family:var(--font-mono);font-size:9px;color:#fff;">' + px + '</span>'
          + '<span style="font-size:8px;color:var(--text-dim);min-width:55px;text-align:right;">' + ts + '</span>'
          + '</div>';
  }
  el.innerHTML = rows;
}

function askSpockAlgo() {
  var panel = document.getElementById('spock-panel');
  if (panel) { panel.scrollIntoView({ behavior: 'smooth', block: 'start' }); }
  askSpock();
}

// ---- SPOCK 2.0 -------------------------------------------

function updateSpockPreview() {
  var sharesEl = document.getElementById('spockShares');
  var entryEl  = document.getElementById('spockEntry');
  var pnlEl    = document.getElementById('spockPnlPreview');
  var pctEl    = document.getElementById('spockPnlPct');
  if (!pnlEl) { return; }

  var shares = sharesEl ? parseFloat(sharesEl.value) || 0 : 0;
  var entry  = entryEl  ? parseFloat(entryEl.value)  || 0 : 0;

  // Get current price from page
  var priceEl = document.getElementById('lastPrice');
  var price   = priceEl ? parseFloat(priceEl.textContent.replace('$', '')) || 0 : 0;

  if (shares > 0 && entry > 0 && price > 0) {
    var pnl   = (price - entry) * shares;
    var pct   = ((price / entry) - 1) * 100;
    var color = pnl >= 0 ? '#00ff88' : '#ff3355';
    var sign  = pnl >= 0 ? '+' : '';
    pnlEl.textContent = sign + '$' + pnl.toFixed(2);
    pnlEl.style.color = color;
    pctEl.textContent = sign + pct.toFixed(2) + '%  |  ' + shares + ' shares @ $' + entry;
    pctEl.style.color = color;
  } else {
    pnlEl.textContent = 'Enter position';
    pnlEl.style.color = 'var(--text-dim)';
    if (pctEl) { pctEl.textContent = '--'; pctEl.style.color = 'var(--text-dim)'; }
  }
}

// Wire up live preview inputs
(function wireSpockInputs() {
  var ids = ['spockShares', 'spockEntry', 'spockPortfolio'];
  function attach() {
    ids.forEach(function(id) {
      var el = document.getElementById(id);
      if (el && !el._spockWired) {
        el.addEventListener('input', updateSpockPreview);
        el._spockWired = true;
      }
    });
  }
  attach();
  setTimeout(attach, 1500);
}());

function askSpock() {
  var portEl   = document.getElementById('spockPortfolio');
  var sharesEl = document.getElementById('spockShares');
  var entryEl  = document.getElementById('spockEntry');
  var btn      = document.getElementById('spockBtn');
  var statusEl = document.getElementById('spockStatus');

  var portfolio = portEl   ? (parseFloat(portEl.value)   || 100000) : 100000;
  var shares    = sharesEl ? (parseFloat(sharesEl.value) || 0)      : 0;
  var entry     = entryEl  ? (parseFloat(entryEl.value)  || 0)      : 0;

  if (shares <= 0 || entry <= 0) {
    if (statusEl) {
      statusEl.textContent = 'Enter shares and entry price first';
      statusEl.style.color = '#ff3355';
    }
    setTimeout(function() {
      if (statusEl) { statusEl.textContent = 'Ready'; statusEl.style.color = 'var(--text-dim)'; }
    }, 3000);
    return;
  }

  // Show loading
  var loadEl  = document.getElementById('spockLoading');
  var emptyEl = document.getElementById('spockEmpty');
  var outEl   = document.getElementById('spockOutput');
  if (loadEl)  { loadEl.style.display  = 'block'; }
  if (emptyEl) { emptyEl.style.display = 'none';  }
  if (outEl)   { outEl.style.display   = 'none';  }
  if (btn)     { btn.disabled = true; btn.style.opacity = '0.6'; btn.textContent = 'ANALYZING...'; }
  if (statusEl){ statusEl.textContent = 'Calling Claude API...'; statusEl.style.color = '#00e5ff'; }

  fetch('/api/spock', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ trigger: 'manual', portfolio: portfolio, shares: shares, entry_price: entry, ticker: _currentTicker })
  })
  .then(function(r) { return r.json(); })
  .then(function() {
    if (statusEl) { statusEl.textContent = 'Thinking... (0s)'; statusEl.style.color = '#00e5ff'; }
    _pollSpock(0);
  })
  .catch(function(err) {
    if (statusEl) { statusEl.textContent = 'Network error: ' + err.message; statusEl.style.color = '#ff3355'; }
    if (loadEl)  { loadEl.style.display = 'none'; }
    if (emptyEl) { emptyEl.style.display = 'block'; }
    if (btn) { btn.disabled = false; btn.style.opacity = '1'; btn.textContent = 'ANALYZE POSITION'; }
  });
}

var _spockPoll = null;
function _pollSpock(n) {
  if (_spockPoll) clearTimeout(_spockPoll);
  var btn=document.getElementById('spockAnalyzeBtn'),statusEl=document.getElementById('spockStatus'),
      loadEl=document.getElementById('spockLoading'),emptyEl=document.getElementById('spockEmpty');
  if (n > 20) {
    fetch('/api/spock/reset').catch(function(){});
    if (statusEl) { statusEl.textContent = 'Timed out - try again'; statusEl.style.color = '#ff3355'; }
    if (loadEl)  loadEl.style.display = 'none';
    if (emptyEl) emptyEl.style.display = 'block';
    if (btn) { btn.disabled = false; btn.style.opacity = '1'; btn.textContent = 'ANALYZE POSITION'; }
    return;
  }
  fetch('/api/spock/status').then(function(r){return r.json();}).then(function(d){
    if (d.running) {
      if (statusEl) statusEl.textContent = 'Thinking... (' + (n*2) + 's)';
      _spockPoll = setTimeout(function(){ _pollSpock(n+1); }, 2000);
    } else if (d.has_analysis && d.analysis) {
      renderSpockAnalysis(d.analysis);
      if (statusEl) { statusEl.textContent = 'Updated ' + (d.analysis.timestamp||''); statusEl.style.color = '#00ff88'; }
      if (btn) { btn.disabled = false; btn.style.opacity = '1'; btn.textContent = 'ANALYZE POSITION'; }
    } else if (n < 4) {
      _spockPoll = setTimeout(function(){ _pollSpock(n+1); }, 2000);
    } else {
      if (loadEl)  loadEl.style.display = 'none';
      if (emptyEl) emptyEl.style.display = 'block';
      if (btn) { btn.disabled = false; btn.style.opacity = '1'; btn.textContent = 'ANALYZE POSITION'; }
    }
  }).catch(function(){ _spockPoll = setTimeout(function(){ _pollSpock(n+1); }, 2000); });
}

function spockExtract(txt, label) {
  // Extract section content following a label like "SITUATION:"
  var lines   = txt.split('\\n');
  var result  = [];
  var found   = false;
  var labelUp = label.toUpperCase();
  // List of all possible section headers to detect end of section
  var headers = ['ACTION', 'CONFIDENCE', 'POSITION SAFETY', 'SELL PLAN',
                 'STOP LOSS', 'BIGGEST RISK', 'MARKET READ', 'WATCH FOR'];
  for (var i = 0; i < lines.length; i++) {
    var trimmed = lines[i].trim();
    var trimUp  = trimmed.toUpperCase();
    if (!found) {
      if (trimUp.indexOf(labelUp + ':') === 0) {
        found = true;
        var rest = trimmed.slice(label.length + 1).trim();
        if (rest) { result.push(rest); }
      }
    } else {
      // Check if this line starts a new section header
      var isHeader = false;
      for (var h = 0; h < headers.length; h++) {
        if (trimUp.indexOf(headers[h] + ':') === 0) { isHeader = true; break; }
      }
      if (isHeader) { break; }
      result.push(trimmed);
    }
  }
  return result.join('\\n').trim() || '--';
}

function spockFmtBullets(txt) {
  // Replace bullet chars at line start with styled arrow
  return (txt || '--').replace(/(\\n|^)[-*] /g, '$1&#9658; ');
}

function spockExtractPrice(txt) {
  // Pull first number sequence from a string (for price/stop values)
  var m = txt.match(/[0-9]+\\.?[0-9]*/);
  return m ? m[0] : null;
}

function spockParseSellPlan(txt) {
  // Returns array of 3 target objects: {price, size, why}
  var targets = [{}, {}, {}];
  var lines   = txt.split('\\n');
  for (var i = 0; i < lines.length; i++) {
    var line   = lines[i].trim();
    var lineUp = line.toUpperCase();
    var tIdx   = -1;
    if (lineUp.indexOf('T1') >= 0 || lineUp.indexOf('FIRST') >= 0) { tIdx = 0; }
    else if (lineUp.indexOf('T2') >= 0 || lineUp.indexOf('MAIN') >= 0)  { tIdx = 1; }
    else if (lineUp.indexOf('T3') >= 0 || lineUp.indexOf('FINAL') >= 0) { tIdx = 2; }
    if (tIdx >= 0) {
      // Price: first number after '$' or just first number
      var priceM = line.match(/\\$([0-9]+\\.?[0-9]*)/);
      if (priceM) { targets[tIdx].price = '$' + priceM[1]; }
      // Size: pattern like "40%" or "40% of position"
      var sizeM  = line.match(/([0-9]+)%/);
      if (sizeM) { targets[tIdx].size = 'Sell ' + sizeM[1] + '% of position'; }
      // Reason: text after "reason:"
      var rIdx = lineUp.indexOf('REASON:');
      if (rIdx >= 0) { targets[tIdx].why = line.slice(rIdx + 7).trim(); }
    }
  }
  return targets;
}

function renderSpockAnalysis(d) {
  var actionColors = {
    'BUY':    '#00ff88', 'ADD':    '#00ff88',
    'HOLD':   '#00e5ff', 'WAIT':   '#ffb300',
    'REDUCE': '#ff6d00', 'EXIT':   '#ff3355',
    'HEDGE':  '#b388ff'
  };
  var confColors = { 'HIGH': '#00ff88', 'MEDIUM': '#ffb300', 'LOW': '#ff3355' };

  var txt = d.full_text || '';

  // Action
  var action  = ((d.action || spockExtract(txt, 'ACTION')).replace(/[\\[\\]]/g, '')).trim().toUpperCase();
  var aEl     = document.getElementById('spockAction');
  if (aEl) { aEl.textContent = action; aEl.style.color = actionColors[action] || '#00e5ff'; }

  // Confidence
  var conf = ((d.confidence || spockExtract(txt, 'CONFIDENCE')).replace(/[\\[\\]]/g, '')).trim().toUpperCase();
  var cEl  = document.getElementById('spockConf');
  if (cEl) { cEl.textContent = conf; cEl.style.color = confColors[conf] || '#00e5ff'; }

  // Position safety
  var safety  = spockExtract(txt, 'POSITION SAFETY');
  var safeEl  = document.getElementById('spockSafe');
  if (safeEl) {
    var firstLine = safety.split('\\n')[0].toUpperCase();
    var isSafe    = firstLine.indexOf('YES') >= 0 || firstLine.indexOf('SAFE') >= 0;
    safeEl.textContent = isSafe ? 'YES' : 'NO';
    safeEl.style.color = isSafe ? '#00ff88' : '#ff3355';
  }

  // Meta
  var trigEl = document.getElementById('spockTrigger');
  var timeEl = document.getElementById('spockTime');
  if (trigEl) { trigEl.textContent = 'Triggered: ' + (d.trigger || 'manual'); }
  if (timeEl) { timeEl.textContent = 'At ' + (d.timestamp || '') + '  |  Price: $' + (d.price || ''); }

  // Sell plan
  var sellText = spockExtract(txt, 'SELL PLAN');
  var targets  = spockParseSellPlan(sellText);
  var tDefs = [
    ['spockT1Price', 'spockT1Size', 'spockT1Why'],
    ['spockT2Price', 'spockT2Size', 'spockT2Why'],
    ['spockT3Price', 'spockT3Size', 'spockT3Why']
  ];
  for (var ti = 0; ti < 3; ti++) {
    var t   = targets[ti] || {};
    var ids = tDefs[ti];
    var pEl = document.getElementById(ids[0]);
    var sEl = document.getElementById(ids[1]);
    var wEl = document.getElementById(ids[2]);
    if (pEl) { pEl.textContent = t.price || '--'; }
    if (sEl) { sEl.textContent = t.size  || '--'; }
    if (wEl) { wEl.textContent = t.why   || '--'; }
  }

  // Stop loss
  var stopTxt   = spockExtract(txt, 'STOP LOSS');
  var stopPrice = spockExtractPrice(stopTxt);
  var stopEl    = document.getElementById('spockStop');
  var stopNote  = document.getElementById('spockStopNote');
  if (stopEl)   { stopEl.textContent   = stopPrice ? '$' + stopPrice : '--'; }
  if (stopNote) { stopNote.textContent = stopTxt.replace(/[0-9]+\\.?[0-9]*/,'').replace(/\\$/g,'').trim() || 'Cut here. No negotiation.'; }

  // Risk, market read, watch for
  var riskEl   = document.getElementById('spockRisk');
  var mktEl    = document.getElementById('spockMarket');
  var watchEl  = document.getElementById('spockWatch');
  if (riskEl)  { riskEl.innerHTML  = spockFmtBullets(spockExtract(txt, 'BIGGEST RISK')); }
  if (mktEl)   { mktEl.innerHTML   = spockFmtBullets(spockExtract(txt, 'MARKET READ')); }
  if (watchEl) { watchEl.innerHTML = spockFmtBullets(spockExtract(txt, 'WATCH FOR')); }

  // Show output panels
  var loadEl  = document.getElementById('spockLoading');
  var emptyEl = document.getElementById('spockEmpty');
  var outEl   = document.getElementById('spockOutput');
  if (loadEl)  { loadEl.style.display  = 'none';  }
  if (emptyEl) { emptyEl.style.display = 'none';  }
  if (outEl)   { outEl.style.display   = 'block'; }
}

function spockSetText(id, val) {
  var el = document.getElementById(id);
  if (el) { el.textContent = val || '--'; }
}

function spockSetHTML(id, val) {
  var el = document.getElementById(id);
  if (el) { el.innerHTML = val || '--'; }
}

// Poll for auto-triggered analyses every 15s
function pollSpockStatus() {
  fetch('/api/spock/status')
  .then(function(r) { return r.json(); })
  .then(function(d) {
    if (!d.has_analysis || !d.analysis) { return; }
    var badge  = document.getElementById('spockTriggerBadge');
    var timeEl = document.getElementById('spockTime');
    var lastTs = timeEl ? timeEl.textContent : '';
    var newTs  = d.analysis.timestamp || '';
    if (newTs && lastTs.indexOf(newTs) < 0) {
      if (badge) {
        badge.textContent    = 'NEW: ' + (d.last_trigger || 'AUTO');
        badge.style.display  = 'inline-block';
      }
      renderSpockAnalysis(d.analysis);
      setTimeout(function() {
        if (badge) { badge.style.display = 'none'; }
      }, 10000);
    }
  })
  .catch(function() {});
}

setInterval(pollSpockStatus, 15000);
setTimeout(pollSpockStatus, 5000);
</script>
</head>
<body>

<!-- ═══ LIVE ALERT TICKER BAR ═══ -->
<div id="alertTicker" style="position:sticky;top:0;z-index:200;background:rgba(5,8,20,0.97);
  border-bottom:1px solid rgba(0,255,136,0.2);display:flex;align-items:center;
  overflow:hidden;height:36px;backdrop-filter:blur(8px);">
  <div style="flex-shrink:0;padding:0 14px;font-size:9px;letter-spacing:3px;
    color:var(--text-dim);border-right:1px solid var(--border);height:100%;
    display:flex;align-items:center;">LIVE SIGNALS</div>
  <div style="flex:1;overflow:hidden;position:relative;height:36px;">
    <div id="tickerScroll" style="display:flex;align-items:center;height:36px;
      white-space:nowrap;animation:tickerMove 50s linear infinite;">
      <span id="tickerContent" style="font-family:var(--font-mono);font-size:10px;padding-left:100%;">
        Initialising signal monitor...</span>
    </div>
  </div>
  <div style="flex-shrink:0;padding:0 16px;border-left:1px solid var(--border);height:100%;
    display:flex;align-items:center;gap:10px;">
    <span style="font-size:9px;color:var(--text-dim);">TSLA</span>
    <span id="tickerPrice" style="font-family:var(--font-mono);font-size:14px;font-weight:700;color:#00ff88;">—</span>
    <span id="tickerSignal" style="font-size:9px;letter-spacing:2px;padding:2px 8px;border-radius:2px;border:1px solid #ffb300;color:#ffb300;">HOLD</span>
  </div>
</div>
<style>
  @keyframes tickerMove { 0%{transform:translateX(0)} 100%{transform:translateX(-50%)} }
</style>

<header>
  <div>
    <div class="logo"><span id="headerTicker">TSLA</span> <span>//</span> BEHAVIORAL INTELLIGENCE</div>
    <div style="font-size:10px;color:var(--text-dim);letter-spacing:2px;margin-top:2px;">⚔️ DARTHVADER 2.0 · BEHAVIORAL STATE ENGINE · PROBABILISTIC SIGNALS · RISK INTELLIGENCE</div>
  </div>
  <div class="header-meta"><span class="live-dot"></span>LIVE<br><span id="clock"></span></div>
</header>

<div class="main-grid">

  <!-- ⚔️ DARTHVADER 2.0 — MASTER INTELLIGENCE BAR -->
  <!-- Ticker selector + price hero -->
  <div class="signal-panel" style="padding:16px 28px;gap:20px;">

    <!-- Ticker display + search -->
    <div style="display:flex;align-items:center;gap:12px;flex-shrink:0;">

      <!-- Big ticker display (non-editable label) -->
      <div>
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);font-family:var(--font-mono);margin-bottom:2px;">ACTIVE TICKER</div>
        <div id="tickerDisplay" style="font-family:var(--font-ui);font-weight:900;font-size:42px;color:#fff;letter-spacing:3px;line-height:1;">TSLA</div>
        <div id="tickerFullName" style="font-size:9px;color:var(--text-dim);letter-spacing:2px;margin-top:2px;">TESLA INC · NASDAQ</div>
        <div id="lastAlertTicker" style="font-size:8px;color:var(--text-dim);margin-top:1px;"></div>
      </div>

      <!-- Divider -->
      <div style="width:1px;height:56px;background:var(--border);flex-shrink:0;margin:0 4px;"></div>

      <!-- Visible search box -->
      <div style="display:flex;flex-direction:column;gap:4px;flex-shrink:0;">
        <div style="font-size:8px;letter-spacing:2px;color:var(--green);font-family:var(--font-mono);">SWITCH TICKER</div>
        <div style="position:relative;">
          <span style="position:absolute;left:9px;top:50%;transform:translateY(-50%);color:var(--green);font-size:13px;pointer-events:none;">⌕</span>
          <input id="tickerSearchInput" type="text" autocomplete="off" spellcheck="false"
            placeholder="Search symbol..."
            style="font-family:var(--font-mono);font-size:13px;color:#fff;font-weight:700;
                   background:var(--bg);border:1px solid rgba(0,255,136,0.5);border-radius:2px;
                   padding:8px 12px 8px 30px;width:190px;outline:none;letter-spacing:1px;
                   text-transform:uppercase;"
            oninput="filterTickerDropdown(this.value)"
            onkeydown="handleTickerKey(event)"
            onfocus="showTickerDropdown()"
            onblur="setTimeout(hideTickerDropdown,200)"/>
          <div id="tickerDropdown" style="display:none;position:fixed;z-index:99999;
            background:#0c0f1a;border:1px solid rgba(0,255,136,0.4);min-width:300px;max-height:340px;
            overflow-y:auto;box-shadow:0 8px 40px rgba(0,0,0,0.95);border-radius:2px;">
          </div>
        </div>
        <div style="font-size:8px;color:var(--text-dim);font-family:var(--font-mono);">↑↓ arrows · Enter to select</div>
      </div>

    </div>

    <!-- Price block -->
    <div style="flex-shrink:0;">
      <div class="price-label">LAST PRICE</div>
      <div class="price-value" id="priceVal">—</div>
    </div>

    <!-- ⚔️ MASTER STATE BAR — the 3-second read -->
    <div style="flex:1;display:grid;grid-template-columns:1fr 1fr 1fr 1fr;gap:1px;background:var(--border);margin:0 8px;">

      <!-- TSLA STATE -->
      <div style="background:var(--bg3);padding:10px 16px;display:flex;flex-direction:column;gap:3px;">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);">MARKET STATE</div>
        <div style="display:flex;align-items:center;gap:6px;">
          <span id="dvQuickIcon" style="font-size:16px;">⚡</span>
          <span id="dvQuickState" style="font-family:var(--font-mono);font-size:13px;font-weight:700;color:#b388ff;letter-spacing:1px;">ANALYZING</span>
        </div>
        <div id="dvStateDesc2" style="font-size:9px;color:var(--text-dim);line-height:1.3;"></div>
      </div>

      <!-- CONFIDENCE -->
      <div style="background:var(--bg3);padding:10px 16px;display:flex;flex-direction:column;gap:3px;">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);">SYSTEM CONFIDENCE</div>
        <div style="display:flex;align-items:baseline;gap:6px;">
          <span id="dvQuickConf" style="font-family:var(--font-mono);font-size:28px;font-weight:700;color:#b388ff;">—%</span>
          <span id="dvQuickPilot" style="font-size:8px;letter-spacing:1px;padding:2px 6px;border:1px solid rgba(0,255,136,0.3);color:#00ff88;border-radius:1px;">—</span>
        </div>
        <div style="background:var(--bg2);height:3px;border-radius:1px;overflow:hidden;">
          <div id="dvQuickConfBar" style="height:100%;background:#b388ff;width:0%;transition:width 1s;"></div>
        </div>
      </div>

      <!-- RISK MODE — dominant visual -->
      <div id="dvRiskModeBar" style="background:var(--bg3);padding:10px 16px;display:flex;flex-direction:column;gap:3px;border-left:3px solid #00ff88;">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);">RISK MODE</div>
        <div id="dvQuickRisk" style="font-family:var(--font-mono);font-size:26px;font-weight:700;color:#00ff88;letter-spacing:2px;">—</div>
        <div id="dvRiskDesc" style="font-size:9px;color:var(--text-dim);">Assessing environment...</div>
      </div>

      <!-- EXPECTED BEHAVIOR / MARKET INTENT -->
      <div style="background:var(--bg3);padding:10px 16px;display:flex;flex-direction:column;gap:3px;">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);">MARKET INTENT</div>
        <div id="dvMarketIntent" style="font-family:var(--font-mono);font-size:11px;font-weight:700;color:var(--gold);line-height:1.4;">—</div>
        <div id="dvQuickBreak" style="font-size:9px;color:var(--text-dim);">Breakout: <span id="dvBreakPct" style="color:#00ff88;">—%</span></div>
      </div>

    </div><!-- /master state bar -->

    <!-- Right: refresh + status -->
    <div style="display:flex;flex-direction:column;gap:8px;align-items:flex-end;flex-shrink:0;">
      <div id="waStatus" style="font-family:var(--font-mono);font-size:9px;padding:3px 8px;border-radius:2px;border:1px solid rgba(255,255,255,0.1);color:var(--text-dim);">⬤ WhatsApp checking...</div>
      <button class="btn-refresh" onclick="manualRefresh()">⟳ REFRESH</button>
      <div style="font-family:var(--font-mono);font-size:9px;color:var(--text-dim);">MODEL REL: <span id="dvQuickRel" style="color:#ffd600;">—%</span></div>
    </div>
    <div id="signalReasons" style="display:none;"></div>
  <div id="signalBadge" class="signal-badge HOLD" style="display:none;">HOLD</div>
  <div class="strength-bar-wrap" style="display:none;"><div class="strength-bar"><div class="strength-fill" id="strengthFill" style="width:0%"></div></div><div class="strength-val"><span id="strengthVal">0</span>/100</div></div>
  </div><!-- /signal-panel -->

  <!-- SYSTEM INTENT NARRATIVE BAR -->
  <div id="intentBar" style="background:rgba(138,43,226,0.06);border-top:1px solid rgba(138,43,226,0.2);
       padding:8px 28px;display:flex;align-items:center;gap:16px;grid-column:1/-1;">
    <span style="font-size:8px;letter-spacing:3px;color:#b388ff;flex-shrink:0;">⚔️ SYSTEM READS</span>
    <span id="intentNarrative" style="font-family:var(--font-mono);font-size:10px;color:var(--text);line-height:1.5;">
      Initializing behavioral analysis...
    </span>
    <div style="margin-left:auto;display:flex;gap:16px;flex-shrink:0;">
      <span style="font-size:8px;color:var(--text-dim);">TREND PERSISTENCE</span>
      <span id="trendPersistence" style="font-family:var(--font-mono);font-size:10px;color:var(--gold);">—</span>
      <span style="font-size:8px;color:var(--text-dim);">FLOW DISLOCATION</span>
      <span id="flowDislocation" style="font-family:var(--font-mono);font-size:10px;color:#40c4ff;">—</span>
      <span style="font-size:8px;color:var(--text-dim);">STRETCH CONDITION</span>
      <span id="stretchCondition" style="font-family:var(--font-mono);font-size:10px;color:#ff9800;">—</span>
    </div>
  </div>

  <!-- SPOCK QUICK READ BAR -->
  <div id="spockQuickBar" style="background:rgba(0,229,255,0.04);border-top:1px solid rgba(0,229,255,0.15);
       padding:7px 28px;display:flex;align-items:center;gap:12px;grid-column:1/-1;min-height:36px;">
    <span style="font-size:8px;letter-spacing:3px;color:#00e5ff;flex-shrink:0;">🖖 SPOCK READ</span>
    <span id="sqAction" style="font-family:var(--font-mono);font-size:11px;font-weight:700;
      padding:2px 10px;border-radius:1px;letter-spacing:1.5px;flex-shrink:0;
      background:rgba(0,229,255,0.12);color:#00e5ff;border:1px solid rgba(0,229,255,0.3);">—</span>
    <span id="sqSentence" style="font-family:var(--font-mono);font-size:10px;color:var(--text);
      flex:1;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;">
      Press READ to get SPOCK market analysis
    </span>
    <span id="sqSpinner" style="display:none;font-size:9px;color:#00e5ff;font-family:var(--font-mono);flex-shrink:0;">ANALYZING...</span>
    <span id="sqTime" style="font-size:8px;color:var(--text-dim);flex-shrink:0;font-family:var(--font-mono);">—</span>
    <span id="sqTicker" style="font-size:8px;color:var(--text-dim);font-family:var(--font-mono);
      padding:1px 6px;border:1px solid rgba(255,255,255,0.1);border-radius:1px;flex-shrink:0;">—</span>
    <button id="sqBtn" onclick="triggerQuickRead()"
      style="flex-shrink:0;background:rgba(0,229,255,0.08);border:1px solid rgba(0,229,255,0.4);
      color:#00e5ff;font-family:var(--font-mono);font-size:9px;letter-spacing:1.5px;
      padding:4px 14px;cursor:pointer;border-radius:1px;"
      onmouseover="this.style.background='rgba(0,229,255,0.2)'"
      onmouseout="this.style.background='rgba(0,229,255,0.08)'">READ</button>
  </div>



  <!-- CHART + NHL ROW — chart:3fr | NHL:340px -->
  <div style="display:grid;grid-template-columns:3fr 340px;gap:1px;background:var(--border);">

    <!-- LEFT: Chart -->
    <div class="panel chart-panel" style="display:flex;flex-direction:column;min-height:400px;">
      <div style="display:flex;gap:0;margin-bottom:12px;border-bottom:1px solid var(--border);">
        <button id="tabPrice" onclick="showChartTab('price')" style="background:none;border:none;border-bottom:2px solid var(--green);color:var(--green);font-family:var(--font-mono);font-size:10px;letter-spacing:2px;padding:8px 16px;cursor:pointer;margin-bottom:-1px;">PRICE</button>
        <button id="tabIchimoku" onclick="showChartTab('ichimoku')" style="background:none;border:none;border-bottom:2px solid transparent;color:var(--text-dim);font-family:var(--font-mono);font-size:10px;letter-spacing:2px;padding:8px 16px;cursor:pointer;margin-bottom:-1px;">ICHIMOKU CLOUD</button>
        <button id="tabHMM" onclick="showChartTab('hmm')" style="background:none;border:none;border-bottom:2px solid transparent;color:var(--text-dim);font-family:var(--font-mono);font-size:10px;letter-spacing:2px;padding:8px 16px;cursor:pointer;margin-bottom:-1px;">HMM REGIMES</button>
        <button id="tabMacd" onclick="showChartTab('macd')" style="background:none;border:none;border-bottom:2px solid transparent;color:var(--text-dim);font-family:var(--font-mono);font-size:10px;letter-spacing:2px;padding:8px 16px;cursor:pointer;margin-bottom:-1px;">MACD</button>
        <button id="tabVolume" onclick="showChartTab('volume')" style="background:none;border:none;border-bottom:2px solid transparent;color:var(--text-dim);font-family:var(--font-mono);font-size:10px;letter-spacing:2px;padding:8px 16px;cursor:pointer;margin-bottom:-1px;">VOLUME</button>
      </div>
      <div id="chartPrice"    style="flex:1;position:relative;height:340px;min-height:340px;"><canvas id="priceChart" width="800" height="340" style="width:100%;display:block;"></canvas></div>
      <div id="chartIchimoku" style="flex:1;position:relative;display:none;"><canvas id="ichimokuChart"></canvas></div>
      <div id="chartHmm"      style="flex:1;position:relative;display:none;"><canvas id="hmmChart"></canvas></div>
      <div id="chartMacd"     style="flex:1;position:relative;display:none;flex-direction:column;gap:4px;">
        <canvas id="macdLineChart" style="flex:1;"></canvas>
        <canvas id="macdHistChart" style="flex:0 0 80px;"></canvas>
      </div>
      <div id="chartVolume"   style="flex:1;position:relative;display:none;flex-direction:column;gap:4px;">
        <canvas id="volBarsChart"   style="flex:1;"></canvas>
        <!-- Volume Profile + POC Stats row -->
        <div style="display:grid;grid-template-columns:1fr 220px;gap:8px;height:160px;">
          <canvas id="volProfileChart" style="width:100%;height:160px;"></canvas>
          <!-- POC Stats sidebar -->
          <div id="pocStatsPanel" style="background:var(--bg2);border:1px solid rgba(201,168,76,0.4);
               border-radius:2px;padding:10px;display:flex;flex-direction:column;gap:6px;">
            <div style="font-size:8px;letter-spacing:2px;color:#c9a84c;margin-bottom:2px;">📊 VOL PROFILE</div>
            <div style="display:flex;justify-content:space-between;font-size:9px;">
              <span style="color:var(--text-dim);">POC</span>
              <span id="pocPrice" style="font-family:var(--font-mono);font-weight:700;color:#c9a84c;">—</span>
            </div>
            <div style="display:flex;justify-content:space-between;font-size:9px;">
              <span style="color:var(--text-dim);">VAH (70%)</span>
              <span id="pocVAH" style="font-family:var(--font-mono);color:#00e5ff;">—</span>
            </div>
            <div style="display:flex;justify-content:space-between;font-size:9px;">
              <span style="color:var(--text-dim);">VAL (70%)</span>
              <span id="pocVAL" style="font-family:var(--font-mono);color:#00e5ff;">—</span>
            </div>
            <div style="border-top:1px solid rgba(255,255,255,0.06);padding-top:5px;">
              <div id="pocRelative" style="font-size:9px;font-family:var(--font-mono);font-weight:700;">—</div>
              <div id="pocInVA" style="font-size:8px;margin-top:3px;color:var(--text-dim);">—</div>
            </div>
            <div style="border-top:1px solid rgba(255,255,255,0.06);padding-top:5px;">
              <div style="font-size:8px;color:var(--text-dim);margin-bottom:3px;">STRUCTURE</div>
              <div id="pocStructure" style="font-size:9px;line-height:1.4;">—</div>
            </div>
            <div style="margin-top:auto;font-size:7px;color:var(--text-dim);line-height:1.5;">
              POC = most traded price<br>
              VAH/VAL = 70% of vol zone<br>
              Above VAH = bullish acceptance<br>
              Below VAL = bearish rejection
            </div>
          </div>
        </div>
      </div>
    </div>

    <!-- RIGHT: Intraday New Highs / New Lows -->
    <div id="nhl-panel" style="background:var(--bg2);display:flex;flex-direction:column;overflow:hidden;">

      <div style="padding:10px 12px;border-bottom:1px solid var(--border);flex-shrink:0;background:var(--bg3);">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;font-weight:700;margin-bottom:8px;">📡 INTRADAY NH / NL</div>
        <div style="display:grid;grid-template-columns:1fr 1fr;gap:6px;margin-bottom:6px;">
          <div style="background:rgba(0,255,136,0.08);border:1px solid rgba(0,255,136,0.3);padding:8px;border-radius:2px;text-align:center;">
            <div style="font-size:8px;letter-spacing:1px;color:#00ff88;margin-bottom:2px;">▲ HIGHS</div>
            <div id="nhCount" style="font-family:var(--font-mono);font-size:24px;font-weight:700;color:#00ff88;line-height:1;">—</div>
          </div>
          <div style="background:rgba(255,51,85,0.08);border:1px solid rgba(255,51,85,0.3);padding:8px;border-radius:2px;text-align:center;">
            <div style="font-size:8px;letter-spacing:1px;color:#ff3355;margin-bottom:2px;">▼ LOWS</div>
            <div id="nlCount" style="font-family:var(--font-mono);font-size:24px;font-weight:700;color:#ff3355;line-height:1;">—</div>
          </div>
        </div>
        <div style="font-size:8px;color:var(--text-dim);">
          <span id="nhlUniverse" style="color:var(--gold);font-family:var(--font-mono);">—</span> tickers ·
          <span id="nhlUpdated" style="color:var(--text-dim);font-family:var(--font-mono);">—</span>
        </div>
      </div>

      <div style="flex:1;display:flex;flex-direction:column;min-height:0;border-bottom:1px solid rgba(0,255,136,0.12);">
        <div style="padding:5px 10px;background:rgba(0,255,136,0.05);border-bottom:1px solid rgba(0,255,136,0.1);font-size:8px;letter-spacing:2px;color:#00ff88;font-weight:700;flex-shrink:0;">▲ MAKING NEW HIGHS</div>
        <div id="nhlHighInner" style="overflow-y:auto;flex:1;scrollbar-width:thin;scrollbar-color:#1e2540 transparent;"></div>
      </div>

      <div style="flex:1;display:flex;flex-direction:column;min-height:0;">
        <div style="padding:5px 10px;background:rgba(255,51,85,0.05);border-bottom:1px solid rgba(255,51,85,0.1);font-size:8px;letter-spacing:2px;color:#ff3355;font-weight:700;flex-shrink:0;">▼ MAKING NEW LOWS</div>
        <div id="nhlLowInner" style="overflow-y:auto;flex:1;scrollbar-width:thin;scrollbar-color:#1e2540 transparent;"></div>
      </div>

    </div>

  </div>


  <!-- DV INTELLIGENCE ROW — STATE + PROB side by side -->
  <div style="display:grid;grid-template-columns:2fr 1fr;gap:1px;background:var(--border);">
  <!-- ═══ SPOCK MASTER SIGNAL PANEL ═══ -->
  <div class="panel" id="master-panel" style="grid-column:1/-1;padding:0;overflow:hidden;border:2px solid rgba(0,255,136,0.4);background:#000a12;">
    <div id="masterBg" style="padding:18px 24px;transition:background 0.5s;background:rgba(0,10,20,0.95);">
      <div style="display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:12px;">

        <!-- Action -->
        <div style="display:flex;align-items:center;gap:20px;">
          <div>
            <div style="font-size:9px;letter-spacing:3px;color:var(--text-dim);margin-bottom:4px;">SPOCK DECISION</div>
            <div id="masterAction" style="font-size:36px;font-weight:900;letter-spacing:4px;font-family:var(--font-mono);color:#00e5ff;">ANALYZING</div>
          </div>
          <div style="text-align:center;">
            <div style="font-size:9px;letter-spacing:2px;color:var(--text-dim);">SCORE</div>
            <div id="masterScore" style="font-size:28px;font-weight:700;font-family:var(--font-mono);color:#00e5ff;">—</div>
            <div style="font-size:9px;color:var(--text-dim);">/ 100</div>
          </div>
        </div>

        <!-- Conviction Meter -->
        <div style="flex:1;min-width:200px;max-width:350px;">
          <div style="display:flex;justify-content:space-between;margin-bottom:6px;">
            <span style="font-size:9px;letter-spacing:2px;color:var(--text-dim);">CONVICTION</span>
            <span id="masterConv" style="font-size:11px;font-weight:700;color:#00e5ff;">—%</span>
          </div>
          <div style="background:rgba(255,255,255,0.06);border-radius:4px;height:8px;overflow:hidden;">
            <div id="masterConvBar" style="height:100%;width:0%;background:#00ff88;border-radius:4px;transition:width 0.5s;"></div>
          </div>
          <div style="display:flex;justify-content:space-between;margin-top:8px;">
            <span style="font-size:9px;color:#00ff88;">● <span id="masterBulls">0</span> BULL</span>
            <span style="font-size:9px;color:var(--text-dim);"><span id="masterNeutral">0</span> NEUTRAL</span>
            <span style="font-size:9px;color:#ff3355;">● <span id="masterBears">0</span> BEAR</span>
          </div>
        </div>

        <!-- Risk + Reasons -->
        <div style="text-align:right;">
          <div style="margin-bottom:8px;">
            <span style="font-size:9px;letter-spacing:2px;color:var(--text-dim);">RISK </span>
            <span id="masterRisk" style="font-size:12px;font-weight:700;letter-spacing:2px;color:#ffb300;">—</span>
          </div>
          <div id="masterReasons" style="font-size:9px;color:var(--text-dim);text-align:right;max-width:300px;line-height:1.6;">
            Waiting for data...
          </div>
        </div>

      </div>
    </div>
  </div>

  <!-- PANEL A: TSLA STATE ENGINE -->
  <!-- ML DIRECTIONAL SIGNAL PANEL -->
  <div class="panel" id="ml-panel" style="grid-column:1/-1;border:2px solid rgba(0,229,255,0.3);background:rgba(0,10,20,0.98);">
    <div class="panel-title" onclick="togglePanel('ml-panel')" style="cursor:pointer;">
      🧠 ML DIRECTIONAL SIGNAL
      <span id="mlPanelHeader" style="font-size:9px;color:var(--text-dim);">ENSEMBLE · 67 FEATURES · AUC — · SCHWAB + SPY/QQQ + 5-MIN BARS</span>
      <span class="panel-collapse-btn" id="btn-ml-panel">▾</span>
    </div>
    <div style="display:grid;grid-template-columns:180px 1fr 1fr 1fr;gap:16px;align-items:start;">
      <div style="text-align:center;padding:20px 16px;background:var(--bg2);border-radius:2px;border:1px solid rgba(0,229,255,0.2);">
        <div style="font-size:8px;letter-spacing:3px;color:var(--text-dim);margin-bottom:8px;">ML SIGNAL</div>
        <div id="mlSignal" style="font-family:var(--font-mono);font-size:26px;font-weight:700;color:#00e5ff;letter-spacing:3px;">—</div>
        <div style="margin-top:10px;font-size:8px;color:var(--text-dim);">CONFIDENCE</div>
        <div id="mlConf" style="font-family:var(--font-mono);font-size:20px;font-weight:700;color:#00e5ff;">—%</div>
      </div>
      <div style="background:var(--bg2);padding:16px;border-radius:2px;border:1px solid rgba(255,255,255,0.06);">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:10px;">UP PROBABILITY (30 MIN)</div>
        <div style="display:flex;align-items:center;gap:10px;margin-bottom:6px;">
          <div style="flex:1;height:8px;background:rgba(255,255,255,0.08);border-radius:4px;overflow:hidden;">
            <div id="mlProbBar" style="height:100%;width:50%;background:#00e5ff;transition:width 0.6s;border-radius:4px;"></div>
          </div>
          <span id="mlProb" style="font-family:var(--font-mono);font-size:13px;color:#00e5ff;min-width:38px;">50%</span>
        </div>
        <div style="display:flex;justify-content:space-between;font-size:8px;color:var(--text-dim);margin-bottom:12px;">
          <span>SELL</span><span>NEUTRAL</span><span>BUY</span>
        </div>
        <div id="mlFactors" style="display:flex;flex-direction:column;gap:4px;">
          <div style="font-size:9px;color:var(--text-dim);">Awaiting model...</div>
        </div>
      </div>
      <div style="background:var(--bg2);padding:16px;border-radius:2px;border:1px solid rgba(255,255,255,0.06);">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:10px;">REGIME CONTEXT</div>
        <div style="display:flex;flex-direction:column;gap:8px;">
          <div style="display:flex;justify-content:space-between;font-size:9px;">
            <span style="color:var(--text-dim);">VOL REGIME</span>
            <span id="mlVolRegime" style="font-family:var(--font-mono);color:var(--text-primary);">—</span>
          </div>
          <div style="display:flex;justify-content:space-between;font-size:9px;">
            <span style="color:var(--text-dim);">TIME WINDOW</span>
            <span id="mlTimeWindow" style="font-family:var(--font-mono);color:var(--text-primary);">—</span>
          </div>
          <div style="display:flex;justify-content:space-between;font-size:9px;">
            <span style="color:var(--text-dim);">SIGNAL QUALITY</span>
            <span id="mlQuality" style="font-family:var(--font-mono);color:var(--text-primary);">—</span>
          </div>
          <div style="display:flex;justify-content:space-between;font-size:9px;">
            <span style="color:var(--text-dim);">MODEL AUC</span>
            <span id="mlAuc" style="font-family:var(--font-mono);color:var(--gold);">—</span>
          </div>
          <div style="display:flex;justify-content:space-between;font-size:9px;">
            <span style="color:var(--text-dim);">MODEL STATUS</span>
            <span id="mlStatus" style="font-family:var(--font-mono);color:var(--text-dim);">—</span>
          </div>
        </div>
      </div>
      <div style="background:var(--bg2);padding:16px;border-radius:2px;border:1px solid rgba(255,255,255,0.06);">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:10px;">BACKTEST STATS</div>
        <div style="display:flex;flex-direction:column;gap:6px;font-size:9px;">
          <div style="display:flex;justify-content:space-between;">
            <span style="color:var(--text-dim);">Win Rate @60%</span>
            <span style="font-family:var(--font-mono);color:#00ff88;">51.7%</span>
          </div>
          <div style="display:flex;justify-content:space-between;">
            <span style="color:var(--text-dim);">Profit Factor</span>
            <span style="font-family:var(--font-mono);color:#00ff88;">1.53x</span>
          </div>
          <div style="display:flex;justify-content:space-between;">
            <span style="color:var(--text-dim);">Avg Win</span>
            <span style="font-family:var(--font-mono);color:#00ff88;">+0.71%</span>
          </div>
          <div style="display:flex;justify-content:space-between;">
            <span style="color:var(--text-dim);">Avg Loss</span>
            <span style="font-family:var(--font-mono);color:#ff3355;">-0.50%</span>
          </div>
          <div style="margin-top:8px;font-size:8px;color:var(--text-dim);line-height:1.6;">
            Trained on 60 days · 4,463 bars<br>
            Top signals: ATR · Time · Volume · VIX · OFI
          </div>
        </div>
      </div>
    </div>
  </div>


  <div class="panel" id="dv-state-panel" style="border:2px solid rgba(138,43,226,0.8);background:rgba(138,43,226,0.06);box-shadow:0 0 24px rgba(138,43,226,0.12);padding:18px;">
    <div style="display:flex;align-items:center;gap:10px;margin-bottom:14px;">
      <span style="font-family:var(--font-mono);font-size:11px;letter-spacing:3px;color:#b388ff;">
        ⚔️ DARTHVADER 2.0 — BEHAVIORAL STATE ENGINE
      </span>
      <span style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-left:auto;">
        L6 META CONTROLLER · UPDATES <span id="dvUpdated" style="color:#b388ff;">—</span>
      </span>
    </div>

    <!-- Master State Card -->
    <div style="display:grid;grid-template-columns:auto 1fr auto;gap:16px;align-items:center;
                background:var(--bg3);border:1px solid var(--border);padding:16px;
                border-radius:2px;margin-bottom:14px;">

      <!-- State icon + name -->
      <div style="text-align:center;">
        <div id="dvStateIcon" style="font-size:48px;line-height:1;">📊</div>
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-top:4px;">CURRENT STATE</div>
      </div>

      <div>
        <div id="dvStateName" style="font-family:var(--font-mono);font-size:24px;font-weight:700;color:#b388ff;letter-spacing:2px;">ANALYZING...</div>
        <div id="dvStateDesc" style="font-size:13px;color:var(--text-dim);margin-top:6px;line-height:1.6;">—</div>
        <div id="dvStateAction" style="font-size:10px;color:var(--gold);margin-top:6px;line-height:1.5;font-style:italic;">—</div>
      </div>

      <div style="text-align:right;">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:4px;">CONFIDENCE</div>
        <div id="dvConfidence" style="font-family:var(--font-mono);font-size:36px;font-weight:700;color:#b388ff;">—%</div>
        <div id="dvPilotMode" style="font-size:8px;letter-spacing:1px;margin-top:4px;padding:2px 8px;border-radius:2px;">—</div>
      </div>
    </div>

    <!-- Market Intent — What the system believes the market wants to do -->
    <div style="background:rgba(138,43,226,0.06);border:1px solid rgba(138,43,226,0.2);padding:12px;border-radius:2px;margin-bottom:14px;">
      <div style="font-size:8px;letter-spacing:3px;color:#b388ff;margin-bottom:6px;">⚔️ MARKET INTENT</div>
      <div id="dvMarketIntentFull" style="font-family:var(--font-mono);font-size:10px;color:var(--text);line-height:1.8;">Analyzing behavioral state...</div>
    </div>

    <!-- State probability bars -->
    <div style="font-size:9px;letter-spacing:2px;color:var(--text-dim);margin-bottom:8px;">STATE PROBABILITY DISTRIBUTION</div>
    <div id="dvStateBars" style="display:flex;flex-direction:column;gap:5px;"></div>

    <!-- Detection signals -->
    <div style="margin-top:12px;">
      <div style="font-size:9px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">DETECTION SIGNALS</div>
      <div id="dvSignals" style="display:flex;flex-direction:column;gap:3px;"></div>
    </div>
  </div>

  <!-- PANEL B: PROBABILISTIC SIGNAL ENGINE -->
  <div class="panel" id="dv-prob-panel" style="border:1px solid rgba(0,255,136,0.2);background:rgba(0,255,136,0.02);padding:18px;">
    <div style="font-size:9px;letter-spacing:3px;color:#00ff88;margin-bottom:14px;">
      🎲 PROBABILISTIC SIGNAL ENGINE — L3
    </div>

    <!-- 3 probability gauges -->
    <div style="display:flex;flex-direction:column;gap:10px;margin-bottom:16px;">

      <div>
        <div style="display:flex;justify-content:space-between;font-size:9px;margin-bottom:3px;">
          <span style="color:#00ff88;letter-spacing:1px;">BREAKOUT (30m)</span>
          <span id="dvPBreak" style="font-family:var(--font-mono);color:#00ff88;font-weight:700;">—%</span>
        </div>
        <div style="background:var(--bg2);height:8px;border-radius:2px;overflow:hidden;">
          <div id="dvPBreakBar" style="height:100%;background:#00ff88;width:0%;transition:width 0.8s;"></div>
        </div>
      </div>

      <div>
        <div style="display:flex;justify-content:space-between;font-size:9px;margin-bottom:3px;">
          <span style="color:#ff3355;letter-spacing:1px;">BREAKDOWN (30m)</span>
          <span id="dvPDown" style="font-family:var(--font-mono);color:#ff3355;font-weight:700;">—%</span>
        </div>
        <div style="background:var(--bg2);height:8px;border-radius:2px;overflow:hidden;">
          <div id="dvPDownBar" style="height:100%;background:#ff3355;width:0%;transition:width 0.8s;"></div>
        </div>
      </div>

      <div>
        <div style="display:flex;justify-content:space-between;font-size:9px;margin-bottom:3px;">
          <span style="color:#40c4ff;letter-spacing:1px;">MEAN REVERT</span>
          <span id="dvPRevert" style="font-family:var(--font-mono);color:#40c4ff;font-weight:700;">—%</span>
        </div>
        <div style="background:var(--bg2);height:8px;border-radius:2px;overflow:hidden;">
          <div id="dvPRevertBar" style="height:100%;background:#40c4ff;width:0%;transition:width 0.8s;"></div>
        </div>
      </div>

    </div>

    <!-- Expected move -->
    <div style="background:var(--bg3);border:1px solid var(--border);padding:10px;border-radius:2px;margin-bottom:12px;">
      <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">EXPECTED MOVE (1H)</div>
      <div style="display:flex;justify-content:space-between;align-items:baseline;">
        <div>
          <span style="font-size:8px;color:var(--text-dim);">Mean: </span>
          <span id="dvExpMean" style="font-family:var(--font-mono);font-size:13px;font-weight:700;color:var(--gold);">—%</span>
        </div>
        <div>
          <span style="font-size:8px;color:var(--text-dim);">±1σ: </span>
          <span id="dvExpStd" style="font-family:var(--font-mono);font-size:13px;color:var(--text-dim);">—%</span>
        </div>
      </div>
    </div>

    <!-- Model reliability -->
    <div style="background:var(--bg3);border:1px solid var(--border);padding:10px;border-radius:2px;">
      <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">MODEL RELIABILITY</div>
      <div style="display:flex;justify-content:space-between;align-items:center;">
        <div id="dvReliability" style="font-family:var(--font-mono);font-size:22px;font-weight:700;">—</div>
        <div id="dvQuality" style="font-size:9px;letter-spacing:2px;padding:3px 8px;border-radius:2px;">—</div>
      </div>
      <div style="background:var(--bg2);height:4px;border-radius:2px;margin-top:6px;overflow:hidden;">
        <div id="dvReliabilityBar" style="height:100%;background:#00ff88;width:0%;transition:width 1s;"></div>
      </div>
    </div>
  </div>

  </div>  <!-- /DV intelligence row -->

  <!-- PANEL C: RISK INTELLIGENCE + L2 FEATURES -->
  <div class="panel" id="dv-risk-panel" style="
      grid-column:1/-1;
      border:1px solid rgba(255,152,0,0.2);
      background:rgba(255,152,0,0.01);
      padding:16px;
  ">
    <div style="font-size:9px;letter-spacing:3px;color:#ff9800;margin-bottom:12px;">
      🛡 RISK INTELLIGENCE — L4 ENGINE · L2 ORDER FLOW FEATURES
    </div>

    <div style="display:grid;grid-template-columns:auto 1fr 1fr 1fr 1fr 1fr 1fr 1fr;gap:12px;align-items:center;">

      <!-- Risk Mode badge -->
      <div id="dvRiskModeBadge" style="
          padding:12px 20px;text-align:center;border-radius:2px;
          border:2px solid #00ff88;background:rgba(0,255,136,0.08);
          min-width:90px;">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:4px;">RISK MODE</div>
        <div id="dvRiskMode" style="font-family:var(--font-mono);font-size:14px;font-weight:700;color:#00ff88;">NORMAL</div>
      </div>

      <!-- L2 Feature cards -->
      <div style="text-align:center;">
        <div style="font-size:8px;letter-spacing:1px;color:var(--text-dim);margin-bottom:3px;">FLOW DISLOCATION</div>
        <div id="dvOFI" style="font-family:var(--font-mono);font-size:14px;font-weight:700;color:var(--text-primary);">—</div>
        <div style="font-size:8px;color:var(--text-dim);">institutional signal</div>
      </div>
      <div style="text-align:center;">
        <div style="font-size:8px;letter-spacing:1px;color:var(--text-dim);margin-bottom:3px;">AGGRESSION</div>
        <div id="dvAggression" style="font-family:var(--font-mono);font-size:14px;font-weight:700;">—</div>
        <div style="font-size:8px;color:var(--text-dim);">buy/sell pressure</div>
      </div>
      <div style="text-align:center;">
        <div style="font-size:8px;letter-spacing:1px;color:var(--text-dim);margin-bottom:3px;">ABSORPTION</div>
        <div id="dvAbsorption" style="font-family:var(--font-mono);font-size:14px;font-weight:700;color:var(--text-primary);">—</div>
        <div style="font-size:8px;color:var(--text-dim);">institutional</div>
      </div>
      <div style="text-align:center;">
        <div style="font-size:8px;letter-spacing:1px;color:var(--text-dim);margin-bottom:3px;">VOL RATIO</div>
        <div id="dvVolRatio" style="font-family:var(--font-mono);font-size:14px;font-weight:700;">—</div>
        <div style="font-size:8px;color:var(--text-dim);">expand/contract</div>
      </div>
      <div style="text-align:center;">
        <div style="font-size:8px;letter-spacing:1px;color:var(--text-dim);margin-bottom:3px;">TREND SCORE</div>
        <div id="dvTrend" style="font-family:var(--font-mono);font-size:14px;font-weight:700;">—</div>
        <div style="font-size:8px;color:var(--text-dim);">bars in direction</div>
      </div>
      <div style="text-align:center;">
        <div style="font-size:8px;letter-spacing:1px;color:var(--text-dim);margin-bottom:3px;">MOM 5B</div>
        <div id="dvMom5" style="font-family:var(--font-mono);font-size:14px;font-weight:700;">—</div>
        <div style="font-size:8px;color:var(--text-dim);">persistence score</div>
      </div>
      <div style="text-align:center;">
        <div style="font-size:8px;letter-spacing:1px;color:var(--text-dim);margin-bottom:3px;">VACUUM</div>
        <div id="dvVacuum" style="font-family:var(--font-mono);font-size:14px;font-weight:700;">—</div>
        <div style="font-size:8px;color:var(--text-dim);">vacuum risk</div>
      </div>

    </div>
  </div>

  <!-- ═══ POC / VOLUME PROFILE PANEL ═══ -->
  <div class="panel" id="poc-panel" style="grid-column:1/-1;border:1px solid rgba(201,168,76,0.5);background:rgba(15,12,0,0.98);">
    <div class="panel-title" onclick="togglePanel('poc-panel')" style="cursor:pointer;">
      📊 Volume Profile — POC · Value Area · Market Structure
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;margin-left:12px;">60-DAY · $1 PRICE BUCKETS · 70% VALUE AREA</span>
      <span class="panel-collapse-btn" id="btn-poc-panel">▾</span>
    </div>

    <!-- TOP ROW: Key POC numbers -->
    <div style="display:grid;grid-template-columns:repeat(6,1fr);gap:10px;margin-bottom:16px;">

      <div style="background:rgba(201,168,76,0.12);border:2px solid rgba(201,168,76,0.6);padding:14px;border-radius:2px;text-align:center;">
        <div style="font-size:8px;letter-spacing:3px;color:#c9a84c;margin-bottom:5px;">POC</div>
        <div id="pocPanelPrice" style="font-family:var(--font-mono);font-size:22px;font-weight:700;color:#c9a84c;">—</div>
        <div style="font-size:8px;color:var(--text-dim);margin-top:4px;">Most traded price (60d)</div>
      </div>

      <div style="background:rgba(0,229,255,0.08);border:1px solid rgba(0,229,255,0.4);padding:14px;border-radius:2px;text-align:center;">
        <div style="font-size:8px;letter-spacing:3px;color:#00e5ff;margin-bottom:5px;">VAH</div>
        <div id="pocPanelVAH" style="font-family:var(--font-mono);font-size:20px;font-weight:700;color:#00e5ff;">—</div>
        <div style="font-size:8px;color:var(--text-dim);margin-top:4px;">Value Area High (70%)</div>
      </div>

      <div style="background:rgba(0,229,255,0.08);border:1px solid rgba(0,229,255,0.4);padding:14px;border-radius:2px;text-align:center;">
        <div style="font-size:8px;letter-spacing:3px;color:#00e5ff;margin-bottom:5px;">VAL</div>
        <div id="pocPanelVAL" style="font-family:var(--font-mono);font-size:20px;font-weight:700;color:#00e5ff;">—</div>
        <div style="font-size:8px;color:var(--text-dim);margin-top:4px;">Value Area Low (70%)</div>
      </div>

      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;text-align:center;">
        <div style="font-size:8px;letter-spacing:3px;color:var(--text-dim);margin-bottom:5px;">PRICE vs POC</div>
        <div id="pocPanelRelative" style="font-family:var(--font-mono);font-size:15px;font-weight:700;">—</div>
        <div id="pocPanelRelPct" style="font-size:10px;color:var(--text-dim);margin-top:4px;">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;text-align:center;">
        <div style="font-size:8px;letter-spacing:3px;color:var(--text-dim);margin-bottom:5px;">VALUE AREA</div>
        <div id="pocPanelInVA" style="font-family:var(--font-mono);font-size:13px;font-weight:700;">—</div>
        <div style="font-size:8px;color:var(--text-dim);margin-top:4px;">Price inside 70% zone?</div>
      </div>

      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;text-align:center;">
        <div style="font-size:8px;letter-spacing:3px;color:var(--text-dim);margin-bottom:5px;">STRUCTURE</div>
        <div id="pocPanelStructure" style="font-family:var(--font-mono);font-size:11px;font-weight:700;line-height:1.4;">—</div>
      </div>

    </div>

    <!-- CHART + LEGEND ROW -->
    <div style="display:grid;grid-template-columns:1fr 260px;gap:14px;">

      <!-- Volume Profile horizontal bar chart -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:12px;border-radius:2px;">
        <div style="font-size:8px;letter-spacing:2px;color:#c9a84c;margin-bottom:8px;">VOLUME BY PRICE — 60 DAYS</div>
        <div style="position:relative;height:260px;">
          <canvas id="pocProfileChart"></canvas>
        </div>
      </div>

      <!-- Right column: interpretation + key levels -->
      <div style="display:flex;flex-direction:column;gap:10px;">

        <!-- Key levels card -->
        <div style="background:var(--bg3);border:1px solid var(--border);padding:12px;border-radius:2px;flex:1;">
          <div style="font-size:8px;letter-spacing:2px;color:#c9a84c;margin-bottom:10px;">KEY LEVELS</div>
          <div id="pocKeyLevels" style="display:flex;flex-direction:column;gap:6px;"></div>
        </div>

        <!-- Interpretation guide -->
        <div style="background:rgba(201,168,76,0.05);border:1px solid rgba(201,168,76,0.2);padding:12px;border-radius:2px;">
          <div style="font-size:8px;letter-spacing:2px;color:#c9a84c;margin-bottom:8px;">HOW TO TRADE IT</div>
          <div style="font-size:9px;color:var(--text-dim);line-height:1.8;">
            <span style="color:#c9a84c;">POC</span> = institutional magnet. Price returns here.<br>
            <span style="color:#00e5ff;">Above VAH</span> = bullish acceptance. Breakout.<br>
            <span style="color:#00e5ff;">Below VAL</span> = bearish rejection. Breakdown.<br>
            <span style="color:#fff;">In Value Area</span> = range. Fade extremes.<br>
            <span style="color:#ff9800;">POC as support</span> = first bounce target on dips.
          </div>
        </div>

      </div>
    </div>
  </div>

  <!-- EXIT ANALYSIS PANEL — full width -->
  <div class="panel" id="exit-panel" style="grid-column:1/-1;border:1px solid rgba(255,255,255,0.06);background:rgba(20,10,5,0.9);">
    <div class="panel-title" onclick="togglePanel('exit-panel')" style="cursor:pointer;" title="Click to collapse" style="color:#ff6d00;margin-bottom:16px;">
      ⚡ Optimal Exit Engine — Best Price to Sell Before Downturn
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;margin-left:12px;">8 METHODS · FIBONACCI · DIVERGENCE · PSAR · STOCHASTIC · WYCKOFF · RESISTANCE</span>
     <span class="panel-collapse-btn" id="btn-exit-panel">▾</span></div>

    <!-- TOP ROW: Urgency + Sell Zone + Stop Loss -->
    <div style="display:grid;grid-template-columns:1fr 1fr 1fr 1fr;gap:12px;margin-bottom:16px;">
      <div style="background:var(--bg3);border:1px solid var(--border);padding:16px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:3px;color:var(--text-dim);text-transform:uppercase;margin-bottom:8px;">Exit Urgency</div>
        <div id="exitUrgency" style="font-family:var(--font-mono);font-size:16px;font-weight:700;color:#00e676;">HOLD — NO TOP YET</div>
        <div style="margin-top:8px;background:var(--bg2);border-radius:2px;height:6px;">
          <div id="exitScoreBar" style="height:6px;border-radius:2px;background:#00e676;width:0%;transition:width 0.8s ease;"></div>
        </div>
        <div id="exitScoreVal" style="font-size:10px;color:var(--text-dim);margin-top:4px;">Score: 0/100</div>
      </div>
      <div style="background:var(--bg3);border:1px solid rgba(255,109,0,0.3);padding:16px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:3px;color:#ff6d00;text-transform:uppercase;margin-bottom:8px;">🎯 Optimal Sell Zone</div>
        <div id="sellZone" style="font-family:var(--font-mono);font-size:18px;color:#ff6d00;font-weight:700;">—</div>
        <div id="upsideToTarget" style="font-size:10px;color:var(--text-dim);margin-top:4px;">—</div>
      </div>
      <div style="background:var(--bg3);border:1px solid rgba(255,23,68,0.3);padding:16px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:3px;color:#ff1744;text-transform:uppercase;margin-bottom:8px;">🛑 Stop Loss</div>
        <div id="stopLoss" style="font-family:var(--font-mono);font-size:18px;color:#ff1744;font-weight:700;">—</div>
        <div style="font-size:10px;color:var(--text-dim);margin-top:4px;">Exit if price falls here</div>
      </div>
      <div style="background:var(--bg3);border:1px solid var(--border);padding:16px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:3px;color:var(--gold);text-transform:uppercase;margin-bottom:8px;">Parabolic SAR</div>
        <div id="psarVal" style="font-family:var(--font-mono);font-size:16px;color:var(--gold);">—</div>
        <div id="psarSignal" style="font-size:10px;color:var(--text-dim);margin-top:4px;">—</div>
      </div>
    </div>

    <!-- MIDDLE ROW: Fibonacci + Resistance + Divergence + Stochastic -->
    <div style="display:grid;grid-template-columns:1fr 1fr 1fr 1fr;gap:12px;margin-bottom:16px;">

      <!-- Fibonacci Levels -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:1px;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--gold);margin-bottom:8px;text-transform:uppercase;">Fibonacci Levels</div>
        <div id="fibLevels" style="display:flex;flex-direction:column;gap:4px;"></div>
      </div>

      <!-- Key Resistance -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:1px;">
        <div style="font-size:9px;letter-spacing:2px;color:#ff6d00;margin-bottom:8px;text-transform:uppercase;">Key Resistance</div>
        <div style="font-size:9px;color:var(--text-dim);margin-bottom:6px;">SELL TARGETS ABOVE:</div>
        <div id="resistanceAbove" style="display:flex;flex-direction:column;gap:4px;"></div>
        <div style="font-size:9px;color:var(--text-dim);margin:8px 0 6px;">SUPPORT BELOW:</div>
        <div id="resistanceBelow" style="display:flex;flex-direction:column;gap:4px;"></div>
      </div>

      <!-- Divergence Warnings -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:1px;">
        <div style="font-size:9px;letter-spacing:2px;color:#ff1744;margin-bottom:8px;text-transform:uppercase;">⚠ Divergence Warnings</div>
        <div id="divergenceList" style="display:flex;flex-direction:column;gap:6px;">
          <div style="font-size:10px;color:var(--text-dim);">No divergences detected</div>
        </div>
        <div style="margin-top:10px;padding-top:10px;border-top:1px solid var(--border);">
          <div style="font-size:9px;letter-spacing:2px;color:var(--gold);margin-bottom:6px;text-transform:uppercase;">Distribution</div>
          <div id="distributionSignal" style="font-family:var(--font-mono);font-size:12px;color:var(--text-dim);">—</div>
        </div>
      </div>

      <!-- Stochastic + ROC -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:1px;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--gold);margin-bottom:8px;text-transform:uppercase;">Stochastic + Momentum</div>
        <div id="stochDisplay" style="display:flex;flex-direction:column;gap:4px;"></div>
        <div style="margin-top:10px;padding-top:10px;border-top:1px solid var(--border);">
          <div style="font-size:9px;color:var(--text-dim);margin-bottom:4px;letter-spacing:1px;text-transform:uppercase;">Rate of Change</div>
          <div id="rocDisplay" style="display:flex;flex-direction:column;gap:4px;"></div>
        </div>
      </div>

    </div>


    <!-- ═══════════════════════════════════════════════════════════
         3-TRANCHE SELL PLAN — staged exits to capture max upside
         ═══════════════════════════════════════════════════════════ -->
    <div style="margin-top:14px;padding-top:14px;border-top:2px solid rgba(255,109,0,0.4);">
      <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:12px;">
        <div style="font-size:9px;letter-spacing:3px;color:#ff6d00;text-transform:uppercase;">
          📋 Staged Sell Plan — Don't Sell All At Once
        </div>
        <div style="text-align:right;">
          <span style="font-size:9px;color:var(--text-dim);">Blended avg exit: </span>
          <span id="avgExitPrice" style="font-family:var(--font-mono);font-size:12px;color:#ff6d00;font-weight:700;">—</span>
          <span id="avgGainPct"   style="font-family:var(--font-mono);font-size:11px;color:var(--gold);margin-left:6px;">—</span>
        </div>
      </div>

      <!-- 3 tranche cards -->
      <div id="sellTranches" style="display:grid;grid-template-columns:repeat(3,1fr);gap:10px;margin-bottom:12px;"></div>

      <!-- Trailing stop ladder -->
      <div style="background:var(--bg3);border:1px solid rgba(255,109,0,0.2);padding:12px;border-radius:1px;">
        <div style="font-size:9px;letter-spacing:2px;color:#ff6d00;margin-bottom:8px;text-transform:uppercase;">🪜 Trailing Stop Ladder — Ratchets Up After Each Tranche</div>
        <div id="trailStopLadder" style="display:flex;gap:0;"></div>
        <div style="font-size:9px;color:var(--text-dim);margin-top:8px;line-height:1.7;">
          After T1 fills → move stop to <strong style="color:var(--text-primary);" id="newStopT1">—</strong> &nbsp;|&nbsp;
          After T2 fills → move stop to <strong style="color:var(--text-primary);" id="newStopT2">—</strong> &nbsp;|&nbsp;
          After T3 → position closed, stop cancelled
        </div>
      </div>

      <!-- Why not sell all at once -->
      <div style="margin-top:10px;font-size:9px;color:var(--text-dim);line-height:1.8;padding:10px 14px;
                   background:rgba(255,109,0,0.05);border-left:3px solid rgba(255,109,0,0.4);">
        <strong style="color:#ff6d00;">WHY STAGED EXITS BEAT SINGLE EXITS</strong><br>
        Markets almost always give one last squeeze above where you think the top is.
        T1 locks profit and removes emotional pressure — you <em>can't</em> lose now.
        T2 captures the primary target where resistance historically stalls rallies.
        T3 lets the final tranche run toward the extension target — this is where 
        the big gains hide. Selling everything at once means you either exit too early 
        (miss upside) or too late (give back gains). Staged exits solve both.
      </div>
    </div>

    <!-- BOTTOM: Exit Reasons -->
    <div style="background:var(--bg3);border:1px solid rgba(255,109,0,0.2);padding:14px;border-radius:1px;">
      <div style="font-size:9px;letter-spacing:2px;color:#ff6d00;margin-bottom:8px;text-transform:uppercase;">Why You Should Consider Exiting</div>
      <div id="exitReasons" style="display:flex;gap:8px;flex-wrap:wrap;">
        <span style="font-size:10px;color:var(--text-dim);">Monitoring for exit signals...</span>
      </div>
    </div>
  </div>

  
  <!-- ALGO RADAR — Real-Time Order Flow Detection -->
  <div class="panel" id="algo-panel" style="grid-column:1/-1;border:1px solid rgba(255,179,0,0.3);background:rgba(15,10,0,0.97);padding:0;">

    <!-- Header with live status -->
    <div style="display:flex;align-items:center;gap:12px;padding:12px 16px;border-bottom:1px solid rgba(255,179,0,0.15);cursor:pointer;" onclick="togglePanel('algo-panel')">
      <span style="font-size:11px;">&#9889;</span>
      <span style="font-family:var(--font-mono);font-size:10px;letter-spacing:3px;color:var(--gold);">ALGO RADAR &mdash; ORDER FLOW DETECTION</span>
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;">10s REFRESH &middot; 5 SIGNALS</span>
      <div id="algoLiveIndicator" style="width:6px;height:6px;border-radius:50%;background:#333;margin-left:4px;"></div>
      <span id="algoStatusText" style="font-size:9px;color:var(--text-dim);">Scanning...</span>
      <span class="panel-collapse-btn" id="btn-algo-panel" style="margin-left:auto;">&#9662;</span>
    </div>

    <!-- 5 signal gauges -->
    <div style="display:grid;grid-template-columns:repeat(5,1fr);border-bottom:1px solid rgba(255,179,0,0.1);">

      <div id="algoSig1" style="padding:12px 14px;border-right:1px solid rgba(255,255,255,0.05);">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">OFI IMBALANCE</div>
        <div id="algoOfiVal" style="font-family:var(--font-mono);font-size:16px;font-weight:700;color:var(--text-dim);">0.00x</div>
        <div id="algoOfiBar" style="height:3px;background:rgba(255,255,255,0.08);margin-top:6px;border-radius:1px;overflow:hidden;">
          <div id="algoOfiBarFill" style="height:100%;width:50%;background:#333;transition:all 0.5s;"></div>
        </div>
        <div id="algoOfiLabel" style="font-size:8px;color:var(--text-dim);margin-top:4px;">NEUTRAL</div>
      </div>

      <div id="algoSig2" style="padding:12px 14px;border-right:1px solid rgba(255,255,255,0.05);">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">AGGRESSION</div>
        <div id="algoAggrVal" style="font-family:var(--font-mono);font-size:16px;font-weight:700;color:var(--text-dim);">0.000</div>
        <div id="algoAggrBar" style="height:3px;background:rgba(255,255,255,0.08);margin-top:6px;border-radius:1px;overflow:hidden;">
          <div id="algoAggrBarFill" style="height:100%;width:50%;background:#333;transition:all 0.5s;"></div>
        </div>
        <div id="algoAggrLabel" style="font-size:8px;color:var(--text-dim);margin-top:4px;">NEUTRAL</div>
      </div>

      <div id="algoSig3" style="padding:12px 14px;border-right:1px solid rgba(255,255,255,0.05);">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">ABSORPTION</div>
        <div id="algoAbsorVal" style="font-family:var(--font-mono);font-size:16px;font-weight:700;color:var(--text-dim);">0.00</div>
        <div id="algoAbsorBar" style="height:3px;background:rgba(255,255,255,0.08);margin-top:6px;border-radius:1px;overflow:hidden;">
          <div id="algoAbsorBarFill" style="height:100%;width:0%;background:#ffb300;transition:all 0.5s;"></div>
        </div>
        <div id="algoAbsorLabel" style="font-size:8px;color:var(--text-dim);margin-top:4px;">PASSIVE</div>
      </div>

      <div id="algoSig4" style="padding:12px 14px;border-right:1px solid rgba(255,255,255,0.05);">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">VOL VACUUM</div>
        <div id="algoVacVal" style="font-family:var(--font-mono);font-size:16px;font-weight:700;color:var(--text-dim);">0.00</div>
        <div id="algoVacBar" style="height:3px;background:rgba(255,255,255,0.08);margin-top:6px;border-radius:1px;overflow:hidden;">
          <div id="algoVacBarFill" style="height:100%;width:0%;background:#b388ff;transition:all 0.5s;"></div>
        </div>
        <div id="algoVacLabel" style="font-size:8px;color:var(--text-dim);margin-top:4px;">NORMAL</div>
      </div>

      <div id="algoSig5" style="padding:12px 14px;">
        <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">PRICE VELOCITY</div>
        <div id="algoVelVal" style="font-family:var(--font-mono);font-size:16px;font-weight:700;color:var(--text-dim);">0/10</div>
        <div id="algoVelBar" style="height:3px;background:rgba(255,255,255,0.08);margin-top:6px;border-radius:1px;overflow:hidden;">
          <div id="algoVelBarFill" style="height:100%;width:50%;background:#333;transition:all 0.5s;"></div>
        </div>
        <div id="algoVelLabel" style="font-size:8px;color:var(--text-dim);margin-top:4px;">NEUTRAL</div>
      </div>

    </div>

    <!-- Active alert banner -->
    <div id="algoAlertBanner" style="display:none;padding:14px 16px;animation:pulseGreen 1s 3;">
      <div style="display:flex;align-items:center;gap:16px;flex-wrap:wrap;">
        <div id="algoAlertIcon" style="font-size:18px;">&#9889;</div>
        <div>
          <div id="algoAlertLabel" style="font-family:var(--font-mono);font-size:13px;font-weight:700;letter-spacing:2px;">--</div>
          <div id="algoAlertDetail" style="font-size:10px;color:var(--text-dim);margin-top:3px;">--</div>
        </div>
        <div style="margin-left:auto;text-align:right;">
          <div id="algoAlertPrice" style="font-family:var(--font-mono);font-size:14px;font-weight:700;">--</div>
          <div id="algoAlertTime" style="font-size:9px;color:var(--text-dim);">--</div>
        </div>
        <button onclick="askSpockAlgo()" style="background:rgba(255,179,0,0.15);border:1px solid var(--gold);color:var(--gold);font-family:var(--font-mono);font-size:10px;padding:6px 14px;cursor:pointer;letter-spacing:2px;white-space:nowrap;border-radius:1px;">
          ASK SPOCK &#8594;
        </button>
      </div>
    </div>

    <!-- Alert history -->
    <div style="padding:10px 16px;">
      <div style="font-size:8px;letter-spacing:2px;color:var(--text-dim);margin-bottom:8px;">RECENT ALGO SIGNALS</div>
      <div id="algoHistory" style="display:flex;flex-direction:column;gap:4px;max-height:120px;overflow-y:auto;">
        <div style="font-size:10px;color:var(--text-dim);">No signals detected yet</div>
      </div>
    </div>

  </div>

  <!-- SPOCK 2.0 — AI TRADING CO-PILOT -->
  <div class="panel" id="spock-panel" style="grid-column:1/-1;border:2px solid rgba(0,229,255,0.35);background:rgba(0,10,20,0.97);position:relative;">
    <div class="panel-title" onclick="togglePanel('spock-panel')" style="cursor:pointer;display:flex;align-items:center;gap:12px;">
      <span style="font-size:14px;">&#128406;</span>
      <span>SPOCK 2.0 &mdash; AI TRADING CO-PILOT</span>
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;">CLAUDE-POWERED &middot; POSITION INTELLIGENCE</span>
      <span id="spockTriggerBadge" style="display:none;font-size:9px;background:rgba(0,229,255,0.2);color:#00e5ff;padding:2px 8px;border-radius:2px;border:1px solid #00e5ff;margin-left:8px;animation:pulseGreen 1s infinite;"></span>
      <span class="panel-collapse-btn" id="btn-spock-panel" style="margin-left:auto;">&#9662;</span>
    </div>

    <!-- POSITION INPUT -->
    <div style="background:rgba(0,229,255,0.04);border:1px solid rgba(0,229,255,0.18);border-radius:2px;padding:16px;margin-bottom:16px;">
      <div style="font-size:9px;letter-spacing:2px;color:#00e5ff;margin-bottom:12px;">&#9654; YOUR POSITION &mdash; ENTER TRADE DETAILS</div>
      <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:10px;align-items:end;">

        <div>
          <div style="font-size:9px;color:var(--text-dim);letter-spacing:1px;margin-bottom:5px;">PORTFOLIO SIZE ($)</div>
          <input id="spockPortfolio" type="number" value="100000" min="1000"
            style="width:100%;background:var(--bg3);border:1px solid rgba(0,229,255,0.3);color:#00e5ff;font-family:var(--font-mono);font-size:13px;font-weight:700;padding:8px 10px;border-radius:1px;box-sizing:border-box;">
        </div>

        <div>
          <div style="font-size:9px;color:var(--text-dim);letter-spacing:1px;margin-bottom:5px;">SHARES HELD</div>
          <input id="spockShares" type="number" value="0" min="0"
            style="width:100%;background:var(--bg3);border:1px solid rgba(0,229,255,0.3);color:#00ff88;font-family:var(--font-mono);font-size:13px;font-weight:700;padding:8px 10px;border-radius:1px;box-sizing:border-box;">
        </div>

        <div>
          <div style="font-size:9px;color:var(--text-dim);letter-spacing:1px;margin-bottom:5px;">ENTRY PRICE ($)</div>
          <input id="spockEntry" type="number" value="0" min="0" step="0.01"
            style="width:100%;background:var(--bg3);border:1px solid rgba(0,229,255,0.3);color:#00ff88;font-family:var(--font-mono);font-size:13px;font-weight:700;padding:8px 10px;border-radius:1px;box-sizing:border-box;">
        </div>

        <!-- Live P&L preview -->
        <div style="background:var(--bg2);border:1px solid rgba(255,255,255,0.08);padding:8px 12px;border-radius:1px;">
          <div style="font-size:9px;color:var(--text-dim);letter-spacing:1px;margin-bottom:4px;">LIVE P&amp;L</div>
          <div id="spockPnlPreview" style="font-family:var(--font-mono);font-size:14px;font-weight:700;color:var(--text-dim);">Enter position</div>
          <div id="spockPnlPct" style="font-size:10px;color:var(--text-dim);margin-top:2px;">&mdash;</div>
        </div>

        <div style="display:flex;flex-direction:column;gap:6px;">
          <button onclick="askSpock()" id="spockBtn"
            style="background:rgba(0,229,255,0.15);border:1px solid #00e5ff;color:#00e5ff;font-family:var(--font-mono);font-size:11px;font-weight:700;padding:9px 16px;cursor:pointer;letter-spacing:2px;border-radius:1px;white-space:nowrap;transition:all 0.2s;">
            &#128406; ANALYZE POSITION
          </button>
          <div id="spockStatus" style="font-size:9px;color:var(--text-dim);text-align:center;">Ready &mdash; enter position and click analyze</div>
        </div>

      </div>
    </div>

    <!-- LOADING STATE -->
    <div id="spockLoading" style="display:none;text-align:center;padding:40px 20px;">
      <div style="font-family:var(--font-mono);font-size:13px;color:#00e5ff;letter-spacing:4px;">&#128406; SPOCK IS ANALYZING YOUR POSITION...</div>
      <div style="font-size:10px;color:var(--text-dim);margin-top:10px;">Processing DarthVader state &middot; options flow &middot; price levels &middot; risk assessment</div>
      <div style="margin-top:16px;height:2px;background:rgba(0,229,255,0.1);border-radius:1px;overflow:hidden;">
        <div style="height:100%;background:#00e5ff;animation:loadBar 2s infinite;width:30%;"></div>
      </div>
    </div>

    <!-- EMPTY STATE -->
    <div id="spockEmpty" style="text-align:center;padding:24px;border:1px dashed rgba(0,229,255,0.15);border-radius:2px;">
      <div style="font-size:11px;color:var(--text-dim);line-height:1.8;">
        Enter your shares held and entry price above, then click <span style="color:#00e5ff;">ANALYZE POSITION</span>.<br>
        Spock will assess position safety, give you exact sell targets, and flag the biggest risks.
      </div>
    </div>

    <!-- ANALYSIS OUTPUT -->
    <div id="spockOutput" style="display:none;">

      <!-- Top action bar -->
      <div style="display:grid;grid-template-columns:140px 130px 130px 1fr;gap:10px;margin-bottom:16px;">
        <div style="background:var(--bg2);border:1px solid rgba(0,229,255,0.25);padding:14px;text-align:center;border-radius:1px;">
          <div style="font-size:9px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">VERDICT</div>
          <div id="spockAction" style="font-family:var(--font-mono);font-size:22px;font-weight:900;color:#00e5ff;">--</div>
        </div>
        <div style="background:var(--bg2);border:1px solid rgba(0,229,255,0.25);padding:14px;text-align:center;border-radius:1px;">
          <div style="font-size:9px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">CONFIDENCE</div>
          <div id="spockConf" style="font-family:var(--font-mono);font-size:18px;font-weight:700;">--</div>
        </div>
        <div style="background:var(--bg2);border:1px solid rgba(0,229,255,0.25);padding:14px;text-align:center;border-radius:1px;">
          <div style="font-size:9px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">POSITION SAFE?</div>
          <div id="spockSafe" style="font-family:var(--font-mono);font-size:16px;font-weight:700;">--</div>
        </div>
        <div style="background:var(--bg2);border:1px solid rgba(0,229,255,0.25);padding:14px;border-radius:1px;">
          <div style="font-size:9px;letter-spacing:2px;color:var(--text-dim);margin-bottom:6px;">ANALYSIS META</div>
          <div id="spockTrigger" style="font-family:var(--font-mono);font-size:10px;color:var(--text-dim);">--</div>
          <div id="spockTime"    style="font-size:9px;color:var(--text-dim);margin-top:3px;">--</div>
        </div>
      </div>

      <!-- SELL PLAN — the most important section -->
      <div style="margin-bottom:16px;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;padding:8px 12px;background:rgba(0,255,136,0.06);border:1px solid rgba(0,255,136,0.2);border-bottom:none;border-radius:2px 2px 0 0;">
          &#9660; SELL PLAN &mdash; EXACT EXIT LEVELS
        </div>
        <div style="display:grid;grid-template-columns:1fr 1fr 1fr;border:1px solid rgba(0,255,136,0.2);">
          <div style="padding:14px;border-right:1px solid rgba(0,255,136,0.15);">
            <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:8px;">T1 &mdash; FIRST SELL</div>
            <div id="spockT1Price" style="font-family:var(--font-mono);font-size:20px;font-weight:700;color:#00ff88;">--</div>
            <div id="spockT1Size"  style="font-size:11px;color:var(--text-dim);margin-top:4px;">--</div>
            <div id="spockT1Why"   style="font-size:10px;color:var(--text-dim);margin-top:6px;line-height:1.5;">--</div>
          </div>
          <div style="padding:14px;border-right:1px solid rgba(0,255,136,0.15);">
            <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:8px;">T2 &mdash; MAIN SELL</div>
            <div id="spockT2Price" style="font-family:var(--font-mono);font-size:20px;font-weight:700;color:#00ff88;">--</div>
            <div id="spockT2Size"  style="font-size:11px;color:var(--text-dim);margin-top:4px;">--</div>
            <div id="spockT2Why"   style="font-size:10px;color:var(--text-dim);margin-top:6px;line-height:1.5;">--</div>
          </div>
          <div style="padding:14px;">
            <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:8px;">T3 &mdash; FINAL SELL</div>
            <div id="spockT3Price" style="font-family:var(--font-mono);font-size:20px;font-weight:700;color:#00ff88;">--</div>
            <div id="spockT3Size"  style="font-size:11px;color:var(--text-dim);margin-top:4px;">--</div>
            <div id="spockT3Why"   style="font-size:10px;color:var(--text-dim);margin-top:6px;line-height:1.5;">--</div>
          </div>
        </div>
      </div>

      <!-- Stop loss + risk + market read -->
      <div style="display:grid;grid-template-columns:1fr 1fr 1fr;gap:12px;margin-bottom:16px;">

        <div style="background:rgba(255,51,85,0.06);border:1px solid rgba(255,51,85,0.3);padding:14px;border-radius:1px;">
          <div style="font-size:9px;letter-spacing:2px;color:#ff3355;margin-bottom:8px;">&#9632; STOP LOSS</div>
          <div id="spockStop" style="font-family:var(--font-mono);font-size:22px;font-weight:900;color:#ff3355;">--</div>
          <div id="spockStopNote" style="font-size:10px;color:var(--text-dim);margin-top:6px;line-height:1.5;">Cut here. No negotiation.</div>
        </div>

        <div style="background:rgba(255,100,0,0.05);border:1px solid rgba(255,100,0,0.25);padding:14px;border-radius:1px;">
          <div style="font-size:9px;letter-spacing:2px;color:#ff6d00;margin-bottom:8px;">&#9888; BIGGEST RISK</div>
          <div id="spockRisk" style="font-size:11px;color:var(--text-primary);line-height:1.6;">--</div>
        </div>

        <div style="background:rgba(0,229,255,0.04);border:1px solid rgba(0,229,255,0.2);padding:14px;border-radius:1px;">
          <div style="font-size:9px;letter-spacing:2px;color:#00e5ff;margin-bottom:8px;">&#128200; MARKET READ</div>
          <div id="spockMarket" style="font-size:11px;color:var(--text-primary);line-height:1.6;">--</div>
        </div>

      </div>

      <!-- Watch for -->
      <div style="background:rgba(255,179,0,0.04);border:1px solid rgba(255,179,0,0.2);padding:14px;border-radius:1px;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--gold);margin-bottom:8px;">&#128064; WATCH FOR</div>
        <div id="spockWatch" style="font-size:11px;color:var(--text-primary);line-height:1.8;">--</div>
      </div>

    </div>
  </div>

  <!-- UNUSUAL OPTIONS ACTIVITY PANEL — full width -->
  <div class="panel" id="uoa-panel" style="grid-column:1/-1;border:2px solid rgba(180,100,255,0.35);background:rgba(10,5,20,0.98);">
    <div class="panel-title" onclick="togglePanel('uoa-panel')" style="cursor:pointer;" title="Click to collapse" style="color:#b388ff;margin-bottom:18px;">
      🔍 Unusual Options Activity — Whale &amp; Sweep Detection
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;margin-left:12px;">VOL/OI RATIO · PREMIUM FLOW · WHALE ALERTS · CALL/PUT BIAS · STRIKE SWEEPS</span>
     <span class="panel-collapse-btn" id="btn-uoa-panel">▾</span></div>

    <!-- TOP ROW: 5 key numbers -->
    <div style="display:grid;grid-template-columns:2fr 1fr 1fr 1fr 1fr;gap:12px;margin-bottom:18px;">

      <!-- Net flow signal — big -->
      <div id="uoaFlowCard" style="background:rgba(180,100,255,0.08);border:2px solid rgba(180,100,255,0.4);
           padding:20px;border-radius:2px;text-align:center;display:flex;flex-direction:column;justify-content:center;gap:8px;">
        <div style="font-size:9px;letter-spacing:3px;color:var(--text-dim);">NET FLOW DIRECTION</div>
        <div id="uoaFlow" style="font-family:var(--font-mono);font-size:24px;font-weight:700;color:#b388ff;">—</div>
        <div id="uoaSignal" style="font-size:10px;color:var(--text-dim);line-height:1.4;">Scanning...</div>
        <!-- Call vs Put bar -->
        <div style="margin-top:4px;">
          <div style="display:flex;justify-content:space-between;font-size:9px;margin-bottom:4px;">
            <span style="color:#00ff88;">CALLS</span>
            <span id="uoaCallPct" style="font-family:var(--font-mono);color:#00ff88;">—%</span>
            <span id="uoaPutPct"  style="font-family:var(--font-mono);color:#ff3355;">—%</span>
            <span style="color:#ff3355;">PUTS</span>
          </div>
          <div style="height:8px;background:var(--bg2);border-radius:4px;overflow:hidden;">
            <div id="uoaFlowBar" style="height:100%;background:linear-gradient(90deg,#00ff88,#ff3355);width:50%;transition:width 0.8s;border-radius:4px;"></div>
          </div>
        </div>
      </div>

      <!-- Whale count -->
      <div style="background:var(--bg3);border:1px solid rgba(180,100,255,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#b388ff;margin-bottom:6px;">🐋 WHALE TRADES</div>
        <div id="uoaWhaleCount" style="font-family:var(--font-mono);font-size:36px;font-weight:700;color:#b388ff;">0</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">&gt;$500K single strike</div>
      </div>

      <!-- Total unusual -->
      <div style="background:var(--bg3);border:1px solid rgba(180,100,255,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#b388ff;margin-bottom:6px;">⚡ UNUSUAL STRIKES</div>
        <div id="uoaUnusualCount" style="font-family:var(--font-mono);font-size:36px;font-weight:700;color:var(--gold);">0</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">vol/OI &gt; 5×</div>
      </div>

      <!-- Call premium -->
      <div style="background:var(--bg3);border:1px solid rgba(0,255,136,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:6px;">CALL PREMIUM</div>
        <div id="uoaCallPrem" style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:#00ff88;">—</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">total $ in calls</div>
      </div>

      <!-- Put premium -->
      <div style="background:var(--bg3);border:1px solid rgba(255,51,85,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ff3355;margin-bottom:6px;">PUT PREMIUM</div>
        <div id="uoaPutPrem" style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:#ff3355;">—</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">total $ in puts</div>
      </div>

    </div>

    <!-- MIDDLE: Whale alerts + Unusual calls + Unusual puts -->
    <div style="display:grid;grid-template-columns:1.2fr 1fr 1fr;gap:12px;margin-bottom:14px;">

      <!-- Whale / Large premium alerts -->
      <div style="background:var(--bg3);border:1px solid rgba(180,100,255,0.3);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#b388ff;margin-bottom:10px;text-transform:uppercase;">🐋 Whale Alerts — &gt;$500K Premium</div>
        <div id="uoaWhaleList" style="display:flex;flex-direction:column;gap:7px;max-height:220px;overflow-y:auto;">
          <div style="font-size:10px;color:var(--text-dim);">Scanning options chain...</div>
        </div>
      </div>

      <!-- Unusual calls -->
      <div style="background:var(--bg3);border:1px solid rgba(0,255,136,0.2);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:10px;text-transform:uppercase;">🟢 Unusual Call Activity</div>
        <div id="uoaCallList" style="display:flex;flex-direction:column;gap:6px;max-height:220px;overflow-y:auto;">
          <div style="font-size:10px;color:var(--text-dim);">No unusual call activity</div>
        </div>
      </div>

      <!-- Unusual puts -->
      <div style="background:var(--bg3);border:1px solid rgba(255,51,85,0.2);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#ff3355;margin-bottom:10px;text-transform:uppercase;">🔴 Unusual Put Activity</div>
        <div id="uoaPutList" style="display:flex;flex-direction:column;gap:6px;max-height:220px;overflow-y:auto;">
          <div style="font-size:10px;color:var(--text-dim);">No unusual put activity</div>
        </div>
      </div>

    </div>

    <!-- BOTTOM: Premium heatmap chart + Reasons -->
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:12px;border-top:1px solid var(--border);padding-top:12px;">

      <!-- Strike premium heatmap (Chart.js bar) -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#b388ff;margin-bottom:8px;text-transform:uppercase;">💰 Premium by Strike — Call vs Put Flow</div>
        <div style="position:relative;height:180px;"><canvas id="uoaHeatmapChart"></canvas></div>
      </div>

      <!-- Flow reasons + legend -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#b388ff;margin-bottom:10px;text-transform:uppercase;">📡 Flow Intelligence</div>
        <div id="uoaReasons" style="display:flex;flex-direction:column;gap:8px;margin-bottom:14px;"></div>
        <div style="padding-top:10px;border-top:1px solid var(--border);font-size:9px;color:var(--text-dim);line-height:1.9;">
          <div style="color:#b388ff;margin-bottom:4px;letter-spacing:1px;">HOW TO READ OPTIONS FLOW</div>
          <strong style="color:var(--text-primary);">Vol/OI &gt; 5×</strong> — new position, not a roll. Someone just opened a fresh bet.<br>
          <strong style="color:var(--text-primary);">Vol/OI &gt; 20×</strong> — aggressive sweep. Trader paid market price, didn't wait for fills.<br>
          <strong style="color:var(--text-primary);">&gt;$500K premium</strong> — institutional or whale size. Not retail.<br>
          <strong style="color:var(--text-primary);">ITM options</strong> — higher conviction. OTM = lottery tickets.<br>
          <strong style="color:var(--text-primary);">Net call heavy</strong> — smart money expects a move up within expiry window.
        </div>
      </div>

    </div>
  </div>

  <!-- CAPITULATION BOUNCE ALERT BANNER -->
  <div id="capBounceAlert" style="display:none;grid-column:1/-1;
       background:linear-gradient(135deg,rgba(0,255,136,0.12),rgba(0,229,255,0.08));
       border:2px solid rgba(0,255,136,0.6);border-radius:3px;
       padding:16px 24px;animation:capPulse 2s ease-in-out infinite;">
    <div style="display:flex;align-items:center;gap:20px;flex-wrap:wrap;">
      <div style="flex-shrink:0;">
        <div style="font-size:9px;letter-spacing:3px;color:#00ff88;margin-bottom:4px;">CAPITULATION BOUNCE DETECTED</div>
        <div id="capPhase" style="font-family:var(--font-mono);font-size:20px;font-weight:700;color:#00ff88;">BOUNCING</div>
        <div id="capConviction" style="font-size:9px;color:var(--text-dim);margin-top:2px;">Conviction: —/100</div>
      </div>
      <div style="flex-shrink:0;border-left:1px solid rgba(0,255,136,0.3);padding-left:20px;">
        <div style="font-size:9px;color:var(--text-dim);margin-bottom:4px;">THE MOVE</div>
        <div id="capDropLine" style="font-family:var(--font-mono);font-size:12px;color:var(--text-primary);">— to — (—%)</div>
        <div id="capRecovery" style="font-size:10px;color:#00e5ff;margin-top:2px;">Recovery: —%</div>
      </div>
      <div style="flex-shrink:0;border-left:1px solid rgba(0,255,136,0.3);padding-left:20px;">
        <div style="font-size:9px;color:var(--text-dim);margin-bottom:6px;">MULTI-DAY ENTRY</div>
        <div style="display:flex;gap:10px;align-items:baseline;">
          <span style="font-size:9px;color:var(--text-dim);">ENTRY</span>
          <span id="capEntry" style="font-family:var(--font-mono);font-size:13px;font-weight:700;color:#00ff88;">$—</span>
          <span style="font-size:9px;color:var(--text-dim);">STOP</span>
          <span id="capStop" style="font-family:var(--font-mono);font-size:13px;font-weight:700;color:#ff3355;">$—</span>
        </div>
        <div style="display:flex;gap:10px;align-items:baseline;margin-top:4px;">
          <span style="font-size:9px;color:var(--text-dim);">T1</span>
          <span id="capT1" style="font-family:var(--font-mono);font-size:11px;color:#00e5ff;">$—</span>
          <span style="font-size:9px;color:var(--text-dim);">T2</span>
          <span id="capT2" style="font-family:var(--font-mono);font-size:11px;color:#00e5ff;">$—</span>
          <span style="font-size:9px;color:var(--text-dim);">T3</span>
          <span id="capT3" style="font-family:var(--font-mono);font-size:11px;color:#00e5ff;">$—</span>
        </div>
      </div>
      <div style="flex:1;min-width:180px;border-left:1px solid rgba(0,255,136,0.3);padding-left:20px;">
        <div style="font-size:9px;color:var(--text-dim);margin-bottom:6px;">SIGNALS CONFIRMING</div>
        <div id="capReasons" style="display:flex;flex-direction:column;gap:3px;"></div>
      </div>
      <div style="flex-shrink:0;display:flex;flex-direction:column;gap:6px;">
        <div style="display:flex;gap:6px;">
          <div id="capOFI"  style="font-size:9px;padding:3px 8px;border-radius:1px;background:rgba(255,255,255,0.05);border:1px solid rgba(255,255,255,0.1);color:var(--text-dim);">OFI</div>
          <div id="capVolX" style="font-size:9px;padding:3px 8px;border-radius:1px;background:rgba(255,255,255,0.05);border:1px solid rgba(255,255,255,0.1);color:var(--text-dim);">VOL EX</div>
        </div>
        <div style="display:flex;gap:6px;">
          <div id="capVWAP" style="font-size:9px;padding:3px 8px;border-radius:1px;background:rgba(255,255,255,0.05);border:1px solid rgba(255,255,255,0.1);color:var(--text-dim);">VWAP</div>
          <div id="capSupp" style="font-size:9px;padding:3px 8px;border-radius:1px;background:rgba(255,255,255,0.05);border:1px solid rgba(255,255,255,0.1);color:var(--text-dim);">SUPPORT</div>
        </div>
        <div id="capDaily" style="font-size:9px;padding:3px 8px;border-radius:1px;background:rgba(255,255,255,0.05);border:1px solid rgba(255,255,255,0.1);color:var(--text-dim);text-align:center;">DAILY TREND</div>
      </div>
    </div>
  </div>
  <style>@keyframes capPulse{0%,100%{box-shadow:0 0 0 0 rgba(0,255,136,0.3);}50%{box-shadow:0 0 20px 4px rgba(0,255,136,0.15);}}</style>

  <!-- PRECISION ENTRY PANEL — full width -->
  <div class="panel" id="entry-panel" style="grid-column:1/-1;border:2px solid rgba(0,255,136,0.35);background:rgba(0,15,5,0.98);">
    <div class="panel-title" onclick="togglePanel('entry-panel')" style="cursor:pointer;" title="Click to collapse" style="color:#00ff88;margin-bottom:18px;">
      🟢 Precision Entry Engine — When to Buy &amp; How Much
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;margin-left:12px;">SELLING CLIMAX · BULLISH DIVERGENCE · SUPPORT LEVELS · STAGED ENTRY · CAPITAL ALLOCATION</span>
     <span class="panel-collapse-btn" id="btn-entry-panel">▾</span></div>

    <!-- TOP ROW: key numbers -->
    <div style="display:grid;grid-template-columns:2fr 1fr 1fr 1fr 1fr;gap:12px;margin-bottom:18px;">

      <!-- Entry urgency — big -->
      <div id="entryUrgencyCard" style="background:rgba(0,255,136,0.06);border:2px solid rgba(0,255,136,0.3);
           padding:20px;border-radius:2px;text-align:center;display:flex;flex-direction:column;justify-content:center;gap:6px;">
        <div style="font-size:9px;letter-spacing:3px;color:var(--text-dim);">ENTRY STATUS</div>
        <div id="entryUrgency" style="font-family:var(--font-mono);font-size:26px;font-weight:700;color:var(--text-dim);">⏳ WAIT</div>
        <div style="display:flex;justify-content:center;align-items:center;gap:10px;">
          <div style="background:var(--bg2);border-radius:2px;height:8px;width:200px;overflow:hidden;">
            <div id="entryScoreBar" style="height:100%;width:0%;background:#00ff88;transition:width 0.8s;border-radius:2px;"></div>
          </div>
          <span id="entryScoreVal" style="font-family:var(--font-mono);font-size:11px;color:var(--text-dim);">0/100</span>
        </div>
      </div>

      <!-- Total deploy % -->
      <div style="background:var(--bg3);border:1px solid rgba(0,255,136,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:6px;">TOTAL DEPLOY</div>
        <div id="entryDeployPct" style="font-family:var(--font-mono);font-size:26px;font-weight:700;color:#00ff88;">—</div>
        <div id="entryDeployDollar" style="font-size:10px;margin-top:4px;color:var(--text-dim);">of your capital</div>
      </div>

      <!-- RSI divergence days -->
      <div style="background:var(--bg3);border:1px solid rgba(0,255,136,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:6px;">RSI DIV DAYS</div>
        <div id="entryDivDays" style="font-family:var(--font-mono);font-size:28px;font-weight:700;color:var(--gold);">—</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">accumulation running</div>
      </div>

      <!-- Invalidation level -->
      <div style="background:var(--bg3);border:1px solid rgba(255,23,68,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--accent-red);margin-bottom:6px;">INVALIDATION</div>
        <div id="entryInvalidation" style="font-family:var(--font-mono);font-size:20px;font-weight:700;color:var(--accent-red);">—</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">thesis wrong below this</div>
      </div>

      <!-- Fear gauge -->
      <div id="entryFearCard" style="background:var(--bg3);border:1px solid rgba(255,193,7,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--gold);margin-bottom:6px;">FEAR GAUGE</div>
        <div id="entryFearVal" style="font-family:var(--font-mono);font-size:20px;font-weight:700;color:var(--gold);">—</div>
        <div id="entryFearLabel" style="font-size:9px;margin-top:4px;color:var(--text-dim);">VIX level</div>
      </div>

    </div>

    <!-- 3-TRANCHE PLAN — the heart of the buy panel -->
    <div style="margin-bottom:18px;">
      <div style="font-size:9px;letter-spacing:3px;color:#00ff88;text-transform:uppercase;margin-bottom:10px;">📋 Staged Entry Plan — How to Buy</div>
      <div id="entryTranches" style="display:grid;grid-template-columns:repeat(3,1fr);gap:10px;"></div>
    </div>

    <!-- SIGNALS + SUPPORT + CHECKLIST -->
    <div style="display:grid;grid-template-columns:1fr 1fr 1fr;gap:12px;border-top:1px solid var(--border);padding-top:14px;">

      <!-- Active entry signals -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:10px;text-transform:uppercase;">🔍 Active Bottom Signals</div>
        <div id="entrySignalList" style="display:flex;flex-direction:column;gap:6px;max-height:200px;overflow-y:auto;"></div>
      </div>

      <!-- Support levels + Fibonacci -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:10px;text-transform:uppercase;">🏗 Key Support Levels</div>
        <div id="entrySupportLevels" style="display:flex;flex-direction:column;gap:5px;margin-bottom:14px;"></div>
        <div style="font-size:9px;letter-spacing:2px;color:var(--gold);margin-bottom:8px;text-transform:uppercase;">📐 Fibonacci Retracement</div>
        <div id="entryFibLevels" style="display:flex;flex-direction:column;gap:4px;"></div>
      </div>

      <!-- Buy checklist — mirrors the sell checklist -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:10px;text-transform:uppercase;">✅ Entry Checklist — Professional Protocol</div>
        <div id="entryChecklist" style="display:flex;flex-direction:column;gap:6px;"></div>
        <div style="margin-top:12px;padding-top:10px;border-top:1px solid var(--border);font-size:9px;color:var(--text-dim);line-height:1.8;">
          <div style="color:#00ff88;margin-bottom:4px;letter-spacing:1px;">WHY STAGED ENTRIES WORK</div>
          Never deploy all capital at once — markets always give you a second chance.
          T1 catches the signal. T2 gets a better price if it dips (it usually does).
          T3 confirms the bottom is in before your final add.
          If the thesis is wrong, invalidation stops you out before real damage.
        </div>
      </div>

    </div>
  </div>

  <!-- PEAK / TOP DETECTION PANEL — full width -->
  <div class="panel" id="peak-panel" style="grid-column:1/-1;border:2px solid rgba(255,23,68,0.4);background:rgba(20,0,5,0.98);">
    <div class="panel-title" onclick="togglePanel('peak-panel')" style="cursor:pointer;" title="Click to collapse" style="color:#ff1744;margin-bottom:18px;">
      🎯 Precision Top Detection — Sell Before the Downturn
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;margin-left:12px;">BUYING CLIMAX · CANDLE PATTERNS · DIVERGENCE · DISTRIBUTION · OPTIONS SKEW · PARABOLIC MOVES</span>
     <span class="panel-collapse-btn" id="btn-peak-panel">▾</span></div>

    <!-- TOP ROW: The 3 numbers that matter most -->
    <div style="display:grid;grid-template-columns:2fr 1fr 1fr 1fr 1fr;gap:12px;margin-bottom:18px;">

      <!-- Peak urgency — big -->
      <div id="peakUrgencyCard" style="background:rgba(255,23,68,0.08);border:2px solid rgba(255,23,68,0.4);
                                        padding:20px;border-radius:2px;text-align:center;
                                        display:flex;flex-direction:column;justify-content:center;gap:6px;">
        <div style="font-size:9px;letter-spacing:3px;color:var(--text-dim);">TOP DETECTION STATUS</div>
        <div id="peakUrgency" style="font-family:var(--font-mono);font-size:26px;font-weight:700;color:#00ff88;">✅ CLEAR</div>
        <div style="display:flex;justify-content:center;align-items:center;gap:10px;">
          <div style="background:var(--bg2);border-radius:2px;height:8px;width:200px;overflow:hidden;">
            <div id="peakScoreBar" style="height:100%;width:0%;background:#ff1744;transition:width 0.8s;border-radius:2px;"></div>
          </div>
          <span id="peakScoreVal" style="font-family:var(--font-mono);font-size:11px;color:var(--text-dim);">0/100</span>
        </div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(255,23,68,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ff6d00;margin-bottom:6px;">SELL TARGET ZONE</div>
        <div id="peakTopTarget" style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:#ff6d00;">—</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">nearest resistance</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(255,23,68,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--accent-red);margin-bottom:6px;">HARD STOP</div>
        <div id="peakHardStop" style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:var(--accent-red);">—</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">below 3-day low</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(255,193,7,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--gold);margin-bottom:6px;">EXIT WINDOW</div>
        <div id="peakCountdown" style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:var(--gold);">—</div>
        <div id="peakExitWindow" style="font-size:9px;margin-top:4px;color:var(--text-dim);line-height:1.5;">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(255,193,7,0.3);padding:16px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--gold);margin-bottom:6px;">RSI DIV DAYS</div>
        <div id="peakDivDays" style="font-family:var(--font-mono);font-size:28px;font-weight:700;color:var(--gold);">—</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">days diverging</div>
      </div>

    </div>

    <!-- SIGNAL CARDS: each of the 9 leading signals -->
    <div style="margin-bottom:14px;">
      <div style="font-size:9px;letter-spacing:3px;color:#ff1744;text-transform:uppercase;margin-bottom:10px;">🔍 Active Top Signals</div>
      <div id="peakSignalCards" style="display:grid;grid-template-columns:repeat(auto-fill,minmax(300px,1fr));gap:8px;"></div>
      <div id="peakClearMsg" style="font-size:11px;color:var(--accent-green);padding:12px 0;display:none;">✅ No topping signals active — continue holding with trailing stop</div>
    </div>

    <!-- BOTTOM: Candle patterns + Checklist -->
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:12px;border-top:1px solid var(--border);padding-top:12px;">

      <!-- Candle pattern log -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#ff6d00;margin-bottom:10px;text-transform:uppercase;">🕯 Recent Candle Patterns</div>
        <div id="peakCandlePatterns" style="display:flex;flex-direction:column;gap:6px;"></div>
        <div style="margin-top:12px;font-size:9px;color:var(--text-dim);line-height:1.8;border-top:1px solid var(--border);padding-top:8px;">
          <strong style="color:var(--text-primary);">Shooting Star</strong> — long upper wick, small body at bottom = buyers rejected<br>
          <strong style="color:var(--text-primary);">Doji at High</strong> — indecision at resistance = potential reversal<br>
          <strong style="color:var(--text-primary);">Bearish Engulfing</strong> — sellers overwhelm buyers in one candle = strong reversal
        </div>
      </div>

      <!-- Top selling checklist -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#ff6d00;margin-bottom:10px;text-transform:uppercase;">✅ Top-Selling Checklist — Professional Protocol</div>
        <div id="peakChecklist" style="display:flex;flex-direction:column;gap:6px;"></div>
      </div>

    </div>
  </div>

  <!-- CTA POSITION SIZING PANEL — full width -->
  <div class="panel" id="cta-panel" style="grid-column:1/-1;border:1px solid rgba(0,255,136,0.3);background:rgba(0,15,8,0.98);">
    <div class="panel-title" onclick="togglePanel('cta-panel')" style="cursor:pointer;" title="Click to collapse" style="color:#00ff88;margin-bottom:18px;">
      📐 CTA Position Sizing Engine
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;margin-left:12px;">VOLATILITY SCALING · TREND SIGNAL · REGIME MULTIPLIER · CORRELATION ADJUSTMENT</span>
     <span class="panel-collapse-btn" id="btn-cta-panel">▾</span></div>

    <!-- ── Input row ── -->
    <div style="display:flex;align-items:center;gap:16px;margin-bottom:20px;padding:16px;background:var(--bg3);border:1px solid rgba(0,255,136,0.2);border-radius:2px;">
      <div style="font-size:9px;letter-spacing:2px;color:#00ff88;white-space:nowrap;">YOUR CAPITAL</div>
      <div style="display:flex;align-items:center;gap:8px;">
        <span style="font-family:var(--font-mono);font-size:18px;color:var(--gold);">$</span>
        <input id="portfolioInput" type="number" value="100000" min="1000" step="1000"
          style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:var(--gold);
                 background:var(--bg2);border:1px solid rgba(0,255,136,0.4);border-radius:2px;
                 padding:8px 12px;width:160px;outline:none;"
          oninput="updatePortfolio()"
          onfocus="this.style.borderColor='#00ff88'" onblur="this.style.borderColor='rgba(0,255,136,0.4)'"/>
      </div>
      <div style="font-size:9px;letter-spacing:2px;color:var(--text-dim);">TARGET VOL</div>
      <div style="display:flex;align-items:center;gap:6px;">
        <input id="targetVolInput" type="range" min="5" max="30" value="12" step="1"
          style="width:100px;accent-color:#00ff88;" oninput="updatePortfolio()"/>
        <span id="targetVolDisplay" style="font-family:var(--font-mono);font-size:14px;color:#00ff88;width:36px;">12%</span>
      </div>
      <button onclick="updatePortfolio()" 
        style="font-family:var(--font-mono);font-size:10px;background:rgba(0,255,136,0.15);
               color:#00ff88;border:1px solid #00ff88;padding:8px 18px;cursor:pointer;
               border-radius:2px;letter-spacing:2px;text-transform:uppercase;"
        onmouseover="this.style.background='rgba(0,255,136,0.3)'"
        onmouseout="this.style.background='rgba(0,255,136,0.15)'">
        ↻ RECALCULATE
      </button>
      <div style="margin-left:auto;text-align:right;">
        <div id="sizingSignalBig" style="font-family:var(--font-mono);font-size:20px;font-weight:700;color:#00ff88;">—</div>
        <div style="font-size:9px;letter-spacing:2px;color:var(--text-dim);">RECOMMENDED ACTION</div>
      </div>
    </div>

    <!-- ── Answer row — the most important numbers ── -->
    <div style="display:grid;grid-template-columns:repeat(5,1fr);gap:12px;margin-bottom:18px;">

      <div style="background:rgba(0,255,136,0.08);border:2px solid rgba(0,255,136,0.5);padding:18px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:6px;">DEPLOY THIS MUCH</div>
        <div id="finalExposure" style="font-family:var(--font-mono);font-size:24px;font-weight:700;color:#00ff88;">—</div>
        <div id="finalExposurePct" style="font-size:11px;margin-top:4px;color:var(--text-dim);">— of portfolio</div>
      </div>

      <div style="background:var(--bg3);border:1px solid var(--border);padding:18px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--gold);margin-bottom:6px;">SHARES TO BUY</div>
        <div id="shareCount" style="font-family:var(--font-mono);font-size:24px;font-weight:700;color:var(--gold);">—</div>
        <div id="sharePrice" style="font-size:11px;margin-top:4px;color:var(--text-dim);">@ $— per share</div>
      </div>

      <div style="background:var(--bg3);border:1px solid var(--border);padding:18px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#40c4ff;margin-bottom:6px;">RANGE (CONS – AGG)</div>
        <div id="shareRange" style="font-family:var(--font-mono);font-size:16px;font-weight:700;color:#40c4ff;line-height:1.4;">—</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">Conservative – Aggressive</div>
      </div>

      <div style="background:var(--bg3);border:1px solid var(--border);padding:18px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ff6d00;margin-bottom:6px;">DAILY 1σ RISK</div>
        <div id="dailyRisk" style="font-family:var(--font-mono);font-size:22px;font-weight:700;color:#ff6d00;">—</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">expected daily P&L swing</div>
      </div>

      <div style="background:var(--bg3);border:1px solid var(--border);padding:18px;border-radius:2px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--accent-red);margin-bottom:6px;">IF SPY DROPS 1%</div>
        <div id="spyImpact" style="font-family:var(--font-mono);font-size:22px;font-weight:700;color:var(--accent-red);">—</div>
        <div id="spyBeta" style="font-size:9px;margin-top:4px;color:var(--text-dim);">beta: —</div>
      </div>

    </div>

    <!-- ── Factor breakdown + vol chart ── -->
    <div style="display:grid;grid-template-columns:1fr 1fr 1fr;gap:12px;margin-bottom:14px;">

      <!-- Factor table -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:10px;text-transform:uppercase;">How We Got There — Factor Breakdown</div>
        <div id="ctaFactorTable" style="display:flex;flex-direction:column;gap:3px;"></div>
      </div>

      <!-- Multiplier gauges -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:12px;text-transform:uppercase;">Live Multipliers</div>
        <div id="ctaMultipliers" style="display:flex;flex-direction:column;gap:14px;"></div>
      </div>

      

    </div>

    <!-- ── Regime breakdown + reasoning ── -->
    <div style="display:grid;grid-template-columns:1fr 1fr;gap:12px;">

      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:10px;text-transform:uppercase;">Regime Breakdown — Why the Multiplier Is What It Is</div>
        <div id="ctaRegimeBreakdown" style="display:grid;grid-template-columns:1fr 1fr;gap:8px;"></div>
      </div>

      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:2px;">
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:10px;text-transform:uppercase;">Algorithm Reasoning</div>
        <div id="ctaReasons" style="display:flex;flex-direction:column;gap:8px;"></div>
        <div style="margin-top:14px;padding-top:10px;border-top:1px solid var(--border);font-size:9px;color:var(--text-dim);line-height:1.8;">
          <div style="color:#00ff88;margin-bottom:4px;letter-spacing:1px;">HOW CTAs THINK</div>
          Volatility scaling automatically <strong style="color:var(--text-primary);">increases</strong> exposure after calm periods 
          and <strong style="color:var(--text-primary);">cuts</strong> it during chaos. This creates long-term convexity — 
          you're larger when markets trend and smaller when they chop. 
          The regime multiplier adjusts for whether the <em>environment</em> favours the trade, 
          not just whether the trade looks good on a chart.
        </div>
      </div>

    </div>
  </div>

  <!-- EXTENDED HOURS PANEL — full width -->
  <div class="panel" id="ext-panel" style="grid-column:1/-1;border:1px solid rgba(120,80,255,0.3);background:rgba(8,5,20,0.97);">
    <div class="panel-title" onclick="togglePanel('ext-panel')" style="cursor:pointer;" title="Click to collapse" style="color:#ce93d8;margin-bottom:16px;">
      ⏰ Extended Hours Activity — Pre-Market · After-Hours · Overnight Gap
      <span id="sessionBadge" style="font-size:9px;letter-spacing:2px;margin-left:12px;padding:3px 10px;border-radius:2px;background:rgba(120,80,255,0.2);color:#ce93d8;">LOADING SESSION...</span>
      <span id="etTimeBadge" style="font-size:9px;color:var(--text-dim);margin-left:8px;">—</span>
     <span class="panel-collapse-btn" id="btn-ext-panel">▾</span></div>

    <!-- ROW 1: Key metrics -->
    <div style="display:grid;grid-template-columns:repeat(6,1fr);gap:10px;margin-bottom:14px;">

      <div style="background:var(--bg3);border:1px solid rgba(120,80,255,0.2);padding:13px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ce93d8;margin-bottom:5px;">PRE-MARKET</div>
        <div id="pmPrice" style="font-family:var(--font-mono);font-size:17px;font-weight:700;color:var(--text-primary);">—</div>
        <div id="pmChange" style="font-size:12px;margin-top:4px;font-family:var(--font-mono);">—</div>
        <div id="pmTrend" style="font-size:9px;margin-top:3px;color:var(--text-dim);">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(120,80,255,0.2);padding:13px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ce93d8;margin-bottom:5px;">AFTER-HOURS</div>
        <div id="ahPrice" style="font-family:var(--font-mono);font-size:17px;font-weight:700;color:var(--text-primary);">—</div>
        <div id="ahChange" style="font-size:12px;margin-top:4px;font-family:var(--font-mono);">—</div>
        <div id="ahVol" style="font-size:9px;margin-top:3px;color:var(--text-dim);">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(120,80,255,0.2);padding:13px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ce93d8;margin-bottom:5px;">OVERNIGHT GAP</div>
        <div id="gapVal" style="font-family:var(--font-mono);font-size:17px;font-weight:700;">—</div>
        <div id="gapDir" style="font-size:10px;margin-top:4px;font-family:var(--font-mono);">—</div>
        <div id="gapFill" style="font-size:9px;margin-top:3px;color:var(--text-dim);">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(120,80,255,0.2);padding:13px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ce93d8;margin-bottom:5px;">PM VWAP</div>
        <div id="pmVwap" style="font-family:var(--font-mono);font-size:17px;font-weight:700;color:var(--gold);">—</div>
        <div style="font-size:9px;margin-top:4px;color:var(--text-dim);">Pre-mkt benchmark</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(120,80,255,0.2);padding:13px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ce93d8;margin-bottom:5px;">PM HIGH / LOW</div>
        <div id="pmHighLow" style="font-family:var(--font-mono);font-size:12px;font-weight:700;color:var(--text-primary);line-height:1.6;">—</div>
        <div id="pmVol" style="font-size:9px;margin-top:3px;color:var(--text-dim);">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(120,80,255,0.2);padding:13px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ce93d8;margin-bottom:5px;">EXT SIGNAL</div>
        <div id="extSignal" style="font-family:var(--font-mono);font-size:13px;font-weight:700;line-height:1.3;">—</div>
        <div id="extScore" style="font-size:9px;margin-top:4px;color:var(--text-dim);">Score: —</div>
      </div>

    </div>


  </div>

  <!-- NEWS PANEL — full width -->
  <div class="panel" id="news-panel" style="grid-column:1/-1;border:1px solid rgba(255,193,7,0.25);background:rgba(15,12,0,0.97);">
    <div class="panel-title" onclick="togglePanel('news-panel')" style="cursor:pointer;" title="Click to collapse" style="color:#ffd600;margin-bottom:16px;">
      📰 Real-Time News — Market Impact on TSLA
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;margin-left:12px;">YAHOO FINANCE · REUTERS · MARKETWATCH · BENZINGA · ELECTREK · SEC 8-K FILINGS</span>
     <span class="panel-collapse-btn" id="btn-news-panel">▾</span></div>

    <!-- Sentiment summary bar -->
    <div style="display:grid;grid-template-columns:repeat(5,1fr);gap:10px;margin-bottom:14px;">
      <div style="background:var(--bg3);border:1px solid rgba(255,193,7,0.2);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ffd600;margin-bottom:5px;">NEWS SIGNAL</div>
        <div id="newsSignal" style="font-family:var(--font-mono);font-size:15px;font-weight:700;">—</div>
        <div id="newsScore" style="font-size:9px;margin-top:4px;color:var(--text-dim);">Score: —</div>
      </div>
      <div style="background:var(--bg3);border:1px solid rgba(0,255,136,0.2);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--accent-green);margin-bottom:5px;">BULLISH</div>
        <div id="newsBullCount" style="font-family:var(--font-mono);font-size:22px;font-weight:700;color:var(--accent-green);">—</div>
        <div style="font-size:9px;color:var(--text-dim);">articles</div>
      </div>
      <div style="background:var(--bg3);border:1px solid rgba(255,51,85,0.2);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--accent-red);margin-bottom:5px;">BEARISH</div>
        <div id="newsBearCount" style="font-family:var(--font-mono);font-size:22px;font-weight:700;color:var(--accent-red);">—</div>
        <div style="font-size:9px;color:var(--text-dim);">articles</div>
      </div>
      <div style="background:var(--bg3);border:1px solid rgba(255,193,7,0.2);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ffd600;margin-bottom:5px;">TOTAL SOURCES</div>
        <div id="newsTotalCount" style="font-family:var(--font-mono);font-size:22px;font-weight:700;color:var(--gold);">—</div>
        <div style="font-size:9px;color:var(--text-dim);">articles scanned</div>
      </div>
      <div style="background:var(--bg3);border:1px solid rgba(255,193,7,0.2);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ffd600;margin-bottom:5px;">LAST REFRESH</div>
        <div id="newsUpdated" style="font-family:var(--font-mono);font-size:10px;font-weight:700;color:var(--text-dim);line-height:1.4;">—</div>
      </div>
    </div>

    <!-- HIGH IMPACT articles (top row) -->
    <div style="margin-bottom:12px;">
      <div style="font-size:9px;letter-spacing:3px;color:#ffd600;text-transform:uppercase;margin-bottom:8px;">🔥 High Impact Headlines</div>
      <div id="highImpactNews" style="display:grid;grid-template-columns:repeat(auto-fill,minmax(340px,1fr));gap:8px;"></div>
    </div>

    <!-- ALL articles feed -->
    <div style="border-top:1px solid var(--border);padding-top:12px;">
      <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px;">
        <div style="font-size:9px;letter-spacing:3px;color:#ffd600;text-transform:uppercase;">All News Feed</div>
        <div style="display:flex;gap:8px;">
          <button onclick="filterNews('all')"    id="filterAll"  style="font-family:var(--font-mono);font-size:9px;background:var(--gold);color:#000;border:none;padding:3px 10px;cursor:pointer;border-radius:2px;">ALL</button>
          <button onclick="filterNews('bull')"   id="filterBull" style="font-family:var(--font-mono);font-size:9px;background:var(--bg3);color:var(--accent-green);border:1px solid var(--accent-green);padding:3px 10px;cursor:pointer;border-radius:2px;">BULLISH</button>
          <button onclick="filterNews('bear')"   id="filterBear" style="font-family:var(--font-mono);font-size:9px;background:var(--bg3);color:var(--accent-red);border:1px solid var(--accent-red);padding:3px 10px;cursor:pointer;border-radius:2px;">BEARISH</button>
          <button onclick="filterNews('sec')"    id="filterSEC"  style="font-family:var(--font-mono);font-size:9px;background:var(--bg3);color:#b388ff;border:1px solid #b388ff;padding:3px 10px;cursor:pointer;border-radius:2px;">SEC FILINGS</button>
        </div>
      </div>
      <div id="newsFeed" style="display:flex;flex-direction:column;gap:6px;max-height:260px;overflow-y:auto;"></div>
    </div>
  </div>

  <!-- SPY MACRO PANEL — full width -->
  <div class="panel" id="spy-panel" style="grid-column:1/-1;border:1px solid rgba(0,180,255,0.25);background:rgba(0,10,25,0.95);">
    <div class="panel-title" onclick="togglePanel('spy-panel')" style="cursor:pointer;" title="Click to collapse" style="color:#29b6f6;margin-bottom:16px;">
      🌍 SPY / Macro Market Monitor — Impact on TSLA
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;margin-left:12px;">S&amp;P 500 · NASDAQ · VIX FEAR INDEX · BONDS · BETA · RELATIVE STRENGTH</span>
     <span class="panel-collapse-btn" id="btn-spy-panel">▾</span></div>

    <!-- ROW 1: Key numbers -->
    <div style="display:grid;grid-template-columns:repeat(7,1fr);gap:10px;margin-bottom:14px;">

      <div style="background:var(--bg3);border:1px solid rgba(0,180,255,0.2);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#29b6f6;margin-bottom:5px;">SPY</div>
        <div id="spyPrice" style="font-family:var(--font-mono);font-size:16px;font-weight:700;color:var(--text-primary);">—</div>
        <div id="spyChange" style="font-size:11px;margin-top:4px;font-family:var(--font-mono);">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(0,180,255,0.2);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#29b6f6;margin-bottom:5px;">QQQ</div>
        <div id="qqqPrice" style="font-family:var(--font-mono);font-size:16px;font-weight:700;color:var(--text-primary);">—</div>
        <div id="qqqChange" style="font-size:11px;margin-top:4px;font-family:var(--font-mono);">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(255,60,60,0.3);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#ef5350;margin-bottom:5px;">VIX FEAR</div>
        <div id="vixValOld" style="font-family:var(--font-mono);font-size:18px;font-weight:700;">—</div>
        <div id="vixRegimeOld" style="font-size:9px;margin-top:4px;">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(0,180,255,0.2);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#29b6f6;margin-bottom:5px;">TSLA Beta</div>
        <div id="betaVal" style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:var(--gold);">—</div>
        <div id="betaDesc" style="font-size:9px;margin-top:4px;color:var(--text-dim);">SPY × beta = TSLA move</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(0,180,255,0.2);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#29b6f6;margin-bottom:5px;">Expected Move</div>
        <div id="expectedMove" style="font-family:var(--font-mono);font-size:16px;font-weight:700;">—</div>
        <div id="actualMove" style="font-size:9px;margin-top:4px;color:var(--text-dim);">Actual: —</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(0,180,255,0.2);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#29b6f6;margin-bottom:5px;">SPY Trend</div>
        <div id="spyTrend" style="font-family:var(--font-mono);font-size:12px;font-weight:700;line-height:1.3;">—</div>
        <div id="spyRsi" style="font-size:9px;margin-top:4px;color:var(--text-dim);">RSI: —</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(0,180,255,0.2);padding:12px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#29b6f6;margin-bottom:5px;">Macro Signal</div>
        <div id="macroSignal" style="font-family:var(--font-mono);font-size:11px;font-weight:700;line-height:1.3;">—</div>
        <div id="macroScore" style="font-size:9px;margin-top:4px;color:var(--text-dim);">Score: —</div>
      </div>

    </div>

    <!-- ROW 2: Charts + Details -->
    <div style="display:grid;grid-template-columns:2fr 3fr;gap:12px;">



      <!-- VIX single line -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:12px 16px;border-radius:1px;display:flex;align-items:center;gap:16px;">
        <span style="font-size:9px;letter-spacing:2px;color:#ff6d00;text-transform:uppercase;flex-shrink:0;">⚡ VIX FEAR INDEX</span>
        <span id="vixVal" style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:#ff6d00;">—</span>
        <span id="vixRegime" style="font-family:var(--font-mono);font-size:11px;color:var(--text-dim);">—</span>
      </div>

      <!-- Key levels + macro reasons -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:1px;display:flex;flex-direction:column;gap:10px;">

        <div>
          <div style="font-size:9px;letter-spacing:2px;color:#29b6f6;margin-bottom:8px;text-transform:uppercase;">SPY Key Levels</div>
          <div id="spyLevels" style="display:flex;flex-direction:column;gap:4px;"></div>
          <div id="spyDetails" style="display:flex;flex-direction:column;gap:3px;margin-top:6px;"></div>
        </div>

        <div style="border-top:1px solid var(--border);padding-top:10px;">
          <div style="font-size:9px;letter-spacing:2px;color:#29b6f6;margin-bottom:8px;text-transform:uppercase;">Why It Matters</div>
          <div id="macroReasons" style="display:flex;flex-direction:column;gap:5px;"></div>
        </div>

        <div style="border-top:1px solid var(--border);padding-top:10px;">
          <div style="font-size:9px;letter-spacing:2px;color:#29b6f6;margin-bottom:6px;text-transform:uppercase;">QQQ / TLT</div>
          <div id="qqqDetails" style="display:flex;flex-direction:column;gap:3px;margin-bottom:6px;"></div>
          <div id="tltDetails" style="font-size:10px;color:var(--text-dim);font-family:var(--font-mono);"></div>
        </div>

        <div style="border-top:1px solid var(--border);padding-top:10px;">
          <div style="font-size:9px;letter-spacing:2px;color:#29b6f6;margin-bottom:6px;text-transform:uppercase;">Relative Strength</div>
          <div style="display:flex;gap:8px;align-items:center;margin-bottom:6px;">
            <span id="rsSignal" style="font-family:var(--font-mono);font-size:11px;font-weight:700;">—</span>
            <span id="rsVal" style="font-size:10px;color:var(--text-dim);">—</span>
          </div>
          <div id="rsDetails" style="display:flex;flex-direction:column;gap:4px;"></div>
        </div>

      </div>
    </div>
  </div>

  <!-- MARKET MAKER PANEL — full width -->
  <div class="panel" id="mm-panel" style="grid-column:1/-1;border:1px solid rgba(138,43,226,0.35);background:rgba(10,5,20,0.95);">
    <div class="panel-title" onclick="togglePanel('mm-panel')" style="cursor:pointer;" title="Click to collapse" style="color:#b388ff;margin-bottom:16px;">
      🎰 Market Maker Mechanics — GEX · Max Pain · Options Flow · Dark Pools
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;margin-left:12px;">CITADEL SECURITIES · VIRTU · SUSQUEHANNA · JANE STREET</span>
     <span class="panel-collapse-btn" id="btn-mm-panel">▾</span></div>

    <!-- ROW 1: Key numbers -->
    <div style="display:grid;grid-template-columns:repeat(6,1fr);gap:10px;margin-bottom:14px;">

      <div style="background:var(--bg3);border:1px solid rgba(138,43,226,0.3);padding:14px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#b388ff;text-transform:uppercase;margin-bottom:6px;">Net GEX</div>
        <div id="mmGexVal" style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:var(--text-primary);">—</div>
        <div id="mmGexSig" style="font-size:9px;margin-top:4px;color:var(--text-dim);">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(138,43,226,0.3);padding:14px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#b388ff;text-transform:uppercase;margin-bottom:6px;">Max Pain</div>
        <div id="mmMaxPain" style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:var(--gold);">—</div>
        <div id="mmPinRisk" style="font-size:9px;margin-top:4px;color:var(--text-dim);">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(138,43,226,0.3);padding:14px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#b388ff;text-transform:uppercase;margin-bottom:6px;">Put / Call Ratio</div>
        <div id="mmPCRatio" style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:var(--text-primary);">—</div>
        <div id="mmPCSignal" style="font-size:9px;margin-top:4px;color:var(--text-dim);">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(138,43,226,0.3);padding:14px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#b388ff;text-transform:uppercase;margin-bottom:6px;">IV Rank</div>
        <div id="mmIVRank" style="font-family:var(--font-mono);font-size:18px;font-weight:700;color:var(--text-primary);">—</div>
        <div id="mmIVSig" style="font-size:9px;margin-top:4px;color:var(--text-dim);">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(138,43,226,0.3);padding:14px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#b388ff;text-transform:uppercase;margin-bottom:6px;">Dealer Hedging</div>
        <div id="mmHedging" style="font-family:var(--font-mono);font-size:11px;font-weight:700;color:var(--text-primary);line-height:1.3;">—</div>
      </div>

      <div style="background:var(--bg3);border:1px solid rgba(138,43,226,0.3);padding:14px;border-radius:1px;text-align:center;">
        <div style="font-size:9px;letter-spacing:2px;color:#b388ff;text-transform:uppercase;margin-bottom:6px;">Expiry / 0DTE</div>
        <div id="mmExpiry" style="font-family:var(--font-mono);font-size:13px;font-weight:700;color:var(--text-primary);">—</div>
        <div id="mmZeroDte" style="font-size:9px;margin-top:4px;color:var(--text-dim);">—</div>
      </div>

    </div>

    <!-- ROW 2: Walls + GEX chart + Dark Pools -->
    <div style="display:grid;grid-template-columns:1fr 2fr;gap:12px;margin-bottom:14px;">

      <!-- Call/Put Walls -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:1px;">
        <div style="font-size:9px;letter-spacing:2px;color:#ff3355;margin-bottom:8px;text-transform:uppercase;">🔴 Call Walls — Resistance</div>
        <div id="mmCallWalls" style="display:flex;flex-direction:column;gap:5px;margin-bottom:12px;"></div>
        <div style="font-size:9px;letter-spacing:2px;color:#00ff88;margin-bottom:8px;text-transform:uppercase;">🟢 Put Walls — Support</div>
        <div id="mmPutWalls" style="display:flex;flex-direction:column;gap:5px;"></div>
      </div>

      <!-- Dark Pool Levels -->
      <div style="background:var(--bg3);border:1px solid var(--border);padding:14px;border-radius:1px;">
        <div style="font-size:9px;letter-spacing:2px;color:var(--gold);margin-bottom:8px;text-transform:uppercase;">🌑 Dark Pool Levels</div>
        <div style="font-size:9px;color:var(--text-dim);margin-bottom:8px;">High-volume nodes = institutional prints</div>
        <div style="font-size:9px;color:#ff6d00;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px;">Above Price (Resistance)</div>
        <div id="dpAbove" style="display:flex;flex-direction:column;gap:4px;margin-bottom:10px;"></div>
        <div style="font-size:9px;color:#00ff88;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px;">Below Price (Support)</div>
        <div id="dpBelow" style="display:flex;flex-direction:column;gap:4px;margin-bottom:10px;"></div>
        <div style="font-size:9px;color:#b388ff;margin-bottom:5px;text-transform:uppercase;letter-spacing:1px;">Volume Gap Days</div>
        <div id="dpGaps" style="display:flex;flex-direction:column;gap:4px;"></div>
      </div>

    </div>


  </div>

  <!-- WALL STREET MODELS PANEL — full width -->
  <div class="panel" id="inst-panel" style="grid-column:1/-1;">
    <div class="panel-title" onclick="togglePanel('inst-panel')" style="cursor:pointer;" title="Click to collapse" style="margin-bottom:16px;">
      Wall Street &amp; Hedge Fund Models
      <span style="font-size:9px;color:var(--text-dim);letter-spacing:2px;margin-left:12px;">GOLDMAN · RENAISSANCE · CITADEL · AQR · JPMORGAN · TWO SIGMA · BRIDGEWATER</span>
     <span class="panel-collapse-btn" id="btn-inst-panel">▾</span></div>
    <div style="display:grid;grid-template-columns:repeat(auto-fill,minmax(280px,1fr));gap:12px;" id="instModelsGrid">
      <div class="no-alerts">Computing institutional models...</div>
    </div>
    <!-- Confluence Meter -->
    <div style="margin-top:16px;padding-top:16px;border-top:1px solid var(--border);">
      <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px;">
        <span style="font-size:9px;letter-spacing:3px;color:var(--gold);text-transform:uppercase;">Model Confluence</span>
        <span id="confluenceLabel" style="font-family:var(--font-mono);font-size:11px;color:var(--text-dim);">—</span>
      </div>
      <div style="display:flex;gap:6px;align-items:center;">
        <span style="font-size:9px;color:var(--accent-red);width:40px;text-align:right;">BEAR</span>
        <div style="flex:1;height:8px;background:linear-gradient(90deg,#ff3355,#1e2540,#00ff88);border-radius:4px;position:relative;">
          <div id="confluenceNeedle" style="position:absolute;top:-4px;width:4px;height:16px;background:var(--gold);border-radius:2px;left:50%;transform:translateX(-50%);transition:left 0.8s ease;"></div>
        </div>
        <span style="font-size:9px;color:var(--accent-green);width:40px;">BULL</span>
      </div>
      <div style="display:flex;justify-content:space-between;margin-top:8px;" id="modelVotes">
      </div>
    </div>
  </div>




  <!-- ═══════════════════════════════════════════════════════════ -->
  <!-- DARTHVADER 2.0 — TSLA BEHAVIORAL STATE ENGINE              -->
  <!-- Layer 6 Meta Controller + Layer 3 Probabilistic Signals    -->
  <!-- ═══════════════════════════════════════════════════════════ -->
  <!-- RIGHT: INSTITUTIONAL -->
  <div class="panel" style="overflow-y:auto;max-height:300px;grid-column:1/-1;">
    <div class="panel-title">Institutional Holdings (SEC 13F)</div>
    <div id="instList"><div class="no-alerts">Loading 13F data from SEC EDGAR...</div></div>
  </div>

  <!-- ALERT LOG -->
  <div class="panel" style="overflow-y:auto;max-height:200px;grid-column:1/-1;">
    <div class="panel-title">Alert Log</div>
    <div id="alertLog"><div class="no-alerts">Monitoring... no signals yet.</div></div>
  </div>

  <!-- SPY / MACRO PANEL — full width -->



</body>
</html>
"""


# ═══════════════════════════════════════════════════════════════
#  ENTRY POINT

# ── Weekly ML retrain scheduler ────────────────────────────────────────────────
def _weekly_retrain_scheduler():
    """Runs forever — triggers ML retrain every Sunday at midnight."""
    import time as _t2
    print("[SCHEDULER] Weekly retrain scheduler active", flush=True)
    while True:
        try:
            now = datetime.now()
            days_until_sun = (6 - now.weekday()) % 7 or 7
            next_sun = (now + timedelta(days=days_until_sun)).replace(
                hour=0, minute=5, second=0, microsecond=0)
            wait = (next_sun - now).total_seconds()
            print(f"[SCHEDULER] Next retrain: {next_sun.strftime('%a %Y-%m-%d %H:%M')} "
                  f"({wait/3600:.1f}h)", flush=True)
            _t2.sleep(max(wait, 300))
            if datetime.now().weekday() == 6:  # Sunday
                print("[SCHEDULER] 🔄 Sunday retrain firing...", flush=True)
                _run_ml_retrain()
        except Exception as _se:
            print(f"[SCHEDULER] Error: {_se}", flush=True)
            import time as _t3; _t3.sleep(3600)


# ── Start background threads with delay so gunicorn can bind port first ──
def start_background_threads():
    time.sleep(3)  # short wait for gunicorn to bind port
    print("[STARTUP] Starting background monitor threads...", flush=True)
    # Pre-load ML model — check feature compatibility and retrain if needed
    _EXPECTED_ML_FEATURES = [
            "ret_1b","ret_3b","ret_6b","ret_12b","ret_48b",
            "rsi_14","rsi_6","rsi_ob","rsi_os","macd_hist","vix","vix_high",
            "vol_ratio","vol_surge","atr_ratio","realized_vol",
            "ofi_6b","ofi_zscore","vwap_dist","above_vwap",
            "tsla_spy_corr","spy_ret_1b","spy_decouple","daily_ret_so_far",
            "above_daily_ma20","daily_trend_up","trend_score","above_ema9","above_ema21",
            "time_of_day","is_open","is_close","is_lunch","day_of_week","bb_pct",
            "dist_from_high","dist_from_low","absorption",
            "earn_proximity","earn_near_5d","earn_near_10d",
            "iv_front","iv_back","iv_term_spread","iv_ratio","pc_ratio","pc_delta",
            "delta_atm","gamma_exposure","theta_decay","vega_exposure","iv_skew",
            # SPY/QQQ market context (NEW — 15 features)
            "spy_rsi","spy_ob","spy_os","spy_macd_bull","spy_bb_pct",
            "spy_mom_5d","spy_above_200",
            "qqq_rsi","qqq_ob","qqq_os","qqq_macd_bull","qqq_mom_5d","qqq_bull",
            "market_ob","market_os"
        ]
    try:
        pkg = _load_ml_model()
        if pkg:
            loaded_cols = pkg.get("feature_cols", [])
            # Check if loaded model's features match what run_analysis sends
            # Check feature count — new model has 47 features (old had 37 or 54)
            if len(loaded_cols) != len(_EXPECTED_ML_FEATURES):
                print(f"[STARTUP] ⚠️ ML feature count mismatch: loaded={len(loaded_cols)} expected={len(_EXPECTED_ML_FEATURES)} — retraining with enhanced model...", flush=True)
                global _ml_model_cache
                _ml_model_cache = None
                threading.Thread(target=_run_ml_retrain, daemon=True).start()
            else:
                n_models = pkg.get("n_models", 1)
                print(f"[STARTUP] ✅ ML ready: {pkg.get('model_name','?')} ({n_models} models) AUC={pkg.get('auc',0):.3f} features={len(loaded_cols)}", flush=True)
        else:
            print("[STARTUP] ❌ ML model NOT found — auto-training now (takes ~60s)...", flush=True)
            threading.Thread(target=_run_ml_retrain, daemon=True).start()
    except Exception as _mle:
        print(f"[STARTUP] ML model load error: {_mle}", flush=True)
    # Run first analysis immediately so dashboard populates fast
    try:
        print("[STARTUP] Running first analysis...", flush=True)
        run_analysis()
    except Exception as e:
        print(f"  ⚠️ First analysis error: {e}")
    # Start continuous loops (monitor_loop already calls run_analysis every 5min)
    for target in [fetch_institutional_periodically, monitor_loop, _weekly_retrain_scheduler]:
        try:
            threading.Thread(target=target, daemon=True).start()
        except Exception as e:
            print(f"  ⚠️ Thread error ({target.__name__}): {e}")

# Wrapped in its own thread so import returns instantly
threading.Thread(target=start_background_threads, daemon=True).start()

if __name__ == "__main__":
    print("""
╔══════════════════════════════════════════════════════╗
║         TSLA ALERT SYSTEM — DARTHVADER 2.0 — Starting Up              ║
╠══════════════════════════════════════════════════════╣
║  Dashboard  →  http://localhost:5050                 ║
║  SMS alerts →  +1 (954) 702-5845                     ║
║  Interval   →  every 5 minutes                       ║
╚══════════════════════════════════════════════════════╝
""")
    port = int(os.getenv("PORT", 5050))
    app.run(host="0.0.0.0", port=port, debug=False, threaded=True, use_reloader=False)
