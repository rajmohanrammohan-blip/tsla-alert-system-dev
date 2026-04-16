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
# ── Import schwab_client (fully before schwab_l2 to avoid circular imports) ──
try:
    import schwab_client as sc
    _SCHWAB_OK = sc.is_configured()
    if _SCHWAB_OK:
        print("[SCHWAB] Credentials found — Schwab API enabled", flush=True)
    else:
        print("[SCHWAB] No credentials — using yfinance fallback", flush=True)
except (ImportError, Exception) as _sc_err:
    print(f"[SCHWAB] schwab_client not available: {_sc_err}", flush=True)
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
        def get_auth_url(): return None, "schwab_client not installed"
        @staticmethod
        def complete_auth_from_url(u): return False, "not installed", ""
    _SCHWAB_OK = False

# Import schwab_l2 AFTER schwab_client is fully loaded (prevents circular import)
try:
    import schwab_l2
    _L2_AVAILABLE = True
except Exception as _l2_err:
    _L2_AVAILABLE = False

# ─────────────────────────────────────────────
#  CONFIG
# ─────────────────────────────────────────────
TICKER          = "TSLA"

# Per-ticker state cache + watchlist
_ticker_cache      = {}   # {symbol: {state, timestamp}}
_WATCHLIST         = ["TSLA", "NVDA", "AAPL", "AMZN", "META", "MSFT", "SPY", "QQQ"]
_WATCHLIST_SCORES  = {}   # {symbol: {price, change, rsi, score, action}}
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
    "ticker": "TSLA",          # always populated — never undefined in JS
    "price": None,
    "price_change_pct": None,
    "session_type": "UNKNOWN",
    "signal": "HOLD",
    "signal_strength": 0,
    "indicators": {},
    "ichimoku": {},
    "hmm": {},
    "institutional_models": {},
    "mm_data":   {},   # Market maker: GEX, Max Pain, options flow
    "uoa_data":  {},   # Unusual options activity — sweeps, whales, flow
    "ml_signal": {"signal":"HOLD","confidence":0,"probability":0.5,"available":False},
    "tsla_4h":      {},
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

    # POC / Value Area in generate_signal
    _poc_s = indicators.get("poc_price", 0) or 0
    _vah_s = indicators.get("vah", 0) or 0
    _val_s = indicators.get("val", 0) or 0
    _cur   = float(indicators.get("current_price", 0) or price_arg)
    if _poc_s > 0:
        if _vah_s > 0 and _cur > _vah_s:
            score += 12; reasons.append(f"Price above VAH ${_vah_s:.0f} — value area breakout ▲")
        elif _val_s > 0 and _cur < _val_s:
            score -= 12; reasons.append(f"Price below VAL ${_val_s:.0f} — value area breakdown ▼")
        elif _cur > _poc_s * 1.01:
            score += 5; reasons.append(f"Price above POC ${_poc_s:.0f}")
        elif _cur < _poc_s * 0.99:
            score -= 5; reasons.append(f"Price below POC ${_poc_s:.0f}")

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
        # SPY — Schwab first (daily bars = 1440min interval)
        spy_hist, _spy_src = _schwab_or_yf("SPY", period_years=1, freq_minutes=1440,
                                             yf_period="6mo", yf_interval="1d")
        # QQQ — Schwab first
        qqq_hist, _qqq_src = _schwab_or_yf("QQQ", period_years=1, freq_minutes=1440,
                                             yf_period="6mo", yf_interval="1d")
        # VIX — yfinance only (Schwab doesn't carry ^VIX)
        vix_hist = yf.Ticker("^VIX").history(period="6mo", interval="1d")
        # TLT — Schwab first
        tlt_hist, _tlt_src = _schwab_or_yf("TLT", period_years=0.5, freq_minutes=1440,
                                             yf_period="3mo", yf_interval="1d")
        print(f"  🌍 Market data: SPY={_spy_src} QQQ={_qqq_src} TLT={_tlt_src}", flush=True)
        if spy_hist.empty:
            print("  ⚠️ SPY hist empty - using fallback", flush=True)
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
            # QQQ 4h RSI (resample from 1h)
            try:
                # QQQ 1h — Schwab first
                _qqq_1h_df, _qqq_1h_src = _schwab_or_yf("QQQ", period_years=0.5,
                    freq_minutes=60, yf_period="60d", yf_interval="1h")
                qqq_1h_closes = _qqq_1h_df["Close"].astype(float) if not _qqq_1h_df.empty else None
                if qqq_1h_closes is not None and len(qqq_1h_closes) > 14:
                    _q1c = qqq_1h_closes
                    try:
                        import pytz as _ptz2
                        _et2 = _ptz2.timezone("America/New_York")
                        _q1c_et = _q1c.copy()
                        if _q1c_et.index.tz is None:
                            _q1c_et.index = _q1c_et.index.tz_localize("UTC")
                        _q1c_et.index = _q1c_et.index.tz_convert(_et2)
                        qqq_4h = _q1c_et.resample("4h", offset="9h30min").last().dropna()
                    except Exception:
                        qqq_4h = _q1c.resample("4h").last().dropna()
                    if len(qqq_4h) > 14:
                        _q4d = qqq_4h.diff()
                        _q4g = _q4d.where(_q4d>0,0).rolling(14).mean()
                        _q4l = -_q4d.where(_q4d<0,0).rolling(14).mean()
                        qqq_rsi_4h = round(float((100-100/(1+_q4g/(_q4l+1e-9))).iloc[-1]),1)
                        result["qqq_rsi_4h"] = qqq_rsi_4h
                        result["qqq_ob_4h"]  = qqq_rsi_4h > 70
                        result["qqq_os_4h"]  = qqq_rsi_4h < 30
                        # Combined SPY+QQQ 4h both overbought = STRONG warning
                        result["mtf_both_ob"] = result.get("spy_ob_4h",False) and qqq_rsi_4h > 70
                        result["mtf_both_os"] = result.get("spy_os_4h",False) and qqq_rsi_4h < 30
                        print(f"  📊 QQQ RSI — 4h:{qqq_rsi_4h} | Daily:{qqq_rsi}", flush=True)
            except Exception:
                result["qqq_rsi_4h"] = qqq_rsi
                result["qqq_ob_4h"] = qqq_rsi > 70
                result["qqq_os_4h"] = qqq_rsi < 30
                result["mtf_both_ob"] = False
                result["mtf_both_os"] = False

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
                for i in range(-min(60, len(vix_closes)), 0) if abs(i) <= len(vix_closes)
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

        # SPY 4h RSI — use Schwab 1h bars first (more reliable on Railway)
        try:
            spy_1h_closes = None
            # Try Schwab 1h bars
            try:
                import schwab_client as _sc_ref
                if _sc_ref.is_configured() and _sc_ref.get_client():
                    _spy_1h_schwab = _sc_ref.get_price_history("SPY", period_years=1, freq_minutes=60)
                    if _spy_1h_schwab is not None and not _spy_1h_schwab.empty and len(_spy_1h_schwab) > 50:
                        spy_1h_closes = _spy_1h_schwab["Close"].astype(float)
                        print(f"  📡 Schwab SPY 1h: {len(spy_1h_closes)} bars", flush=True)
            except Exception as _sch_e:
                pass
            # Fall back to yfinance
            if spy_1h_closes is None:
                spy_1h = yf.Ticker("SPY").history(period="60d", interval="1h")
                if not spy_1h.empty and len(spy_1h) > 14:
                    spy_1h_closes = spy_1h["Close"].astype(float)
            if spy_1h_closes is not None and len(spy_1h_closes) > 14:
                _s1c  = spy_1h_closes
                _s1d  = _s1c.diff()
                _s1g  = _s1d.where(_s1d>0,0).rolling(14).mean()
                _s1l  = -_s1d.where(_s1d<0,0).rolling(14).mean()
                spy_rsi_1h = round(float((100-100/(1+_s1g/(_s1l+1e-9))).iloc[-1]),1)
                # Resample 1h → 4h with ET timezone alignment
                try:
                    import pytz as _ptz
                    _et = _ptz.timezone("America/New_York")
                    _s1c_et = _s1c.copy()
                    if _s1c_et.index.tz is None:
                        _s1c_et.index = _s1c_et.index.tz_localize("UTC")
                    _s1c_et.index = _s1c_et.index.tz_convert(_et)
                    spy_4h = _s1c_et.resample("4h", offset="9h30min").last().dropna()
                except Exception:
                    spy_4h = _s1c.resample("4h").last().dropna()
                if len(spy_4h) > 14:
                    _s4d = spy_4h.diff()
                    _s4g = _s4d.where(_s4d>0,0).rolling(14).mean()
                    _s4l = -_s4d.where(_s4d<0,0).rolling(14).mean()
                    spy_rsi_4h = round(float((100-100/(1+_s4g/(_s4l+1e-9))).iloc[-1]),1)
                else:
                    spy_rsi_4h = spy_rsi_1h
                result["spy_rsi_1h"]  = spy_rsi_1h
                result["spy_rsi_4h"]  = spy_rsi_4h
                result["spy_ob_1h"]   = spy_rsi_1h > 70
                result["spy_os_1h"]   = spy_rsi_1h < 30
                result["spy_ob_4h"]   = spy_rsi_4h > 70
                result["spy_os_4h"]   = spy_rsi_4h < 30
                # Multi-timeframe confluence
                result["spy_mtf_ob"]  = spy_rsi_4h > 70 and spy_rsi > 65  # 4h + daily both OB
                result["spy_mtf_os"]  = spy_rsi_4h < 30 and spy_rsi < 35  # 4h + daily both OS
                print(f"  📊 SPY RSI — Daily:{spy_rsi} | 4h:{spy_rsi_4h} | 1h:{spy_rsi_1h}", flush=True)
                if result["spy_mtf_ob"]: print("  ⚠️ SPY MULTI-TIMEFRAME OVERBOUGHT", flush=True)
                if result["spy_mtf_os"]: print("  ✅ SPY MULTI-TIMEFRAME OVERSOLD — bounce potential", flush=True)
        except Exception as _1he:
            print(f"  ⚠️ SPY 4h RSI failed: {_1he} — using daily RSI as fallback", flush=True)
            result["spy_rsi_1h"] = spy_rsi; result["spy_rsi_4h"] = spy_rsi
            result["spy_ob_1h"] = result["spy_ob"]; result["spy_ob_4h"] = result["spy_ob"]
            result["spy_os_1h"] = result["spy_os"]; result["spy_os_4h"] = result["spy_os"]
            result["spy_mtf_ob"] = False; result["spy_mtf_os"] = False

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
            for i in range(-min(60, len(spy_closes)), 0)
        ]

        # RS chart — normalized to 100 at 60 days ago
        base_tsla = float(tsla_closes.iloc[-60]) if len(tsla_closes) >= 60 else float(tsla_closes.iloc[0])
        base_spy  = float(spy_closes.iloc[-60])  if len(spy_closes)  >= 60 else float(spy_closes.iloc[0])
        base_qqq  = float(qqq_closes.iloc[-60])  if qqq_closes is not None and len(qqq_closes) >= 60 else None
        result["rs_history"] = []
        for i in range(-min(60, len(tsla_closes), len(spy_closes)), 0):
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
def _schwab_or_yf(symbol, period_years, freq_minutes, yf_period="6mo", yf_interval="1d"):
    """
    Fetch price history — Schwab first, yfinance fallback.
    Returns a DataFrame with Close/High/Low/Open/Volume columns.
    """
    import schwab_client as _sc_h
    # Try Schwab first
    try:
        if _sc_h.is_configured() and _sc_h.get_client():
            df = _sc_h.get_price_history(symbol, period_years=period_years, freq_minutes=freq_minutes)
            if df is not None and not df.empty and len(df) > 10:
                return df, "schwab"
    except Exception as _se:
        pass
    # Fall back to yfinance
    try:
        import yfinance as _yf_fb
        df = _yf_fb.Ticker(symbol).history(period=yf_period, interval=yf_interval)
        if not df.empty:
            return df, "yfinance"
    except Exception:
        pass
    import pandas as _pd_fb
    return _pd_fb.DataFrame(), "failed"


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
            for i in range(-min(60, len(close)), 0)
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
                           for i in range(-min(60, len(filtered)), 0) if i < len(filtered)]
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
                         for i in range(-min(60, len(zscore)), 0) if not pd.isna(zscore.iloc[i])]
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
                       for i in range(-min(60, len(smi_norm)), 0) if not pd.isna(smi_norm.iloc[i])]
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

        # Cap at 100 — scores above 100 erode user trust
        exit_score = min(100, exit_score)

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
            # IV Rank: compare current ATM IV to 52-week IV range
            # Use the options chain front-month ATM IV vs historical range
            try:
                import yfinance as _yf2
                # VIX only available via yfinance (Schwab doesn't carry ^VIX)
                _vix_hist = _yf2.Ticker("^VIX").history(period="1y", interval="1d")
                if not _vix_hist.empty and len(_vix_hist) > 50:
                    _vix_closes = _vix_hist["Close"].astype(float)
                    _vix_high52 = float(_vix_closes.max())
                    _vix_low52  = float(_vix_closes.min())
                    _vix_now    = float(_vix_closes.iloc[-1])
                    # Scale: current TSLA IV relative to VIX range
                    _vix_rank   = (_vix_now - _vix_low52) / (_vix_high52 - _vix_low52 + 1e-9) * 100
                    # Blend: 50% VIX rank + 50% chain percentile rank
                    _chain_high = round(float(np.percentile(iv_list, 90)) * 100, 1)
                    _chain_low  = round(float(np.percentile(iv_list, 10)) * 100, 1)
                    _chain_rank = (_chain_high > 0 and
                                   round((iv_now - _chain_low) / (_chain_high - _chain_low + 1e-9) * 100, 1))
                    iv_rank = round((_vix_rank * 0.6 + (_chain_rank or 50) * 0.4), 1)
                    iv_rank = max(0, min(100, iv_rank))
                    iv_high = _chain_high
                    iv_low  = _chain_low
                else:
                    raise ValueError("no VIX history")
            except Exception:
                # Fallback: chain cross-sectional percentile
                iv_high = round(float(np.percentile(iv_list, 90)) * 100, 1)
                iv_low  = round(float(np.percentile(iv_list, 10)) * 100, 1)
                iv_rank = round((iv_now - iv_low) / (iv_high - iv_low + 1e-9) * 100, 1) if iv_high > iv_low else 50
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


def fetch_stocktwits_sentiment(ticker="TSLA"):
    """
    Fetch StockTwits bull/bear ratio — free API, no key needed.
    Contrarian signal: >85% bulls = sell, <20% bulls = buy.
    """
    result = {"bull_pct": None, "bear_pct": None, "signal": "NEUTRAL",
              "message_vol": None, "contrarian_signal": None}
    try:
        import requests as _req
        url = f"https://api.stocktwits.com/api/2/streams/symbol/{ticker}.json"
        resp = _req.get(url, timeout=5,
                       headers={"User-Agent": "Mozilla/5.0"})
        if resp.status_code == 200:
            data = resp.json()
            msgs = data.get("messages", [])
            if msgs:
                bulls = sum(1 for m in msgs if m.get("entities", {}).get("sentiment", {}).get("basic") == "Bullish")
                bears = sum(1 for m in msgs if m.get("entities", {}).get("sentiment", {}).get("basic") == "Bearish")
                total = bulls + bears
                if total > 0:
                    bull_pct = round(bulls / total * 100, 1)
                    bear_pct = round(bears / total * 100, 1)
                    result["bull_pct"]      = bull_pct
                    result["bear_pct"]      = bear_pct
                    result["message_vol"]   = len(msgs)
                    # Contrarian: extreme bulls = sell signal, extreme bears = buy
                    if bull_pct > 85:
                        result["signal"] = "CONTRARIAN_SELL"
                        result["contrarian_signal"] = f"StockTwits {bull_pct:.0f}% bulls — extreme, contrarian SELL"
                    elif bull_pct < 20:
                        result["signal"] = "CONTRARIAN_BUY"
                        result["contrarian_signal"] = f"StockTwits {bull_pct:.0f}% bulls — extreme fear, contrarian BUY"
                    elif bull_pct > 65:
                        result["signal"] = "BULLISH_CROWD"
                    elif bull_pct < 40:
                        result["signal"] = "BEARISH_CROWD"
                    print(f"  🐦 StockTwits {ticker}: {bull_pct:.0f}% bulls / {bear_pct:.0f}% bears "
                          f"({len(msgs)} msgs) → {result['signal']}", flush=True)
    except Exception as _ste:
        pass
    return result


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
            for i in range(-min(60, len(roll_vol)), 0) if not np.isnan(roll_vol.iloc[i])
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

        # Earnings proximity reduces position size — binary event risk
        _earn_ctx2 = state.get("earnings_context", {}) if isinstance(state, dict) else {}
        if _earn_ctx2.get("earnings_mode"):
            _days2 = _earn_ctx2.get("days_away", 99)
            if _days2 <= 3:
                regime_mult = min(regime_mult, 0.40)
                print(f"  📅 Earnings in {_days2}d: size capped at 40%", flush=True)
            elif _days2 <= 7:
                regime_mult = min(regime_mult, 0.60)
                print(f"  📅 Earnings in {_days2}d: size capped at 60%", flush=True)
        # SPY/QQQ MTF overbought → reduce size further
        if spy_data.get("mtf_both_ob"):
            regime_mult = min(regime_mult, regime_mult * 0.75)
            print("  ⚠️ Market MTF overbought: size reduced 25%", flush=True)
        regime_mult = round(min(max(regime_mult, 0.10), 1.20), 3)

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
    # Track alert for quality scoring — use freshest price
    _live_p, _price_age = _get_live_price()
    _cur_price = _live_p or state.get("price", 0) or 0
    # Block signal-quality alerts during ML retrain (prevents garbage conf=100 signals)
    _RETRAIN_BLOCKED_KEYS = {"signal_BUY", "signal_SELL", "exit_alert", "entry_signal", "peak_top", "cap_bounce"}
    if _ml_retraining and (alert_key.startswith("signal_") or alert_key in _RETRAIN_BLOCKED_KEYS):
        print(f"  ⚠️ Alert suppressed — ML retrain in progress ({alert_key})", flush=True)
        return
    # Only block if BOTH: price_history empty AND it's outside regular hours
    # Don't block during market hours even if 1-min loop hasn't warmed up yet
    from datetime import datetime as _dt
    _now = _dt.now()
    _in_market = (_now.weekday() < 5 and
                  (_now.hour > 9 or (_now.hour == 9 and _now.minute >= 30)) and
                  _now.hour < 20)  # include pre/post market
    _price_stale = (_price_age is None or _price_age > 600) and not _in_market
    if _price_stale:
        print(f"  ⚠️ Alert price may be stale (age={_price_age}s, outside market) — skipping alert", flush=True)
        return  # Don't send alert with stale overnight price
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
        return
    # Price delta deduplication — don't repeat same alert if price barely moved
    _last_alert_price = state.get(f"_last_alert_price_{alert_key}", 0) or 0
    _cur_p = state.get("price", 0) or 0
    if _last_alert_price > 0 and _cur_p > 0:
        _delta_pct = abs(_cur_p - _last_alert_price) / _last_alert_price * 100
        if _delta_pct < 0.5 and last and (datetime.now() - last).total_seconds() < 1800:
            print(f"⏳ Alert deduplicated ({alert_key}) — price only moved {_delta_pct:.2f}% (need 0.5%)")
            return
    state[f"_last_alert_price_{alert_key}"] = _cur_p
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


def _get_live_price():
    """Get freshest available price — from 1-min tick, then state, then Schwab."""
    # _price_history has 1-min ticks
    if _price_history:
        tick = _price_history[-1]
        age  = time.time() - tick.get("ts", 0)
        if age < 300:  # less than 5 min old
            return float(tick["price"]), age
    # Fall back to state
    sp = state.get("price")
    if sp:
        return float(sp), 999
    return None, None


def log_alert(message, alert_key="default"):
    """Log to dashboard and send WhatsApp if configured."""
    print(f"🔔 ALERT: {message[:80]}...")
    send_whatsapp(message, alert_key)


# ═══════════════════════════════════════════════════════════════
#  CORE MONITOR LOOP
# ═══════════════════════════════════════════════════════════════

last_signal = None




# ─────────────────────────────────────────────────────────────
#  SPOCK BRAIN — Self-Learning Decision Engine
# ─────────────────────────────────────────────────────────────
import uuid as _uuid

_spock_decisions = []   # rolling log of all SPOCK decisions + outcomes
_spock_accuracy  = {    # running accuracy stats
    "total": 0, "correct_1h": 0, "correct_4h": 0, "correct_1d": 0,
    "win_rate_1h": None, "win_rate_4h": None, "win_rate_1d": None,
    "by_action": {},     # per-action win rates
    "by_conviction": {}, # high/low conviction win rates
    "last_correction":   None,
    "corrections_fired": 0,
}
_spock_weights = {      # SPOCK tier weights — self-adjusting
    "uoa":        30,   # Tier 1
    "ml":         30,
    "gex":        20,   # Tier 2
    "darthvader": 20,
    "signal":     10,   # Tier 3
    "entry_exit": 10,
    "hmm":         8,
    "macro":      10,
    "ofi":        10,   # Tier 3.5 volume
    "absorption":  6,
    "poc":         5,
    "vol_4h":      6,
    "cap":         5,   # Tier 4
    "ichimoku":    5,
    "news":        5,
    "momentum":    5,
}


def calculate_swing_context(closes, highs, lows, price, mm_data):
    """
    Multi-day swing context:
    - Weekly OI gravitational center
    - Daily candle pattern (bullish engulfing, morning star)
    - Descending channel from ATH
    - Key weekly support/resistance
    """
    import numpy as np
    result = {
        "weekly_gravity":   None,  # max OI strike for this week
        "daily_pattern":    None,  # candle pattern name
        "pattern_signal":   "NEUTRAL",
        "channel_top":      None,  # descending channel resistance
        "channel_mid":      None,
        "in_channel":       None,
        "swing_bias":       "NEUTRAL",
        "swing_reasons":    [],
    }
    try:
        # Weekly OI gravity = Max Pain (already computed)
        result["weekly_gravity"] = mm_data.get("max_pain")

        # Daily candle patterns from last 3 daily closes
        if len(closes) >= 78 * 3:  # 3 trading days of 5-min bars
            def _daily_ohlc(i_day):
                """Get OHLC for i_day days ago (0=today)"""
                start = -(i_day+1)*78
                end   = -i_day*78 if i_day > 0 else len(closes)
                sl = slice(max(0, len(closes)+start), max(0, len(closes)+end) if end < 0 else len(closes))
                d_c = closes.iloc[sl]
                d_h = highs.iloc[sl]
                d_l = lows.iloc[sl]
                if len(d_c) == 0: return None
                return {
                    "open":  float(d_c.iloc[0]),
                    "close": float(d_c.iloc[-1]),
                    "high":  float(d_h.max()),
                    "low":   float(d_l.min()),
                }

            d0 = _daily_ohlc(0)  # today
            d1 = _daily_ohlc(1)  # yesterday
            d2 = _daily_ohlc(2)  # 2 days ago

            if d0 and d1:
                # Bullish engulfing: yesterday red, today green and bigger
                if (d1["close"] < d1["open"] and       # yesterday red
                    d0["close"] > d0["open"] and       # today green
                    d0["close"] > d1["open"] and       # today close > yesterday open
                    d0["open"]  < d1["close"]):        # today open < yesterday close
                    result["daily_pattern"]  = "BULLISH_ENGULFING"
                    result["pattern_signal"] = "BUY"
                    result["swing_reasons"].append("Daily bullish engulfing — high conviction reversal signal")

                # Bearish engulfing
                elif (d1["close"] > d1["open"] and
                      d0["close"] < d0["open"] and
                      d0["close"] < d1["open"] and
                      d0["open"]  > d1["close"]):
                    result["daily_pattern"]  = "BEARISH_ENGULFING"
                    result["pattern_signal"] = "SELL"
                    result["swing_reasons"].append("Daily bearish engulfing — distribution signal")

                # Morning star (3-day): big down, small body, big up
                elif d2 and (d2["close"] < d2["open"] and
                             abs(d1["close"]-d1["open"]) < abs(d2["close"]-d2["open"]) * 0.5 and
                             d0["close"] > d0["open"] and
                             d0["close"] > (d2["open"] + d2["close"])/2):
                    result["daily_pattern"]  = "MORNING_STAR"
                    result["pattern_signal"] = "BUY"
                    result["swing_reasons"].append("Morning star pattern — 3-day bullish reversal confirmed")

        # Descending channel from Dec 2025 ATH ($498.83)
        # Channel: ATH=$498.83 on ~Dec 17 2025, roughly 120 trading days ago
        # Slope: approximate ~$1/day decline
        _ath     = 498.83
        _days_since_ath = 120  # approximate
        _slope   = (_ath - price) / _days_since_ath
        _ch_top  = round(_ath - _slope * (_days_since_ath - 10), 2)  # channel resistance
        _ch_mid  = round(_ch_top - (_ath - price) * 0.3, 2)
        result["channel_top"] = _ch_top
        result["channel_mid"] = _ch_mid
        result["in_channel"]  = price < _ch_top

        if price > _ch_top * 0.98:  # within 2% of channel resistance
            result["swing_reasons"].append(f"Near descending channel resistance ${_ch_top:.0f} — caution")
            result["swing_bias"] = "BEARISH"
        elif price < _ch_mid * 0.98:
            result["swing_reasons"].append(f"Well below channel mid ${_ch_mid:.0f} — oversold swing")
            result["swing_bias"] = "BULLISH"

        # Set overall swing bias
        if result["pattern_signal"] == "BUY":
            result["swing_bias"] = "BULLISH"
        elif result["pattern_signal"] == "SELL":
            result["swing_bias"] = "BEARISH"

    except Exception as _se:
        pass
    return result


def calculate_market_breadth(spy_data):
    """
    Fetch VIX term structure (VIX vs VIX3M) and market breadth.
    VIX backwardation = panic, weight mean-reversion signals higher.
    """
    result = {
        "vix":         spy_data.get("vix", 20),
        "vix3m":       None,
        "vix_backw":   False,   # VIX > VIX3M = backwardation = panic
        "vix_contango":False,   # VIX < VIX3M = normal = risk-on
        "term_spread": None,    # VIX - VIX3M
        "breadth_signal": "NEUTRAL",
    }
    try:
        import yfinance as _yf_b
        # VIX3M (3-month VIX) — VIXM or ^VIX3M
        _v3m = _yf_b.Ticker("^VIX3M").history(period="5d", interval="1d")
        if not _v3m.empty:
            vix3m = round(float(_v3m["Close"].iloc[-1]), 2)
            vix   = float(result["vix"] or 20)
            spread = round(vix - vix3m, 2)
            result["vix3m"]       = vix3m
            result["term_spread"] = spread
            result["vix_backw"]   = spread > 0    # VIX > VIX3M = backwardation
            result["vix_contango"]= spread < -1   # normal market
            if spread > 2:
                result["breadth_signal"] = "PANIC"      # strong backwardation
            elif spread > 0:
                result["breadth_signal"] = "STRESS"     # mild backwardation
            elif spread < -3:
                result["breadth_signal"] = "COMPLACENT" # very steep contango
            else:
                result["breadth_signal"] = "NORMAL"
            print(f"  📊 VIX Term: {vix:.1f} vs VIX3M:{vix3m:.1f} spread={spread:+.1f} "
                  f"({result['breadth_signal']})", flush=True)
    except Exception as _be:
        pass
    return result


def calculate_vwap_bands(closes, highs, lows, volumes):
    """
    Compute intraday VWAP + 1σ/2σ bands from 5-min bars.
    Also compute anchored VWAP from session low (swing support).
    
    Returns dict with vwap, bands, distance, signal.
    """
    import numpy as np
    result = {
        "vwap": None, "upper1": None, "lower1": None,
        "upper2": None, "lower2": None,
        "anchored_vwap": None, "above_vwap": None,
        "vwap_dist_pct": None, "vwap_signal": "NEUTRAL",
        "anchored_above": None,
    }
    try:
        typical = (highs + lows + closes) / 3
        cum_vol  = volumes.cumsum()
        cum_tp   = (typical * volumes).cumsum()
        vwap_s   = cum_tp / (cum_vol + 1e-9)

        # Standard deviation bands
        cum_var  = ((typical - vwap_s) ** 2 * volumes).cumsum()
        std_s    = (cum_var / (cum_vol + 1e-9)) ** 0.5

        price    = float(closes.iloc[-1])
        vwap_now = float(vwap_s.iloc[-1])
        std_now  = float(std_s.iloc[-1])

        result["vwap"]    = round(vwap_now, 2)
        result["upper1"]  = round(vwap_now + std_now, 2)
        result["upper2"]  = round(vwap_now + 2*std_now, 2)
        result["lower1"]  = round(vwap_now - std_now, 2)
        result["lower2"]  = round(vwap_now - 2*std_now, 2)

        above_vwap = price > vwap_now
        dist_pct   = (price - vwap_now) / vwap_now * 100
        result["above_vwap"]    = above_vwap
        result["vwap_dist_pct"] = round(dist_pct, 3)

        # VWAP signal
        if price > vwap_now + std_now:
            result["vwap_signal"] = "EXTENDED_ABOVE"   # overbought vs VWAP
        elif price > vwap_now:
            result["vwap_signal"] = "ABOVE_VWAP"        # bullish
        elif price > vwap_now - std_now:
            result["vwap_signal"] = "BELOW_VWAP"        # bearish
        else:
            result["vwap_signal"] = "EXTENDED_BELOW"    # oversold vs VWAP

        # Anchored VWAP from session low (last 20 bars)
        low_idx = int(lows.iloc[-78:].values.argmin())  # low of day
        if low_idx >= 0:
            anc_typical = typical.iloc[-78+low_idx:]
            anc_vol     = volumes.iloc[-78+low_idx:]
            anc_cv      = (anc_typical * anc_vol).cumsum()
            anc_v       = anc_vol.cumsum()
            anc_vwap    = float((anc_cv / (anc_v + 1e-9)).iloc[-1])
            result["anchored_vwap"]  = round(anc_vwap, 2)
            result["anchored_above"] = price > anc_vwap

    except Exception as e:
        pass
    return result


def calculate_vwap_bands_daily(closes, highs, lows, volumes):
    """Same but filters to today's bars only before computing."""
    from datetime import date as _d
    try:
        _today = _d.today()
        _mask  = closes.index.date == _today
        if _mask.sum() < 3:
            _last_date = closes.index.date[-1]
            _mask = closes.index.date == _last_date
        return calculate_vwap_bands(
            closes[_mask], highs[_mask], lows[_mask], volumes[_mask])
    except Exception:
        return calculate_vwap_bands(closes, highs, lows, volumes)


# ── Signal Weight Feedback — rolling accuracy per signal type ────────────────
_signal_accuracy_table = {}   # {signal_type: {correct:0, total:0, weight_adj:1.0}}

def _update_signal_weight(signal_type, was_correct):
    """Update rolling accuracy for a signal type and adjust its SPOCK weight."""
    if signal_type not in _signal_accuracy_table:
        _signal_accuracy_table[signal_type] = {
            "correct": 0, "total": 0, "weight_adj": 1.0, "history": []}
    entry = _signal_accuracy_table[signal_type]
    entry["history"].append(1 if was_correct else 0)
    entry["history"] = entry["history"][-20:]  # rolling 20
    entry["total"]   = len(entry["history"])
    entry["correct"] = sum(entry["history"])
    win_rate = entry["correct"] / max(entry["total"], 1)

    # Adjust weight: good signal → boost, bad signal → reduce
    if entry["total"] >= 5:
        if win_rate >= 0.70:
            entry["weight_adj"] = min(1.5, entry["weight_adj"] + 0.05)
        elif win_rate >= 0.55:
            entry["weight_adj"] = min(1.2, entry["weight_adj"])
        elif win_rate < 0.40:
            entry["weight_adj"] = max(0.5, entry["weight_adj"] - 0.1)
        elif win_rate < 0.50:
            entry["weight_adj"] = max(0.7, entry["weight_adj"] - 0.05)

    print(f"[FEEDBACK] {signal_type}: {win_rate:.0%} win ({entry['correct']}/{entry['total']}) "
          f"→ weight={entry['weight_adj']:.2f}", flush=True)


def get_signal_weight(signal_type):
    """Get current weight multiplier for a signal type. Default=1.0."""
    return _signal_accuracy_table.get(signal_type, {}).get("weight_adj", 1.0)


def _run_signal_feedback_update(decisions):
    """
    Called after outcomes are measured. Updates signal type weights
    based on which signals were actually correct.
    """
    for dec in decisions:
        if dec.get("outcome_1h") not in ("CORRECT", "WRONG"):
            continue
        was_correct = dec["outcome_1h"] == "CORRECT"
        # Map decision to signal types that contributed
        action = dec.get("action", "HOLD")
        for sig_type in ["ml_ensemble", "uoa_flow", "darthvader", "spock_master"]:
            _update_signal_weight(sig_type, was_correct)


# ══════════════════════════════════════════════════════════════════════════════
# SPOCK SELF-LEARNING ENGINE
# 4-stage feedback loop that runs after every 10 measured outcomes:
#
#  Stage 1 — OUTCOME MEASUREMENT
#    After 1h/4h/1d: compare signal direction vs actual price move
#    Classify each decision: CORRECT / WRONG / NEUTRAL
#
#  Stage 2 — ROOT CAUSE ANALYSIS  
#    Which features / conditions were present in wrong calls?
#    Per-regime accuracy (bull/bear/sideways market)
#    Per-conviction-band accuracy (low/medium/high conviction)
#
#  Stage 3 — WEIGHT ADJUSTMENT
#    Reduce weight of signals that keep being wrong
#    Raise conviction threshold if wrong calls had high conviction
#    Tighten RSI/score thresholds if calls at extremes keep failing
#
#  Stage 4 — LABEL-CORRECTED RETRAIN
#    Inject WRONG decisions as opposite-label training samples
#    These are the most valuable training examples — real outcomes
#    Retrain ML on augmented dataset
# ══════════════════════════════════════════════════════════════════════════════

# Persistent learning state (survives across cycles but not restarts)
_learning_state = {
    "total_decisions":    0,
    "total_correct":      0,
    "total_wrong":        0,
    "last_correction_ts": 0,
    "corrections_made":   0,
    "weight_history":     [],  # [{ts, changes}]
    "threshold_history":  [],  # [{ts, old, new, reason}]
    "regime_accuracy": {
        "bull":    {"correct": 0, "wrong": 0},
        "bear":    {"correct": 0, "wrong": 0},
        "neutral": {"correct": 0, "wrong": 0},
    },
    "conviction_accuracy": {
        "high":   {"correct": 0, "wrong": 0},   # conviction >= 70
        "medium": {"correct": 0, "wrong": 0},   # conviction 45-69
        "low":    {"correct": 0, "wrong": 0},   # conviction < 45
    },
    "feature_error_rates": {},  # {feature: {high_val_wrong, high_val_right}}
    "alert_outcomes": [],       # [{alert_key, was_profitable, price_move}]
}

# Dynamic thresholds — start at defaults, adjusted by learning
_dynamic_thresholds = {
    "spock_score_buy":    40,    # min score to send BUY
    "spock_score_sell":  -40,    # max score to send SELL
    "conviction_buy":     35,    # min conviction for BUY
    "conviction_sell":    35,    # min conviction for SELL
    "ml_conf_bypass":     80,    # ML conf needed for hard bypass
    "correction_trigger": 0.50,  # retrigger correction if win_rate drops below this
}


def _run_full_learning_cycle(decisions):
    """
    Full 4-stage self-learning cycle.
    Called when we have 10+ newly measured decisions.
    """
    measured = [d for d in decisions if d.get("outcome_1h") in ("CORRECT","WRONG")]
    if len(measured) < 10:
        return

    correct = [d for d in measured if d["outcome_1h"] == "CORRECT"]
    wrong   = [d for d in measured if d["outcome_1h"] == "WRONG"]
    win_rate = len(correct) / max(len(measured), 1)

    print(f"\n[LEARN] ═══ Self-Learning Cycle ═══", flush=True)
    print(f"[LEARN] Decisions: {len(measured)} | Correct: {len(correct)} | Wrong: {len(wrong)} | Win: {win_rate:.0%}", flush=True)

    # ── Stage 2: Root Cause Analysis ──────────────────────────────────────
    _stage2_root_cause(correct, wrong)

    # ── Stage 3: Threshold + Weight Adjustment ────────────────────────────
    if win_rate < _dynamic_thresholds["correction_trigger"]:
        _stage3_adjust(correct, wrong, win_rate)
    elif win_rate > 0.70:
        _stage3_reward(win_rate)

    # ── Stage 4: Label-corrected retrain ─────────────────────────────────
    if len(wrong) >= 5:
        _stage4_retrain_with_labels(wrong, correct)

    _learning_state["total_decisions"] += len(measured)
    _learning_state["total_correct"]   += len(correct)
    _learning_state["total_wrong"]     += len(wrong)


def _stage2_root_cause(correct, wrong):
    """Analyze which conditions caused wrong calls."""
    if not wrong:
        return

    # Per-regime accuracy
    for d in correct + wrong:
        regime = d.get("regime", "neutral")
        outcome = "correct" if d in correct else "wrong"
        r_key = "bull" if "bull" in regime.lower() else ("bear" if "bear" in regime.lower() else "neutral")
        _learning_state["regime_accuracy"][r_key][outcome] += 1

    # Per-conviction accuracy
    for d in correct + wrong:
        conv = d.get("conviction", 0)
        bucket = "high" if conv >= 70 else ("medium" if conv >= 45 else "low")
        outcome = "correct" if d in correct else "wrong"
        _learning_state["conviction_accuracy"][bucket][outcome] += 1

    # Feature analysis: which features were elevated in wrong calls?
    all_feats = set()
    for d in correct + wrong:
        all_feats.update(d.get("features", {}).keys())

    feat_analysis = {}
    for feat in all_feats:
        wrong_vals = [d["features"].get(feat, 0) for d in wrong if feat in d.get("features", {})]
        right_vals = [d["features"].get(feat, 0) for d in correct if feat in d.get("features", {})]
        if wrong_vals and right_vals:
            w_avg = sum(wrong_vals) / len(wrong_vals)
            r_avg = sum(right_vals) / len(right_vals)
            if abs(w_avg) > 0.001 and abs(w_avg - r_avg) / (abs(r_avg) + 0.001) > 0.3:
                feat_analysis[feat] = {"wrong_avg": round(w_avg, 4), "right_avg": round(r_avg, 4)}

    if feat_analysis:
        top_diff = sorted(feat_analysis.items(),
                         key=lambda x: abs(x[1]["wrong_avg"] - x[1]["right_avg"]), reverse=True)[:5]
        print(f"[LEARN] Features most different in wrong calls:", flush=True)
        for feat, vals in top_diff:
            print(f"[LEARN]   {feat:25s} wrong={vals['wrong_avg']:+.3f} right={vals['right_avg']:+.3f}", flush=True)
        _learning_state["feature_error_rates"] = dict(top_diff[:10])

    # Regime report
    for regime, counts in _learning_state["regime_accuracy"].items():
        tot = counts["correct"] + counts["wrong"]
        if tot > 0:
            wr = counts["correct"] / tot * 100
            print(f"[LEARN] Regime {regime:7s}: {wr:.0f}% win ({counts['correct']}/{tot})", flush=True)

    # Conviction report
    for band, counts in _learning_state["conviction_accuracy"].items():
        tot = counts["correct"] + counts["wrong"]
        if tot > 0:
            wr = counts["correct"] / tot * 100
            print(f"[LEARN] Conviction {band:6s}: {wr:.0f}% win ({counts['correct']}/{tot})", flush=True)


def _stage3_adjust(correct, wrong, win_rate):
    """Adjust thresholds and signal weights when win_rate is too low."""
    global _dynamic_thresholds
    changes = []

    # 1. Wrong calls with high conviction → conviction threshold is too low
    high_conv_wrong = [d for d in wrong if d.get("conviction", 0) >= 70]
    if len(high_conv_wrong) >= 3:
        old = _dynamic_thresholds["conviction_buy"]
        new = min(60, old + 5)
        _dynamic_thresholds["conviction_buy"]  = new
        _dynamic_thresholds["conviction_sell"] = new
        changes.append(f"conviction: {old}%→{new}%")

    # 2. Wrong calls clustered at certain score range → tighten score threshold
    wrong_scores = [abs(d.get("score", 0)) for d in wrong]
    if wrong_scores:
        avg_wrong_score = sum(wrong_scores) / len(wrong_scores)
        if avg_wrong_score < 50:
            # Wrong calls were marginal scores — raise the bar
            old = _dynamic_thresholds["spock_score_buy"]
            new = min(55, old + 5)
            _dynamic_thresholds["spock_score_buy"]  = new
            _dynamic_thresholds["spock_score_sell"] = -new
            changes.append(f"score_threshold: {old}→{new}")

    # 3. Regime-based adjustments
    bear_acc = _learning_state["regime_accuracy"]["bear"]
    bear_tot = bear_acc["correct"] + bear_acc["wrong"]
    if bear_tot >= 5 and bear_acc["correct"] / max(bear_tot, 1) < 0.40:
        # System is bad at calling in bear regime — raise bar further
        old = _dynamic_thresholds["spock_score_buy"]
        _dynamic_thresholds["spock_score_buy"] = min(65, old + 5)
        changes.append(f"bear_regime: score_buy→{_dynamic_thresholds['spock_score_buy']}")

    # 4. Signal weights — reduce weight of signals dominant in wrong calls
    # Compare which sub-signals had highest contribution in WRONG vs CORRECT
    wrong_ml   = sum(1 for d in wrong   if d.get("features", {}).get("rsi_14", 50) > 70)
    correct_ml = sum(1 for d in correct if d.get("features", {}).get("rsi_14", 50) > 70)
    if wrong_ml > correct_ml * 1.5 and wrong_ml >= 3:
        # RSI > 70 calls were mostly wrong — update signal weight
        _update_signal_weight("rsi_overbought", False)
        changes.append("rsi_overbought signal weight reduced")

    if changes:
        _learning_state["threshold_history"].append({
            "ts": datetime.now().isoformat(),
            "win_rate": round(win_rate * 100, 1),
            "changes": changes,
        })
        _learning_state["corrections_made"] += 1
        print(f"[LEARN] ⚙️ Threshold adjustments: {changes}", flush=True)
    else:
        print(f"[LEARN] No threshold changes needed", flush=True)


def _stage3_reward(win_rate):
    """When win_rate is high, gently relax thresholds to catch more signals."""
    global _dynamic_thresholds
    changes = []
    if _dynamic_thresholds["conviction_buy"] > 35:
        old = _dynamic_thresholds["conviction_buy"]
        new = max(35, old - 2)
        _dynamic_thresholds["conviction_buy"]  = new
        _dynamic_thresholds["conviction_sell"] = new
        changes.append(f"conviction relaxed: {old}%→{new}%")
    if _dynamic_thresholds["spock_score_buy"] > 40:
        old = _dynamic_thresholds["spock_score_buy"]
        new = max(40, old - 3)
        _dynamic_thresholds["spock_score_buy"]  = new
        _dynamic_thresholds["spock_score_sell"] = -new
        changes.append(f"score threshold relaxed: {old}→{new}")
    if changes:
        print(f"[LEARN] ✅ High win rate {win_rate:.0%} — relaxing thresholds: {changes}", flush=True)


def _stage4_retrain_with_labels(wrong_decisions, correct_decisions):
    """
    The most powerful step: inject real outcomes as training labels.

    For each WRONG decision: the bar features are saved.
    We add them to the training set with the OPPOSITE label.
    Example: BUY at $348 → price dropped → add as SELL training sample.

    This teaches the model the exact conditions where it was wrong.
    Over time, the model learns to avoid repeating the same mistakes.
    """
    import json as _json
    label_file = "/tmp/spock_corrective_labels.json"

    # Load existing corrective labels
    try:
        with open(label_file) as f:
            corrective_labels = _json.load(f)
    except Exception:
        corrective_labels = []

    new_labels = 0
    for d in wrong_decisions:
        feats = d.get("features", {})
        if not feats or len(feats) < 20:
            continue
        action = d.get("action", "HOLD")
        # Wrong BUY → label as 0 (price went down). Wrong SELL → label as 1 (price went up)
        correct_label = 0 if "BUY" in action else 1
        corrective_labels.append({
            "features": feats,
            "label":    correct_label,
            "price":    d.get("price"),
            "ts":       d.get("ts", 0),
            "pnl":      d.get("pnl_1h", 0),
            "source":   "spock_correction",
        })
        new_labels += 1

    # Keep last 500 corrective labels (don't let old mistakes dominate)
    corrective_labels = corrective_labels[-500:]

    try:
        with open(label_file, "w") as f:
            _json.dump(corrective_labels, f)
        print(f"[LEARN] 📝 Saved {new_labels} corrective labels ({len(corrective_labels)} total)", flush=True)
    except Exception as _le:
        print(f"[LEARN] Label save error: {_le}", flush=True)
        return

    # Trigger ML retrain — it will load corrective labels
    print(f"[LEARN] 🔄 Triggering corrective retrain with real outcome labels...", flush=True)
    import threading as _thr3
    _thr3.Thread(target=_run_ml_retrain_with_corrections, daemon=True).start()


def _run_ml_retrain_with_corrections():
    """Retrain ML model using both historical bars AND corrective outcome labels."""
    import json as _json, os as _os

    label_file = "/tmp/spock_corrective_labels.json"
    corrective_labels = []
    try:
        with open(label_file) as f:
            corrective_labels = _json.load(f)
    except Exception:
        pass

    if not corrective_labels:
        _run_ml_retrain()  # fall back to standard retrain
        return

    print(f"[LEARN-RETRAIN] Starting corrective retrain with {len(corrective_labels)} outcome labels", flush=True)

    # The corrective labels get mixed into the training data
    # Store them in a global so _run_ml_retrain can pick them up
    global _ml_corrective_labels
    _ml_corrective_labels = corrective_labels

    _run_ml_retrain()  # standard retrain — modified to use corrective labels


def _apply_dynamic_thresholds_to_spock(score, conviction, action):
    """
    Apply dynamically adjusted thresholds to SPOCK decision.
    Returns (final_action, adjusted) tuple.
    """
    min_score_buy  = _dynamic_thresholds["spock_score_buy"]
    min_score_sell = abs(_dynamic_thresholds["spock_score_sell"])
    min_conv       = _dynamic_thresholds["conviction_buy"]

    if action in ("BUY", "STRONG BUY"):
        score_ok = abs(score) >= (min_score_buy + 25 if "STRONG" in action else min_score_buy)
        conv_ok  = conviction >= min_conv
        if not (score_ok and conv_ok):
            return "HOLD — THRESHOLD", True
    elif action in ("SELL", "STRONG SELL"):
        score_ok = abs(score) >= (min_score_sell + 25 if "STRONG" in action else min_score_sell)
        conv_ok  = conviction >= min_conv
        if not (score_ok and conv_ok):
            return "HOLD — THRESHOLD", True
    return action, False



def _spock_log_decision(action, score, conviction, price, features_snapshot,
                        mtf_dir, mtf_conf, reasons):
    """Log a SPOCK decision for later outcome measurement."""
    if action == "HOLD" and "LOW CONVICTION" not in action:
        return  # only log actionable decisions
    decision = {
        "id":          str(_uuid.uuid4())[:8],
        "timestamp":   time.time(),
        "price":       round(price, 2),
        "action":      action,
        "score":       score,
        "conviction":  conviction,
        "mtf_dir":     mtf_dir,
        "mtf_conf":    mtf_conf,
        "reasons":     reasons[:3],
        "features":    {k: round(float(v), 4) for k, v in features_snapshot.items()
                       if isinstance(v, (int, float))},
        # Outcomes — filled in later
        "price_1h":    None, "price_4h":   None, "price_1d":   None,
        "outcome_1h":  None, "outcome_4h": None, "outcome_1d": None,
        "pnl_1h":      None, "pnl_4h":    None, "pnl_1d":     None,
        "measured":    False,
    }
    _spock_decisions.append(decision)
    # Keep last 500 decisions
    if len(_spock_decisions) > 500:
        _spock_decisions.pop(0)
    print(f"[SPOCK-BRAIN] Decision logged: {action} @ ${price} "
          f"| score={score:+d} | conv={conviction}% | id={decision['id']}", flush=True)


def _spock_measure_outcomes(current_price):
    """
    Check past decisions against current price.
    Called every analysis cycle.
    """
    now = time.time()
    changed = False

    for dec in _spock_decisions:
        if dec.get("measured"):
            continue
        elapsed_h = (now - dec["timestamp"]) / 3600
        entry_price = dec["price"]
        if entry_price <= 0:
            continue

        pnl = (current_price - entry_price) / entry_price * 100
        action = dec["action"]
        # Outcome classifier — lower threshold, no pure NEUTRAL
        def _outcome(pnl_pct, action):
            threshold = 0.15   # 0.15% = meaningful move (was 0.3% — too high for AH)
            if   action in ("BUY","STRONG BUY")   and pnl_pct >  threshold: return "CORRECT"
            elif action in ("SELL","STRONG SELL")  and pnl_pct < -threshold: return "CORRECT"
            elif action in ("BUY","STRONG BUY")   and pnl_pct < -threshold: return "WRONG"
            elif action in ("SELL","STRONG SELL")  and pnl_pct >  threshold: return "WRONG"
            else: return "NEUTRAL"  # price barely moved — inconclusive

        # 1-hour outcome
        if elapsed_h >= 1.0 and dec["outcome_1h"] is None:
            dec["price_1h"]   = round(current_price, 2)
            dec["pnl_1h"]     = round(pnl, 3)
            dec["outcome_1h"] = _outcome(pnl, action)
            changed = True
            print(f"[SPOCK-BRAIN] 1h outcome: {dec['id']} {action} @ ${entry_price} → "
                  f"${current_price} ({pnl:+.2f}%) = {dec['outcome_1h']}", flush=True)

        # 4-hour outcome
        if elapsed_h >= 4.0 and dec["outcome_4h"] is None:
            dec["price_4h"]   = round(current_price, 2)
            dec["pnl_4h"]     = round(pnl, 3)
            dec["outcome_4h"] = _outcome(pnl, action)
            changed = True
            print(f"[SPOCK-BRAIN] 4h outcome: {dec['id']} {action} @ ${entry_price} → "
                  f"${current_price} ({pnl:+.2f}%) = {dec['outcome_4h']}", flush=True)

        # 1-day outcome
        if elapsed_h >= 24.0 and dec["outcome_1d"] is None:
            dec["price_1d"]   = round(current_price, 2)
            dec["pnl_1d"]     = round(pnl, 3)
            dec["outcome_1d"] = _outcome(pnl, action)
            dec["measured"]   = True
            changed = True
            print(f"[SPOCK-BRAIN] 1d outcome: {dec['id']} {action} @ ${entry_price} → "
                  f"${current_price} ({pnl:+.2f}%) = {dec['outcome_1d']}", flush=True)

    if changed:
        _spock_update_accuracy()


def _spock_update_accuracy():
    """Recompute rolling accuracy stats from decision log."""
    # Use last 50 measured decisions
    measured = [d for d in _spock_decisions if d.get("outcome_1h") is not None][-50:]
    if not measured:
        return

    total     = len(measured)
    # Only count CORRECT/WRONG — exclude NEUTRAL from denominator
    decisive_1h = [d for d in measured if d.get("outcome_1h") in ("CORRECT","WRONG")]
    corr_1h     = sum(1 for d in decisive_1h if d["outcome_1h"] == "CORRECT")
    measured_4h = [d for d in measured if d.get("outcome_4h") in ("CORRECT","WRONG")]
    measured_1d = [d for d in measured if d.get("outcome_1d") in ("CORRECT","WRONG")]
    corr_4h     = sum(1 for d in measured_4h if d["outcome_4h"] == "CORRECT")
    corr_1d     = sum(1 for d in measured_1d if d["outcome_1d"] == "CORRECT")

    _spock_accuracy["total"]        = total
    _spock_accuracy["decisive_1h"]  = len(decisive_1h)
    _spock_accuracy["correct_1h"]   = corr_1h
    _spock_accuracy["win_rate_1h"]  = round(corr_1h / len(decisive_1h) * 100, 1) if decisive_1h else None
    _spock_accuracy["win_rate_4h"]  = round(corr_4h / len(measured_4h) * 100, 1) if measured_4h else None
    _spock_accuracy["win_rate_1d"]  = round(corr_1d / len(measured_1d) * 100, 1) if measured_1d else None

    # By action
    for action in ("BUY","STRONG BUY","SELL","STRONG SELL"):
        grp = [d for d in measured if d["action"] == action and d["outcome_1h"]]
        if grp:
            wr = round(sum(1 for d in grp if d["outcome_1h"]=="CORRECT") / len(grp) * 100, 1)
            _spock_accuracy["by_action"][action] = {"total": len(grp), "win_rate_1h": wr}

    # By conviction level
    high_conv = [d for d in measured if d["conviction"] >= 70 and d["outcome_1h"]]
    low_conv  = [d for d in measured if d["conviction"] < 55  and d["outcome_1h"]]
    if high_conv:
        _spock_accuracy["by_conviction"]["high_70plus"] = round(
            sum(1 for d in high_conv if d["outcome_1h"]=="CORRECT") / len(high_conv) * 100, 1)
    if low_conv:
        _spock_accuracy["by_conviction"]["low_under55"] = round(
            sum(1 for d in low_conv if d["outcome_1h"]=="CORRECT") / len(low_conv) * 100, 1)

    wr1h = _spock_accuracy["win_rate_1h"]
    wr4h = _spock_accuracy["win_rate_4h"]
    print(f"[SPOCK-BRAIN] Accuracy: 1h={wr1h}% | 4h={wr4h}% | "
          f"n={total} decisions", flush=True)
    # Run signal weight feedback update
    _run_signal_feedback_update(measured)

    # Run full 4-stage learning cycle when we have enough measured decisions
    _new_measured = [d for d in _spock_decisions if d.get("outcome_1h") in ("CORRECT","WRONG")]
    if len(_new_measured) >= 10 and len(_new_measured) % 10 == 0:
        # Every 10 decisions, run a full learning cycle
        import threading as _thr_lrn
        _thr_lrn.Thread(target=_run_full_learning_cycle, args=(_new_measured,), daemon=True).start()
        print(f"[LEARN] Full learning cycle triggered ({len(_new_measured)} total decisions)", flush=True)

    # Trigger self-correction if win rate too low
    if total >= 20 and wr1h is not None and wr1h < 55:
        _spock_self_correct(measured)


def _spock_self_correct(measured_decisions):
    """
    Self-correction: when win rate < 55%, analyze what went wrong
    and adjust SPOCK weights + trigger ML retrain with correct labels.
    """
    now_str = datetime.now().strftime("%Y-%m-%d %H:%M")
    if _spock_accuracy.get("last_correction"):
        last = _spock_accuracy["last_correction"]
        # Don't correct more than once per 24h
        if (time.time() - last) < 86400:
            return

    wrong = [d for d in measured_decisions if d.get("outcome_1h") == "WRONG"]
    print(f"[SPOCK-BRAIN] ⚠️ Self-correction triggered! win_rate={_spock_accuracy['win_rate_1h']}% "
          f"| {len(wrong)} wrong decisions", flush=True)

    # Analyze which features are most common in wrong decisions
    feature_wrong_avg = {}
    feature_right_avg = {}
    right = [d for d in measured_decisions if d.get("outcome_1h") == "CORRECT"]

    all_feats = set()
    for d in measured_decisions:
        all_feats.update(d.get("features", {}).keys())

    for feat in all_feats:
        wrong_vals = [d["features"].get(feat, 0) for d in wrong if feat in d.get("features", {})]
        right_vals = [d["features"].get(feat, 0) for d in right if feat in d.get("features", {})]
        if wrong_vals:
            feature_wrong_avg[feat] = sum(wrong_vals) / len(wrong_vals)
        if right_vals:
            feature_right_avg[feat] = sum(right_vals) / len(right_vals)

    # Weight adjustments — reduce weight for features dominant in wrong calls
    weight_changes = []
    for tier, weight_key in [
        ("ofi", "ofi"), ("absorption", "absorption"),
        ("uoa", "uoa"), ("ml", "ml"),
    ]:
        wrong_ofi  = abs(feature_wrong_avg.get("ofi_ratio", 0))
        right_ofi  = abs(feature_right_avg.get("ofi_ratio", 0))
        if wrong_ofi > right_ofi * 1.5:
            # OFI was higher in wrong calls — reduce its weight
            old_w = _spock_weights.get("ofi", 10)
            new_w = max(4, old_w - 3)
            _spock_weights["ofi"] = new_w
            weight_changes.append(f"ofi: {old_w}→{new_w}")
            break

    # Check if wrong calls clustered in certain conviction range
    wrong_conv = [d["conviction"] for d in wrong]
    if wrong_conv and sum(wrong_conv)/len(wrong_conv) < 60:
        # Wrong calls were mostly low conviction — raise threshold
        print("[SPOCK-BRAIN] Wrong calls were low conviction — raising conviction gate to 60%", flush=True)

    print(f"[SPOCK-BRAIN] Weight adjustments: {weight_changes}", flush=True)
    print(f"[SPOCK-BRAIN] Triggering corrective retrain...", flush=True)

    # Trigger ML retrain — the new training labels will reflect actual outcomes
    import threading as _thr2
    _thr2.Thread(target=_run_ml_retrain, daemon=True).start()

    _spock_accuracy["last_correction"] = time.time()
    _spock_accuracy["corrections_fired"] = _spock_accuracy.get("corrections_fired", 0) + 1


def _spock_detect_breakout(price, closes, volumes, mm_data, spy_data):
    """
    Breakout volume detector.
    Checks if price is crossing a key level with or without volume confirmation.
    Returns breakout signal for SPOCK scoring.
    """
    result = {"breakout": False, "fake": False, "level": None,
              "direction": None, "vol_ratio": 1.0, "score": 0, "reason": ""}
    try:
        # Key levels: max pain, round numbers near price, recent highs/lows
        max_pain = float(mm_data.get("max_pain", 0) or 0)
        round_levels = [round(price / 5) * 5 + i*5 for i in range(-4, 5)]
        key_levels = sorted(set([max_pain] + round_levels + [
            round(closes.max() / 5) * 5,   # recent high
            round(closes.min() / 5) * 5,   # recent low
        ]))
        key_levels = [l for l in key_levels if 0 < l < price * 2]

        # Volume ratio vs 20-bar avg
        vol_now = float(volumes.iloc[-1]) if len(volumes) > 0 else 0
        vol_avg = float(volumes.iloc[-20:].mean()) if len(volumes) >= 20 else vol_now
        vol_ratio = vol_now / (vol_avg + 1e-9)
        result["vol_ratio"] = round(vol_ratio, 2)

        prev_price = float(closes.iloc[-2]) if len(closes) >= 2 else price

        # Check if price just crossed a key level
        for level in key_levels:
            if abs(level - price) / price < 0.005:   # within 0.5% of key level
                crossed_up   = prev_price < level <= price
                crossed_down = prev_price > level >= price

                if crossed_up or crossed_down:
                    result["level"]     = level
                    result["direction"] = "UP" if crossed_up else "DOWN"

                    if vol_ratio >= 2.0:
                        # High volume = confirmed breakout
                        result["breakout"] = True
                        pts = 15 if vol_ratio >= 3.0 else 10
                        result["score"]  = pts if crossed_up else -pts
                        result["reason"] = (
                            f"{'↑' if crossed_up else '↓'} Breakout through ${level:.0f} "
                            f"on {vol_ratio:.1f}x volume — CONFIRMED"
                        )
                    elif vol_ratio < 0.7:
                        # Low volume = likely fake/trap
                        result["fake"]   = True
                        pts = -10
                        result["score"]  = pts if crossed_up else 10
                        result["reason"] = (
                            f"{'↑' if crossed_up else '↓'} Break of ${level:.0f} "
                            f"on LOW volume ({vol_ratio:.1f}x) — POSSIBLE FAKE"
                        )
                    break

    except Exception as e:
        print(f"  ⚠️ Breakout detector error: {e}", flush=True)
    return result

def calculate_tsla_4h(ticker=None):
    """
    Compute TSLA technical indicators on 4-hour bars.
    Returns dict with RSI, MACD, BB, EMA, trend state.
    """
    _ticker = ticker or TICKER
    result = {
        "rsi_4h": 50.0, "macd_hist_4h": 0.0, "bb_pct_4h": 0.5,
        "above_ema20_4h": True, "above_ema50_4h": True,
        "trend_4h": "NEUTRAL", "ob_4h": False, "os_4h": False,
        "macd_bull_4h": False, "vol_ratio_4h": 1.0,
        "ema20_4h": 0.0, "ema50_4h": 0.0,
    }
    try:
        import yfinance as yf
        import numpy as np

        # Fetch 1h bars — try Schwab first (more reliable on Railway)
        closes_1h  = None
        volumes_1h = None
        try:
            import schwab_client as _sc2
            if _sc2.is_configured() and _sc2.get_client():
                _t1h = _sc2.get_price_history(_ticker, period_years=1, freq_minutes=60)
                if _t1h is not None and not _t1h.empty and len(_t1h) > 50:
                    closes_1h  = _t1h["Close"].astype(float)
                    volumes_1h = _t1h["Volume"].astype(float) if "Volume" in _t1h else closes_1h * 0
                    print(f"  📡 Schwab {_ticker} 1h: {len(closes_1h)} bars for 4h analysis", flush=True)
        except Exception:
            pass
        if closes_1h is None:
            hist_1h = yf.Ticker(_ticker).history(period="60d", interval="1h")
            if hist_1h.empty or len(hist_1h) < 20:
                return result
            closes_1h  = hist_1h["Close"].astype(float)
            volumes_1h = hist_1h["Volume"].astype(float)
        if closes_1h is None or len(closes_1h) < 20:
            return result

        # Resample to 4h — must convert to ET first so bars align to market hours
        # UTC resample("4h") gives wrong boundaries (market opens at 13:30 UTC)
        try:
            import pytz
            et = pytz.timezone("America/New_York")
            closes_et  = closes_1h.copy()
            volumes_et = volumes_1h.copy()
            if closes_et.index.tz is None:
                closes_et.index  = closes_et.index.tz_localize("UTC")
                volumes_et.index = volumes_et.index.tz_localize("UTC")
            closes_et.index  = closes_et.index.tz_convert(et)
            volumes_et.index = volumes_et.index.tz_convert(et)
            # Resample with 9:30 ET offset so bars = 9:30-13:30, 13:30-16:00 etc
            closes_4h  = closes_et.resample("4h", offset="9h30min").last().dropna()
            volumes_4h = volumes_et.resample("4h", offset="9h30min").sum().reindex(
                closes_4h.index, fill_value=0)
        except Exception:
            # Fallback: use UTC resample (less accurate but works)
            closes_4h  = closes_1h.resample("4h").last().dropna()
            volumes_4h = volumes_1h.resample("4h").sum().reindex(closes_4h.index, fill_value=0)

        if len(closes_4h) < 14:
            return result

        price_4h = float(closes_4h.iloc[-1])

        # RSI 14 on 4h
        delta = closes_4h.diff()
        gain  = delta.where(delta > 0, 0).rolling(14).mean()
        loss  = -delta.where(delta < 0, 0).rolling(14).mean()
        rsi_4h = round(float((100 - 100 / (1 + gain / (loss + 1e-9))).iloc[-1]), 1)

        # MACD on 4h
        ema12 = closes_4h.ewm(span=12, adjust=False).mean()
        ema26 = closes_4h.ewm(span=26, adjust=False).mean()
        macd  = ema12 - ema26
        sig   = macd.ewm(span=9, adjust=False).mean()
        macd_hist_4h = float((macd - sig).iloc[-1])
        macd_prev    = float((macd - sig).iloc[-2]) if len(closes_4h) > 2 else macd_hist_4h
        macd_cross_up = macd_hist_4h > 0 and macd_prev <= 0   # fresh bull cross

        # Bollinger %B on 4h
        ma20  = closes_4h.rolling(20).mean()
        std20 = closes_4h.rolling(20).std().replace(0, 1)
        bb_pct_4h = float(((closes_4h - (ma20 - 2*std20)) / (4*std20 + 1e-9)).iloc[-1])

        # EMA 20 and 50 on 4h
        ema20_4h = float(closes_4h.ewm(span=20, adjust=False).mean().iloc[-1])
        ema50_4h = float(closes_4h.ewm(span=50, adjust=False).mean().iloc[-1]) if len(closes_4h) >= 50 else ema20_4h

        # Volume ratio (current 4h bar vs avg of last 20 4h bars)
        vol_avg = float(volumes_4h.iloc[-20:-1].mean() or 1)
        vol_ratio_4h = float(volumes_4h.iloc[-1]) / vol_avg

        # 4h trend state
        above_ema20 = price_4h > ema20_4h
        above_ema50 = price_4h > ema50_4h
        if above_ema20 and above_ema50 and macd_hist_4h > 0:
            trend_4h = "BULLISH"
        elif not above_ema20 and not above_ema50 and macd_hist_4h < 0:
            trend_4h = "BEARISH"
        elif above_ema20 and not above_ema50:
            trend_4h = "RECOVERING"
        elif not above_ema20 and above_ema50:
            trend_4h = "WEAKENING"
        else:
            trend_4h = "NEUTRAL"

        result.update({
            "rsi_4h":         rsi_4h,
            "macd_hist_4h":   round(macd_hist_4h, 4),
            "macd_bull_4h":   macd_hist_4h > 0,
            "macd_cross_up":  macd_cross_up,
            "bb_pct_4h":      round(bb_pct_4h, 3),
            "ema20_4h":       round(ema20_4h, 2),
            "ema50_4h":       round(ema50_4h, 2),
            "above_ema20_4h": above_ema20,
            "above_ema50_4h": above_ema50,
            "vol_ratio_4h":   round(vol_ratio_4h, 2),
            "trend_4h":       trend_4h,
            "ob_4h":          rsi_4h > 70,
            "os_4h":          rsi_4h < 30,
            "price_4h":       round(price_4h, 2),
        })

    except Exception as e:
        print(f"  ⚠️ TSLA 4h error: {e}", flush=True)

    return result


def calculate_spock_mtf_narrative(tsla_4h, spy_data, price):
    """
    SPOCK multi-timeframe narrative engine.
    Synthesizes TSLA 4h + SPY 4h + QQQ 4h into a next-move estimate.

    Returns dict:
        direction:   UP / DOWN / SIDEWAYS
        magnitude:   small / medium / large
        timeframe:   intraday / swing
        confidence:  LOW / MEDIUM / HIGH / VERY HIGH
        narrative:   human-readable explanation
        tsla_state:  what TSLA is doing on 4h
        spy_state:   what SPY is doing on 4h
        alignment:   CONFIRMED / CONTRADICTED / NEUTRAL
    """
    t_rsi    = tsla_4h.get("rsi_4h", 50)
    t_trend  = tsla_4h.get("trend_4h", "NEUTRAL")
    t_macd   = tsla_4h.get("macd_hist_4h", 0)
    t_cross  = tsla_4h.get("macd_cross_up", False)
    t_bb     = tsla_4h.get("bb_pct_4h", 0.5)
    t_ob     = tsla_4h.get("ob_4h", False)
    t_os     = tsla_4h.get("os_4h", False)
    t_ema20  = tsla_4h.get("above_ema20_4h", True)
    t_ema50  = tsla_4h.get("above_ema50_4h", True)
    t_vol    = tsla_4h.get("vol_ratio_4h", 1.0)

    s_rsi_4h = float(spy_data.get("spy_rsi_4h", 50) or 50)
    s_ob_4h  = spy_data.get("spy_ob_4h", False)
    s_os_4h  = spy_data.get("spy_os_4h", False)
    s_rsi_d  = float(spy_data.get("spy_rsi", 50) or 50)
    s_mtf_ob = spy_data.get("spy_mtf_ob", False)
    s_mtf_os = spy_data.get("spy_mtf_os", False)

    q_rsi_4h = float(spy_data.get("qqq_rsi_4h", 50) or 50)
    q_ob_4h  = spy_data.get("qqq_ob_4h", False)
    q_os_4h  = spy_data.get("qqq_os_4h", False)

    mtf_both_ob = spy_data.get("mtf_both_ob", False)
    mtf_both_os = spy_data.get("mtf_both_os", False)

    bull_signals = 0
    bear_signals = 0
    reasons      = []

    # ── Analyze TSLA 4h ──────────────────────────────────────────────────────
    if t_os:
        bull_signals += 2
        reasons.append(f"TSLA 4h RSI oversold ({t_rsi:.0f}) — bounce historically likely")
    elif t_rsi < 40:
        bull_signals += 1
        reasons.append(f"TSLA 4h RSI approaching oversold ({t_rsi:.0f})")
    elif t_ob:
        bear_signals += 2
        reasons.append(f"TSLA 4h RSI overbought ({t_rsi:.0f}) — pullback risk")
    elif t_rsi > 60:
        bear_signals += 1

    if t_cross:
        bull_signals += 2
        reasons.append("TSLA 4h MACD just crossed bullish — momentum shift")
    elif t_macd > 0 and t_macd > 0:
        bull_signals += 1
    elif t_macd < 0:
        bear_signals += 1

    if t_trend == "BULLISH":
        bull_signals += 1
        reasons.append("TSLA 4h trend BULLISH (above EMA20+50, MACD positive)")
    elif t_trend == "BEARISH":
        bear_signals += 2
        reasons.append("TSLA 4h trend BEARISH (below EMA20+50)")
    elif t_trend == "RECOVERING":
        bull_signals += 1
        reasons.append("TSLA recovering — above EMA20 but not yet EMA50")
    elif t_trend == "WEAKENING":
        bear_signals += 1

    if t_bb < 0.1:
        bull_signals += 1
        reasons.append("TSLA near lower Bollinger band on 4h — mean reversion likely")
    elif t_bb > 0.9:
        bear_signals += 1
        reasons.append("TSLA near upper Bollinger band on 4h — stretched")

    if t_vol > 2.0:
        # Very high 4h volume — strong confirmation
        if bull_signals > bear_signals:
            bull_signals += 2
            reasons.append(f"Strong 4h volume surge ({t_vol:.1f}x avg) — institutional conviction BUY")
        elif bear_signals > bull_signals:
            bear_signals += 2
            reasons.append(f"Strong 4h volume surge ({t_vol:.1f}x avg) — institutional conviction SELL")
        else:
            reasons.append(f"High 4h volume ({t_vol:.1f}x avg) — watching for direction")
    elif t_vol > 1.5:
        if bull_signals > bear_signals:
            bull_signals += 1
            reasons.append(f"Elevated 4h volume ({t_vol:.1f}x avg) confirming bullish move")
        elif bear_signals > bull_signals:
            bear_signals += 1
            reasons.append(f"Elevated 4h volume ({t_vol:.1f}x avg) confirming bearish move")
    elif t_vol < 0.5:
        # Very low volume — low conviction, fade the move
        reasons.append(f"Low 4h volume ({t_vol:.1f}x avg) — low conviction, be cautious")

    # ── Cross-reference SPY/QQQ 4h ──────────────────────────────────────────
    if mtf_both_ob:
        bear_signals += 3
        reasons.append(f"SPY+QQQ both overbought on 4h+daily (SPY:{s_rsi_4h:.0f}, QQQ:{q_rsi_4h:.0f}) — market top risk")
    elif mtf_both_os:
        bull_signals += 3
        reasons.append(f"SPY+QQQ both oversold on 4h+daily — market bottom, TSLA to follow")
    elif s_ob_4h and q_ob_4h:
        bear_signals += 2
        reasons.append(f"SPY+QQQ both overbought on 4h (SPY:{s_rsi_4h:.0f}, QQQ:{q_rsi_4h:.0f})")
    elif s_os_4h and q_os_4h:
        bull_signals += 2
        reasons.append(f"SPY+QQQ both oversold on 4h — market finding support")
    elif s_ob_4h:
        bear_signals += 1
        reasons.append(f"SPY overbought on 4h (RSI {s_rsi_4h:.0f})")
    elif s_os_4h:
        bull_signals += 1
        reasons.append(f"SPY oversold on 4h (RSI {s_rsi_4h:.0f})")

    # ── Alignment check ──────────────────────────────────────────────────────
    # TSLA oversold + SPY oversold = maximum confluence bull
    # TSLA oversold + SPY overbought = TSLA-specific problem
    tsla_bull = bull_signals > bear_signals
    tsla_bear = bear_signals > bull_signals

    if t_os and (s_os_4h or q_os_4h):
        alignment = "CONFIRMED"
        bull_signals += 1
        reasons.append("✅ Triple confluence: TSLA oversold + market oversold")
    elif t_ob and (s_ob_4h or q_ob_4h):
        alignment = "CONFIRMED"
        bear_signals += 1
        reasons.append("⚠️ Triple confluence: TSLA overbought + market overbought")
    elif t_os and s_ob_4h:
        alignment = "CONTRADICTED"
        reasons.append("⚡ CONFLICT: TSLA oversold but SPY overbought — TSLA-specific weakness, caution")
    elif t_ob and s_os_4h:
        alignment = "CONTRADICTED"
        reasons.append("⚡ CONFLICT: TSLA overbought but SPY oversold — TSLA running ahead, fade risk")
    else:
        alignment = "NEUTRAL"

    # ── Final direction ──────────────────────────────────────────────────────
    net = bull_signals - bear_signals
    total = bull_signals + bear_signals + 1

    if net >= 4:
        direction  = "UP"
        magnitude  = "large" if net >= 6 else "medium"
        timeframe  = "swing (1-3 days)" if t_trend in ("BULLISH","RECOVERING") else "intraday"
        confidence = "VERY HIGH" if net >= 6 else "HIGH"
    elif net >= 2:
        direction  = "UP"
        magnitude  = "small" if net == 2 else "medium"
        timeframe  = "intraday to swing"
        confidence = "MEDIUM"
    elif net <= -4:
        direction  = "DOWN"
        magnitude  = "large" if net <= -6 else "medium"
        timeframe  = "swing (1-3 days)" if t_trend == "BEARISH" else "intraday"
        confidence = "VERY HIGH" if net <= -6 else "HIGH"
    elif net <= -2:
        direction  = "DOWN"
        magnitude  = "small" if net == -2 else "medium"
        timeframe  = "intraday to swing"
        confidence = "MEDIUM"
    else:
        direction  = "SIDEWAYS"
        magnitude  = "small"
        timeframe  = "intraday"
        confidence = "LOW"

    # Build TSLA state string
    tsla_state_str = (
        f"RSI {t_rsi:.0f} "
        f"({'OVERSOLD' if t_os else 'OVERBOUGHT' if t_ob else 'NEUTRAL'}) | "
        f"MACD {'▲' if t_macd > 0 else '▼'} | "
        f"{'Above' if t_ema20 else 'Below'} EMA20 | "
        f"Trend: {t_trend}"
    )
    spy_state_str = (
        f"SPY 4h RSI {s_rsi_4h:.0f} "
        f"({'OB' if s_ob_4h else 'OS' if s_os_4h else 'OK'}) | "
        f"QQQ 4h RSI {q_rsi_4h:.0f} "
        f"({'OB' if q_ob_4h else 'OS' if q_os_4h else 'OK'})"
    )

    return {
        "direction":   direction,
        "magnitude":   magnitude,
        "timeframe":   timeframe,
        "confidence":  confidence,
        "alignment":   alignment,
        "tsla_state":  tsla_state_str,
        "spy_state":   spy_state_str,
        "reasons":     reasons[:4],
        "bull_signals": bull_signals,
        "bear_signals": bear_signals,
        "net_score":   net,
    }



def detect_vix_regime_flip(spy_data):
    """
    Detect VIX spike or crash that signals macro regime shift.
    VIX drops >15% in one session = fear-to-relief flip → BUY signal.
    VIX spikes >25% in one session = sudden panic → exit longs.
    Returns dict with flip type and signal.
    """
    result = {"flip": None, "signal": "NEUTRAL", "vix_change_pct": None}
    try:
        import yfinance as _yf_vix
        _vix_h = _yf_vix.Ticker("^VIX").history(period="5d", interval="1d")
        if len(_vix_h) >= 2:
            _vix_today = float(_vix_h["Close"].iloc[-1])
            _vix_prev  = float(_vix_h["Close"].iloc[-2])
            _chg_pct   = (_vix_today - _vix_prev) / _vix_prev * 100
            result["vix_change_pct"] = round(_chg_pct, 1)
            result["vix_today"]      = round(_vix_today, 2)
            result["vix_prev"]       = round(_vix_prev, 2)

            if _chg_pct <= -15:
                result["flip"]   = "FEAR_TO_RELIEF"
                result["signal"] = "STRONG_BUY"
                print(f"  🚨 VIX REGIME FLIP: {_vix_prev:.1f}→{_vix_today:.1f} "
                      f"({_chg_pct:+.1f}%) — fear-to-relief, MACRO BUY SIGNAL", flush=True)
            elif _chg_pct >= 25:
                result["flip"]   = "PANIC_SPIKE"
                result["signal"] = "STRONG_SELL"
                print(f"  🚨 VIX PANIC SPIKE: {_vix_prev:.1f}→{_vix_today:.1f} "
                      f"({_chg_pct:+.1f}%) — sudden panic, EXIT LONGS", flush=True)
            elif _chg_pct <= -8:
                result["flip"]   = "RELIEF"
                result["signal"] = "BUY"
            elif _chg_pct >= 15:
                result["flip"]   = "STRESS"
                result["signal"] = "SELL"
    except Exception:
        pass
    return result

def check_hard_risk_rules(price, spy_data, indicators, mm_data):
    """
    Hard override rules that gate all signals regardless of SPOCK score.
    Returns: (allow_buy, allow_sell, risk_override, reasons)
    """
    allow_buy  = True
    allow_sell = True
    reasons    = []
    risk_override = None

    vix       = float(spy_data.get("vix", 20) or 20)
    spy_rsi4h = float(spy_data.get("spy_rsi_4h", 50) or 50)
    qqq_rsi4h = float(spy_data.get("qqq_rsi_4h", 50) or 50)
    gap_pct   = float(indicators.get("gap_pct", 0) or 0)
    beta      = float(spy_data.get("beta_20d", 2.0) or 2.0)
    spy_move  = float(spy_data.get("spy_change_pct", 0) or 0)
    implied_tsla_move = abs(spy_move * beta)

    # Rule 1: VIX > 30 — no new longs
    if vix > 30:
        allow_buy = False
        risk_override = "DEFENSIVE"
        reasons.append(f"⛔ VIX={vix:.1f} > 30 — no new longs in fear regime")

    # Rule 2: VIX > 25 — reduce size signal
    elif vix > 25:
        risk_override = "CAUTION"
        reasons.append(f"⚠️ VIX={vix:.1f} > 25 — elevated fear, reduce size")

    # Rule 3: SPY + QQQ both 4h RSI > 88 — no new longs
    if spy_rsi4h > 88 and qqq_rsi4h > 88:
        allow_buy = False
        risk_override = "EXTREME"
        reasons.append(f"⛔ SPY 4h RSI={spy_rsi4h:.0f} + QQQ 4h RSI={qqq_rsi4h:.0f} — market extremely overbought")

    # Rule 4: Gap down > 3% — suppress BUY for first 30 min
    if gap_pct < -3.0:
        allow_buy = False
        reasons.append(f"⛔ Gap down {gap_pct:.1f}% — wait for gap fill attempt before buying")

    # Rule 5: Beta-adjusted SPY move implies > 5% TSLA move
    if implied_tsla_move > 5.0:
        risk_override = "EXTREME"
        reasons.append(f"⚠️ SPY move {spy_move:.1f}% × beta {beta:.1f}x = {implied_tsla_move:.1f}% implied TSLA move")

    # Rule 6: GEX extremely negative (< -300M) — amplified moves, reduce size
    gex = float(mm_data.get("gex_total", 0) or 0)
    if gex < -300:
        risk_override = risk_override or "HIGH"
        reasons.append(f"⚠️ GEX={gex:.0f}M — dealers short gamma, moves amplified")

    return allow_buy, allow_sell, risk_override, reasons

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

    # 2. ML Ensemble — apply feedback weight
    ml_sig  = ml_signal.get("signal", "HOLD")
    ml_conf = ml_signal.get("confidence", 0) or 0
    ml_prob = ml_signal.get("probability", 0.5) or 0.5
    _ml_w   = get_signal_weight("ml_ensemble")
    if ml_sig == "BUY" and ml_conf >= 30:
        pts = min(30, int(ml_conf * 0.4 * _ml_w))
        score += pts; reasons.append(f"ML ensemble BUY (conf {ml_conf}%, prob {ml_prob:.0%}, weight={_ml_w:.2f})")
        votes["bull"] += 1
    elif ml_sig == "SELL" and ml_conf >= 30:
        pts = min(30, int(ml_conf * 0.4 * _ml_w))
        score -= pts; reasons.append(f"ML ensemble SELL (conf {ml_conf}%, prob {ml_prob:.0%}, weight={_ml_w:.2f})")
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

    # 7b. Level 2 bid/ask imbalance — real institutional order book
    _l2 = state.get("l2_data", {}) if isinstance(state, dict) else {}
    if not _l2.get("stale", True) and _l2.get("bid_ask_imb") is not None:
        _imb      = float(_l2.get("bid_ask_imb", 50))
        _l2_sig   = _l2.get("l2_signal", "NEUTRAL")
        _tape_sig = _l2.get("tape_signal", "NEUTRAL")
        _sweep    = _l2.get("sweep_detected", False)
        _lp_cnt   = int(_l2.get("large_print_count", 0))
        if _l2_sig == "STRONG_ABSORPTION":
            score += 15; reasons.append(f"L2: {_imb:.0f}% bid-side — institutions absorbing at bid")
            votes["bull"] += 1
        elif _l2_sig == "BULLISH_IMBALANCE":
            score += 8; votes["bull"] += 1
        elif _l2_sig == "OFFER_HEAVY":
            score -= 15; reasons.append(f"L2: {_imb:.0f}% bid-side — heavy offer, sellers stacked")
            votes["bear"] += 1
        elif _l2_sig == "BEARISH_IMBALANCE":
            score -= 8; votes["bear"] += 1
        else:
            votes["neutral"] += 1
        if _tape_sig == "AGGRESSIVE_BUYING":
            score += 10; reasons.append("Tape: aggressive buying — bid-side sweeps dominating")
            votes["bull"] += 1
        elif _tape_sig == "AGGRESSIVE_SELLING":
            score -= 10; votes["bear"] += 1
        if _sweep:
            score += 12; reasons.append("L2 SWEEP: ask lifted through multiple levels")
            votes["bull"] += 1
        if _lp_cnt >= 3:
            score += 8; reasons.append(f"{_lp_cnt} large prints (5000+ shares) — institutional")
            votes["bull"] += 1

    # 8. SPY/QQQ macro backdrop
    macro_score = float(spy_data.get("macro_score", 0) or 0)
    spy_ob = spy_data.get("spy_ob", False)
    spy_os = spy_data.get("spy_os", False)
    qqq_ob = spy_data.get("qqq_ob", False)
    qqq_os = spy_data.get("qqq_os", False)
    # Multi-timeframe confluence — much stronger signal
    spy_mtf_ob = spy_data.get("spy_mtf_ob", False)
    spy_mtf_os = spy_data.get("spy_mtf_os", False)
    mtf_both_ob = spy_data.get("mtf_both_ob", False)
    mtf_both_os = spy_data.get("mtf_both_os", False)
    spy_rsi_4h = float(spy_data.get("spy_rsi_4h", 50) or 50)
    qqq_rsi_4h = float(spy_data.get("qqq_rsi_4h", 50) or 50)

    if mtf_both_ob:
        score -= 15; reasons.append(f"SPY+QQQ overbought on 4h+daily (SPY 4h RSI:{spy_rsi_4h:.0f}, QQQ 4h RSI:{qqq_rsi_4h:.0f})")
        votes["bear"] += 1
    elif mtf_both_os:
        score += 15; reasons.append(f"SPY+QQQ oversold on 4h+daily — high-conviction bounce setup")
        votes["bull"] += 1
    elif spy_ob and qqq_ob:
        score -= 10; reasons.append("SPY + QQQ both overbought daily — market stretched")
        votes["bear"] += 1
    elif spy_os and qqq_os:
        score += 10; reasons.append("SPY + QQQ both oversold daily — market washed out")
        votes["bull"] += 1

    # VIX regime flip — macro event signal (highest priority)
    _vix_flip = state.get("vix_flip", {}) if isinstance(state, dict) else {}
    if _vix_flip.get("signal") == "STRONG_BUY":
        score += 20; votes["bull"] += 1
        reasons.append(f"🚨 VIX fear-to-relief flip ({_vix_flip.get('vix_change_pct',0):+.0f}%) — macro BUY")
    elif _vix_flip.get("signal") == "STRONG_SELL":
        score -= 20; votes["bear"] += 1
        reasons.append(f"🚨 VIX panic spike ({_vix_flip.get('vix_change_pct',0):+.0f}%) — macro SELL")
    elif _vix_flip.get("signal") == "BUY":
        score += 10; votes["bull"] += 1
        reasons.append(f"VIX relief ({_vix_flip.get('vix_change_pct',0):+.0f}%) — risk-off easing")
    elif _vix_flip.get("signal") == "SELL":
        score -= 10; votes["bear"] += 1
        reasons.append(f"VIX stress spike ({_vix_flip.get('vix_change_pct',0):+.0f}%) — caution")

    # VIX term structure — backwardation = panic = favor mean-reversion
    _breadth = state.get("breadth", {}) if isinstance(state, dict) else {}
    _term_spread = float(_breadth.get("term_spread", 0) or 0)
    if _breadth.get("vix_backw") and _term_spread > 2:
        if score < 0:
            score += 12; reasons.append(f"VIX backwardation (+{_term_spread:.1f}) — panic peak, mean-reversion likely")
            votes["bull"] += 1
        else:
            reasons.append(f"VIX backwardation — stress elevated, use caution")
    elif _breadth.get("breadth_signal") == "COMPLACENT":
        score -= 5; votes["bear"] += 1
    # 4h alone is also meaningful
    elif spy_rsi_4h > 72:
        score -= 6; reasons.append(f"SPY overbought on 4h (RSI {spy_rsi_4h:.0f}) — pullback risk")
        votes["bear"] += 1
    elif spy_rsi_4h < 28:
        score += 6; reasons.append(f"SPY oversold on 4h (RSI {spy_rsi_4h:.0f}) — bounce likely")
        votes["bull"] += 1
    elif macro_score >= 20:
        score += 6; votes["bull"] += 1
    elif macro_score <= -20:
        score -= 6; votes["bear"] += 1
    else:
        votes["neutral"] += 1

    # ── TIER 3.5: VOLUME SIGNALS (±10 pts each) ─────────────────────────────────

    # 8b. OFI — Order Flow Imbalance (institutional buy/sell pressure)
    _dv_ft    = dv_result.get("features", {}) if isinstance(dv_result, dict) else {}
    ofi_ratio  = float(_dv_ft.get("ofi_ratio",  0) or 0)
    absorption = float(_dv_ft.get("absorption",  0) or 0)
    if ofi_ratio > 2.0:
        score += 10; reasons.append(f"OFI {ofi_ratio:.1f}x — institutions actively BUYING")
        votes["bull"] += 1
    elif ofi_ratio < -2.0:
        score -= 10; reasons.append(f"OFI {ofi_ratio:.1f}x — institutions actively SELLING")
        votes["bear"] += 1
    else:
        votes["neutral"] += 1

    # 8c. Absorption — institutions defending a price level
    if absorption > 2.0:
        score += 6; reasons.append(f"High absorption ({absorption:.1f}x) — smart money holding price")
        votes["bull"] += 1
    elif absorption < 0.3:
        score -= 4; reasons.append("No absorption — price level not defended")
        votes["bear"] += 1

    # 8d. Volume Profile POC + Value Area — institutional support/resistance
    poc_data  = state.get("poc_data", {}) if isinstance(state, dict) else {}
    poc_price = float(poc_data.get("poc", 0) or 0)
    vah       = float(poc_data.get("vah", 0) or 0)
    val       = float(poc_data.get("val", 0) or 0)
    in_va     = poc_data.get("in_va", True)

    if poc_price > 0:
        poc_dist = (price - poc_price) / price * 100

        # Price vs VAH (Value Area High) — breakout above = bullish
        if vah > 0 and price > vah:
            score += 10; reasons.append(f"Price ABOVE Value Area High ${vah:.0f} — bullish breakout")
            votes["bull"] += 1
        # Price vs VAL (Value Area Low) — break below = bearish
        elif val > 0 and price < val:
            score -= 10; reasons.append(f"Price BELOW Value Area Low ${val:.0f} — bearish breakdown")
            votes["bear"] += 1
        # Price vs POC (inside value area)
        elif poc_dist > 1.5:
            score += 5; reasons.append(f"Price {poc_dist:.1f}% above POC ${poc_price:.0f} — bullish structure")
            votes["bull"] += 1
        elif poc_dist < -1.5:
            score -= 5; reasons.append(f"Price {abs(poc_dist):.1f}% below POC ${poc_price:.0f} — bearish structure")
            votes["bear"] += 1
        else:
            # Price AT POC — magnet zone, low directional signal
            reasons.append(f"Price at POC ${poc_price:.0f} — magnet zone, watch for breakout direction")
            votes["neutral"] += 1

    # 8e. 4h volume — high volume confirms the dominant direction
    tsla_4h_vol = float(state.get("tsla_4h", {}).get("vol_ratio_4h", 1.0) or 1.0) if isinstance(state, dict) else 1.0
    if tsla_4h_vol > 2.0 and score != 0:
        amp = 6 if score > 0 else -6
        score += amp
        reasons.append(f"4h volume surge ({tsla_4h_vol:.1f}x avg) — institutional conviction")
        votes["bull" if amp > 0 else "bear"] += 1

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

    # 10b. Swing context — daily candle patterns + channel
    _swing = state.get("swing_context", {}) if isinstance(state, dict) else {}
    _sw_pattern = _swing.get("pattern_signal", "NEUTRAL")
    _sw_bias    = _swing.get("swing_bias", "NEUTRAL")
    if _sw_pattern == "BUY":
        score += 8; reasons.append(f"Daily {_swing.get('daily_pattern','pattern')} — multi-day bullish setup")
        votes["bull"] += 1
    elif _sw_pattern == "SELL":
        score -= 8; reasons.append(f"Daily {_swing.get('daily_pattern','pattern')} — multi-day bearish setup")
        votes["bear"] += 1
    # Channel resistance warning
    if _swing.get("channel_top") and price >= _swing["channel_top"] * 0.98:
        score -= 6; reasons.append(f"Near descending channel resistance ${_swing['channel_top']:.0f}")
        votes["bear"] += 1

    # 11. News sentiment + StockTwits contrarian
    news_score = float(news_data.get("score", 0) or 0) if news_data else 0
    if news_score >= 20:
        score += 5; votes["bull"] += 1
    elif news_score <= -20:
        score -= 5; votes["bear"] += 1
    else:
        votes["neutral"] += 1
    # StockTwits contrarian signal
    _st = (news_data or {}).get("stocktwits", {})
    _st_sig = _st.get("signal", "NEUTRAL")
    if _st_sig == "CONTRARIAN_BUY":
        score += 7; reasons.append(_st.get("contrarian_signal","StockTwits extreme fear → contrarian BUY"))
        votes["bull"] += 1
    elif _st_sig == "CONTRARIAN_SELL":
        score -= 7; reasons.append(_st.get("contrarian_signal","StockTwits extreme bulls → contrarian SELL"))
        votes["bear"] += 1

    # 11b. VWAP relationship — institutional reference level
    _vb = state.get("vwap_bands", {}) if isinstance(state, dict) else {}
    _vwap_sig = _vb.get("vwap_signal", "NEUTRAL")
    _anc_above = _vb.get("anchored_above", None)
    _vwap_dist = float(_vb.get("vwap_dist_pct", 0) or 0)
    if _vwap_sig == "ABOVE_VWAP" and _anc_above:
        score += 8; reasons.append(f"Price above VWAP + anchored VWAP — institutional support confirmed")
        votes["bull"] += 1
    elif _vwap_sig == "EXTENDED_ABOVE":
        score -= 5; reasons.append(f"Price extended above VWAP ({_vwap_dist:+.1f}%) — overbought vs VWAP")
        votes["bear"] += 1
    elif _vwap_sig == "BELOW_VWAP" and _anc_above is False:
        score -= 8; reasons.append(f"Price below VWAP and anchored VWAP — institutional selling")
        votes["bear"] += 1
    elif _vwap_sig == "EXTENDED_BELOW":
        score += 5; reasons.append(f"Price extended below VWAP ({_vwap_dist:+.1f}%) — oversold vs VWAP")
        votes["bull"] += 1

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

    total_votes    = votes["bull"] + votes["bear"] + votes["neutral"]
    decisive_votes = votes["bull"] + votes["bear"]
    # Conviction = directional agreement among models that took a stance
    # Neutral votes show uncertainty but don't dilute the conviction of those that voted
    if decisive_votes > 0:
        bull_pct   = round(votes["bull"] / decisive_votes * 100)
        bear_pct   = round(votes["bear"] / decisive_votes * 100)
    else:
        bull_pct = bear_pct = 0
    # Scale by participation: if only 2/12 models voted, conviction is lower
    participation = round(decisive_votes / max(total_votes, 1) * 100)
    raw_conviction = max(bull_pct, bear_pct)
    conviction = round(raw_conviction * (0.5 + participation / 200))  # blend: 50-100% of raw

    # Score is primary gate. Conviction is secondary — don't let broken
    # conviction scorer silence a high-confidence score.
    # If score is strong (>=65), act on it even with lower conviction.
    # If score is moderate (40-64), require conviction >= 40%.
    min_conv_strong = 35   # strong signal — low bar, score speaks for itself
    min_conv_normal = 45   # moderate signal — need some agreement

    # Use dynamically learned thresholds
    _dyn_score_buy  = _dynamic_thresholds.get("spock_score_buy", 40)
    _dyn_conv       = _dynamic_thresholds.get("conviction_buy", 35)

    if score >= (_dyn_score_buy + 25) and conviction >= _dyn_conv:
        action = "STRONG BUY";  color = "#00ff88"
    elif score >= _dyn_score_buy and conviction >= _dyn_conv:
        action = "BUY";         color = "#69f0ae"
    elif score <= -(_dyn_score_buy + 25) and conviction >= _dyn_conv:
        action = "STRONG SELL"; color = "#ff1744"
    elif score <= -_dyn_score_buy and conviction >= _dyn_conv:
        action = "SELL";        color = "#ff6d00"
    else:
        action = "HOLD";        color = "#00e5ff"
        if score >= _dyn_score_buy and conviction < _dyn_conv:
            action = "HOLD — LOW CONVICTION"; color = "#ffb300"
        elif score <= -_dyn_score_buy and conviction < _dyn_conv:
            action = "HOLD — LOW CONVICTION"; color = "#ffb300"

    # Apply hard risk rules to SPOCK as well
    _hr_allow_buy, _, _hr_risk, _hr_reasons = check_hard_risk_rules(
        price, spy_data, indicators or {}, mm_data)
    if not _hr_allow_buy and score > 0:
        score = min(score, 20)   # cap bullish score — but don't zero it
        if _hr_reasons:
            reasons.insert(0, _hr_reasons[0])
        votes["neutral"] += 1   # neutral, not bear — risk is elevated not reversed

    # Risk level — includes SPY/QQQ overbought state
    vix = float(spy_data.get("vix", 20) or 20)
    abs_gex = abs(gex)
    spy_rsi_4h = float(spy_data.get("spy_rsi_4h", 50) or 50)
    qqq_rsi_4h = float(spy_data.get("qqq_rsi_4h", 50) or 50)
    mtf_both_ob = spy_data.get("mtf_both_ob", False)
    earn_ctx    = state.get("earnings_context", {}) if isinstance(state, dict) else {}
    near_earn   = earn_ctx.get("earnings_mode", False)

    if vix >= 35 or abs_gex >= 500 or (spy_rsi_4h > 88 and qqq_rsi_4h > 88):
        risk = "EXTREME"
    elif vix >= 25 or abs_gex >= 200 or mtf_both_ob or near_earn:
        risk = "HIGH"
    elif vix >= 18 or abs_gex >= 100 or spy_rsi_4h > 75:
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

def run_analysis(refresh_4h=True, refresh_news=True):
    global last_signal
    print(f"\n[ANALYSIS] {TICKER} @ {datetime.now().strftime('%H:%M:%S')}...", flush=True)
    poc_data = state.get("poc_data", {})  # init early — computed later, use last known until then
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
                    # TSLA daily for institutional models — Schwab first
                    hist, _inst_src = _schwab_or_yf(TICKER, period_years=0.5, freq_minutes=1440,
                                                     yf_period="6mo", yf_interval="1d")
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
        # VWAP must reset daily — filter to today's bars only
        from datetime import date as _date
        _today_str = str(_date.today())
        _today_mask = hist.index.date == _date.today()
        if _today_mask.sum() > 0:
            _h_today = hist[_today_mask]
            _vwap_h = _h_today["High"].astype(float)
            _vwap_l = _h_today["Low"].astype(float)
            _vwap_c = _h_today["Close"].astype(float)
            _vwap_v = _h_today["Volume"].astype(float)
        else:
            # Weekend/pre-market: use last trading day
            _last_date = hist.index.date[-1]
            _mask = hist.index.date == _last_date
            _h_today = hist[_mask]
            _vwap_h = _h_today["High"].astype(float)
            _vwap_l = _h_today["Low"].astype(float)
            _vwap_c = _h_today["Close"].astype(float)
            _vwap_v = _h_today["Volume"].astype(float)
        vwap_r   = calculate_vwap(_vwap_h, _vwap_l, _vwap_c, _vwap_v)
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
            # VIX term structure + breadth
            try:
                _breadth = calculate_market_breadth(spy_data)
                spy_data.update(_breadth)
                state["breadth"] = _breadth
            except Exception: pass
            # VIX regime flip detector — macro event detection
            try:
                _vix_flip = detect_vix_regime_flip(spy_data)
                state["vix_flip"] = _vix_flip
                if _vix_flip.get("flip") == "FEAR_TO_RELIEF":
                    _flip_msg = (
                        f"🚨 *MACRO REGIME FLIP* — VIX CRASHED\n"
                        f"━━━━━━━━━━━━━━━━━━━━━━\n"
                        f"VIX: {_vix_flip.get('vix_prev','?')} → {_vix_flip.get('vix_today','?')} "
                        f"({_vix_flip.get('vix_change_pct',0):+.1f}%)\n"
                        f"📊 Fear-to-relief regime flip detected\n"
                        f"⚡ High-beta stocks (TSLA beta=2x) historically surge\n"
                        f"💰 Current TSLA: ${price:.2f} | Consider aggressive BUY\n"
                        f"⚠️ This is a macro signal, not a technical one"
                    )
                    log_alert(_flip_msg, alert_key="vix_regime_flip")
                    print("  🚨 MACRO RELIEF DETECTED — VIX flip alert sent", flush=True)
                elif _vix_flip.get("flip") == "PANIC_SPIKE":
                    _panic_msg = (
                        f"🚨 *VIX PANIC SPIKE* — EXIT LONGS\n"
                        f"━━━━━━━━━━━━━━━━━━━━━━\n"
                        f"VIX: {_vix_flip.get('vix_prev','?')} → {_vix_flip.get('vix_today','?')} "
                        f"({_vix_flip.get('vix_change_pct',0):+.1f}%)\n"
                        f"⛔ Sudden panic — reduce all positions immediately"
                    )
                    log_alert(_panic_msg, alert_key="vix_panic_spike")
            except Exception: pass
        except Exception as _e:
            print(f"  ⚠️ SPY analysis error: {_e}")
            spy_data = {"macro_score":0,"macro_signal":"ERROR","spy_trend":"UNKNOWN","spy_change_pct":0,"beta_20d":2.0,"vix":20,"vix_regime":"UNKNOWN","rs_signal":"NEUTRAL","divergence_warning":False,"expected_tsla_move":0,"tsla_spy_deviation":0}

        # ══ NEWS ENGINE ══
        if refresh_news or not state.get("news_data"):
            print("  📰 Fetching real-time news...")
            try:
                raw_articles = fetch_news()
                news_data    = calculate_news_sentiment(raw_articles)
                # Add StockTwits sentiment
                try:
                    _st = fetch_stocktwits_sentiment(TICKER)
                    news_data["stocktwits"] = _st
                    if _st.get("contrarian_signal"):
                        print(f"  ⚡ Contrarian: {_st['contrarian_signal']}", flush=True)
                except Exception: pass
                state["news_data"] = news_data
            except Exception as _e:
                print(f"  ⚠️ News error: {_e}")
                raw_articles = []
                news_data    = {"score":0,"signal":"ERROR","bull_count":0,"bear_count":0,"articles":[]}
        else:
            print("  📰 News: [cached]", flush=True)
            news_data    = state.get("news_data", {"score":0,"signal":"NEUTRAL","articles":[]})
            raw_articles = news_data.get("articles", [])

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
                        _prev_gex = state.get("mm_data", {}).get("gex_total", None)
                        _curr_gex = _schwab_opts.get('gex_total', 0)
                        _gex_stale = (_prev_gex is not None and _prev_gex == _curr_gex)
                        print(f"  📡 Schwab options: {len(_schwab_opts['calls'])} calls, "
                              f"{len(_schwab_opts['puts'])} puts, "
                              f"GEX={_curr_gex:.0f}M "
                              f"PC={_schwab_opts.get('pc_ratio',0):.2f}"
                              f"{' [STALE-AH]' if _gex_stale else ''}", flush=True)
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
            "vix":        float(spy_data.get("vix", 20) or 20),
            "ret_1b":     float(closes.pct_change(1).iloc[-1] or 0),
            "ret_3b":     float(closes.pct_change(3).iloc[-1] or 0),
            "poc_price":  float(poc_data.get("poc", 0) or 0),
            "vah":        float(poc_data.get("vah", 0) or 0),
            "val":        float(poc_data.get("val", 0) or 0),
            "current_price": price,
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
            # Use last 30 trading days = ~2340 bars of 5-min data
            _poc_lookback = min(2340, len(closes))
            for i in range(-_poc_lookback, 0):
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

        except Exception as _vol_profile_err:
            print(f"  ⚠️ vol_profile error: {_vol_profile_err}", flush=True)
            vol_profile = []
            poc_data    = {}

        # ── Intraday VWAP Bands ────────────────────────────────────────────
        try:
            vwap_bands = calculate_vwap_bands_daily(closes, highs, lows, volumes)
            state["vwap_bands"] = vwap_bands
            _vb = vwap_bands
            print(f"  📊 VWAP: ${_vb.get('vwap','?')} | {_vb.get('vwap_signal','?')} | "
                  f"Dist:{_vb.get('vwap_dist_pct',0):+.2f}% | "
                  f"Anchored:${_vb.get('anchored_vwap','?')} "
                  f"({'above' if _vb.get('anchored_above') else 'below'})", flush=True)
        except Exception as _vwap_err:
            state["vwap_bands"] = {}

        # macd_history — last 60 days of MACD line, signal, histogram
        macd_history = []
        try:
            exp12 = closes.ewm(span=12, adjust=False).mean()
            exp26 = closes.ewm(span=26, adjust=False).mean()
            macd_line   = exp12 - exp26
            signal_line = macd_line.ewm(span=9, adjust=False).mean()
            histogram   = macd_line - signal_line
            for i in range(-min(60, len(histogram)), 0):
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

        # Compute price_change_pct from daily open reference
        try:
            _prev_close = float(closes.iloc[-2]) if len(closes) > 1 else price
            _price_chg_pct = round((price - _prev_close) / max(_prev_close, 0.01) * 100, 2)
        except Exception:
            _price_chg_pct = 0.0

        state.update({
            "ticker":             TICKER,
            "price":              price,
            "price_change_pct":   _price_chg_pct,
            "session_type":       ext_data.get("session", "UNKNOWN"),
            "signal":             signal,
            "signal_strength":    strength,
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

        # ── TSLA 4h Multi-Timeframe Analysis (cached every 15 min) ─────
        if refresh_4h or not state.get("tsla_4h"):
            try:
                tsla_4h_data = calculate_tsla_4h(TICKER)
                state["tsla_4h"] = tsla_4h_data
                print(f"  📊 TSLA 4h: RSI={tsla_4h_data['rsi_4h']} | "
                      f"Trend={tsla_4h_data['trend_4h']} | "
                      f"MACD={'▲' if tsla_4h_data['macd_bull_4h'] else '▼'} | "
                      f"BB={tsla_4h_data['bb_pct_4h']:.2f}", flush=True)
            except Exception as _4he:
                print(f"  ⚠️ TSLA 4h error: {_4he}", flush=True)
                tsla_4h_data = state.get("tsla_4h", {})
        else:
            tsla_4h_data = state.get("tsla_4h", {})
            print(f"  📊 TSLA 4h: [cached] RSI={tsla_4h_data.get('rsi_4h','?')} "
                  f"Trend={tsla_4h_data.get('trend_4h','?')}", flush=True)

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

        # ── HARD RISK RULES — override everything ─────────────────────────
        _allow_buy, _allow_sell, _risk_ovr, _risk_reasons = check_hard_risk_rules(
            price, spy_data, indicators, mm_data)
        if _risk_ovr:
            state["hard_risk"] = {"override": _risk_ovr, "reasons": _risk_reasons}
            print(f"  🛡 Hard risk: {_risk_ovr} — {'; '.join(_risk_reasons[:2])}", flush=True)
        if signal == "BUY"  and not _allow_buy:
            print(f"  ⛔ BUY blocked by hard risk rule: {_risk_reasons[0] if _risk_reasons else ''}", flush=True)
            signal = "HOLD"
        if signal == "SELL" and not _allow_sell:
            signal = "HOLD"

        # SPOCK conviction check — don't alert if SPOCK disagrees
        _spock = state.get("master_signal", {})
        _spock_action    = _spock.get("action", "HOLD")
        _spock_conv      = _spock.get("conviction", 0) or 0
        _spock_ok_buy    = _spock_conv >= 55 and "BUY"  in _spock_action
        _spock_ok_sell   = _spock_conv >= 55 and "SELL" in _spock_action

        # Signal coherence — check last alert direction to prevent BUY+SELL flip
        _last_sell_time = _last_wa_send.get("signal_SELL")
        _last_buy_time  = _last_wa_send.get("signal_BUY")
        _atr = float(indicators.get("atr_ratio", 0.01) or 0.01) * price * 5  # 5x ATR = meaningful move
        _last_sell_price = state.get("_last_sell_price", 0) or 0
        _last_buy_price  = state.get("_last_buy_price", 0) or 0

        if signal != "HOLD" and signal != last_signal:
            # Momentum check
            if signal == "BUY"  and not _momentum_ok_buy:
                print(f"  ⚠️ BUY suppressed — momentum down ({_recent_momentum:.3%})", flush=True)
                signal = "HOLD"
            if signal == "SELL" and not _momentum_ok_sell:
                print(f"  ⚠️ SELL suppressed — momentum up ({_recent_momentum:.3%})", flush=True)
                signal = "HOLD"
            # Recompute with lower threshold
            _spock_ok_buy  = _spock_conv >= 35 and "BUY"  in _spock_action
            _spock_ok_sell = _spock_conv >= 35 and "SELL" in _spock_action

            # ── HARD BYPASS RULE ────────────────────────────────────────────
            # If ML conf > 80 AND capitulation/bounce detected AND price below
            # value area — send BUY regardless of conviction score.
            # This prevents the scorer from silencing a 97% confidence signal
            # at a capitulation low (the April 9 $340 miss).
            _ml_sig   = state.get("ml_signal", {})
            _ml_conf  = float(_ml_sig.get("confidence", 0) or 0)
            _dv_state = state.get("darthvader", {}).get("tsla_state", {}).get("state", "")
            _poc_val  = poc_data.get("val", 0) if isinstance(poc_data, dict) else 0
            _cap_bounce = any(x in _dv_state.upper() for x in
                              ["CAPITULATION", "BOUNCE", "MEAN_REVERSION", "REVERSAL"])
            _at_low   = _poc_val > 0 and price <= _poc_val * 1.02  # within 2% of VAL
            _bypass_buy = (
                _ml_conf >= 80 and
                _ml_sig.get("signal") == "BUY" and
                _cap_bounce and
                not _ml_retraining and
                _ml_ready
            )
            if _bypass_buy and signal in ("HOLD", "BUY"):
                signal = "BUY"
                print(f"  🚨 BYPASS: ML conf={_ml_conf:.0f}% + {_dv_state} → BUY forced through", flush=True)

            # SPOCK conviction check (with lowered threshold)
            if signal == "BUY"  and not _spock_ok_buy and not _bypass_buy:
                print(f"  ⚠️ BUY suppressed — SPOCK conviction too low ({_spock_conv}% / need 35%)", flush=True)
                signal = "HOLD"
            if signal == "SELL" and not _spock_ok_sell:
                print(f"  ⚠️ SELL suppressed — SPOCK conviction too low ({_spock_conv}% / need 35%)", flush=True)
                signal = "HOLD"
            # Coherence: suppress BUY if SELL fired recently AND price hasn't moved 1 ATR
            if signal == "BUY" and _last_sell_time:
                _sell_age_min = (datetime.now() - _last_sell_time).total_seconds() / 60
                _price_moved  = abs(price - _last_sell_price) if _last_sell_price else 999
                if _sell_age_min < 60 and _price_moved < _atr:
                    print(f"  ⚠️ BUY suppressed — SELL fired {_sell_age_min:.0f}min ago, price only moved ${_price_moved:.2f} (need ${_atr:.2f})", flush=True)
                    signal = "HOLD"
            # Coherence: suppress SELL if BUY fired recently AND price hasn't moved 1 ATR
            if signal == "SELL" and _last_buy_time:
                _buy_age_min  = (datetime.now() - _last_buy_time).total_seconds() / 60
                _price_moved  = abs(price - _last_buy_price) if _last_buy_price else 999
                if _buy_age_min < 60 and _price_moved < _atr:
                    print(f"  ⚠️ SELL suppressed — BUY fired {_buy_age_min:.0f}min ago, price only moved ${_price_moved:.2f} (need ${_atr:.2f})", flush=True)
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
                f"  SPY: {(state.get("spy_data") or spy_data).get("spy_trend","UNKNOWN")} | VIX: {vix}\n"
                f"  {(state.get("spy_data") or spy_data).get("macro_signal","?")}\n"
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
            # Track last alert prices for coherence check
            if signal == "BUY":  state["_last_buy_price"]  = price
            if signal == "SELL": state["_last_sell_price"] = price

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
                        # Earnings dates — yfinance is most reliable source for this
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
                    "next_earnings":  str(_future[0]) if _earn_dates and _future else "Unknown",
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
                # Volume Profile / POC features
                "poc_dist":        float(poc_data.get("price_vs_poc", 0) or 0) / 100,  # % from POC
                "above_poc":       1 if poc_data.get("above_poc", True) else 0,
                "in_value_area":   1 if poc_data.get("in_va", True) else 0,
                "above_vah":       1 if price > float(poc_data.get("vah", price) or price) else 0,
                "below_val":       1 if price < float(poc_data.get("val", price) or price) else 0,
                # Multi-timeframe SPY/QQQ (NEW — 4h + 1h)
                "spy_rsi_4h":      float(spy_data.get("spy_rsi_4h", 50) or 50),
                "spy_rsi_1h":      float(spy_data.get("spy_rsi_1h", 50) or 50),
                "spy_ob_4h":       1 if spy_data.get("spy_ob_4h", False) else 0,
                "spy_os_4h":       1 if spy_data.get("spy_os_4h", False) else 0,
                "spy_ob_1h":       1 if spy_data.get("spy_ob_1h", False) else 0,
                "spy_os_1h":       1 if spy_data.get("spy_os_1h", False) else 0,
                "spy_mtf_ob":      1 if spy_data.get("spy_mtf_ob", False) else 0,
                "spy_mtf_os":      1 if spy_data.get("spy_mtf_os", False) else 0,
                "qqq_rsi_4h":      float(spy_data.get("qqq_rsi_4h", 50) or 50),
                "qqq_ob_4h":       1 if spy_data.get("qqq_ob_4h", False) else 0,
                "mtf_both_ob":     1 if spy_data.get("mtf_both_ob", False) else 0,
                "mtf_both_os":     1 if spy_data.get("mtf_both_os", False) else 0,
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
            state["ml_signal"]         = ml_signal
            state["_last_ml_features"] = _ml_features  # for SPOCK decision logging

            # ── MASTER SIGNAL — synthesize all models ──────────────────────
            try:
                # Level 2 / Tape signal
                try:
                    if _L2_AVAILABLE and not schwab_l2._l2_state.get("stale", True):
                        _l2 = schwab_l2.get_l2_signal()
                        state["l2_data"] = _l2
                        _imb = _l2.get("bid_ask_imb", 50)
                        _tape = _l2.get("tape_signal", "NEUTRAL")
                        _sweep = _l2.get("sweep_detected", False)
                        _lp = len(_l2.get("large_prints", []))
                        print(f"  📊 L2: Bid/Ask imb={_imb:.0f}% | Tape={_tape} | "
                              f"LargePrints={_lp} | Sweep={_sweep}", flush=True)
                        # Large print + sweep = immediate alert candidate
                        if _sweep or _lp >= 3:
                            print(f"  🚨 INSTITUTIONAL ACTIVITY: sweep={_sweep} large_prints={_lp}", flush=True)
                    else:
                        state["l2_data"] = {"stale": True}
                except Exception as _l2e:
                    state["l2_data"] = {}

                # Swing context
                try:
                    _swing = calculate_swing_context(closes, highs, lows, price, mm_data)
                    state["swing_context"] = _swing
                    if _swing.get("daily_pattern"):
                        print(f"  📈 Daily pattern: {_swing['daily_pattern']} ({_swing['pattern_signal']})", flush=True)
                    if _swing.get("swing_reasons"):
                        print(f"  📈 Swing: {' | '.join(_swing['swing_reasons'][:2])}", flush=True)
                except Exception as _swe:
                    state["swing_context"] = {}

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
                # Add MTF narrative
                mtf = calculate_spock_mtf_narrative(
                    tsla_4h  = state.get("tsla_4h", {}),
                    spy_data = spy_data,
                    price    = price,
                )
                master["mtf"] = mtf

                # Breakout volume detector
                try:
                    breakout = _spock_detect_breakout(
                        price, closes, volumes, mm_data, spy_data)
                    master["breakout"] = breakout
                    if breakout["score"] != 0:
                        print(f"  🚨 BREAKOUT: {breakout['reason']}", flush=True)
                except Exception as _be:
                    master["breakout"] = {}

                state["master_signal"] = master

                # Log decision for self-learning
                if master["action"] not in ("HOLD",):
                    try:
                        _ml_feats = state.get("_last_ml_features", {})
                        _spock_log_decision(
                            action    = master["action"],
                            score     = master["score"],
                            conviction= master["conviction"],
                            price     = price,
                            features_snapshot = _ml_feats,
                            mtf_dir   = mtf.get("direction","?"),
                            mtf_conf  = mtf.get("confidence","?"),
                            reasons   = master["reasons"],
                        )
                    except Exception as _le:
                        pass

                # Measure outcomes of past decisions
                try:
                    _spock_measure_outcomes(price)
                except Exception as _oe:
                    pass

                # Add accuracy stats to state
                # Save spy_data to state for WA alerts + dashboard
                if spy_data and isinstance(spy_data, dict):
                    state["spy_data"] = spy_data
                state["spock_accuracy"] = _spock_accuracy
                state["spock_weights"]  = _spock_weights
                print(f"  🖖 SPOCK MTF: {mtf['direction']} {mtf['magnitude']} | "
                      f"conf={mtf['confidence']} | align={mtf['alignment']}", flush=True)
                # Apply breakout score to master
                bk = master.get("breakout", {})
                if bk.get("score", 0) != 0:
                    master["score"] = max(-100, min(100, master["score"] + bk["score"]))
                    if bk["score"] > 0:
                        master["reasons"].insert(0, bk["reason"])
                        master["bull_votes"] += 1
                    else:
                        master["reasons"].insert(0, bk["reason"])
                        master["bear_votes"] += 1

                print(f"  🖖 SPOCK MASTER: {master['action']} | score={master['score']:+d} | "
                      f"conviction={master['conviction']}% | risk={master['risk']} | "
                      f"bulls={master['bull_votes']} bears={master['bear_votes']} neutral={master.get('neutral_votes','?')}", flush=True)
                if master.get('reasons'):
                    print(f"  🖖 Top reasons: {' | '.join(master['reasons'][:2])}", flush=True)
            except Exception as _me:
                print(f"  ⚠️ Master signal error: {_me}", flush=True)
                state["master_signal"] = {"action":"HOLD","score":0,"conviction":0,
                                          "risk":"MEDIUM","color":"#00e5ff","reasons":[]}
            _regime_str = ml_signal.get('regime', '')
            _matched    = ml_signal.get('features_matched', 0)
            _total      = ml_signal.get('features_total', 84)
            _mismatch   = _matched < _total * 0.9  # more than 10% features missing
            if _mismatch:
                print(f"  ⚠️ ML feature mismatch ({_matched}/{_total}) — forcing HOLD", flush=True)
                ml_signal = {**ml_signal, "signal": "HOLD", "confidence": 0}
                state["ml_signal"] = ml_signal
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
                f"🌍 SPY: {(state.get("spy_data") or spy_data).get("spy_trend","UNKNOWN")} | VIX: {(state.get("spy_data") or spy_data).get("vix","?")}"
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
        # Suppress SELL ZONE during confirmed capitulation bounce — system is bullish internally
        _dv_st  = state.get("darthvader", {}).get("tsla_state", {}).get("state", "")
        _cap_on = any(x in _dv_st.upper() for x in ["CAPITULATION","MEAN_REVERSION"])
        _cap_cf = state.get("darthvader", {}).get("tsla_state", {}).get("confidence", 0) or 0
        if _cap_on and _cap_cf >= 70 and exit_score < 75:
            print(f"  ⚠️ EXIT SELL suppressed — {_dv_st} active (conf={_cap_cf}%)", flush=True)
        elif exit_score >= 55 and prev_exit_score < 55:  # Raised from 45→55 to reduce noise
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
                f"🌍 SPY: {(state.get("spy_data") or spy_data).get("spy_trend","UNKNOWN")} | VIX: {(state.get("spy_data") or spy_data).get("vix","?")}\n"
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
                f"🌍 SPY Trend: {(state.get("spy_data") or spy_data).get("spy_trend","UNKNOWN")}\n"
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


# ── Tiered frequency caches ─────────────────────────────────────────────────
_cache_4h      = {"ts": 0, "data": None}   # refresh every 15 min
_cache_news    = {"ts": 0, "data": None}   # refresh every 15 min
_price_history = []                         # rolling 1-min price ticks

def _get_quick_price():
    """Fetch just the current price — fast, lightweight."""
    try:
        import schwab_client as sc_mod
        sc = sc_mod.get_client() if hasattr(sc_mod, "get_client") else None
        if sc:
            q = sc_mod.get_quote(TICKER)
            if q and q.get("price"):
                return float(q["price"])
    except Exception:
        pass
    try:
        import yfinance as yf
        t = yf.Ticker(TICKER)
        fast = t.fast_info
        return float(fast.get("last_price") or fast.get("regularMarketPrice") or 0)
    except Exception:
        return None


def _check_flash_move(current_price):
    """
    Check if price moved >1% in the last 1-5 minutes.
    Returns (triggered, pct_move, direction) 
    """
    if len(_price_history) < 2:
        return False, 0, ""
    oldest = _price_history[0]["price"]
    if oldest <= 0:
        return False, 0, ""
    pct = (current_price - oldest) / oldest * 100
    if abs(pct) >= 1.0:
        direction = "UP" if pct > 0 else "DOWN"
        return True, round(pct, 2), direction
    return False, 0, ""


def _fast_price_loop():
    """
    Tier 1: runs every 60s during market hours.
    Checks price only — triggers full analysis on flash moves.
    """
    import time as _t
    print("[PRICE-LOOP] 1-min price monitor started", flush=True)
    _last_alert_price = 0
    _last_flash_ts    = 0

    while True:
        try:
            now = datetime.now()
            # Only run during market hours (Mon-Fri 9:30-16:00 ET)
            is_market = (now.weekday() < 5 and
                         (now.hour > 9 or (now.hour == 9 and now.minute >= 30)) and
                         now.hour < 16)

            if is_market:
                price = _get_quick_price()
                if price and price > 0:
                    # Add to rolling 5-min history
                    _price_history.append({"ts": time.time(), "price": price})
                    # Keep only last 5 ticks (5 min window)
                    while len(_price_history) > 5:
                        _price_history.pop(0)

                    # Update state price immediately (always — even on first startup)
                    state["price"]  = price
                    state["ticker"] = TICKER

                    # Flash move detection
                    flash, pct, direction = _check_flash_move(price)
                    now_ts = time.time()
                    if flash and (now_ts - _last_flash_ts) > 300:  # 5-min cooldown
                        _last_flash_ts = now_ts
                        print(f"[PRICE-LOOP] ⚡ FLASH MOVE: {pct:+.2f}% in ~5min "
                              f"({direction}) @ ${price}", flush=True)
                        # Send immediate WA alert for big moves
                        if abs(pct) >= 2.0:
                            emoji = "🚀" if direction == "UP" else "💥"
                            _flash_msg = (
                                f"{emoji} {TICKER} *FLASH MOVE* {pct:+.2f}% in 5min\n"
                                f"💰 Price: *${price}*\n"
                                f"⚡ Triggered immediate analysis"
                            )
                            _send_whatsapp(_flash_msg, "flash_move")
                        # Trigger full analysis immediately
                        import threading as _tflash
                        _tflash.Thread(target=run_analysis, daemon=True).start()

                    print(f"[PRICE] ${price} | "
                          f"{'📈' if pct >= 0 else '📉'} {pct:+.2f}% (5min) | "
                          f"{'MARKET' if is_market else 'CLOSED'}", flush=True)

        except Exception as e:
            print(f"[PRICE-LOOP] Error: {e}", flush=True)

        _t.sleep(60)  # check every 60 seconds


def monitor_loop():
    """
    Tier 2: Full analysis every 5 minutes.
    Uses caches for slow-changing signals (4h, news).
    """
    cycle = 0
    while True:
        cycle += 1
        now_ts = time.time()
        print(f"[LOOP] cycle {cycle} starting", flush=True)

        # Decide what to refresh this cycle
        refresh_4h   = (now_ts - _cache_4h["ts"])   > 900   # every 15 min
        refresh_news = (now_ts - _cache_news["ts"]) > 900   # every 15 min

        if refresh_4h:
            print(f"[LOOP] Refreshing 4h cache (was {(now_ts-_cache_4h['ts'])/60:.0f}min old)", flush=True)
        if refresh_news:
            print(f"[LOOP] Refreshing news cache", flush=True)

        run_analysis(
            refresh_4h   = refresh_4h,
            refresh_news = refresh_news,
        )

        # Update caches after run
        if refresh_4h:
            _cache_4h["ts"]   = now_ts
            _cache_4h["data"] = state.get("tsla_4h", {})
        if refresh_news:
            _cache_news["ts"]   = now_ts
            _cache_news["data"] = state.get("news_data", {})

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
        # Cap large lists to avoid massive JSON responses
        lst = list(obj)[:200] if len(obj) > 200 else list(obj)
        return [_sanitize(x, _depth+1) for x in lst]
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
        import traceback
        print(f"  ❌ api_state serialization error: {e}", flush=True)
        print(traceback.format_exc()[:500], flush=True)
        try:
            # Fallback: strip heavy/problematic keys and sanitize
            dv_full = state.get("darthvader", {})
            safe = {
                "ticker":        TICKER,
                "price":         state.get("price"),
                "price_change_pct": state.get("price_change_pct"),
                "session_type":  state.get("session_type", "UNKNOWN"),
                "last_updated":  state.get("last_updated"),
                "signal":        state.get("signal", "HOLD"),
                "master_signal": state.get("master_signal", {}),
                "ml_signal":     state.get("ml_signal", {}),
                "spy_data":      state.get("spy_data", {}),
                "mm_data":       state.get("mm_data", {}),
                "uoa_data":      state.get("uoa_data", {}),
                "poc_data":      state.get("poc_data", {}),
                "vwap_bands":    state.get("vwap_bands", {}),
                "tsla_4h":       state.get("tsla_4h", {}),
                "sizing":        state.get("sizing", {}),
                "earnings_context": state.get("earnings_context", {}),
                "breadth":       state.get("breadth", {}),
                "vix_flip":      state.get("vix_flip", {}),
                "swing_context": state.get("swing_context", {}),
                "alerts_log":    state.get("alerts_log", [])[:20],
                "spock_accuracy":state.get("spock_accuracy", {}),
                "ml_ready":      _ml_ready,
                "ml_retraining": _ml_retraining,
                "wa_enabled":    WA_ENABLED,
                "wa_phone_tail": GREEN_PHONE[-4:] if GREEN_PHONE else "",
                "darthvader": {
                    "features":    dv_full.get("features", {}),
                    "tsla_state":  dv_full.get("tsla_state", {}),
                    "risk_mode":   dv_full.get("risk_mode", "NORMAL"),
                },
            }
            return jsonify(_sanitize(safe))
        except Exception as e2:
            print(f"  ❌ api_state fallback also failed: {e2}", flush=True)
            return jsonify({"ticker": TICKER, "price": state.get("price"),
                            "last_updated": state.get("last_updated"),
                            "master_signal": {"action":"HOLD","score":0,"conviction":0,
                                              "risk":"UNKNOWN","reasons":[]},
                            "_error": "serialization_failed"})

@app.route("/api/switch_ticker")
def api_switch_ticker():
    global TICKER, _DV_CACHE, _ml_model_cache, _ml_load_errors
    sym = request.args.get("ticker", "TSLA").upper().strip()
    if not sym or not sym.replace(".", "").isalpha() or len(sym) > 6:
        return jsonify({"status": "error", "msg": "invalid ticker"}), 400

    if sym == TICKER:
        return jsonify({"status": "same", "ticker": TICKER})

    # Save current ticker state to cache
    _ticker_cache[TICKER] = {
        "state":     dict(state),
        "timestamp": time.time(),
    }

    TICKER = sym

    # Restore cached state if available and recent (< 10 min)
    cached = _ticker_cache.get(TICKER)
    if cached and (time.time() - cached["timestamp"]) < 600:
        state.clear()
        state.update(cached["state"])
        print(f"  🔄 Switched to {TICKER} (from cache)", flush=True)
        threading.Thread(target=run_analysis, daemon=True).start()
        return jsonify({"status": "switched_cached", "ticker": TICKER})

    # Fresh switch — reset state and retrain
    _DV_CACHE = {"ts": 0, "data": None}
    state.clear()
    state.update({"ticker": TICKER, "price": None, "darthvader": {}, "last_updated": None})
    _ml_model_cache = None
    _ml_load_errors = []
    print(f"  🔄 Switched to {TICKER} (fresh)", flush=True)
    threading.Thread(target=_run_ml_retrain, daemon=True).start()
    threading.Thread(target=run_analysis, daemon=True).start()
    return jsonify({"status": "switched", "ticker": TICKER})


@app.route("/api/watchlist")
def api_watchlist():
    """Return SPOCK quick-read for all watchlist tickers."""
    return jsonify({
        "watchlist": _WATCHLIST,
        "scores":    _WATCHLIST_SCORES,
        "current":   TICKER,
    })


@app.route("/api/watchlist/add")
def api_watchlist_add():
    global _WATCHLIST
    sym = request.args.get("ticker", "").upper().strip()
    if sym and sym.replace(".", "").isalpha() and len(sym) <= 6 and sym not in _WATCHLIST:
        _WATCHLIST.append(sym)
    return jsonify({"watchlist": _WATCHLIST})


@app.route("/api/watchlist/remove")
def api_watchlist_remove():
    global _WATCHLIST
    sym = request.args.get("ticker", "").upper().strip()
    if sym in _WATCHLIST and sym != TICKER:
        _WATCHLIST.remove(sym)
    return jsonify({"watchlist": _WATCHLIST})




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
    global _ml_retraining, _ml_ready
    _ml_retraining  = True
    _ml_ready       = False
    _ml_model_cache = None  # clear stale cache so old feature set isn't served during retrain
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
        # SPY daily — Schwab first for accuracy
        try:
            _spy_d, _spy_d_src = _schwab_or_yf("SPY", period_years=2, freq_minutes=1440,
                                                  yf_period="2y", yf_interval="1d")
            spy_daily_closes = _spy_d["Close"].astype(float) if not _spy_d.empty else _pd_rt.Series()
            print(f"[ML-RETRAIN] SPY daily: {len(spy_daily_closes)} bars ({_spy_d_src})", flush=True)
        except Exception: spy_daily_closes = _pd_rt.Series()

        # QQQ daily — Schwab first
        try:
            _qqq_d, _qqq_d_src = _schwab_or_yf("QQQ", period_years=2, freq_minutes=1440,
                                                   yf_period="2y", yf_interval="1d")
            qqq_daily_closes = _qqq_d["Close"].astype(float) if not _qqq_d.empty else _pd_rt.Series()
            print(f"[ML-RETRAIN] QQQ daily: {len(qqq_daily_closes)} bars ({_qqq_d_src})", flush=True)
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
            # Don't trim TSLA to SPY length — pad SPY instead
            # This prevents losing 90% of training data when SPY has fewer bars
            tsla_len = len(closes)
            spy_len  = len(spy_closes)
            if spy_len < tsla_len:
                # Pad SPY with last known value to match TSLA length
                pad = _pd_rt.Series(
                    [float(spy_closes.iloc[-1])] * (tsla_len - spy_len),
                    index=range(spy_len, tsla_len)
                )
                spy_closes = _pd_rt.concat([spy_closes, pad]).reset_index(drop=True)
                print(f"[ML-RETRAIN] SPY padded {spy_len}→{tsla_len} bars", flush=True)
            elif spy_len > tsla_len:
                spy_closes = spy_closes.iloc[:tsla_len]
            idx    = hist5.index[:tsla_len]
            spy_ok = True
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
        # 60 trading days * 78 bars/day = 4680 bars (yfinance 60d 5-min)
        # 2 years * 252 days * 78 bars/day = 39,312 bars (Schwab 2yr 5-min)
        if n >= 4000:
            LOOKBACK = 78   # 5-min bars — 1 trading day lookback
            MIN_START = 200
            FORWARD   = 6   # predict 30min ahead (6x5min bars)
        elif n >= 800:
            LOOKBACK = 7    # 1h bars — 1 trading day lookback
            MIN_START = 50
            FORWARD   = 2   # predict 2h ahead
        else:
            LOOKBACK = 5    # daily bars — 1 week lookback
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

                # Volume Profile POC — rolling 50-bar window
                _poc_dist_r = 0.0; _above_poc_r = 1; _in_va_r = 1
                _above_vah_r = 0; _below_val_r = 0
                try:
                    _w = 50
                    _bc = closes.iloc[max(0,i-_w):i+1]
                    _bv = volumes.iloc[max(0,i-_w):i+1] if len(volumes) > i else _bc * 0
                    if len(_bc) > 10:
                        _bn = {}
                        for _bp2, _bv2 in zip(_bc, _bv):
                            _k2 = round(float(_bp2)/0.5)*0.5
                            _bn[_k2] = _bn.get(_k2, 0) + float(_bv2)
                        if _bn:
                            _poc2 = max(_bn, key=_bn.get)
                            _sb   = sorted(_bn.keys())
                            _tv   = sum(_bn.values()); _tgt = _tv*0.70
                            _ac   = 0; _vlo = _poc2; _vhi = _poc2
                            _li   = _sb.index(_poc2); _hi2 = _li
                            while _ac < _tgt and (_li>0 or _hi2<len(_sb)-1):
                                _lv = _bn.get(_sb[_li-1],0) if _li>0 else 0
                                _hv = _bn.get(_sb[_hi2+1],0) if _hi2<len(_sb)-1 else 0
                                if _lv>=_hv and _li>0: _li-=1; _vlo=_sb[_li]; _ac+=_lv
                                elif _hi2<len(_sb)-1: _hi2+=1; _vhi=_sb[_hi2]; _ac+=_hv
                                else: break
                            _cp = float(price)
                            _poc_dist_r  = (_cp-_poc2)/(_poc2+1e-9)
                            _above_poc_r = 1 if _cp>_poc2 else 0
                            _in_va_r     = 1 if _vlo<=_cp<=_vhi else 0
                            _above_vah_r = 1 if _cp>_vhi else 0
                            _below_val_r = 1 if _cp<_vlo else 0
                except Exception: pass

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
                # Volume Profile POC features (computed per bar)
                _poc_dist_r, _above_poc_r, _in_va_r, _above_vah_r, _below_val_r,
                # MTF proxies (daily values used in training)
                _spy_rsi_r, _spy_rsi_r,
                _spy_ob_r, _spy_os_r,
                _spy_ob_r, _spy_os_r,
                1 if _spy_ob_r and _spy_ob_r else 0,
                1 if _spy_os_r and _spy_os_r else 0,
                _qqq_rsi_r, _qqq_ob_r,
                1 if _spy_ob_r and _qqq_ob_r else 0,
                1 if _spy_os_r and _qqq_os_r else 0,
                ]
                X_rows.append(row)
                future = float(closes.iloc[min(i+FORWARD, n-1)])
                threshold = 1.0005 if FORWARD <= 2 else 1.001
                y_rows.append(1 if future > price*threshold else 0)
            except Exception as _le:
                skipped_errors += 1
                if skipped_errors <= 3: print(f"[ML-RETRAIN] bar {i} err: {_le}", flush=True)
        print(f"[ML-RETRAIN] {len(X_rows)} samples ({skipped_errors} errors), pos_rate={sum(y_rows)/max(len(y_rows),1):.2f}", flush=True)
        min_samples = 500 if FORWARD == 6 else (50 if FORWARD == 1 else 200)
        if len(X_rows) < min_samples:
            print(f"[ML-RETRAIN] Not enough samples ({len(X_rows)} < {min_samples})", flush=True); return

        X  = _pd_rt.DataFrame(X_rows).replace([np.inf,-np.inf],0).fillna(0).values

        # ── Inject corrective labels from self-learning ─────────────────────
        if _ml_corrective_labels:
            import numpy as _np_cl
            n_injected = 0
            for cl in _ml_corrective_labels:
                try:
                    cl_feats = cl.get("features", {})
                    if len(cl_feats) < len(feat_cols) * 0.7:
                        continue
                    cl_row = [float(cl_feats.get(f, 0) or 0) for f in feat_cols]
                    cl_label = int(cl.get("label", 0))
                    for _ in range(3):  # weight 3x — real outcomes
                        X_rows.append(cl_row)
                        y_rows.append(cl_label)
                    n_injected += 1
                except Exception: pass
            if n_injected:
                X = _pd_rt.DataFrame(X_rows).replace([np.inf,-np.inf],0).fillna(0).values
                print(f"[ML-RETRAIN] ✅ Injected {n_injected} corrective labels ({n_injected*3} weighted rows)", flush=True)
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
            # SPY/QQQ market context
            "spy_rsi","spy_ob","spy_os","spy_macd_bull","spy_bb_pct",
            "spy_mom_5d","spy_above_200",
            "qqq_rsi","qqq_ob","qqq_os","qqq_macd_bull","qqq_mom_5d","qqq_bull",
            "market_ob","market_os",
            # Volume Profile / POC
            "poc_dist","above_poc","in_value_area","above_vah","below_val",
            # Multi-timeframe SPY/QQQ (4h + 1h) — NEW
            "spy_rsi_4h","spy_rsi_1h",
            "spy_ob_4h","spy_os_4h","spy_ob_1h","spy_os_1h",
            "spy_mtf_ob","spy_mtf_os",
            "qqq_rsi_4h","qqq_ob_4h",
            "mtf_both_ob","mtf_both_os",
        ]

        assert len(feat_cols)==X.shape[1], f"Mismatch {len(feat_cols)} vs {X.shape[1]}"

        X_df   = _pd_rt.DataFrame(X, columns=feat_cols)
        scaler = StandardScaler()
        # Fit on DataFrame to preserve feature names (avoids sklearn warning)
        X_s    = scaler.fit_transform(X_df)
        X_s_df = _pd_rt.DataFrame(X_s, columns=feat_cols)
        # Verify scaler has feature names
        if hasattr(scaler, 'feature_names_in_') and scaler.feature_names_in_ is None:
            import numpy as _np_sc
            scaler.feature_names_in_ = _np_sc.array(feat_cols)

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
        # Also save to /tmp as session backup (survives Railway restarts within session)
        try:
            import shutil as _sh
            _sh.copy2(pkl_path, f"/tmp/{TICKER.lower()}_model_backup.pkl")
        except Exception: pass

        # Also save regime-specific models by splitting training data
        try:
            _save_regime_models(X_df, y, feat_cols, scaler, models_trained, pkg)
        except Exception as _re: print(f"[ML-RETRAIN] Regime models: {_re}", flush=True)
        _ml_model_cache = pkg
        _ml_load_errors = []
        _ml_ready       = True
        _ml_retraining  = False
        print("[ML-RETRAIN] ✅ Model ready — alerts enabled", flush=True)
        # Remove stale old pkl files so they can't be loaded by mistake
        import os as _os2
        for _old_name in ["tsla_model.pkl", "./tsla_model.pkl"]:
            try:
                if _os2.path.exists(_old_name) and _old_name != pkl_path:
                    _os2.remove(_old_name)
            except Exception: pass
        print(f"[ML-RETRAIN] Saved — {pkg['model_name']} AUC={auc:.3f} on {len(X)} bars, {len(feat_cols)} features.", flush=True)

        # ── Feature importance (LightGBM gives the clearest view) ──
        try:
            lgbm_model = next((m for m in models_trained if "LGB" in type(m).__name__), None)
            if lgbm_model and hasattr(lgbm_model, "feature_importances_"):
                importances = lgbm_model.feature_importances_
                feat_imp = sorted(zip(feat_cols, importances), key=lambda x: -x[1])
                print("[ML-RETRAIN] === TOP 20 FEATURE IMPORTANCE ===", flush=True)
                for fname, imp in feat_imp[:20]:
                    bar = "█" * int(imp / max(importances) * 20)
                    group = ("SPY/QQQ" if any(x in fname for x in ["spy_","qqq_","market_"])
                             else "Greeks" if any(x in fname for x in ["delta","gamma","theta","vega","iv_skew"])
                             else "Options" if any(x in fname for x in ["iv_","pc_","earn"])
                             else "TSLA")
                    print(f"  [{group:7s}] {fname:25s} {imp:6.1f}  {bar}", flush=True)

                # Group importance by category
                spy_qqq_imp = sum(imp for f, imp in feat_imp if any(x in f for x in ["spy_","qqq_","market_"]))
                tsla_imp    = sum(imp for f, imp in feat_imp if not any(x in f for x in ["spy_","qqq_","market_"]))
                total_imp   = spy_qqq_imp + tsla_imp
                print(f"[ML-RETRAIN] SPY/QQQ importance: {spy_qqq_imp/total_imp*100:.1f}%  "
                      f"TSLA-specific: {tsla_imp/total_imp*100:.1f}%", flush=True)

                # Store in pkg for API access
                pkg["feature_importance"] = {f: float(i) for f, i in feat_imp}
                pkg["spy_qqq_importance_pct"] = round(spy_qqq_imp/total_imp*100, 1)
        except Exception as _fie:
            print(f"[ML-RETRAIN] Feature importance error: {_fie}", flush=True)

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
        f"/app/{TICKER.lower()}_model.pkl",
        f"{TICKER.lower()}_model.pkl", f"./{TICKER.lower()}_model.pkl",
        f"/tmp/{TICKER.lower()}_model_backup.pkl",  # session backup
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
    result["ml_ready"]      = _ml_ready
    result["ml_retraining"] = _ml_retraining
    result["learning"] = {
        "total_decisions":    _learning_state["total_decisions"],
        "total_correct":      _learning_state["total_correct"],
        "total_wrong":        _learning_state["total_wrong"],
        "corrections_made":   _learning_state["corrections_made"],
        "corrective_labels":  len(_ml_corrective_labels),
        "thresholds":         _dynamic_thresholds,
        "regime_accuracy":    _learning_state["regime_accuracy"],
    }
    result["master_signal"] = state.get("master_signal", {})
    result["tsla_4h"]        = state.get("tsla_4h", {})
    result["ticker"]          = TICKER  # always include current ticker in state
    result["vwap_bands"]     = state.get("vwap_bands", {})
    # L2 — sanitize large_prints list for JSON
    _l2_raw = state.get("l2_data", {})
    result["l2_data"] = {
        "bid_ask_imb":   _l2_raw.get("bid_ask_imb"),
        "top5_bid_size": _l2_raw.get("top5_bid_size"),
        "top5_ask_size": _l2_raw.get("top5_ask_size"),
        "l2_signal":     _l2_raw.get("l2_signal"),
        "tape_signal":   _l2_raw.get("tape_signal"),
        "sweep_detected":_l2_raw.get("sweep_detected"),
        "large_print_count": len(_l2_raw.get("large_prints", [])),
        "stale":         _l2_raw.get("stale", True),
        "running":       schwab_l2._l2_state.get("running", False) if _L2_AVAILABLE else False,
    }
    result["swing_context"]  = state.get("swing_context", {})
    result["breadth"]        = state.get("breadth", {})
    result["hard_risk"]      = state.get("hard_risk", {})
    result["vix_flip"]       = state.get("vix_flip", {})
    result["signal_weights"] = _signal_accuracy_table
    result["spock_accuracy"] = state.get("spock_accuracy", {})
    result["spock_weights"]  = state.get("spock_weights", {})
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

@app.route("/api/price_ticks")
def api_price_ticks():
    """Recent 1-min price ticks for flash move monitoring."""
    return jsonify({
        "ticks":      _price_history[-10:],
        "flash_move": _check_flash_move(state.get("price", 0)),
    })


@app.route("/api/spock/accuracy")
def api_spock_accuracy():
    """SPOCK self-learning accuracy dashboard."""
    decisions = _spock_decisions[-100:]  # last 100
    measured  = [d for d in decisions if d.get("outcome_1h")]
    return jsonify({
        "accuracy":    _spock_accuracy,
        "weights":     _spock_weights,
        "total_logged": len(_spock_decisions),
        "recent_decisions": [
            {
                "id":         d["id"],
                "time":       datetime.fromtimestamp(d["timestamp"]).strftime("%H:%M"),
                "action":     d["action"],
                "price":      d["price"],
                "score":      d["score"],
                "conviction": d["conviction"],
                "outcome_1h": d.get("outcome_1h"),
                "outcome_4h": d.get("outcome_4h"),
                "pnl_1h":     d.get("pnl_1h"),
                "pnl_4h":     d.get("pnl_4h"),
                "reasons":    d.get("reasons", []),
            }
            for d in reversed(decisions[-20:])
        ],
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



@app.route("/stream")
def stream():
    """Server-Sent Events stream — pushes state to frontend every 5s."""
    def _event_gen():
        import json as _json
        while True:
            try:
                # Always inject ticker + status so frontend never gets undefined
                _base = {**state,
                    "ticker":        TICKER,
                    "wa_enabled":    WA_ENABLED,
                    "wa_phone_tail": GREEN_PHONE[-4:] if GREEN_PHONE else "",
                    "ml_ready":      _ml_ready,
                    "ml_retraining": _ml_retraining,
                }
                # If analysis hasn't run yet, send a loading heartbeat
                # so the frontend knows the server is alive and populates
                # ticker/session even before first full cycle completes
                if not _base.get("last_updated"):
                    _base["_loading"] = True
                payload = _sanitize(_base)
                data = _json.dumps(payload)
                yield f"data: {data}\n\n"
            except Exception as _se:
                yield 'data: {"error":"stream_error"}\n\n'
            time.sleep(5)
    return app.response_class(_event_gen(),
                              mimetype="text/event-stream",
                              headers={"Cache-Control": "no-cache",
                                       "X-Accel-Buffering": "no"})


@app.route("/health")
def health(): return jsonify({"status": "ok"}), 200

@app.route("/api/status")
def api_status():
    """Lightweight status — just price, signal, ticker. Fast to load."""
    ms = state.get("master_signal", {})
    return jsonify({
        "ticker":     TICKER,
        "price":      state.get("price"),
        "signal":     ms.get("action", "—"),
        "score":      ms.get("score", 0),
        "conviction": ms.get("conviction", 0),
        "risk":       ms.get("risk", "—"),
        "updated":    state.get("last_updated"),
        "ml_ready":   _ml_ready,
        "ml_retrain": _ml_retraining,
    })

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
_ml_ready         = False
_ml_retraining    = False
_ml_corrective_labels = []   # injected by self-learning when outcomes are wrong

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
    # IMPORTANT: /app paths come FIRST — retrain saves there and must not be
    # shadowed by the stale tsla_model.pkl bundled in the repo working dir
    _script_dir = os.path.dirname(os.path.abspath(__file__))
    _paths = [
        f"/app/{TICKER.lower()}_model.pkl",
        f"/tmp/{TICKER.lower()}_model_backup.pkl",
        os.path.join(_script_dir, f"{TICKER.lower()}_model.pkl"),
        os.path.join(os.getcwd(), f"{TICKER.lower()}_model.pkl"),
        f"{TICKER.lower()}_model.pkl",
        f"./{TICKER.lower()}_model.pkl",
        "/app/tsla_model.pkl",
        "tsla_model.pkl", "./tsla_model.pkl",
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
            # Only use regime model if it has same feature count as current base model
            base = _ml_model_cache if _ml_model_cache is not None else _load_ml_model()
            if base and len(pkg.get("feature_cols", [])) == len(base.get("feature_cols", [])):
                return pkg, regime
        except Exception:
            pass
    # Fall back to in-memory cache first (most current after retrain)
    if _ml_model_cache is not None:
        return _ml_model_cache, "base"
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
        _is_stale = len(cols) != 84
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
            # Quick intraday — try Schwab 1min first
            try:
                import schwab_client as _sc_q
                if _sc_q.is_configured() and _sc_q.get_client():
                    df = _sc_q.get_price_history(tkr, period_years=0.005, freq_minutes=1)
                    if df is None or df.empty: raise ValueError("empty")
                else: raise ValueError("not configured")
            except Exception:
                df = yf.Ticker(tkr).history(period="1d", interval="1m")
            if df is None or df.empty or len(df) < 5:
                # 5-min chart — use cached Schwab data or yfinance fallback
                _cached = state.get("schwab_hist")
                if _cached is not None and not _cached.empty:
                    df = _cached.tail(78)
                else:
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

DASHBOARD_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>SPOCK — TSLA Intelligence</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Space+Mono:ital,wght@0,400;0,700;1,400&family=Syne:wght@400;600;700;800&display=swap" rel="stylesheet">
<style>
:root {
  --bg:       #080b10;
  --bg2:      #0d1117;
  --bg3:      #121820;
  --border:   #1e2a38;
  --buy:      #00ff88;
  --sell:     #ff3355;
  --hold:     #ffb300;
  --neutral:  #4a6580;
  --text:     #c8d8e8;
  --dim:      #4a6580;
  --accent:   #00c8ff;
  --extreme:  #ff6b00;
}
* { box-sizing: border-box; margin: 0; padding: 0; }
body {
  background: var(--bg);
  color: var(--text);
  font-family: 'Space Mono', monospace;
  min-height: 100vh;
  overflow-x: hidden;
}

/* ── TOP BAR ── */
.topbar {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 14px 28px;
  border-bottom: 1px solid var(--border);
  background: var(--bg2);
}
.topbar-brand {
  font-family: 'Syne', sans-serif;
  font-weight: 800;
  font-size: 18px;
  letter-spacing: 0.08em;
  color: var(--accent);
}
.topbar-price {
  font-size: 22px;
  font-weight: 700;
  color: #fff;
}
.topbar-change { font-size: 13px; margin-left: 8px; }
.topbar-time { font-size: 11px; color: var(--dim); }

/* ── MAIN GRID ── */
.main {
  display: grid;
  grid-template-columns: 420px 1fr;
  grid-template-rows: auto auto;
  gap: 1px;
  background: var(--border);
  min-height: calc(100vh - 53px);
}

/* ── SPOCK PANEL (left) ── */
.spock-panel {
  background: var(--bg2);
  padding: 32px 28px;
  display: flex;
  flex-direction: column;
  gap: 24px;
  grid-row: 1 / 3;
}
.spock-label {
  font-family: 'Syne', sans-serif;
  font-size: 11px;
  letter-spacing: 0.2em;
  color: var(--dim);
  text-transform: uppercase;
}
.spock-action {
  font-family: 'Syne', sans-serif;
  font-size: 64px;
  font-weight: 800;
  line-height: 1;
  transition: color 0.4s;
}
.spock-action.BUY, .spock-action[data-action="STRONG BUY"] { color: var(--buy); }
.spock-action.SELL, .spock-action[data-action="STRONG SELL"] { color: var(--sell); }
.spock-action.HOLD { color: var(--hold); }

.score-row {
  display: flex;
  align-items: center;
  gap: 16px;
}
.score-bar-wrap {
  flex: 1;
  height: 6px;
  background: var(--border);
  border-radius: 3px;
  overflow: hidden;
  position: relative;
}
.score-bar-fill {
  position: absolute;
  top: 0;
  height: 100%;
  border-radius: 3px;
  transition: all 0.5s;
}
.score-num {
  font-size: 28px;
  font-weight: 700;
  min-width: 52px;
  text-align: right;
  color: #fff;
}
.score-label { font-size: 11px; color: var(--dim); }

.conviction-row {
  display: flex;
  justify-content: space-between;
  align-items: center;
}
.conviction-pct {
  font-size: 36px;
  font-weight: 700;
  font-family: 'Syne', sans-serif;
  color: #fff;
}
.conviction-label { font-size: 11px; color: var(--dim); text-align: right; }

.risk-badge {
  display: inline-block;
  padding: 4px 12px;
  border-radius: 2px;
  font-size: 11px;
  font-weight: 700;
  letter-spacing: 0.1em;
}
.risk-LOW    { background: rgba(0,255,136,0.1); color: var(--buy); border: 1px solid var(--buy); }
.risk-MEDIUM { background: rgba(0,200,255,0.1); color: var(--accent); border: 1px solid var(--accent); }
.risk-HIGH   { background: rgba(255,107,0,0.1); color: var(--extreme); border: 1px solid var(--extreme); }
.risk-EXTREME{ background: rgba(255,51,85,0.15); color: var(--sell); border: 1px solid var(--sell); }
.risk-DEFENSIVE { background: rgba(255,179,0,0.1); color: var(--hold); border: 1px solid var(--hold); }

/* ── REASONS ── */
.reasons-list { display: flex; flex-direction: column; gap: 8px; }
.reason-item {
  padding: 10px 14px;
  background: var(--bg3);
  border-left: 2px solid var(--border);
  font-size: 12px;
  color: var(--text);
  border-radius: 0 4px 4px 0;
  line-height: 1.5;
}
.reason-item.bull { border-left-color: var(--buy); }
.reason-item.bear { border-left-color: var(--sell); }

/* ── SIZE / TARGET ROW ── */
.meta-grid {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 12px;
}
.meta-card {
  background: var(--bg3);
  border: 1px solid var(--border);
  border-radius: 6px;
  padding: 14px 16px;
}
.meta-card-label { font-size: 10px; color: var(--dim); letter-spacing: 0.08em; margin-bottom: 6px; }
.meta-card-val { font-size: 18px; font-weight: 700; color: #fff; }
.meta-card-sub { font-size: 11px; color: var(--dim); margin-top: 2px; }

/* ── MACRO ALERT ── */
.macro-alert {
  background: rgba(255,51,85,0.08);
  border: 1px solid var(--sell);
  border-radius: 6px;
  padding: 14px 16px;
  font-size: 12px;
  display: none;
}
.macro-alert.active { display: block; }
.macro-alert-title { color: var(--sell); font-weight: 700; margin-bottom: 4px; }

/* ── RIGHT PANEL ── */
.right-panel {
  background: var(--bg);
  display: flex;
  flex-direction: column;
}

/* ── TABS ── */
.tabs {
  display: flex;
  gap: 0;
  border-bottom: 1px solid var(--border);
  background: var(--bg2);
}
.tab {
  padding: 12px 20px;
  font-size: 11px;
  letter-spacing: 0.08em;
  color: var(--dim);
  cursor: pointer;
  border-bottom: 2px solid transparent;
  transition: all 0.2s;
  text-transform: uppercase;
}
.tab:hover { color: var(--text); }
.tab.active { color: var(--accent); border-bottom-color: var(--accent); }

/* ── TAB CONTENT ── */
.tab-content { display: none; padding: 24px; flex: 1; }
.tab-content.active { display: grid; }

/* Options tab */
#tab-options { grid-template-columns: 1fr 1fr 1fr; gap: 16px; }
/* Market tab */
#tab-market { grid-template-columns: 1fr 1fr; gap: 16px; }
/* Data tab */
#tab-data { grid-template-columns: 1fr 1fr; gap: 16px; }
/* Alerts tab */
#tab-alerts { grid-template-columns: 1fr; gap: 12px; }

.data-card {
  background: var(--bg2);
  border: 1px solid var(--border);
  border-radius: 8px;
  padding: 18px 20px;
}
.data-card h3 {
  font-family: 'Syne', sans-serif;
  font-size: 11px;
  letter-spacing: 0.15em;
  color: var(--dim);
  text-transform: uppercase;
  margin-bottom: 14px;
}
.data-row {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 7px 0;
  border-bottom: 1px solid var(--border);
  font-size: 12px;
}
.data-row:last-child { border-bottom: none; }
.data-row-label { color: var(--dim); }
.data-row-val { color: #fff; font-weight: 700; }
.data-row-val.bull { color: var(--buy); }
.data-row-val.bear { color: var(--sell); }
.data-row-val.warn { color: var(--hold); }
.data-row-val.extreme { color: var(--extreme); }

/* ── UOA WHALES ── */
.whale-list { display: flex; flex-direction: column; gap: 6px; margin-top: 8px; }
.whale-item {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 8px 12px;
  background: var(--bg3);
  border-radius: 4px;
  font-size: 11px;
}
.whale-call { color: var(--buy); font-weight: 700; }
.whale-put  { color: var(--sell); font-weight: 700; }

/* ── ALERT LOG ── */
.alert-item {
  background: var(--bg2);
  border: 1px solid var(--border);
  border-radius: 6px;
  padding: 14px 18px;
  font-size: 12px;
}
.alert-item-header {
  display: flex;
  justify-content: space-between;
  margin-bottom: 6px;
}
.alert-signal { font-weight: 700; }
.alert-signal.BUY  { color: var(--buy); }
.alert-signal.SELL { color: var(--sell); }
.alert-time { color: var(--dim); font-size: 11px; }
.alert-reason { color: var(--dim); }

/* ── VOTE BREAKDOWN ── */
.vote-row {
  display: flex;
  gap: 8px;
  align-items: center;
}
.vote-pill {
  padding: 3px 10px;
  border-radius: 20px;
  font-size: 11px;
  font-weight: 700;
}
.vote-bull { background: rgba(0,255,136,0.15); color: var(--buy); }
.vote-bear { background: rgba(255,51,85,0.15); color: var(--sell); }
.vote-neut { background: rgba(74,101,128,0.2); color: var(--dim); }

/* ── ML RETRAIN BANNER ── */
.qtick {
  padding: 4px 10px;
  background: var(--bg3);
  border: 1px solid var(--border);
  border-radius: 3px;
  font-size: 11px;
  color: var(--dim);
  cursor: pointer;
  transition: all 0.15s;
  white-space: nowrap;
}
.qtick:hover { border-color: var(--accent); color: var(--accent); }
.qtick.active { background: var(--accent); color: #000; border-color: var(--accent); font-weight: 700; }
.wl-item {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px 12px;
  background: var(--bg3);
  border: 1px solid var(--border);
  border-radius: 4px;
  cursor: pointer;
  white-space: nowrap;
  transition: border-color 0.2s;
  font-size: 11px;
}
.wl-item:hover { border-color: var(--accent); }
.wl-item.active-ticker { border-color: var(--accent); background: rgba(0,200,255,0.08); }
.wl-sym { font-weight: 700; color: #fff; }
.wl-price { color: var(--dim); }
.wl-chg { font-size: 10px; }
.wl-score-dot {
  width: 6px; height: 6px;
  border-radius: 50%;
  flex-shrink: 0;
}
.retrain-banner {
  background: rgba(255,179,0,0.08);
  border-bottom: 1px solid var(--hold);
  padding: 8px 28px;
  font-size: 11px;
  color: var(--hold);
  display: none;
  align-items: center;
  gap: 8px;
}
.retrain-banner.active { display: flex; }

/* ── SPOCK accuracy ── */
.accuracy-row {
  display: flex;
  gap: 16px;
}
.acc-item { text-align: center; }
.acc-val { font-size: 22px; font-weight: 700; color: #fff; }
.acc-label { font-size: 10px; color: var(--dim); margin-top: 2px; }

/* ── PULSE ANIMATION for live price ── */
@keyframes pulse { 0%,100%{opacity:1} 50%{opacity:0.5} }
.live-dot {
  width: 7px; height: 7px;
  border-radius: 50%;
  background: var(--buy);
  animation: pulse 2s infinite;
  display: inline-block;
  margin-right: 6px;
}
@keyframes fadeIn { from{opacity:0;transform:translateY(6px)} to{opacity:1;transform:none} }
.fade-in { animation: fadeIn 0.4s ease forwards; }

/* ── SCORE BAR COLOURS ── */
.bar-buy  { background: var(--buy); right: 50%; }
.bar-sell { background: var(--sell); left: 50%; }
.bar-hold { background: var(--hold); left: 50%; }
</style>
</head>
<body>

<!-- ML RETRAIN BANNER -->
<div class="retrain-banner" id="retrainBanner">
  ⚙️ ML model retraining — signals suppressed until complete
</div>

<!-- TOP BAR -->
<div class="topbar">
  <div class="topbar-brand">🖖 SPOCK · <span id="brandTicker">TSLA</span></div>

  <!-- TICKER SEARCH -->
  <div style="display:flex;align-items:center;gap:8px;">
    <div style="position:relative">
      <input id="tickerInput" type="text" placeholder="Symbol..." maxlength="6"
        style="width:90px;padding:6px 10px;background:var(--bg3);border:1px solid var(--border);
               color:#fff;font-family:'Space Mono',monospace;font-size:13px;border-radius:4px;
               text-transform:uppercase;outline:none;"
        onkeydown="if(event.key==='Enter')switchTicker(this.value)"
        oninput="this.value=this.value.toUpperCase()">
    </div>
    <button onclick="switchTicker(document.getElementById('tickerInput').value)"
      style="padding:6px 12px;background:var(--accent);color:#000;border:none;
             font-family:'Space Mono',monospace;font-size:11px;font-weight:700;
             border-radius:4px;cursor:pointer;">GO</button>
  </div>

  <!-- QUICK TICKERS -->
  <div style="display:flex;gap:6px;flex-wrap:wrap;" id="quickTickers">
    <span class="qtick active" onclick="switchTicker('TSLA')">TSLA</span>
    <span class="qtick" onclick="switchTicker('NVDA')">NVDA</span>
    <span class="qtick" onclick="switchTicker('AAPL')">AAPL</span>
    <span class="qtick" onclick="switchTicker('AMZN')">AMZN</span>
    <span class="qtick" onclick="switchTicker('META')">META</span>
    <span class="qtick" onclick="switchTicker('MSFT')">MSFT</span>
    <span class="qtick" onclick="switchTicker('SPY')">SPY</span>
  </div>

  <!-- PRICE -->
  <div style="display:flex;align-items:center;gap:16px;">
    <div>
      <span class="live-dot"></span>
      <span style="font-size:11px;color:var(--dim);margin-right:4px;" id="topTicker">TSLA</span>
      <span class="topbar-price" id="topPrice">—</span>
      <span class="topbar-change" id="topChange">—</span>
    </div>
    <div style="text-align:right">
      <div class="topbar-time" id="topTime">—</div>
      <div class="topbar-time" id="topSession">—</div>
    </div>
  </div>
</div>

<!-- WATCHLIST BAR -->
<div id="watchlistBar" style="background:var(--bg2);border-bottom:1px solid var(--border);
     padding:8px 28px;display:flex;gap:16px;overflow-x:auto;align-items:center;">
  <span style="font-size:10px;color:var(--dim);letter-spacing:0.1em;white-space:nowrap;">WATCHLIST</span>
  <div id="watchlistItems" style="display:flex;gap:12px;"></div>
</div>

<!-- MAIN -->
<div class="main">

  <!-- ══ LEFT: SPOCK BRAIN ══ -->
  <div class="spock-panel">
    <div>
      <div class="spock-label">SPOCK DECISION</div>
      <div class="spock-action" id="spockAction">—</div>
    </div>

    <!-- Score bar -->
    <div>
      <div class="spock-label" style="margin-bottom:8px">SCORE</div>
      <div class="score-row">
        <div class="score-bar-wrap">
          <!-- center line -->
          <div style="position:absolute;left:50%;top:0;width:1px;height:100%;background:var(--border);z-index:1"></div>
          <div class="score-bar-fill" id="scoreBarFill"></div>
        </div>
        <div>
          <div class="score-num" id="scoreNum">—</div>
          <div class="score-label">/ 100</div>
        </div>
      </div>
    </div>

    <!-- Conviction + Risk -->
    <div class="conviction-row">
      <div>
        <div class="spock-label">CONVICTION</div>
        <div class="conviction-pct" id="convPct">—</div>
      </div>
      <div style="text-align:right">
        <div class="spock-label">RISK</div>
        <div style="margin-top:6px">
          <span class="risk-badge" id="riskBadge">—</span>
        </div>
      </div>
    </div>

    <!-- Vote breakdown -->
    <div>
      <div class="spock-label" style="margin-bottom:8px">MODEL VOTES</div>
      <div class="vote-row" id="voteRow">
        <span class="vote-pill vote-bull" id="voteBull">— BULL</span>
        <span class="vote-pill vote-bear" id="voteBear">— BEAR</span>
        <span class="vote-pill vote-neut" id="voteNeut">— NEUTRAL</span>
      </div>
    </div>

    <!-- Reasons -->
    <div>
      <div class="spock-label" style="margin-bottom:10px">WHY</div>
      <div class="reasons-list" id="reasonsList">
        <div class="reason-item" style="color:var(--dim)">
          Analysis running — data loads every 5 minutes.<br>
          If blank after 60s, check Railway logs for errors.
        </div>
      </div>
    </div>

    <!-- Meta: size + target -->
    <div class="meta-grid">
      <div class="meta-card">
        <div class="meta-card-label">POSITION SIZE</div>
        <div class="meta-card-val" id="ctaSize">—</div>
        <div class="meta-card-sub" id="ctaShares">—</div>
      </div>
      <div class="meta-card">
        <div class="meta-card-label">MAX PAIN TARGET</div>
        <div class="meta-card-val" id="maxPain">—</div>
        <div class="meta-card-sub" id="gexVal">GEX —</div>
      </div>
      <div class="meta-card">
        <div class="meta-card-label">VWAP</div>
        <div class="meta-card-val" id="vwapVal">—</div>
        <div class="meta-card-sub" id="vwapSig">—</div>
      </div>
      <div class="meta-card">
        <div class="meta-card-label">SPOCK ACCURACY</div>
        <div class="meta-card-val" id="accVal">—</div>
        <div class="meta-card-sub" id="accSub">1h win rate</div>
      </div>
    </div>

    <!-- Macro alert -->
    <div class="macro-alert" id="macroAlert">
      <div class="macro-alert-title" id="macroAlertTitle">—</div>
      <div id="macroAlertBody">—</div>
    </div>

    <!-- Earnings warning -->
    <div class="macro-alert" id="earnWarn" style="border-color:var(--hold)">
      <div class="macro-alert-title" style="color:var(--hold)" id="earnWarnText">—</div>
    </div>
  </div>

  <!-- ══ RIGHT: TABS ══ -->
  <div class="right-panel">
    <div class="tabs">
      <div class="tab active" onclick="switchTab('options')">Options</div>
      <div class="tab" onclick="switchTab('market')">Market</div>
      <div class="tab" onclick="switchTab('data')">Data</div>
      <div class="tab" onclick="switchTab('alerts')">Alerts</div>
    </div>

    <!-- OPTIONS TAB -->
    <div class="tab-content active" id="tab-options">
      <div class="data-card">
        <h3>Market Maker</h3>
        <div class="data-row"><span class="data-row-label">GEX</span><span class="data-row-val" id="mm-gex">—</span></div>
        <div class="data-row"><span class="data-row-label">Max Pain</span><span class="data-row-val" id="mm-mp">—</span></div>
        <div class="data-row"><span class="data-row-label">P/C Ratio</span><span class="data-row-val" id="mm-pc">—</span></div>
        <div class="data-row"><span class="data-row-label">IV Rank</span><span class="data-row-val" id="mm-ivr">—</span></div>
        <div class="data-row"><span class="data-row-label">Hedging</span><span class="data-row-val" id="mm-hedge">—</span></div>
      </div>
      <div class="data-card">
        <h3>Unusual Options Activity</h3>
        <div class="data-row"><span class="data-row-label">Net Flow</span><span class="data-row-val" id="uoa-flow">—</span></div>
        <div class="data-row"><span class="data-row-label">Whale Trades</span><span class="data-row-val" id="uoa-whales">—</span></div>
        <div class="data-row"><span class="data-row-label">Unusual Count</span><span class="data-row-val" id="uoa-unusual">—</span></div>
        <div class="data-row"><span class="data-row-label">Call Premium</span><span class="data-row-val bull" id="uoa-calls">—</span></div>
        <div class="data-row"><span class="data-row-label">Put Premium</span><span class="data-row-val bear" id="uoa-puts">—</span></div>
      </div>
      <div class="data-card">
        <h3>Earnings</h3>
        <div class="data-row"><span class="data-row-label">Next Earnings</span><span class="data-row-val warn" id="earn-next">—</span></div>
        <div class="data-row"><span class="data-row-label">Days Away</span><span class="data-row-val" id="earn-days">—</span></div>
        <div class="data-row"><span class="data-row-label">Mode Active</span><span class="data-row-val" id="earn-mode">—</span></div>
        <div class="data-row"><span class="data-row-label">Size Reduction</span><span class="data-row-val warn" id="earn-size">—</span></div>
      </div>
    </div>

    <!-- MARKET TAB -->
    <div class="tab-content" id="tab-market">
      <div class="data-card">
        <h3>SPY / Market</h3>
        <div class="data-row"><span class="data-row-label">SPY Price</span><span class="data-row-val" id="spy-price">—</span></div>
        <div class="data-row"><span class="data-row-label">SPY RSI Daily</span><span class="data-row-val" id="spy-rsi-d">—</span></div>
        <div class="data-row"><span class="data-row-label">SPY RSI 4h</span><span class="data-row-val" id="spy-rsi-4h">—</span></div>
        <div class="data-row"><span class="data-row-label">VIX</span><span class="data-row-val" id="vix-val">—</span></div>
        <div class="data-row"><span class="data-row-label">VIX Regime</span><span class="data-row-val" id="vix-regime">—</span></div>
        <div class="data-row"><span class="data-row-label">Macro Signal</span><span class="data-row-val" id="macro-sig">—</span></div>
        <div class="data-row"><span class="data-row-label">MTF Overbought</span><span class="data-row-val" id="spy-mtf">—</span></div>
      </div>
      <div class="data-card">
        <h3>QQQ / Tech</h3>
        <div class="data-row"><span class="data-row-label">QQQ RSI Daily</span><span class="data-row-val" id="qqq-rsi-d">—</span></div>
        <div class="data-row"><span class="data-row-label">QQQ RSI 4h</span><span class="data-row-val" id="qqq-rsi-4h">—</span></div>
        <div class="data-row"><span class="data-row-label">VIX Term Spread</span><span class="data-row-val" id="vix-spread">—</span></div>
        <div class="data-row"><span class="data-row-label">Breadth Signal</span><span class="data-row-val" id="breadth-sig">—</span></div>
        <div class="data-row"><span class="data-row-label">VIX Flip</span><span class="data-row-val" id="vix-flip">—</span></div>
        <div class="data-row"><span class="data-row-label">Beta vs SPY</span><span class="data-row-val" id="beta-val">—</span></div>
      </div>
    </div>

    <!-- DATA TAB -->
    <div class="tab-content" id="tab-data">
      <div class="data-card">
        <h3>Volume Profile</h3>
        <div class="data-row"><span class="data-row-label">POC</span><span class="data-row-val" id="poc-val">—</span></div>
        <div class="data-row"><span class="data-row-label">VAH</span><span class="data-row-val" id="vah-val">—</span></div>
        <div class="data-row"><span class="data-row-label">VAL</span><span class="data-row-val" id="val-val">—</span></div>
        <div class="data-row"><span class="data-row-label">Price vs POC</span><span class="data-row-val" id="poc-dist">—</span></div>
        <div class="data-row"><span class="data-row-label">In Value Area</span><span class="data-row-val" id="in-va">—</span></div>
      </div>
      <div class="data-card">
        <h3>VWAP + Price Structure</h3>
        <div class="data-row"><span class="data-row-label">VWAP</span><span class="data-row-val" id="vwap-v">—</span></div>
        <div class="data-row"><span class="data-row-label">VWAP +1σ</span><span class="data-row-val" id="vwap-u1">—</span></div>
        <div class="data-row"><span class="data-row-label">VWAP -1σ</span><span class="data-row-val" id="vwap-l1">—</span></div>
        <div class="data-row"><span class="data-row-label">VWAP Signal</span><span class="data-row-val" id="vwap-sig">—</span></div>
        <div class="data-row"><span class="data-row-label">Anchored VWAP</span><span class="data-row-val" id="anc-vwap">—</span></div>
        <div class="data-row"><span class="data-row-label">TSLA 4h RSI</span><span class="data-row-val" id="tsla-4h-rsi">—</span></div>
        <div class="data-row"><span class="data-row-label">TSLA 4h Trend</span><span class="data-row-val" id="tsla-4h-trend">—</span></div>
        <div class="data-row"><span class="data-row-label">Daily Pattern</span><span class="data-row-val" id="swing-pattern">—</span></div>
      </div>
    </div>

    <!-- ALERTS TAB -->
    <div class="tab-content" id="tab-alerts">
      <div id="alertsList" style="display:flex;flex-direction:column;gap:10px;">
        <div class="alert-item" style="color:var(--dim)">No alerts yet.</div>
      </div>
    </div>
  </div>
</div>

<script>
// ── Tab switching ──
function switchTab(name) {
  document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
  document.querySelectorAll('.tab-content').forEach(c => c.classList.remove('active'));
  event.target.classList.add('active');
  document.getElementById('tab-' + name).classList.add('active');
}

// ── Helpers ──
function setText(id, val, cls) {
  var el = document.getElementById(id);
  if (!el) return;
  el.textContent = val ?? '—';
  if (cls) { el.className = 'data-row-val ' + cls; }
}
function rsiClass(v) {
  if (!v) return '';
  if (v > 75) return 'extreme';
  if (v > 65) return 'warn';
  if (v < 35) return 'bull';
  return '';
}
function fmt(v, decimals=2) {
  if (v == null || v === '') return '—';
  return parseFloat(v).toFixed(decimals);
}

// ── Main update ──
function updateUI(s) {
  if (!s) return;
  // Global safety net — catch any crash and log it
  try { _updateUI_inner(s); } catch(e) { console.error('[SPOCK] updateUI crash:', e, e.stack); }
}
function _updateUI_inner(s) {
  if (!s) return;

  // Debug: log first response to help diagnose loading issues
  if (!window._firstLoad) {
    window._firstLoad = true;
    console.log('[SPOCK] First state received:', {
      ticker: s.ticker, price: s.price,
      signal: s.master_signal?.action,
      updated: s.last_updated,
      loading: s._loading,
      keys: Object.keys(s).length + ' keys'
    });
  }

  // If analysis hasn't run yet, show spinner in SPOCK panel and return
  // (ticker button + top bar still update so the UI feels alive)
  if (s._loading && !s.last_updated) {
    var tEl = document.getElementById('topTicker');
    if (tEl && s.ticker) { tEl.textContent = s.ticker; _currentTicker = s.ticker; }
    var bt = document.getElementById('brandTicker'); if(bt && s.ticker) bt.textContent = s.ticker;
    var aEl = document.getElementById('spockAction');
    if (aEl) { aEl.textContent = 'LOADING…'; aEl.style.color = 'var(--dim)'; }
    document.querySelectorAll('.qtick').forEach(function(el) {
      el.classList.toggle('active', el.textContent === s.ticker);
    });
    var banner = document.getElementById('retrainBanner');
    if (s.ml_retraining && banner) banner.classList.add('active');
    return;
  }

  // Top bar — show loading state if no price yet
  var price = s.price || 0;
  var priceEl = document.getElementById('topPrice');
  if (price) {
    priceEl.textContent = '$' + parseFloat(price).toFixed(2);
    priceEl.style.color = '#fff';
  } else {
    priceEl.textContent = 'Loading...';
    priceEl.style.color = 'var(--dim)';
  }
  var tickerEl = document.getElementById('topTicker');
  if (tickerEl && s.ticker) {
    tickerEl.textContent = s.ticker;
  var bt = document.getElementById('brandTicker'); if(bt && s.ticker) bt.textContent = s.ticker;
    _currentTicker = s.ticker;
    // Sync quick ticker buttons
    document.querySelectorAll('.qtick').forEach(function(el) {
      el.classList.toggle('active', el.textContent === s.ticker);
    });
  }
  var chg = s.price_change_pct;
  if (chg != null) {
    var chgEl = document.getElementById('topChange');
    chgEl.textContent = (chg >= 0 ? '+' : '') + parseFloat(chg).toFixed(2) + '%';
    chgEl.style.color = chg >= 0 ? 'var(--buy)' : 'var(--sell)';
  }
  document.getElementById('topTime').textContent = s.last_updated || '—';
  document.getElementById('topSession').textContent = s.session_type || '';

  // ML retrain banner
  var banner = document.getElementById('retrainBanner');
  if (s.ml_retraining) banner.classList.add('active');
  else banner.classList.remove('active');

  // ── SPOCK ──
  var ms = s.master_signal || {};
  var action = ms.action || 'HOLD';
  var score  = ms.score  || 0;
  var conv   = ms.conviction || 0;
  var risk   = ms.risk || 'MEDIUM';

  var actionEl = document.getElementById('spockAction');
  // Show loading if analysis hasn't run yet
  if (!s.last_updated && !action) {
    actionEl.textContent = 'LOADING';
    actionEl.style.color = 'var(--dim)';
    // Don't return — keep rendering other available data
  }
  actionEl.textContent = action || '—';
  actionEl.className   = 'spock-action fade-in';
  var baseAction = action.replace('STRONG ','').replace(' — LOW CONVICTION','');
  actionEl.classList.add(baseAction);
  actionEl.setAttribute('data-action', action);

  // Score bar
  var scoreNum = document.getElementById('scoreNum');
  scoreNum.textContent = (score >= 0 ? '+' : '') + score;
  var fill = document.getElementById('scoreBarFill');
  var pct  = Math.abs(score) / 2; // score -100..100 → 0..50% of bar from center
  fill.style.width = pct + '%';
  fill.className = 'score-bar-fill ' +
    (score > 10 ? 'bar-buy' : score < -10 ? 'bar-sell' : 'bar-hold');

  // Conviction
  document.getElementById('convPct').textContent = conv + '%';

  // Risk badge
  var rb = document.getElementById('riskBadge');
  rb.textContent = risk;
  rb.className = 'risk-badge risk-' + risk.replace(' ','_');

  // Votes
  setText('voteBull', (ms.bull_votes || 0) + ' BULL');
  setText('voteBear', (ms.bear_votes || 0) + ' BEAR');
  setText('voteNeut', (ms.neutral_votes || 0) + ' NEUTRAL');

  // Reasons
  var reasons = ms.reasons || [];
  var rl = document.getElementById('reasonsList');
  if (reasons.length) {
    rl.innerHTML = reasons.slice(0,4).map(function(r) {
      var cls = r.toLowerCase().indexOf('buy') >= 0 || r.indexOf('↑') >= 0 ? 'bull' :
                r.toLowerCase().indexOf('sell') >= 0 || r.indexOf('↓') >= 0 ? 'bear' : '';
      return '<div class="reason-item ' + cls + '">' + r + '</div>';
    }).join('');
  }

  // CTA size
  var sz = s.sizing || {};
  setText('ctaSize', sz.final_exposure ? '$' + Math.round(sz.final_exposure).toLocaleString() : '—');
  setText('ctaShares', sz.share_count ? sz.share_count + ' shares · ' + (sz.sizing_signal || '') : '—');

  // Max Pain + GEX
  var mm = s.mm_data || {};
  setText('maxPain', mm.max_pain ? '$' + mm.max_pain : '—');
  var gex = mm.gex_total;
  setText('gexVal', gex != null ? 'GEX ' + (gex >= 0 ? '+' : '') + Math.round(gex) + 'M' : 'GEX —');
  try { document.getElementById('gexVal').style.color = gex > 0 ? 'var(--buy)' : gex < 0 ? 'var(--sell)' : 'var(--dim)'; } catch(_){}

  // VWAP
  var vb = s.vwap_bands || {};
  setText('vwapVal', vb.vwap ? '$' + vb.vwap : '—');
  setText('vwapSig', vb.vwap_signal || '—');
  try { document.getElementById('vwapSig').style.color =
    (vb.vwap_signal||'').includes('ABOVE') ? 'var(--buy)' : 'var(--sell)'; } catch(_){}

  // SPOCK accuracy
  var acc = s.spock_accuracy || {};
  var wr1h = acc.win_rate_1h;
  setText('accVal', wr1h != null ? wr1h + '%' : '—');
  setText('accSub', '1h · n=' + (acc.decisive_1h || acc.total || 0));

  // Macro / VIX flip alert
  var flip = s.vix_flip || {};
  var macroEl = document.getElementById('macroAlert');
  if (flip.flip === 'FEAR_TO_RELIEF') {
    macroEl.classList.add('active');
    document.getElementById('macroAlertTitle').textContent = '🚨 VIX REGIME FLIP — MACRO BUY';
    document.getElementById('macroAlertBody').textContent =
      'VIX ' + flip.vix_prev + ' → ' + flip.vix_today + ' (' + flip.vix_change_pct + '%) · Fear-to-relief · High-beta surge likely';
  } else if (flip.flip === 'PANIC_SPIKE') {
    macroEl.classList.add('active');
    macroEl.style.borderColor = 'var(--sell)';
    document.getElementById('macroAlertTitle').textContent = '🚨 VIX PANIC SPIKE — EXIT LONGS';
    document.getElementById('macroAlertBody').textContent =
      'VIX ' + flip.vix_prev + ' → ' + flip.vix_today + ' (' + flip.vix_change_pct + '%)';
  } else {
    macroEl.classList.remove('active');
  }

  // Earnings warning
  var earn = s.earnings_context || {};
  var ew = document.getElementById('earnWarn');
  if (earn.earnings_mode) {
    ew.classList.add('active');
    document.getElementById('earnWarnText').textContent =
      '⚠️ EARNINGS IN ' + (earn.days_away || '?') + ' DAYS — size reduced';
  } else {
    ew.classList.remove('active');
  }

  // ══ TABS ══

  // Options tab
  setText('mm-gex', gex != null ? (gex >= 0 ? '+' : '') + Math.round(gex) + 'M' : '—',
    gex > 100 ? 'bull' : gex < -100 ? 'bear' : '');
  setText('mm-mp', mm.max_pain ? '$' + mm.max_pain : '—');
  setText('mm-pc', mm.pc_ratio ? parseFloat(mm.pc_ratio).toFixed(3) : '—');
  setText('mm-ivr', mm.iv_rank != null ? mm.iv_rank + '%' : '—');
  setText('mm-hedge', mm.hedging_pressure || '—');

  var uoa = s.uoa_data || {};
  var flow = (uoa.net_flow || '').includes('BULL') ? 'bull' : (uoa.net_flow||'').includes('BEAR') ? 'bear' : '';
  setText('uoa-flow', uoa.net_flow || '—', flow);
  var _wc = uoa.whale_alerts ? uoa.whale_alerts.length : (uoa.whale_count || 0);
  setText('uoa-whales', _wc ? _wc + ' trades' : '—');
  setText('uoa-unusual', uoa.total_unusual != null ? uoa.total_unusual : (uoa.unusual_count != null ? uoa.unusual_count : '—'));
  var _cp = uoa.total_call_premium || uoa.call_premium || 0;
  setText('uoa-calls', _cp ? '$' + (_cp/1e6).toFixed(1) + 'M calls' : '—', 'bull');
  var _pp = uoa.total_put_premium || uoa.put_premium || 0;
  setText('uoa-puts', _pp ? '$' + (_pp/1e6).toFixed(1) + 'M puts' : '—', 'bear');

  setText('earn-next', earn.next_earnings || earn.next_date || '—');
  setText('earn-days', earn.days_away != null ? earn.days_away + ' days' : '—',
    earn.days_away <= 7 ? 'warn' : '');
  setText('earn-mode', earn.earnings_mode ? 'YES ⚠️' : 'No', earn.earnings_mode ? 'warn' : '');
  setText('earn-size', earn.earnings_mode ?
    (earn.days_away <= 3 ? 'Max 40%' : 'Max 60%') : 'Normal', 'warn');

  // Market tab
  var spy = s.spy_data || {};
  setText('spy-price', spy.spy_price ? '$' + parseFloat(spy.spy_price).toFixed(2) : '—');
  setText('spy-rsi-d', spy.spy_rsi ? fmt(spy.spy_rsi, 1) : '—', rsiClass(spy.spy_rsi));
  setText('spy-rsi-4h', spy.spy_rsi_4h ? fmt(spy.spy_rsi_4h, 1) : '—', rsiClass(spy.spy_rsi_4h));
  setText('vix-val', spy.vix ? fmt(spy.vix, 2) : '—',
    spy.vix > 30 ? 'extreme' : spy.vix > 20 ? 'warn' : 'bull');
  setText('vix-regime', spy.vix_regime || '—');
  setText('macro-sig', spy.macro_signal || '—',
    (spy.macro_signal||'').includes('BULL') || (spy.macro_signal||'').includes('TAIL') ? 'bull' :
    (spy.macro_signal||'').includes('BEAR') || (spy.macro_signal||'').includes('HEAD') ? 'bear' : '');
  setText('spy-mtf', spy.mtf_both_ob ? '⚠️ YES — overbought' : 'No', spy.mtf_both_ob ? 'extreme' : 'bull');

  var breadth = s.breadth || {};
  setText('qqq-rsi-d', spy.qqq_rsi ? fmt(spy.qqq_rsi, 1) : '—', rsiClass(spy.qqq_rsi));
  setText('qqq-rsi-4h', spy.qqq_rsi_4h ? fmt(spy.qqq_rsi_4h, 1) : '—', rsiClass(spy.qqq_rsi_4h));
  setText('vix-spread', breadth.term_spread != null ? (breadth.term_spread >= 0 ? '+' : '') + breadth.term_spread : '—',
    breadth.vix_backw ? 'extreme' : '');
  setText('breadth-sig', breadth.breadth_signal || '—',
    breadth.breadth_signal === 'PANIC' ? 'extreme' : breadth.breadth_signal === 'COMPLACENT' ? 'warn' : '');
  var flipSig = flip.flip || '';
  setText('vix-flip', flipSig || 'None',
    flipSig === 'FEAR_TO_RELIEF' ? 'bull' : flipSig === 'PANIC_SPIKE' ? 'bear' : '');
  setText('beta-val', spy.beta_20d ? fmt(spy.beta_20d, 2) + 'x' : '—');

  // Data tab
  var poc = s.poc_data || {};
  setText('poc-val', poc.poc ? '$' + poc.poc : '—');
  setText('vah-val', poc.vah ? '$' + poc.vah : '—');
  setText('val-val', poc.val ? '$' + poc.val : '—',
    price && poc.val && price <= poc.val * 1.02 ? 'extreme' : '');
  setText('poc-dist', poc.price_vs_poc != null ?
    (poc.price_vs_poc >= 0 ? '+' : '') + fmt(poc.price_vs_poc, 1) + '%' : '—',
    poc.above_poc ? 'bull' : 'bear');
  setText('in-va', poc.in_va ? 'Yes' : 'No', poc.in_va ? 'bull' : 'warn');

  setText('vwap-v',  vb.vwap   ? '$' + vb.vwap   : '—');
  setText('vwap-u1', vb.upper1 ? '$' + vb.upper1 : '—');
  setText('vwap-l1', vb.lower1 ? '$' + vb.lower1 : '—');
  setText('vwap-sig', vb.vwap_signal || '—',
    (vb.vwap_signal||'').includes('ABOVE') ? 'bull' : 'bear');
  setText('anc-vwap', vb.anchored_vwap ?
    '$' + vb.anchored_vwap + (vb.anchored_above ? ' ↑ above' : ' ↓ below') : '—',
    vb.anchored_above ? 'bull' : 'bear');

  var t4h = s.tsla_4h || {};
  setText('tsla-4h-rsi', t4h.rsi_4h ? fmt(t4h.rsi_4h, 1) : '—', rsiClass(t4h.rsi_4h));
  setText('tsla-4h-trend', t4h.trend_4h || '—',
    (t4h.trend_4h||'').includes('BULL') ? 'bull' :
    (t4h.trend_4h||'').includes('BEAR') ? 'bear' : '');

  var sw = s.swing_context || {};
  setText('swing-pattern', sw.daily_pattern || 'None',
    sw.pattern_signal === 'BUY' ? 'bull' : sw.pattern_signal === 'SELL' ? 'bear' : '');

  // Alerts tab
  var alerts = s.alerts_log || [];
  var al = document.getElementById('alertsList');
  if (alerts.length) {
    al.innerHTML = alerts.slice(0,20).map(function(a) {
      return '<div class="alert-item fade-in">' +
        '<div class="alert-item-header">' +
          '<span class="alert-signal ' + (a.signal||'') + '">' + (a.signal||'?') + ' @ $' + (a.price||'?') + '</span>' +
          '<span class="alert-time">' + (a.time||'') + '</span>' +
        '</div>' +
        '<div class="alert-reason">' + (a.reason||'') + '</div>' +
      '</div>';
    }).join('');
  }
}

// ── Ticker switching ──
var _currentTicker = 'TSLA';

async function switchTicker(sym) {
  sym = (sym || '').trim().toUpperCase();
  if (!sym || sym.length > 6) return;
  if (sym === _currentTicker) return;

  // Visual feedback
  document.getElementById('topTicker').textContent = sym;
  document.getElementById('topPrice').textContent = '...';
  document.getElementById('spockAction').textContent = '—';
  document.getElementById('scoreNum').textContent = '—';

  // Update active quick button
  document.querySelectorAll('.qtick').forEach(function(el) {
    el.classList.toggle('active', el.textContent === sym);
  });

  try {
    var r = await fetch('/api/switch_ticker?ticker=' + sym);
    var d = await r.json();
    _currentTicker = sym;
    document.getElementById('tickerInput').value = '';
    // Fetch new state immediately
    setTimeout(fetchState, 500);
    setTimeout(fetchState, 2000);
  } catch(e) {
    console.error('Switch failed:', e);
  }
}

// ── Watchlist update ──
async function refreshWatchlist() {
  try {
    var r = await fetch('/api/watchlist');
    var d = await r.json();
    var container = document.getElementById('watchlistItems');
    if (!container) return;
    var scores = d.scores || {};
    var wl = d.watchlist || [];
    var current = d.current || _currentTicker;
    container.innerHTML = wl.map(function(sym) {
      var sc = scores[sym] || {};
      var chg = sc.change || 0;
      var chgStr = (chg >= 0 ? '+' : '') + (chg || 0).toFixed(2) + '%';
      var chgColor = chg >= 0 ? 'var(--buy)' : 'var(--sell)';
      var dotColor = sc.score > 20 ? 'var(--buy)' : sc.score < -20 ? 'var(--sell)' : 'var(--hold)';
      var isCurrent = sym === current;
      return '<div class="wl-item' + (isCurrent ? ' active-ticker' : '') + '" onclick="switchTicker(\'' + sym + '\')">' +
        '<div class="wl-score-dot" style="background:' + dotColor + '"></div>' +
        '<span class="wl-sym">' + sym + '</span>' +
        '<span class="wl-price">' + (sc.price ? '$' + sc.price : '—') + '</span>' +
        '<span class="wl-chg" style="color:' + chgColor + '">' + chgStr + '</span>' +
        (sc.rsi ? '<span style="color:var(--dim);font-size:10px">RSI ' + sc.rsi + '</span>' : '') +
        '</div>';
    }).join('');
  } catch(e) {}
}

// ── Fetch state ──
async function fetchState() {
  try {
    var r = await fetch('/api/state');
    if (!r.ok) {
      console.warn('fetchState HTTP ' + r.status);
      return;
    }
    var d = await r.json();
    if (d && typeof d === 'object') {
      // Debug: log what we received
      if (!window._gotData && d.last_updated) {
        window._gotData = true;
        console.log('[SPOCK] Full state received:', {
          ticker: d.ticker, price: d.price, updated: d.last_updated,
          action: d.master_signal && d.master_signal.action,
          score:  d.master_signal && d.master_signal.score,
          keys: Object.keys(d).length
        });
      }
      updateUI(d);
    }
  } catch(e) {
    console.error('[SPOCK] fetchState error:', e);
  }
}

// ── SSE stream ──
try {
  var _sse = new EventSource('/stream');
  _sse.onmessage = function(e) {
    try {
      var d = JSON.parse(e.data);
      if (d && typeof d === 'object' && !d.error) updateUI(d);
    } catch(_) {}
  };
  _sse.onerror = function() { _sse.close(); };
} catch(_) {}

// ── Clock ──
function updateClock() {
  // already shown via topTime from state
}

// Immediate load
fetchState();
setInterval(fetchState, 5000);
// Watchlist — refresh every 30s
refreshWatchlist();
setInterval(refreshWatchlist, 30000);
</script>
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
    threading.Thread(target=_scan_watchlist, daemon=True).start()
    print("[SCHEDULER] Watchlist scanner started", flush=True)
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
def _scan_watchlist():
    """Background: get quick RSI/score for each watchlist ticker every 5 min."""
    import time as _t
    _t.sleep(30)  # give main analysis time to start first
    while True:
        try:
            for sym in list(_WATCHLIST):
                if sym == TICKER:
                    continue
                try:
                    q = sc.get_quote(sym) if sc.is_configured() else {}
                    price = float(q.get("price", 0) or 0)
                    chg   = float(q.get("change_pct", 0) or 0)
                    if price <= 0:
                        import yfinance as _yfw
                        _fi = _yfw.Ticker(sym).fast_info
                        price = float(getattr(_fi, "last_price", 0) or 0)
                        prev  = float(getattr(_fi, "previous_close", price) or price)
                        chg   = round((price - prev) / max(prev, 1) * 100, 2)
                    _rsi = 50; _wl_score = 0; _wl_action = "HOLD"
                    try:
                        import yfinance as _yfw2
                        _h = _yfw2.Ticker(sym).history(period="30d", interval="1d")
                        if not _h.empty and len(_h) >= 14:
                            _c = _h["Close"].astype(float)
                            _d = _c.diff()
                            _g = _d.where(_d > 0, 0).rolling(14).mean()
                            _l = -_d.where(_d < 0, 0).rolling(14).mean()
                            _rsi = round(float((100 - 100 / (1 + _g / (_l + 1e-9))).iloc[-1]), 1)
                            _ret5 = round((_c.iloc[-1] / _c.iloc[-5] - 1) * 100, 2) if len(_c) >= 5 else 0
                            if _rsi < 35:   _wl_score = -40; _wl_action = "OVERSOLD"
                            elif _rsi < 45: _wl_score = -15; _wl_action = "WEAK"
                            elif _rsi > 75: _wl_score = +40; _wl_action = "OVERBOUGHT"
                            elif _rsi > 60: _wl_score = +15; _wl_action = "STRONG"
                    except Exception: pass
                    _WATCHLIST_SCORES[sym] = {
                        "price": round(price, 2), "change": round(chg, 2),
                        "rsi": _rsi, "score": _wl_score, "action": _wl_action,
                        "updated": _t.strftime("%H:%M"),
                    }
                except Exception: pass
        except Exception: pass
        _t.sleep(300)


def start_background_threads():
    time.sleep(3)  # short wait for gunicorn to bind port
    print("[STARTUP] Starting background monitor threads...", flush=True)
    # Start Level 2 streaming
    if _L2_AVAILABLE and sc.is_configured():
        try:
            schwab_l2.start_l2_stream(TICKER)
        except Exception as _l2e:
            print(f"  ⚠️ L2 stream failed to start: {_l2e}", flush=True)
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
            "market_ob","market_os",
            "spy_rsi_4h","spy_rsi_1h",
            "spy_ob_4h","spy_os_4h","spy_ob_1h","spy_os_1h",
            "spy_mtf_ob","spy_mtf_os",
            "qqq_rsi_4h","qqq_ob_4h",
            "mtf_both_ob","mtf_both_os",
            # POC / Volume Profile
            "poc_dist","above_poc","in_value_area","above_vah","below_val"
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
                _ml_model_cache = None   # clear so retrain can write fresh
                # Keep old pkg available via local var for first analysis cycle
                _startup_stale_pkg = pkg
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
    for target in [fetch_institutional_periodically, monitor_loop,
                   _weekly_retrain_scheduler, _fast_price_loop]:
        try:
            threading.Thread(target=target, daemon=True).start()
            if target.__name__ == "_fast_price_loop":
                print("  ✅ 1-min price monitor started", flush=True)
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
