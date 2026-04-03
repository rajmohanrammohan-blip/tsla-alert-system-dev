"""
schwab_client.py — Schwab API integration for TSLA Alert System
Replaces yfinance for: price history, options chain (with Greeks), real-time quotes
Auth: OAuth2 with token stored in SCHWAB_TOKEN_JSON env var (Railway-friendly)

Environment variables required:
    SCHWAB_APP_KEY      — Your Schwab app key (Client ID)
    SCHWAB_APP_SECRET   — Your Schwab app secret
    SCHWAB_TOKEN_JSON   — Full OAuth token JSON (set after first auth)
    SCHWAB_CALLBACK_URL — https://127.0.0.1 (default)
"""

import os, json, time, logging
from datetime import datetime, timedelta
from functools import lru_cache

log = logging.getLogger("schwab_client")

# ── Env vars ─────────────────────────────────────────────────────────────────
SCHWAB_APP_KEY      = os.environ.get("SCHWAB_APP_KEY", "")
SCHWAB_APP_SECRET   = os.environ.get("SCHWAB_APP_SECRET", "")
SCHWAB_TOKEN_JSON   = os.environ.get("SCHWAB_TOKEN_JSON", "")
SCHWAB_CALLBACK_URL = os.environ.get("SCHWAB_CALLBACK_URL", "https://127.0.0.1")

_client = None          # cached schwab client
_client_ts = 0          # when it was created
_token_cache = {}       # in-memory token (refreshed automatically)

def is_configured():
    """True if Schwab credentials are present."""
    return bool(SCHWAB_APP_KEY and SCHWAB_APP_SECRET)

def _token_read():
    """Read token from env var or in-memory cache. Handles multiple formats robustly."""
    global _token_cache
    if _token_cache:
        return _token_cache

    raw = (SCHWAB_TOKEN_JSON or "").strip()
    if not raw or raw in ("PENDING", "null", "{}", ""):
        if raw == "PENDING":
            log.info("[SCHWAB] Token is PENDING — complete auth at /schwab-setup")
        return None

    # Also check /tmp for token saved by _token_write during this session
    if not raw or raw == "PENDING":
        try:
            with open("/tmp/schwab_token.json") as f:
                raw = f.read().strip()
        except Exception:
            pass

    try:
        parsed = json.loads(raw)
    except Exception as e:
        log.error(f"[SCHWAB] Token JSON parse error: {e}")
        log.error(f"[SCHWAB] First 100 chars of token: {repr(raw[:100])}")
        log.error("[SCHWAB] Go to /schwab-setup to re-authenticate")
        return None

    # Handle case where user pasted the full /api/schwab/complete_auth response
    # instead of just the token_json value inside it
    if isinstance(parsed, dict) and "token_json" in parsed:
        log.info("[SCHWAB] Detected full response format — extracting token_json")
        inner = parsed["token_json"]
        try:
            parsed = json.loads(inner) if isinstance(inner, str) else inner
        except Exception as e:
            log.error(f"[SCHWAB] Could not parse inner token_json: {e}")
            return None

    # Handle double-encoded string (token_json was a string, not parsed)
    if isinstance(parsed, str):
        try:
            parsed = json.loads(parsed)
        except Exception as e:
            log.error(f"[SCHWAB] Double-encoded token parse failed: {e}")
            return None

    # Validate it has the required schwab-py structure
    if not isinstance(parsed, dict) or "creation_timestamp" not in parsed:
        log.error(f"[SCHWAB] Token missing creation_timestamp — keys: {list(parsed.keys()) if isinstance(parsed, dict) else type(parsed)}")
        log.error("[SCHWAB] Re-authenticate at /schwab-setup")
        return None

    _token_cache = parsed
    log.info(f"[SCHWAB] Token loaded OK (created: {parsed.get('creation_timestamp')})")
    return _token_cache

def _token_write(token):
    """Store updated token in memory (and log for Railway env var update)."""
    global _token_cache
    _token_cache = token
    token_str = json.dumps(token)
    # Log so Railway logs show the new token — operator can update env var
    log.info(f"[SCHWAB] Token refreshed — update SCHWAB_TOKEN_JSON env var with: {token_str[:80]}...")
    # Also try to write to /tmp for persistence within the session
    try:
        with open("/tmp/schwab_token.json", "w") as f:
            json.dump(token, f)
    except Exception:
        pass

def get_client():
    """Return cached Schwab client, creating if needed. Returns None if not configured."""
    global _client, _client_ts
    if not is_configured():
        return None

    # Recreate client every 23 hours (tokens expire after 30min but auto-refresh)
    if _client and (time.time() - _client_ts) < 82800:
        return _client

    try:
        import schwab
        token = _token_read()
        if token is None:
            log.warning("[SCHWAB] No token — need first-time auth. Call /api/schwab/auth_url")
            return None

        _client = schwab.auth.client_from_access_functions(
            api_key        = SCHWAB_APP_KEY,
            app_secret     = SCHWAB_APP_SECRET,
            token_read_func  = _token_read,
            token_write_func = _token_write,
            enforce_enums    = True,
        )
        _client_ts = time.time()
        log.info("[SCHWAB] Client created OK")
        return _client

    except Exception as e:
        log.error(f"[SCHWAB] Client creation failed: {e}")
        _client = None
        return None

# ── Price History ─────────────────────────────────────────────────────────────

def get_price_history(symbol, period_years=2, freq_minutes=5):
    """
    Fetch OHLCV bars from Schwab.
    Returns DataFrame with columns: Open, High, Low, Close, Volume
    indexed by datetime. Falls back to yfinance if Schwab unavailable.
    """
    client = get_client()
    if client is None:
        return _yf_fallback_history(symbol, period_years, freq_minutes)

    try:
        import schwab
        import pandas as pd

        C = schwab.client.Client

        # Map freq_minutes to Schwab enums
        freq_map = {
            1:  (C.PriceHistory.FrequencyType.MINUTE, C.PriceHistory.Frequency.EVERY_MINUTE),
            5:  (C.PriceHistory.FrequencyType.MINUTE, C.PriceHistory.Frequency.EVERY_FIVE_MINUTES),
            10: (C.PriceHistory.FrequencyType.MINUTE, C.PriceHistory.Frequency.EVERY_TEN_MINUTES),
            15: (C.PriceHistory.FrequencyType.MINUTE, C.PriceHistory.Frequency.EVERY_FIFTEEN_MINUTES),
            30: (C.PriceHistory.FrequencyType.MINUTE, C.PriceHistory.Frequency.EVERY_THIRTY_MINUTES),
        }
        freq_type, freq = freq_map.get(freq_minutes, freq_map[5])

        # Schwab supports up to 10 years of 5-min data with YEAR period type
        period_type = C.PriceHistory.PeriodType.YEAR
        period_val  = min(period_years, 10)
        if period_val == 1:
            period = C.PriceHistory.Period.SIX_MONTHS
        else:
            # Use year count (1,2,3,5,10,15,20 are valid)
            valid = [1, 2, 3, 5, 10, 15, 20]
            period_val = min(valid, key=lambda x: abs(x - period_years))
            period_enum_map = {
                1: None,  # handled above
                2: C.PriceHistory.Period.TWO_DAYS,   # not right but we override
            }
            # Actually use needByEndDate for precise control
            period = C.PriceHistory.Period.FIFTEEN_YEARS  # max, we'll trim

        end_dt   = datetime.now()
        start_dt = end_dt - timedelta(days=365 * period_years)

        resp = client.get_price_history(
            symbol,
            period_type          = period_type,
            frequency_type       = freq_type,
            frequency            = freq,
            start_datetime       = start_dt,
            end_datetime         = end_dt,
            need_extended_hours_data = False,
        )

        if resp.status_code != 200:
            log.warning(f"[SCHWAB] price_history HTTP {resp.status_code} — falling back to yfinance")
            return _yf_fallback_history(symbol, period_years, freq_minutes)

        data = resp.json()
        candles = data.get("candles", [])
        if not candles:
            log.warning("[SCHWAB] Empty candles — falling back")
            return _yf_fallback_history(symbol, period_years, freq_minutes)

        df = pd.DataFrame(candles)
        df["datetime"] = pd.to_datetime(df["datetime"], unit="ms", utc=True)
        df = df.set_index("datetime").rename(columns={
            "open": "Open", "high": "High", "low": "Low",
            "close": "Close", "volume": "Volume"
        })[["Open","High","Low","Close","Volume"]]
        df.index = df.index.tz_convert("America/New_York")
        log.info(f"[SCHWAB] {symbol} price_history: {len(df)} bars ({freq_minutes}m)")
        return df

    except Exception as e:
        log.error(f"[SCHWAB] price_history error: {e}")
        return _yf_fallback_history(symbol, period_years, freq_minutes)


def _yf_fallback_history(symbol, period_years, freq_minutes):
    """Fallback to yfinance when Schwab unavailable."""
    try:
        import yfinance as yf
        interval_map = {1:"1m", 5:"5m", 10:"10m", 15:"15m", 30:"30m"}
        interval = interval_map.get(freq_minutes, "5m")
        # yfinance 5m limit: 60 days; use 1h for longer history
        if freq_minutes <= 5 and period_years > 0.16:
            period = "60d"
        else:
            period = f"{min(period_years, 2)}y"
        df = yf.download(symbol, period=period, interval=interval,
                         progress=False, auto_adjust=True)
        if hasattr(df.columns, "levels"):
            df.columns = df.columns.get_level_values(0)
        log.info(f"[SCHWAB-FALLBACK] yfinance {symbol}: {len(df)} bars")
        return df
    except Exception as e:
        log.error(f"[SCHWAB-FALLBACK] yfinance failed: {e}")
        import pandas as pd
        return pd.DataFrame()


# ── Options Chain with Greeks ─────────────────────────────────────────────────

def get_option_chain(symbol, current_price=None):
    """
    Fetch full options chain with real Greeks from Schwab.
    Returns dict with:
        calls / puts: list of strike dicts with delta, gamma, theta, vega, iv, volume, oi
        front_iv, back_iv, iv_term_spread
        pc_ratio, pc_delta
        max_pain, gex
    Falls back to yfinance if Schwab unavailable.
    """
    client = get_client()
    if client is None:
        return _yf_fallback_options(symbol)

    try:
        import schwab
        C = schwab.client.Client

        resp = client.get_option_chain(
            symbol,
            contract_type     = C.Options.ContractType.ALL,
            include_underlying_quote = True,
            strategy          = C.Options.Strategy.SINGLE,
        )

        if resp.status_code != 200:
            log.warning(f"[SCHWAB] option_chain HTTP {resp.status_code}")
            return _yf_fallback_options(symbol)

        data  = resp.json()
        price = current_price or data.get("underlyingPrice", 0) or 0

        calls_raw = data.get("callExpDateMap", {})
        puts_raw  = data.get("putExpDateMap",  {})

        calls_list, puts_list = [], []
        total_call_prem = total_put_prem = 0
        total_call_vol  = total_put_vol  = 0
        gex_total = 0

        # Parse all expiries
        for exp_key, strikes in calls_raw.items():
            exp_str = exp_key.split(":")[0]
            try:
                exp_dt = datetime.strptime(exp_str, "%Y-%m-%d")
                dte = max((exp_dt.date() - datetime.now().date()).days, 0)
            except Exception:
                dte = 0

            for strike_str, opts in strikes.items():
                for opt in opts:
                    strike   = float(strike_str)
                    delta    = float(opt.get("delta",    0) or 0)
                    gamma    = float(opt.get("gamma",    0) or 0)
                    theta    = float(opt.get("theta",    0) or 0)
                    vega     = float(opt.get("vega",     0) or 0)
                    iv       = float(opt.get("volatility", 0) or 0) / 100
                    volume   = int(opt.get("totalVolume", 0) or 0)
                    oi       = int(opt.get("openInterest", 0) or 0)
                    bid      = float(opt.get("bid", 0) or 0)
                    ask      = float(opt.get("ask", 0) or 0)
                    mid      = (bid + ask) / 2 if ask > 0 else float(opt.get("last", 0) or 0)
                    premium  = volume * mid * 100

                    total_call_prem += premium
                    total_call_vol  += volume

                    # GEX contribution: gamma * oi * 100 * price^2 / 1e8
                    gex_total += gamma * oi * 100 * (price**2) / 1e8

                    calls_list.append({
                        "expiry": exp_str, "dte": dte, "strike": strike,
                        "delta": round(delta,4), "gamma": round(gamma,6),
                        "theta": round(theta,4), "vega": round(vega,4),
                        "iv": round(iv, 4), "volume": volume, "oi": oi,
                        "mid": round(mid, 2), "premium_usd": round(premium),
                        "bid": bid, "ask": ask,
                        "moneyness": "ITM" if strike < price else ("ATM" if abs(strike-price)/max(price,1) < 0.02 else "OTM"),
                    })

        for exp_key, strikes in puts_raw.items():
            exp_str = exp_key.split(":")[0]
            try:
                exp_dt = datetime.strptime(exp_str, "%Y-%m-%d")
                dte = max((exp_dt.date() - datetime.now().date()).days, 0)
            except Exception:
                dte = 0

            for strike_str, opts in strikes.items():
                for opt in opts:
                    strike   = float(strike_str)
                    delta    = float(opt.get("delta",    0) or 0)
                    gamma    = float(opt.get("gamma",    0) or 0)
                    theta    = float(opt.get("theta",    0) or 0)
                    vega     = float(opt.get("vega",     0) or 0)
                    iv       = float(opt.get("volatility", 0) or 0) / 100
                    volume   = int(opt.get("totalVolume", 0) or 0)
                    oi       = int(opt.get("openInterest", 0) or 0)
                    bid      = float(opt.get("bid", 0) or 0)
                    ask      = float(opt.get("ask", 0) or 0)
                    mid      = (bid + ask) / 2 if ask > 0 else float(opt.get("last", 0) or 0)
                    premium  = volume * mid * 100

                    total_put_prem += premium
                    total_put_vol  += volume
                    # Puts add negative GEX
                    gex_total -= gamma * oi * 100 * (price**2) / 1e8

                    puts_list.append({
                        "expiry": exp_str, "dte": dte, "strike": strike,
                        "delta": round(delta,4), "gamma": round(gamma,6),
                        "theta": round(theta,4), "vega": round(vega,4),
                        "iv": round(iv, 4), "volume": volume, "oi": oi,
                        "mid": round(mid, 2), "premium_usd": round(premium),
                        "bid": bid, "ask": ask,
                        "moneyness": "ITM" if strike > price else ("ATM" if abs(strike-price)/max(price,1) < 0.02 else "OTM"),
                    })

        # Sort by expiry then strike
        calls_list.sort(key=lambda x: (x["expiry"], x["strike"]))
        puts_list.sort( key=lambda x: (x["expiry"], x["strike"]))

        # IV term structure: front vs back month
        expiries = sorted(set(c["expiry"] for c in calls_list))
        front_iv = back_iv = 0.3
        if len(expiries) >= 1:
            front_calls = [c for c in calls_list if c["expiry"] == expiries[0] and c["iv"] > 0]
            front_iv = float(sum(c["iv"] for c in front_calls) / max(len(front_calls), 1))
        if len(expiries) >= 2:
            back_calls = [c for c in calls_list if c["expiry"] == expiries[1] and c["iv"] > 0]
            back_iv  = float(sum(c["iv"] for c in back_calls) / max(len(back_calls), 1))

        # PC ratio
        pc_ratio = total_put_vol / max(total_call_vol, 1)

        # Max pain: strike where option sellers (MMs) lose least
        max_pain = _calc_max_pain(calls_list, puts_list, price)

        log.info(f"[SCHWAB] {symbol} options: {len(calls_list)} calls, {len(puts_list)} puts, "
                 f"front_iv={front_iv:.2f} back_iv={back_iv:.2f} gex={gex_total:.1f}M pc={pc_ratio:.2f}")

        return {
            "calls":          calls_list,
            "puts":           puts_list,
            "front_iv":       round(front_iv,  4),
            "back_iv":        round(back_iv,   4),
            "iv_term_spread": round(back_iv - front_iv, 4),
            "iv_ratio":       round(front_iv / (back_iv + 1e-9), 3),
            "pc_ratio":       round(pc_ratio, 3),
            "total_call_premium": round(total_call_prem),
            "total_put_premium":  round(total_put_prem),
            "gex_total":      round(gex_total, 1),
            "max_pain":       max_pain,
            "expiries":       expiries[:6],
            "source":         "schwab",
        }

    except Exception as e:
        log.error(f"[SCHWAB] option_chain error: {e}")
        import traceback; traceback.print_exc()
        return _yf_fallback_options(symbol)


def _calc_max_pain(calls, puts, current_price):
    """Calculate max pain strike (where total option value is minimized for buyers)."""
    try:
        strikes = sorted(set(c["strike"] for c in calls) | set(p["strike"] for p in puts))
        if not strikes:
            return round(current_price / 5) * 5

        min_pain, max_pain_strike = float("inf"), strikes[0]
        for test_strike in strikes:
            call_pain = sum(max(0, test_strike - c["strike"]) * c["oi"] for c in calls)
            put_pain  = sum(max(0, p["strike"] - test_strike) * p["oi"] for p in puts)
            total = call_pain + put_pain
            if total < min_pain:
                min_pain = total
                max_pain_strike = test_strike
        return max_pain_strike
    except Exception:
        return round(current_price / 5) * 5


def _yf_fallback_options(symbol):
    """Fallback options data from yfinance (no Greeks)."""
    try:
        import yfinance as yf
        tkr     = yf.Ticker(symbol)
        exps    = tkr.options
        if not exps:
            return {}
        calls_list, puts_list = [], []
        total_call_prem = total_put_prem = 0
        front_iv = back_iv = 0.3
        for exp_idx, exp in enumerate(exps[:4]):
            chain = tkr.option_chain(exp)
            for _, row in chain.calls.iterrows():
                iv   = float(row.get("impliedVolatility", 0.3) or 0.3)
                vol  = int(row.get("volume", 0) or 0)
                oi   = int(row.get("openInterest", 0) or 0)
                mid  = float(row.get("lastPrice", 0) or 0)
                prem = vol * mid * 100
                total_call_prem += prem
                calls_list.append({"expiry":exp,"strike":float(row["strike"]),"iv":round(iv,4),
                                    "volume":vol,"oi":oi,"mid":round(mid,2),"premium_usd":round(prem),
                                    "delta":0,"gamma":0,"theta":0,"vega":0})
            for _, row in chain.puts.iterrows():
                iv   = float(row.get("impliedVolatility", 0.3) or 0.3)
                vol  = int(row.get("volume", 0) or 0)
                oi   = int(row.get("openInterest", 0) or 0)
                mid  = float(row.get("lastPrice", 0) or 0)
                prem = vol * mid * 100
                total_put_prem += prem
                puts_list.append({"expiry":exp,"strike":float(row["strike"]),"iv":round(iv,4),
                                   "volume":vol,"oi":oi,"mid":round(mid,2),"premium_usd":round(prem),
                                   "delta":0,"gamma":0,"theta":0,"vega":0})
            if exp_idx == 0 and calls_list:
                front_iv = sum(c["iv"] for c in calls_list[:10]) / min(len(calls_list), 10)
            if exp_idx == 1 and calls_list:
                back_iv = front_iv * 1.05
        pc_ratio = (sum(p["volume"] for p in puts_list) /
                    max(sum(c["volume"] for c in calls_list), 1))
        return {
            "calls": calls_list, "puts": puts_list,
            "front_iv": round(front_iv,4), "back_iv": round(back_iv,4),
            "iv_term_spread": round(back_iv-front_iv,4),
            "iv_ratio": round(front_iv/(back_iv+1e-9),3),
            "pc_ratio": round(pc_ratio,3),
            "total_call_premium": round(total_call_prem),
            "total_put_premium":  round(total_put_prem),
            "gex_total": 0, "max_pain": 0, "expiries": list(exps[:4]),
            "source": "yfinance",
        }
    except Exception as e:
        log.error(f"[SCHWAB-FALLBACK] options failed: {e}")
        return {}


# ── Real-time Quote ───────────────────────────────────────────────────────────

def get_quote(symbol):
    """
    Get real-time quote from Schwab (no delay).
    Returns dict: price, bid, ask, volume, change_pct, last_size
    Falls back to yfinance if unavailable.
    """
    client = get_client()
    if client is None:
        return _yf_fallback_quote(symbol)

    try:
        resp = client.get_quote(symbol)
        if resp.status_code != 200:
            return _yf_fallback_quote(symbol)

        data = resp.json().get(symbol, {})
        q    = data.get("quote", {})
        ref  = data.get("reference", {})

        price      = float(q.get("lastPrice",  0) or q.get("mark", 0) or 0)
        bid        = float(q.get("bidPrice",   0) or 0)
        ask        = float(q.get("askPrice",   0) or 0)
        volume     = int(q.get("totalVolume",  0) or 0)
        prev_close = float(q.get("closePrice", price) or price)
        change_pct = round((price - prev_close) / max(prev_close, 1) * 100, 2)

        log.debug(f"[SCHWAB] {symbol} quote: ${price} ({change_pct:+.2f}%)")
        return {
            "price": price, "bid": bid, "ask": ask,
            "volume": volume, "change_pct": change_pct,
            "prev_close": prev_close,
            "description": ref.get("description", symbol),
            "source": "schwab",
        }
    except Exception as e:
        log.error(f"[SCHWAB] quote error: {e}")
        return _yf_fallback_quote(symbol)


def _yf_fallback_quote(symbol):
    try:
        import yfinance as yf
        t = yf.Ticker(symbol)
        info = t.fast_info
        price = float(getattr(info, "last_price", 0) or 0)
        prev  = float(getattr(info, "previous_close", price) or price)
        return {
            "price": price, "bid": 0, "ask": 0,
            "volume": int(getattr(info, "three_month_average_volume", 0) or 0),
            "change_pct": round((price-prev)/max(prev,1)*100, 2),
            "prev_close": prev, "source": "yfinance",
        }
    except Exception:
        return {"price": 0, "change_pct": 0, "source": "yfinance_failed"}


# ── Account / Positions (for future trade execution) ─────────────────────────

def get_positions(account_hash=None):
    """
    Get current positions from Schwab account.
    Returns list of position dicts.
    """
    client = get_client()
    if client is None:
        return []
    try:
        if account_hash:
            resp = client.get_account(account_hash, fields=[client.Account.Fields.POSITIONS])
        else:
            resp = client.get_accounts(fields=[client.Account.Fields.POSITIONS])
        if resp.status_code != 200:
            return []

        data = resp.json()
        if isinstance(data, list):
            accounts = data
        else:
            accounts = [data]

        positions = []
        for acct in accounts:
            acct_data   = acct.get("securitiesAccount", {})
            acct_number = acct_data.get("accountNumber", "?")
            for pos in acct_data.get("positions", []):
                inst = pos.get("instrument", {})
                positions.append({
                    "symbol":       inst.get("symbol", "?"),
                    "asset_type":   inst.get("assetType", "EQUITY"),
                    "shares":       float(pos.get("longQuantity", 0)),
                    "short_shares": float(pos.get("shortQuantity", 0)),
                    "avg_price":    float(pos.get("averagePrice", 0)),
                    "market_value": float(pos.get("marketValue", 0)),
                    "unrealized_pnl": float(pos.get("unrealizedPnL", 0)),
                    "account":      acct_number,
                })
        log.info(f"[SCHWAB] Got {len(positions)} positions")
        return positions
    except Exception as e:
        log.error(f"[SCHWAB] positions error: {e}")
        return []


def get_account_summary():
    """Get portfolio value, cash, day P&L."""
    client = get_client()
    if client is None:
        return {}
    try:
        resp = client.get_accounts()
        if resp.status_code != 200:
            return {}
        accounts = resp.json()
        if not isinstance(accounts, list):
            accounts = [accounts]
        total_value = total_cash = day_pnl = 0
        for acct in accounts:
            sa = acct.get("securitiesAccount", {})
            cv = sa.get("currentBalances", {})
            total_value += float(cv.get("liquidationValue", 0) or 0)
            total_cash  += float(cv.get("cashBalance", 0) or 0)
            day_pnl     += float(sa.get("initialBalances", {}).get("dayTradingEquity", 0) or 0)
        return {
            "total_value": round(total_value, 2),
            "cash":        round(total_cash,  2),
            "day_pnl":     round(day_pnl,     2),
            "source":      "schwab",
        }
    except Exception as e:
        log.error(f"[SCHWAB] account_summary error: {e}")
        return {}


# ── First-Time OAuth Setup ────────────────────────────────────────────────────

def get_auth_url():
    """
    Generate the OAuth2 authorization URL for first-time setup.
    User visits this URL, logs in, and we capture the redirect URL.
    """
    if not is_configured():
        return None, "SCHWAB_APP_KEY and SCHWAB_APP_SECRET not set"
    try:
        import schwab
        ctx = schwab.auth.get_auth_context(SCHWAB_APP_KEY, SCHWAB_CALLBACK_URL)
        return ctx.authorization_url, None
    except Exception as e:
        return None, str(e)


def complete_auth_from_url(redirected_url):
    """
    Complete OAuth flow after user visits auth URL and is redirected.
    redirected_url = the full URL the browser was redirected to (https://127.0.0.1?code=...)
    Returns (success, message, token_json_string)
    """
    if not is_configured():
        return False, "Credentials not set", ""
    try:
        import schwab
        from urllib.parse import urlparse, parse_qs

        # Extract state from the redirected URL to reconstruct matching auth_context
        parsed = urlparse(redirected_url)
        params = parse_qs(parsed.query)
        state  = params.get("state", [""])[0]

        if not state:
            return False, "No state parameter in redirect URL — make sure you copied the full URL", ""

        # Reconstruct auth_context with the ORIGINAL state from the redirect
        ctx = schwab.auth.AuthContext(
            callback_url      = SCHWAB_CALLBACK_URL,
            authorization_url = f"https://api.schwabapi.com/v1/oauth/authorize",
            state             = state,
        )

        client = schwab.auth.client_from_received_url(
            api_key          = SCHWAB_APP_KEY,
            app_secret       = SCHWAB_APP_SECRET,
            received_url     = redirected_url,
            auth_context     = ctx,
            token_write_func = _token_write,
        )
        global _client, _client_ts
        _client    = client
        _client_ts = time.time()
        token_str  = json.dumps(_token_cache)
        return True, "Auth complete! Add token_json as SCHWAB_TOKEN_JSON in Railway Variables.", token_str
    except Exception as e:
        import traceback
        return False, f"Auth failed: {e}", ""


print("[schwab_client] Module loaded. Configured:", is_configured())
