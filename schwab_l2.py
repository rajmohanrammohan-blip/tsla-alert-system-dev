# ══════════════════════════════════════════════════════════════════════════════
# LEVEL 2 / TAPE — Schwab Streaming WebSocket
# Real-time bid/ask depth, large print detection, sweep detection
# Uses schwab-py StreamClient (asyncio, runs in background thread)
# ══════════════════════════════════════════════════════════════════════════════
import asyncio, threading, collections

_l2_state = {
    "bids":           [],      # [{price, size, num_mm}]
    "asks":           [],      # [{price, size, num_mm}]
    "bid_ask_imb":    0.0,     # 0-100: % of size on bid side (>60 = bullish absorption)
    "top5_bid_size":  0,       # total size at top 5 bid levels
    "top5_ask_size":  0,       # total size at top 5 ask levels
    "large_prints":   [],      # recent trades > 5000 shares
    "sweep_detected": False,   # True if ask lifted through multiple levels < 1s
    "last_tape":      [],      # last 50 tape prints [{price, size, side, ts}]
    "tape_signal":    "NEUTRAL",
    "l2_signal":      "NEUTRAL",
    "updated":        0,
    "running":        False,
    "error":          None,
}

_l2_thread     = None
_l2_loop       = None
_last_sweep_ts = 0

def _process_l2_book(msg):
    """Process Level 2 book update from Schwab stream."""
    global _last_sweep_ts
    try:
        content = msg.get("content", [])
        for item in content:
            bids_raw = item.get("BIDS", item.get("2", []))
            asks_raw = item.get("ASKS", item.get("3", []))

            # Parse bids and asks
            bids = []
            for b in (bids_raw or []):
                if isinstance(b, dict):
                    bids.append({
                        "price": float(b.get("0", b.get("price", 0))),
                        "size":  int(b.get("1", b.get("size", 0))),
                        "n_mm":  int(b.get("2", b.get("num_mm", 1))),
                    })
            asks = []
            for a in (asks_raw or []):
                if isinstance(a, dict):
                    asks.append({
                        "price": float(a.get("0", a.get("price", 0))),
                        "size":  int(a.get("1", a.get("size", 0))),
                        "n_mm":  int(a.get("2", a.get("num_mm", 1))),
                    })

            bids.sort(key=lambda x: -x["price"])  # highest bid first
            asks.sort(key=lambda x:  x["price"])  # lowest ask first

            # Top 5 levels
            top5_bid = sum(b["size"] for b in bids[:5])
            top5_ask = sum(a["size"] for a in asks[:5])
            total    = top5_bid + top5_ask + 1e-9
            imb      = round(top5_bid / total * 100, 1)

            # Sweep detection: ask depleted rapidly
            now = asyncio.get_event_loop().time()
            sweep = False
            if asks and top5_ask < 500 and (now - _last_sweep_ts) > 30:
                sweep = True
                _last_sweep_ts = now
                print(f"  🚨 L2 SWEEP DETECTED — ask side thin ({top5_ask} shares)", flush=True)

            # L2 signal
            if imb >= 80:
                l2_sig = "STRONG_ABSORPTION"   # institutions absorbing at bid
            elif imb >= 65:
                l2_sig = "BULLISH_IMBALANCE"
            elif imb <= 20:
                l2_sig = "OFFER_HEAVY"         # sellers stacked
            elif imb <= 35:
                l2_sig = "BEARISH_IMBALANCE"
            else:
                l2_sig = "NEUTRAL"

            _l2_state.update({
                "bids":           bids[:10],
                "asks":           asks[:10],
                "bid_ask_imb":    imb,
                "top5_bid_size":  top5_bid,
                "top5_ask_size":  top5_ask,
                "sweep_detected": sweep,
                "l2_signal":      l2_sig,
                "updated":        now,
            })
    except Exception as e:
        _l2_state["error"] = str(e)


def _process_level1(msg):
    """Process Level 1 quote (includes last sale = tape)."""
    try:
        content = msg.get("content", [])
        for item in content:
            last_price = float(item.get("LAST_PRICE", item.get("3", 0)) or 0)
            last_size  = int(item.get("LAST_SIZE",  item.get("9", 0)) or 0)
            bid        = float(item.get("BID_PRICE", item.get("1", 0)) or 0)
            ask        = float(item.get("ASK_PRICE", item.get("2", 0)) or 0)

            if last_price <= 0 or last_size <= 0:
                continue

            # Determine side: above midpoint = buy, below = sell
            mid  = (bid + ask) / 2 if bid > 0 and ask > 0 else last_price
            side = "BUY" if last_price >= mid else "SELL"
            ts   = asyncio.get_event_loop().time()

            tape_entry = {
                "price": last_price,
                "size":  last_size,
                "side":  side,
                "ts":    ts,
            }
            _l2_state["last_tape"].append(tape_entry)
            _l2_state["last_tape"] = _l2_state["last_tape"][-100:]  # keep last 100

            # Large print detection: > 5000 shares = institutional
            if last_size >= 5000:
                print(f"  🐋 LARGE PRINT: {last_size:,} shares @ ${last_price:.2f} {side}", flush=True)
                _l2_state["large_prints"].append(tape_entry)
                _l2_state["large_prints"] = _l2_state["large_prints"][-20:]

            # Tape signal: last 20 trades buy/sell ratio
            tape = _l2_state["last_tape"][-20:]
            if len(tape) >= 5:
                buy_vol  = sum(t["size"] for t in tape if t["side"] == "BUY")
                sell_vol = sum(t["size"] for t in tape if t["side"] == "SELL")
                tot      = buy_vol + sell_vol + 1e-9
                if buy_vol / tot > 0.70:
                    _l2_state["tape_signal"] = "AGGRESSIVE_BUYING"
                elif sell_vol / tot > 0.70:
                    _l2_state["tape_signal"] = "AGGRESSIVE_SELLING"
                else:
                    _l2_state["tape_signal"] = "MIXED"
    except Exception as e:
        pass  # tape errors are non-critical


async def _run_l2_stream(ticker):
    """Async coroutine: connects to Schwab stream and subscribes to L2 + Level1."""
    import schwab_client as _sc
    client = _sc.get_client()
    if client is None:
        _l2_state["error"] = "No Schwab client available"
        print("  ⚠️ L2: No Schwab client — check credentials", flush=True)
        return
    if client is None:
        _l2_state["error"] = "No Schwab client"
        return

    try:
        stream = schwab.streaming.StreamClient(client, account_id=_get_account_id())
        await stream.login()

        # Subscribe to NASDAQ Level 2 book
        stream.add_nasdaq_book_handler(_process_l2_book)
        await stream.nasdaq_book_subs([ticker])

        # Subscribe to Level 1 for tape (last sale, bid/ask size)
        stream.add_level_one_equity_handler(_process_level1)
        await stream.level_one_equity_subs(
            [ticker],
            fields=[
                stream.LevelOneEquityFields.LAST_PRICE,
                stream.LevelOneEquityFields.LAST_SIZE,
                stream.LevelOneEquityFields.BID_PRICE,
                stream.LevelOneEquityFields.ASK_PRICE,
                stream.LevelOneEquityFields.BID_SIZE,
                stream.LevelOneEquityFields.ASK_SIZE,
                stream.LevelOneEquityFields.TOTAL_VOLUME,
            ]
        )

        _l2_state["running"] = True
        print(f"  📡 L2 stream active: {ticker} Level 2 + tape", flush=True)

        # Keep running — handle_message processes all incoming messages
        while True:
            await stream.handle_message()

    except Exception as e:
        _l2_state["error"] = str(e)
        _l2_state["running"] = False
        print(f"  ⚠️ L2 stream error: {e}", flush=True)


def _get_account_id():
    """Get first Schwab account ID for streaming."""
    try:
        import schwab_client as _sc
        client = _sc.get_client()
        if client is None:
            return None
        resp = client.get_accounts()
        if resp.status_code == 200:
            accounts = resp.json()
            if isinstance(accounts, list) and accounts:
                return accounts[0].get("securitiesAccount", {}).get("accountNumber")
    except Exception:
        pass
    return None


def start_l2_stream(ticker="TSLA"):
    """
    Start Level 2 streaming in a background thread.
    Call once at startup. Non-blocking.
    """
    global _l2_thread, _l2_loop

    if _l2_state.get("running"):
        return  # already running

    def _thread_target():
        global _l2_loop
        # Use schwab via schwab_client (which is already installed as schwab-py)
        try:
            import schwab
        except ImportError:
            try:
                import schwab_client as _sc_check
                import importlib, sys
                # schwab-py is installed as 'schwab' package
                print("  ⚠️ L2: schwab package not found — L2 requires schwab-py", flush=True)
                return
            except Exception:
                return
        _l2_loop = asyncio.new_event_loop()
        asyncio.set_event_loop(_l2_loop)
        try:
            _l2_loop.run_until_complete(_run_l2_stream(ticker))
        except Exception as e:
            _l2_state["error"] = str(e)
        finally:
            _l2_state["running"] = False

    _l2_thread = threading.Thread(target=_thread_target, daemon=True, name="l2-stream")
    _l2_thread.start()
    print(f"  📡 L2 stream thread started for {ticker}", flush=True)


def get_l2_signal():
    """
    Returns current L2 signal dict for SPOCK consumption.
    Includes bid/ask imbalance, tape signal, large prints, sweep.
    """
    age = asyncio.get_event_loop().time() - _l2_state.get("updated", 0) if _l2_loop else 9999
    stale = age > 60  # data older than 60s is stale (market closed)
    return {
        **_l2_state,
        "stale": stale,
        "age_seconds": round(age, 1),
    }
