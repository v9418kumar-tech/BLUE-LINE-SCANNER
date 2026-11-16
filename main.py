import os
import json
import gzip
import threading
import logging
import math
import uuid
from datetime import datetime, timedelta
from urllib.parse import quote
from concurrent.futures import ThreadPoolExecutor, as_completed
from zoneinfo import ZoneInfo

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from flask import Flask, jsonify, request, render_template_string

app = Flask(__name__)
logging.basicConfig(level=logging.INFO)

TOKEN = os.getenv("UPSTOX_ACCESS_TOKEN", "").strip()
BASE = "https://api.upstox.com"
INSTRUMENTS_URL = (
    "https://assets.upstox.com/market-quote/"
    "instruments/exchange/complete.json.gz"
)
IST = ZoneInfo("Asia/Kolkata")

# EXISTING SCANNER CONDITIONS: UNCHANGED
MIN_PRICE = 100.0
MAX_PRICE_EXCLUSIVE = 2000.0  # Strict filter: share price must be below ₹2000
MIN_AVG_TURNOVER = 5 * 1_00_00_000.0
LOOKBACK_DAYS = 20

QUOTE_BATCH_SIZE = 500
QUOTE_WORKERS = 3
HISTORY_WORKERS = 8
HISTORICAL_SCAN_WORKERS = 20  # Concurrent per-instrument historical API requests
HISTORICAL_PROGRESS_STEP = 200  # Report historical progress in 200-share steps
TIMEOUT = 15
TOP_RESULTS = 20
TOP_GAIN_RESULTS = 5
MAX_OPEN_LOW_GAP_PCT = 0.01  # Open-Low gap must be between 0% and 0.01%

INSTRUMENT_CACHE = "nse_instruments_cache.json"
DAILY_CACHE = "volume_history_cache.json"
HISTORICAL_CACHE_PREFIX = "historical_stats_cache_"
HISTORICAL_TIME_CACHE_PREFIX = "historical_time_cache_"

JOBS = {}
JOBS_LOCK = threading.Lock()
CACHE_LOCK = threading.Lock()
LOCAL = threading.local()

# VELOCITY TRACKING: previous scan score by symbol
PREVIOUS_SCORES = {}


def split_top20_gain_results(pool):
    """Build Plus/Minus Top 5 from the displayed Top 20 using the same strength_score."""
    minus_rows = []
    plus_rows = []

    for source in pool:
        gain_pct = source.get("gain_pct")
        if gain_pct is None:
            continue

        gain_value = _safe_number(gain_pct)
        # Gain% selects the PLUS or MINUS list only; it does not change the score.
        if gain_value == 0:
            continue

        # Reuse the exact score already calculated for the main Top 20.
        # Do not calculate blue_top_score or any additional component scores.
        item = dict(source)
        if gain_value < 0:
            minus_rows.append(item)
        else:
            plus_rows.append(item)

    minus_rows.sort(key=lambda item: _safe_number(item.get("strength_score")), reverse=True)
    plus_rows.sort(key=lambda item: _safe_number(item.get("strength_score")), reverse=True)
    return minus_rows[:TOP_GAIN_RESULTS], plus_rows[:TOP_GAIN_RESULTS]


def filter_detection_below_previous_close(pool):
    """Keep only rows with a valid Detection Price strictly below Previous Close."""
    eligible = []
    for row in pool:
        detection_price = _safe_number(row.get("detection_price"))
        previous_close = _safe_number(row.get("previous_close"))
        if detection_price > 0 and previous_close > 0 and detection_price < previous_close:
            eligible.append(row)
    return eligible


def now_ist():
    return datetime.now(IST)


def today():
    return now_ist().date()


def today_s():
    return today().isoformat()


def session():
    s = getattr(LOCAL, "session", None)
    if s is None:
        s = requests.Session()
        retry = Retry(
            total=3, connect=3, read=2, backoff_factor=0.5,
            status_forcelist=(429, 500, 502, 503, 504),
            allowed_methods=frozenset(["GET"]),
            respect_retry_after_header=True, raise_on_status=False,
        )
        adapter = HTTPAdapter(max_retries=retry, pool_connections=20, pool_maxsize=20)
        s.mount("https://", adapter)
        s.mount("http://", adapter)
        s.headers.update({"Accept": "application/json", "Authorization": f"Bearer {TOKEN}"})
        LOCAL.session = s
    return s


def parse_ts(value):
    d = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
    if d.tzinfo is None:
        return d.replace(tzinfo=IST)
    return d.astimezone(IST)


def fmt_time(value):
    try:
        return parse_ts(value).strftime("%I:%M %p").lstrip("0")
    except Exception:
        return None


def detection_clock():
    return now_ist().strftime("%I:%M:%S %p").lstrip("0")


def progress(jid, message):
    with JOBS_LOCK:
        if jid in JOBS:
            JOBS[jid]["message"] = message


def save_json(path, data):
    try:
        with CACHE_LOCK:
            tmp = path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, separators=(",", ":"))
            os.replace(tmp, path)
    except Exception as e:
        logging.warning("Cache save error %s: %r", path, e)


def load_json(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def history_cache_path(selected_date):
    return HISTORICAL_CACHE_PREFIX + selected_date.isoformat() + ".json"


def time_cache_path(selected_date):
    return HISTORICAL_TIME_CACHE_PREFIX + selected_date.isoformat() + ".json"


# NSE EQUITY INSTRUMENTS
def is_equity(x):
    if x.get("segment") != "NSE_EQ" or x.get("instrument_type") != "EQ":
        return False
    if x.get("security_type") not in (None, "", "NORMAL"):
        return False
    key = str(x.get("instrument_key") or "")
    symbol = str(x.get("trading_symbol") or "").upper().strip()
    if not key or not symbol:
        return False
    combined = symbol + " " + str(x.get("name") or "").upper() + " " + str(x.get("short_name") or "").upper()
    excluded = ("ETF", "EXCHANGE TRADED FUND", "MUTUAL FUND", "INDEX FUND", "SME")
    if any(word in combined for word in excluded):
        return False
    if symbol.endswith("BEES") or symbol.endswith(("-BE", "-BZ")):
        return False
    return True


def load_instruments():
    cached = load_json(INSTRUMENT_CACHE)
    if cached.get("date") == today_s() and cached.get("items"):
        return cached["items"]
    r = session().get(INSTRUMENTS_URL, timeout=30)
    r.raise_for_status()
    raw = json.loads(gzip.decompress(r.content).decode("utf-8"))
    items = [{"key": x["instrument_key"], "symbol": x["trading_symbol"]} for x in raw if is_equity(x)]
    save_json(INSTRUMENT_CACHE, {"date": today_s(), "items": items})
    logging.info("Loaded %s NSE equity instruments", len(items))
    return items


# LIVE QUOTES
def quote_batch(batch):
    r = session().get(
        BASE + "/v2/market-quote/quotes",
        params={"instrument_key": ",".join(x["key"] for x in batch)},
        timeout=TIMEOUT,
    )
    if r.status_code != 200:
        raise RuntimeError(f"Quote API {r.status_code}: {r.text[:200]}")
    data = r.json().get("data", {})
    output = {}
    if isinstance(data, dict):
        for q in data.values():
            if isinstance(q, dict):
                key = q.get("instrument_token")
                if key:
                    output[key] = q
    return output


def get_quotes(items):
    batches = [items[i:i + QUOTE_BATCH_SIZE] for i in range(0, len(items), QUOTE_BATCH_SIZE)]
    output = {}
    with ThreadPoolExecutor(max_workers=min(QUOTE_WORKERS, max(1, len(batches)))) as executor:
        futures = [executor.submit(quote_batch, b) for b in batches]
        for future in as_completed(futures):
            output.update(future.result())
    return output


# HISTORICAL DAILY CANDLES
def daily_history(key, end_date=None):
    end_date = end_date or today()
    start_date = end_date - timedelta(days=60)
    url = f"{BASE}/v3/historical-candle/{quote(key, safe='|')}/days/1/{end_date.isoformat()}/{start_date.isoformat()}"
    r = session().get(url, timeout=TIMEOUT)
    if r.status_code != 200:
        logging.warning("Daily history error %s: %s", key, r.status_code)
        return None
    candles = r.json().get("data", {}).get("candles", [])
    return candles if isinstance(candles, list) else []


def parse_daily_rows(candles):
    rows = []
    for c in candles or []:
        if not isinstance(c, list) or len(c) < 6:
            continue
        try:
            rows.append({"ts": c[0], "open": float(c[1]), "high": float(c[2]), "low": float(c[3]), "close": float(c[4]), "volume": float(c[5])})
        except (TypeError, ValueError):
            continue
    try:
        rows.sort(key=lambda x: parse_ts(x["ts"]), reverse=True)
    except Exception:
        return []
    return rows


def daily_stats(key):
    candles = daily_history(key)
    if candles is None:
        return None
    completed = []
    for row in parse_daily_rows(candles):
        try:
            if parse_ts(row["ts"]).date() < today():
                completed.append(row)
        except Exception:
            continue
    if len(completed) < LOOKBACK_DAYS:
        return None
    previous = completed[0]
    last = completed[:LOOKBACK_DAYS]
    avg_volume = sum(x["volume"] for x in last) / LOOKBACK_DAYS
    avg_turnover = sum(x["close"] * x["volume"] for x in last) / LOOKBACK_DAYS
    if avg_volume <= 0:
        return None
    return {
        "previous_close": previous["close"],
        "previous_volume": previous["volume"],
        "average_volume": avg_volume,
        "average_turnover": avg_turnover,
    }


def daily_stats_for_date(key, selected_date):
    candles = daily_history(key, selected_date)
    if candles is None:
        raise RuntimeError("Historical daily API request failed")
    rows = parse_daily_rows(candles)
    target = None
    prior = []
    for row in rows:
        try:
            row_date = parse_ts(row["ts"]).date()
        except Exception:
            continue
        if row_date == selected_date:
            target = row
        elif row_date < selected_date and len(prior) < LOOKBACK_DAYS:
            prior.append(row)
    if target is None or len(prior) < LOOKBACK_DAYS:
        return None
    avg_volume = sum(x["volume"] for x in prior) / LOOKBACK_DAYS
    avg_turnover = sum(x["close"] * x["volume"] for x in prior) / LOOKBACK_DAYS
    if avg_volume <= 0:
        return None
    return {
        "target_open": target["open"],
        "target_high": target["high"],
        "target_low": target["low"],
        "target_close": target["close"],
        "target_volume": target["volume"],
        "previous_close": prior[0]["close"],
        "previous_volume": prior[0]["volume"],
        "average_volume": avg_volume,
        "average_turnover": avg_turnover,
    }


# DAILY CACHE
def load_daily_cache():
    data = load_json(DAILY_CACHE)
    if data.get("date") == today_s() and isinstance(data.get("stats"), dict):
        return data["stats"]
    return {}


def save_daily_cache(cache):
    save_json(DAILY_CACHE, {"date": today_s(), "stats": cache})


# INTRADAY DATA
def intraday(key, selected_date=None):
    selected_date = selected_date or today()
    encoded_key = quote(key, safe="|")
    if selected_date == today():
        url = f"{BASE}/v3/historical-candle/intraday/{encoded_key}/minutes/1"
    else:
        url = f"{BASE}/v3/historical-candle/{encoded_key}/minutes/1/{selected_date.isoformat()}/{selected_date.isoformat()}"
    r = session().get(url, timeout=TIMEOUT)
    if r.status_code != 200:
        logging.warning("Intraday API error %s: %s", key, r.status_code)
        return []
    candles = r.json().get("data", {}).get("candles", [])
    return candles if isinstance(candles, list) else []


# VOLUME MULTIPLE TIMES: 0.20x, 0.25x, 0.5x AND 1x TO 6x
def volume_times(key, average_volume, selected_date, multiplier, candles=None):
    """Calculate volume milestones and the latest completed post-detection candle close."""
    output = {f"time_{n}x": None for n in range(1, 7)}
    output.update({"time_020": None, "time_quarter": None, "time_half": None})
    output.update({
        "detection_time": None, "detection_price": None,
    })
    if average_volume is None or average_volume <= 0:
        return output
    if candles is None:
        try:
            candles = intraday(key, selected_date)
        except Exception as e:
            logging.warning("Intraday request failed for %s: %r", key, e)
            return output

    rows = []
    seen_minutes = set()
    session_start, session_end = 9 * 60 + 15, 15 * 60 + 30
    now = now_ist()
    for c in candles:
        if not isinstance(c, list) or len(c) < 6:
            continue
        try:
            ts = parse_ts(c[0]).replace(second=0, microsecond=0)
            if ts.date() != selected_date:
                continue
            minute_of_day = ts.hour * 60 + ts.minute
            if not (session_start <= minute_of_day < session_end):
                continue
            if selected_date == today() and ts + timedelta(minutes=1) > now:
                continue
            if ts in seen_minutes:
                continue
            open_price, high_price, close_price = float(c[1]), float(c[2]), float(c[4])
            volume = float(c[5])
            if volume < 0 or min(open_price, high_price, close_price) <= 0:
                continue
            seen_minutes.add(ts)
            rows.append((ts, volume, open_price, close_price, high_price))
        except Exception:
            continue

    rows.sort(key=lambda x: x[0])
    cumulative, found = 0.0, set()
    threshold_020_found = False
    quarter_found = False
    half_found = False
    for ts, volume, open_price, close_price, high_price in rows:
        cumulative += volume
        event_time = ts + timedelta(minutes=1)
        time_text = event_time.strftime("%I:%M %p").lstrip("0")
        if not threshold_020_found and cumulative >= average_volume * 0.20:
            output["time_020"] = time_text
            threshold_020_found = True
        if not quarter_found and cumulative >= average_volume * 0.25:
            output["time_quarter"] = time_text
            quarter_found = True
        if not half_found and cumulative >= average_volume * 0.50:
            output["time_half"] = time_text
            half_found = True
        for n in range(1, 7):
            if n not in found and cumulative >= average_volume * n:
                output[f"time_{n}x"] = time_text
                found.add(n)
        if output["detection_time"] is None and cumulative >= average_volume * multiplier:
            output["detection_time"] = time_text
            output["detection_price"] = close_price
    # Detection Price/Time remain tied to the selected Volume Multiple threshold.
    return output





def attach_volume_times(results, time_cache, selected_date, multiplier, jid=None):
    """Calculate required volume milestones for all scored NSE candidates before final Top 20 selection."""
    if not results:
        return

    required_keys = ["time_020", "time_quarter", "time_half"] + [f"time_{n}x" for n in range(1, 7)] + [
        "detection_time", "detection_price",
    ]
    is_live_date = selected_date == today()
    cache_changed = False

    def calculate_one(result):
        key = result["instrument_key"]
        cached = time_cache.get(key)
        cache_valid = (
            not is_live_date
            and isinstance(cached, dict)
            and cached.get("_multiplier") == multiplier
            and cached.get("_volume_time_rule_version") == "volume_top30_v8_add_020_milestone"
            and all(field in cached for field in required_keys)
        )
        if cache_valid:
            return key, {field: cached.get(field) for field in required_keys}, False

        candles = intraday(key, selected_date)
        values = volume_times(key, result["average_volume"], selected_date, multiplier, candles=candles)
        return key, {field: values.get(field) for field in required_keys}, True

    result_by_key = {result["instrument_key"]: result for result in results}
    max_workers = min(8, len(results))
    with ThreadPoolExecutor(max_workers=max(1, max_workers)) as executor:
        futures = [executor.submit(calculate_one, result) for result in results]
        for future in as_completed(futures):
            try:
                key, values, recomputed = future.result()
                result = result_by_key.get(key)
                if result is None:
                    continue
                result.update(values)
                if recomputed:
                    time_cache[key] = {
                        **values, "_multiplier": multiplier,
                        "_volume_time_rule_version": "volume_top30_v8_add_020_milestone",
                    }
                    cache_changed = True
            except Exception as exc:
                logging.warning("Required volume-time calculation failed: %r", exc)

    if cache_changed:
        save_json(time_cache_path(selected_date), time_cache)


# SCORING SYSTEM: 100 POINTS MAXIMUM
def calculate_strength_score(result):
    """Final comparative scoring is performed in sort_results_by_score after all shares are collected."""
    result["strength_score"] = 0.0
    return 0.0


def apply_strength_score(result):
    # Provisional score is replaced after all qualifying shares have been collected.
    result["strength_score"] = 0.0
    return result


def _safe_number(value):
    try:
        number = float(value or 0)
        return number if math.isfinite(number) else 0.0
    except (TypeError, ValueError):
        return 0.0


def _daily_gain_score(gain):
    """Gain score: 4 points per 1% positive gain, capped at 40."""
    if gain is None or not math.isfinite(gain) or gain <= 0:
        return 0.0
    return min(gain * 4.0, 40.0)


def _vratio_score(vratio):
    """V.Ratio score: 50/6 points per 1.0x, capped at 50."""
    value = max(0.0, _safe_number(vratio))
    return min(value * (50.0 / 6.0), 50.0)


def _volume_multiple_score(volume_multiple):
    """Volume Multiple score: 3 points per 1.0x, capped at 60."""
    value = max(0.0, _safe_number(volume_multiple))
    return min(value * 3.0, 60.0)


def apply_opening_gap_filter(results):
    """Calculate Open-Low Gap for display only; do not filter shares by it."""
    for result in results:
        open_price = _safe_number(result.get("open"))
        low_price = _safe_number(result.get("day_low"))
        if open_price > 0 and low_price > 0:
            result["open_low_gap_pct"] = ((open_price - low_price) / open_price) * 100.0
        else:
            result["open_low_gap_pct"] = None
    return results


def sort_results_by_score(results):
    """
    Capped score:
    positive Daily Gain% = min(gain * 4, 40);
    Volume Multiple = min(multiple * 3, 60);
    V.Ratio = min(ratio * (50/6), 50).
    Open-to-Low Gap% is informational only and does not affect eligibility or score.
    Total score cannot exceed 150.
    """
    if not results:
        return results

    scored = []
    pending = []
    for result in results:
        previous_close = _safe_number(result.get("previous_close"))
        ltp = _safe_number(result.get("ltp"))
        open_price = _safe_number(result.get("open"))
        previous_volume = _safe_number(result.get("previous_volume"))
        today_volume = _safe_number(result.get("today_volume"))

        daily_gain = ((ltp - previous_close) / previous_close * 100.0) if previous_close > 0 else None
        low_price = _safe_number(result.get("day_low"))
        opening_gap = ((open_price - low_price) / open_price * 100.0) if open_price > 0 and low_price > 0 else None

        result["gain_pct"] = daily_gain
        result["opening_gap_pct"] = ((open_price - previous_close) / previous_close * 100.0) if open_price > 0 and previous_close > 0 else None
        result["_score_vratio"] = today_volume / previous_volume if previous_volume > 0 else 0.0

        if daily_gain is None:
            result.update({
                "gain_score": None, "volume_score": None, "gain_vol_score": None,
                "vratio_score": None, "gap_score": None, "strength_score": None,
            })
            pending.append(result)
            continue

        result["_score_gain_pct"] = _safe_number(daily_gain)
        result["_score_gap_pct"] = _safe_number(opening_gap) if opening_gap is not None else 0.0
        result["volume_score"] = round(
            _volume_multiple_score(result.get("volume_multiple")), 2
        )
        scored.append(result)

    if scored:
        for result in scored:
            result["gain_score"] = round(
                _daily_gain_score(result["_score_gain_pct"]), 2
            )
            result["gain_vol_score"] = round(
                result["gain_score"] + result["volume_score"], 2
            )
            result["vratio_score"] = round(
                _vratio_score(result["_score_vratio"]), 2
            )
            result["gap_score"] = 0.0
            result["strength_score"] = round(
                result["volume_score"] + result["vratio_score"] + result["gain_score"], 2
            )

        scored.sort(key=lambda r: (
            -r["strength_score"],
            -r["_score_gain_pct"],
            _safe_number(r.get("volume_multiple")),
            -r["_score_vratio"],
            abs(r["_score_gap_pct"]),
        ))

    results[:] = scored + pending

    # VELOCITY: percentage change in each share's strength score
    # compared with that share's score in the previous completed scan.
    global PREVIOUS_SCORES
    for res in results:
        sym = res.get("symbol")
        curr_s = float(res.get("strength_score") or 0)
        old_s = PREVIOUS_SCORES.get(sym, curr_s)
        vel = ((curr_s - old_s) / old_s * 100.0) if old_s > 0 else 0.0
        res["velocity"] = round(vel, 2)
        PREVIOUS_SCORES[sym] = curr_s

    return results


# LIVE SCANNER HELPERS
def live_candidate(inst, q):
    if not q:
        return None
    try:
        ltp = float(q.get("last_price") or 0)
        volume = float(q.get("volume") or 0)
        ohlc = q.get("ohlc") or {}
        op = float(ohlc.get("open") or 0)
        day_high = float(ohlc.get("high") or 0)
        day_low = float(ohlc.get("low") or 0)
    except (TypeError, ValueError):
        return None
    if not (MIN_PRICE < ltp < MAX_PRICE_EXCLUSIVE) or op <= 0 or ltp <= op or volume <= 0:
        return None
    return {"instrument_key": inst["key"], "symbol": inst["symbol"], "ltp": ltp, "open": op,
            "day_high": day_high, "day_low": day_low, "today_volume": volume}


def build_result(candidate, stats, multiplier):
    if not stats:
        return None
    try:
        avg = float(stats["average_volume"])
        prev_volume = float(stats["previous_volume"])
        turnover = float(stats["average_turnover"])
        volume = float(candidate["today_volume"])
    except (KeyError, TypeError, ValueError):
        return None
    if avg <= 0:
        return None
    if volume < avg * multiplier or turnover < MIN_AVG_TURNOVER:
        return None
    result = {
        "instrument_key": candidate["instrument_key"], "symbol": candidate["symbol"],
        "previous_close": float(stats["previous_close"]), "open": candidate["open"],
        "day_high": candidate.get("day_high"), "day_low": candidate.get("day_low"),
        "ltp": candidate["ltp"], "previous_volume": prev_volume, "today_volume": volume,
        "average_volume": avg, "total_volume_multiple": volume / avg, "volume_multiple": volume / avg, "average_turnover": turnover,
    }
    return apply_strength_score(result)


# HISTORICAL SCAN
def run_historical_scan(jid, multiplier, selected_date):
    try:
        with JOBS_LOCK:
            JOBS[jid] = {"status": "running", "message": "Historical scan start ho raha hai...", "results": [], "error": None}
        items = load_instruments()
        stats_path = history_cache_path(selected_date)
        stats_cache = load_json(stats_path)
        time_cache = load_json(time_cache_path(selected_date))
        missing = [inst for inst in items if inst["key"] not in stats_cache]
        progress(jid, f"{len(items)} shares; historical data {len(missing)} shares ka baaki hai...")
        results = []

        def make_result(inst, stats):
            if not isinstance(stats, dict) or stats.get("_no_data"):
                return None
            try:
                avg = float(stats["average_volume"]); volume = float(stats["target_volume"])
                prev_volume = float(stats["previous_volume"]); turnover = float(stats["average_turnover"])
                op = float(stats["target_open"]); close = float(stats["target_close"])
                previous_close = float(stats["previous_close"])
            except (KeyError, TypeError, ValueError):
                return None
            if avg <= 0 or not (MIN_PRICE < close < MAX_PRICE_EXCLUSIVE) or close <= op:
                return None
            if volume < avg * multiplier or turnover < MIN_AVG_TURNOVER:
                return None
            result = {
                "instrument_key": inst["key"], "symbol": inst["symbol"], "previous_close": previous_close,
                "open": op, "day_high": stats.get("target_high"), "day_low": stats.get("target_low"),
                "ltp": close, "previous_volume": prev_volume, "today_volume": volume,
                "average_volume": avg, "total_volume_multiple": volume / avg, "volume_multiple": volume / avg, "average_turnover": turnover,
            }
            return apply_strength_score(result)

        for inst in items:
            result = make_result(inst, stats_cache.get(inst["key"]))
            if result:
                results.append(result)
        completed = 0
        if missing:
            with ThreadPoolExecutor(max_workers=HISTORICAL_SCAN_WORKERS) as executor:
                futures = {executor.submit(daily_stats_for_date, inst["key"], selected_date): inst for inst in missing}
                for future in as_completed(futures):
                    inst = futures[future]
                    try:
                        stats = future.result()
                        stats_cache[inst["key"]] = stats if stats else {"_no_data": True}
                        result = make_result(inst, stats)
                        if result:
                            results.append(result)
                    except Exception as e:
                        logging.warning("Historical data error %s: %r", inst["symbol"], e)
                    completed += 1
                    if completed % HISTORICAL_PROGRESS_STEP == 0 or completed == len(missing):
                        save_json(stats_path, stats_cache)
                        progress(jid, f"Historical data {completed}/{len(missing)}; matches {len(results)}")
            save_json(stats_path, stats_cache)
        # Evaluate Detection Price for every NSE candidate that passed the existing
        # quote/history/score filters. Only after this full-universe eligibility
        # check do we rank and select the final Top 20.
        sort_results_by_score(results)
        apply_opening_gap_filter(results)
        if results:
            attach_volume_times(results, time_cache, selected_date, multiplier)
        eligible_results = filter_detection_below_previous_close(results)
        sort_results_by_score(eligible_results)
        displayed = eligible_results[:TOP_RESULTS]
        minus_top5_results, plus_top5_results = split_top20_gain_results(displayed)
        if displayed:
            scan_time = detection_clock()
            for result in displayed:
                result["scan_run_time"] = scan_time
            message = (
                f"{selected_date.isoformat()} ka scan complete. Sabhi eligible NSE candidates mein "
                f"Detection Price < Previous Close shart lagane ke baad {len(eligible_results)} shares mile. "
                f"TOP 20 dikhaye ja rahe hain. Sabse majboot share: "
                f"{displayed[0]['symbol']} (Score {displayed[0].get('strength_score', 0)}, "
                f"{displayed[0]['volume_multiple']:.2f}x volume)."
            )
        else:
            message = f"{selected_date.isoformat()} ko Detection Price < Previous Close shart wala koi share nahi mila."
        if selected_date < today() - timedelta(days=30):
            message += " Purane din ka 1-minute data Upstox par available na bhi ho sakta hai."
        with JOBS_LOCK:
            JOBS[jid] = {
                "status": "complete", "message": message, "results": displayed,
                "minus_top5_results": minus_top5_results,
                "plus_top5_results": plus_top5_results,
                "total_matches": len(eligible_results), "error": None,
            }
    except Exception as e:
        logging.exception("Historical scan failed")
        with JOBS_LOCK:
            JOBS[jid] = {"status": "error", "message": "Historical scan mein error aaya.", "results": [], "error": str(e)}


# LIVE SCAN
def run_scan(jid, multiplier, selected_date):
    if selected_date != today():
        run_historical_scan(jid, multiplier, selected_date)
        return
    try:
        with JOBS_LOCK:
            JOBS[jid] = {"status": "running", "message": "NSE shares load ho rahe hain...", "results": [], "error": None}
        items = load_instruments()
        progress(jid, f"{len(items)} shares ke live quotes liye ja rahe hain...")
        quotes = get_quotes(items)
        candidates = []
        for inst in items:
            candidate = live_candidate(inst, quotes.get(inst["key"]))
            if candidate:
                candidates.append(candidate)
        progress(jid, f"{len(candidates)} live candidates; daily history check ho rahi hai...")
        cache = load_daily_cache()
        missing = [c for c in candidates if c["instrument_key"] not in cache]
        completed = 0

        # Keep the main TOP 20 table empty while history and Detection checks run.
        # Publish only the completed, fully validated final TOP 20.
        if missing:
            with ThreadPoolExecutor(max_workers=HISTORY_WORKERS) as executor:
                futures = {executor.submit(daily_stats, c["instrument_key"]): c for c in missing}
                for future in as_completed(futures):
                    candidate = futures[future]
                    key = candidate["instrument_key"]
                    try:
                        stats = future.result()
                        if stats:
                            cache[key] = stats
                    except Exception as e:
                        logging.warning("Daily stats error %s: %r", candidate["symbol"], e)
                    completed += 1
                    if completed % 25 == 0 or completed == len(missing):
                        save_daily_cache(cache)
                        progress(jid, f"Daily history {completed}/{len(missing)} complete; cache {len(cache)}")
            save_daily_cache(cache)
        results = []
        for candidate in candidates:
            result = build_result(candidate, cache.get(candidate["instrument_key"]), multiplier)
            if result:
                results.append(result)
        # Score all eligible NSE candidates, calculate Detection Price for all,
        # then apply the user's Detection Price < Previous Close rule and select Top 20.
        sort_results_by_score(results)
        apply_opening_gap_filter(results)
        detection_candidates = results
        scan_time = detection_clock()
        if results:
            message = (
                f"{len(results)} qualifying candidates mile. Detection Price check ke baad "
                f"sirf Det.Price < Prev.Close wale TOP 20 dikhaye jayenge."
            )
        else:
            message = "Koi share selected conditions meet nahi karta."
        with JOBS_LOCK:
            JOBS[jid] = {
                "status": "running", "message": message,
                "results": [],
                "results_ready": False, "results_version": completed + 1,
                "minus_top5_results": [], "plus_top5_results": [],
                "total_matches": len(results), "error": None,
            }
        if detection_candidates:
            time_cache = load_json(time_cache_path(selected_date))
            attach_volume_times(detection_candidates, time_cache, selected_date, multiplier, jid=jid)
            eligible_results = filter_detection_below_previous_close(detection_candidates)
            sort_results_by_score(eligible_results)
            displayed = eligible_results[:TOP_RESULTS]
            for result in displayed:
                result["scan_run_time"] = scan_time
            minus_top5_results, plus_top5_results = split_top20_gain_results(displayed)
            with JOBS_LOCK:
                JOBS[jid] = {
                    "status": "complete", "message": f"Detection Price < Previous Close shart par {len(eligible_results)} shares mile; TOP 20 aur PLUS/MINUS Top 5 update ho gaye.",
                    "results": [dict(item) for item in displayed],
                    "results_ready": bool(displayed), "results_version": completed + 2,
                    "minus_top5_results": minus_top5_results,
                    "plus_top5_results": plus_top5_results,
                    "total_matches": len(eligible_results), "error": None,
                }
        else:
            with JOBS_LOCK:
                JOBS[jid] = {
                    "status": "complete",
                    "message": "Koi eligible NSE candidate nahi mila jiska Detection Price Previous Close se kam ho.",
                    "results": [], "results_ready": False,
                    "minus_top5_results": [], "plus_top5_results": [],
                    "total_matches": 0, "error": None,
                }
    except Exception as e:
        logging.exception("Live scan failed")
        with JOBS_LOCK:
            JOBS[jid] = {"status": "error", "message": "Scan mein error aaya.", "results": [], "error": str(e)}


HTML = r"""
<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>NSE VOLUME SCANNER</title>
<style>
* { box-sizing: border-box; }
body { margin:0; padding:20px; background:#0b1220; color:#e5e7eb; font-family:Arial,sans-serif; }
.container { max-width:1800px; margin:auto; }
h1 { font-size:28px; margin-bottom:12px; }
.subtitle { color:#94a3b8; line-height:1.5; margin-bottom:24px; }
.controls { display:flex; flex-wrap:wrap; gap:12px; align-items:center; margin-bottom:18px; }
input,select,button { padding:12px; border:1px solid #334155; border-radius:9px; font-size:15px; }
input,select { background:#111827; color:white; }
button { background:#2563eb; color:white; border:0; font-weight:bold; cursor:pointer; }
button:disabled { opacity:.55; cursor:wait; }
.status { margin:12px 0; color:#cbd5e1; }
.message { padding:14px; background:#111827; border-radius:10px; margin-bottom:16px; line-height:1.5; overflow-wrap:anywhere; }
.table-wrap { width:100%; overflow-x:auto; border:1px solid #263244; border-radius:10px; }
table { width:100%; min-width:1500px; border-collapse:collapse; table-layout:auto; }
th,td { padding:7px 6px; border-bottom:1px solid #263244; text-align:right; white-space:nowrap; font-size:12px; }
th { background:#111827; color:#cbd5e1; font-size:11px; line-height:1.2; }
th:first-child,td:first-child { text-align:left; }
.symbol { color:#f8fafc; font-weight:bold; }

/* Main TOP 20: Detection Price yellow; keep its value prominent. */
#results td.detect-price { color:#facc15 !important; font-weight:700 !important; }

/* Blue highlight: entire row when Volume Multiple is greater than V.Ratio. */
tr.blue-volume-row td {
    background: #173b70 !important;
    color: #eff6ff !important;
}
tr.blue-volume-row td.detect-price,
tr.blue-volume-row td.multiple,
tr.blue-volume-row td.vratio {
    color: #fde047 !important;
    font-weight: 700 !important;
}
.gain-top-panel { margin-top:18px; background:#111c2e; border:1px solid #315d91; border-radius:14px; padding:14px; }
.gain-top-panel h2 { margin:0 0 8px; color:#8fc4ff; font-size:18px; }
.gain-top-explain { color:#94a3b8; font-size:13px; margin-bottom:12px; line-height:1.5; }
.gain-top-panel table { width:100%; min-width:700px; border-collapse:collapse; }
.gain-top-panel th,.gain-top-panel td { padding:9px 7px; border-bottom:1px solid #263449; text-align:right; white-space:nowrap; font-size:12px; }
.gain-top-panel th { color:#dbeafe; background:#1b2b43; }
.gain-top-panel th:nth-child(2),.gain-top-panel td:nth-child(2) { text-align:left; }
.gain-top-panel td:nth-child(2) { color:#bfdbfe; font-weight:700; }

/* PLUS/MINUS TOP 5: Highlight Gap%, Det. Time, Det. Price and LTP in yellow. */
.gain-top-panel th:nth-child(3),
.gain-top-panel td:nth-child(3),
.gain-top-panel th:nth-child(5),
.gain-top-panel td:nth-child(5),
.gain-top-panel th:nth-child(6),
.gain-top-panel td:nth-child(6),
.gain-top-panel th:nth-child(7),
.gain-top-panel td:nth-child(7) {
    color: #facc15 !important;
    font-weight: 700 !important;
}

.multiple { color:#facc15; font-weight:bold; }
.total-volume-multiple { color:#facc15; font-weight:bold; }
.score { color:#a7f3d0; font-weight:bold; }
.gain { color:#facc15; font-weight:bold; }
.gap { color:#ffffff; font-weight:bold; }
.time { color:#67e8f9; font-weight:bold; }
.detection { color:#86efac; font-weight:bold; }
.candle-green { color:#4ade80; font-weight:bold; }
.candle-red { color:#f87171; font-weight:bold; }
.no-time { color:#64748b; }
.auto-controls { display:flex; flex-wrap:wrap; gap:10px; align-items:center; padding:12px; margin:0 0 18px; background:#111827; border:1px solid #263244; border-radius:10px; }
.auto-status { color:#cbd5e1; font-size:14px; }
.toggle-label { display:flex; align-items:center; gap:8px; }
#autoScan { width:20px; height:20px; accent-color:#2563eb; }
.note { color:#94a3b8; font-size:13px; margin-top:12px; line-height:1.6; }

/* Requested column colors: Volume Multiple yellow; Gap% white. */
.vratio { color:#facc15 !important; font-weight:bold; }
.one-x { color:#facc15 !important; font-weight:bold; }

@media(max-width:650px) {
    body { padding:12px; }
    h1 { font-size:24px; }
    th,td { padding:7px 6px; }
}

td.open-price,
td.same-time-speed {
    color: #facc15 !important;
    font-weight: 700 !important;
}


 .early-panel { margin-top: 24px; padding: 16px; border: 1px solid #334155; border-radius: 10px; background: #101b2d; }
.early-panel h2 { margin: 0 0 8px; font-size: 20px; color: #86efac; }
.early-explain { color: #94a3b8; font-size: 13px; line-height: 1.5; margin-bottom: 12px; }
.early-panel table { width: 100%; min-width: 0 !important; border-collapse: collapse; table-layout: fixed; }
.early-panel .table-wrap { overflow-x: hidden; }
.early-panel th, .early-panel td { font-size: 11px; padding: 8px 4px; }
.early-panel th:nth-child(1), .early-panel td:nth-child(1) { width: 10%; }
.early-panel th:nth-child(2), .early-panel td:nth-child(2) { width: 29%; overflow-wrap: anywhere; }
.early-panel th:nth-child(3), .early-panel td:nth-child(3) { width: 16%; }
.early-panel th:nth-child(4), .early-panel td:nth-child(4) { width: 15%; }
.early-panel th:nth-child(5), .early-panel td:nth-child(5) { width: 30%; }
.early-panel th, .early-panel td { padding: 9px 10px; border-bottom: 1px solid #263449; text-align: right; white-space: nowrap; }
.early-panel th:nth-child(2), .early-panel td:nth-child(2) { text-align: left; }
.early-panel th { color: #cbd5e1; background: #172338; }
.early-name { color: #86efac; font-weight: 700; }
</style>
</head>
<body>
<div class="container">
<h1>NSE VOLUME SCANNER</h1>
<div class="subtitle">
NSE Equity Only | ₹100 &lt; Price &lt; ₹2,000 | Full NSE Detection Check | Top 20 Shares | 20-Day Avg Turnover ≥ ₹5 Cr | Historical data cache enabled | Open-Low Gap shown for information only |
Selected Date Volume
</div>
<div class="controls">
<label for="scanDate">Date:</label>
<input id="scanDate" type="date" value="{{ today_date }}" max="{{ today_date }}">
<label for="multiplier">Volume Multiplier:</label>
<select id="multiplier">
<option value="0.20" selected>0.20× (20%)</option><option value="0.25">¼× (0.25×)</option><option value="0.5">½× (0.5×)</option>
<option value="1">1×</option><option value="2">2×</option><option value="3">3×</option>
<option value="4">4×</option><option value="5">5×</option><option value="6">6×</option>
<option value="7">7×</option><option value="8">8×</option><option value="9">9×</option><option value="10">10×</option>
</select>
<button id="scanBtn" onclick="startScan()">SCAN</button>
</div>
<div class="auto-controls">
<label class="toggle-label" for="autoScan"><input id="autoScan" type="checkbox"> Auto Scan</label>
<span class="auto-status" id="autoStatus">Auto Scan बंद है।</span>
<label for="autoInterval">Interval:</label>
<select id="autoInterval">
<option value="30">30 सेकंड</option><option value="60" selected>60 सेकंड (1 मिनट)</option>
<option value="120">120 सेकंड (2 मिनट)</option><option value="300">300 सेकंड (5 मिनट)</option>
</select>
</div>
<div id="status" class="status">Ready.</div>
<div id="message" class="message">Manual Scan शुरू करने के लिए SCAN बटन दबाएँ।</div>
<div class="table-wrap">
<table><thead><tr>
<th>Rank</th><th>Sym</th><th>Score</th><th>Gap%</th><th>Det.Time</th><th>Det.Price</th><th>Prev.Close</th><th>LTP</th><th>Open</th><th>Low Price</th><th>High Price</th><th>Gain%</th><th>Vol×</th><th>V.Ratio</th><th>Open-Low Gap%</th>
<th>Prev.Vol</th><th>Today.Vol</th><th>Avg.Vol20D</th>
<th>Avg.Turn</th><th>0.20× Time</th><th>¼ Time</th><th>½ Time</th><th>1×</th><th>2×</th><th>3×</th>
<th>4×</th><th>5×</th><th>6×</th>

</tr></thead><tbody id="results"><tr><td colspan="28" style="text-align:center">No result yet.</td></tr></tbody></table>
</div>

<div class="gain-top-panel">
  <h2>MINUS TOP 5</h2>
  <div class="gain-top-explain">Final TOP 20 में से केवल Negative Gain% वाले शेयर। Score = मुख्य TOP 20 वाला वही strength_score। Gain% केवल PLUS या MINUS सूची चुनने के लिए है।</div>
  <div class="table-wrap"><table>
    <thead><tr><th>Rank</th><th>Share</th><th>Gap%</th><th>Score</th><th>Det. Time</th><th>Det.Price</th><th>Prev.Close</th><th>LTP</th><th>Open</th><th>Vol.*</th><th>V.Ratio</th><th>Gain%</th></tr></thead>
    <tbody id="minusBlueTopResults"><tr><td colspan="12" style="text-align:center">Minus Gain results ka intezar hai.</td></tr></tbody>
  </table></div>
</div>
<div class="gain-top-panel">
  <h2>PLUS TOP 5</h2>
  <div class="gain-top-explain">Final TOP 20 में से केवल Positive Gain% वाले शेयर। Score = मुख्य TOP 20 वाला वही strength_score। Gain% केवल PLUS या MINUS सूची चुनने के लिए है।</div>
  <div class="table-wrap"><table>
    <thead><tr><th>Rank</th><th>Share</th><th>Gap%</th><th>Score</th><th>Det. Time</th><th>Det.Price</th><th>Prev.Close</th><th>LTP</th><th>Open</th><th>Vol.*</th><th>V.Ratio</th><th>Gain%</th></tr></thead>
    <tbody id="plusBlueTopResults"><tr><td colspan="12" style="text-align:center">Plus Gain results ka intezar hai.</td></tr></tbody>
  </table></div>
</div>

</div>
<div class="note">
<strong>Main Top 20 Score calculation (अधिकतम 150 अंक):</strong>
तीनों मापदंडों के अंक जोड़कर कुल स्कोर बनता है. Gain के अधिकतम 40, Volume Multiple के अधिकतम 60 और V.Ratio के अधिकतम 50 अंक हैं.
Gain अंक = min(Positive Gain% × 4, 40); शून्य या negative Gain पर 0 अंक.
Volume अंक = min(Volume Multiple × 3, 60).
V.Ratio अंक = min(V.Ratio × (50 ÷ 6), 50).
कुल स्कोर अधिकतम 150 होगा. किसी एक मापदंड के संदर्भ मान तक पहुँचने के बाद उस मापदंड के अंक और नहीं बढ़ेंगे.
Gap% = (Open Price − Previous Close) ÷ Previous Close × 100; यह Opening Gap है और केवल जानकारी के लिए दिखाया जाता है, eligibility या score को प्रभावित नहीं करता. Open-Low Gap% = (Open Price − Low Price) ÷ Open Price × 100; यह अलग कॉलम है और केवल जानकारी के लिए है.
Price eligibility: शेयर का LTP/selected-date close strictly ₹100 से अधिक और ₹2,000 से कम होना चाहिए. ठीक ₹100 या ₹2,000 शामिल नहीं होंगे. Open-Low Gap पर कोई eligibility सीमा लागू नहीं है; सभी अन्य शर्तें यथावत हैं.
Open-Low Gap% केवल जानकारी के लिए है; इसके कोई score points नहीं हैं.
<strong>PLUS TOP 5 और MINUS TOP 5 Score:</strong> दोनों सूचियों में मुख्य TOP 20 के लिए पहले से निकाला गया वही strength_score इस्तेमाल होता है. कोई अलग score या अतिरिक्त score calculation नहीं होती. Gain% केवल PLUS (positive) या MINUS (negative) सूची चुनने के लिए है. दोनों सूचियों में strength_score सबसे अधिक वाला शेयर Rank 1 होगा.
Price Momentum का कोई अलग score नहीं है. Main Top 20 का कुल स्कोर अधिकतम 150 है.
0.20× Time = cumulative intraday volume ke 20-day average daily volume ke 20% tak pahunchne wali pehli completed 1-minute candle ka close/availability time. ¼ Time = isi tarah 25% threshold ka pehla samay. ½ Time = isi tarah 50% threshold ka pehla samay. 1× se 6× Time bhi isi niyam se calculate hote hain. Detection Time (Volume Threshold) = selected multiplier tak pahunchne wali completed 1-minute candle ke close/availability ka samay. Yeh browser par result dikhne ka samay nahi hai. Live scan mein adhuri current candle shamil nahi hoti. Eligibility ke liye aaj ka cumulative volume sirf 20-day average daily volume × selected multiplier se compare hota hai; pichhle din ka poora volume cross karna zaroori nahi hai. Prev.Vol column aur V.Ratio sirf reference/scoring ke liye hain.
EMA20, Stoch RSI, MACD aur Bearish signal ki columns aur unki calculations load kam karne ke liye hata di gayi hain.
</div>
</div>
<script>
let scanInProgress = false;
let autoTimer = null;
let currentJobId = null;
let lastRenderedResultsVersion = null;

function numberFormat(v) {
    if (v == null || v === "") return "-";
    return Number(v).toLocaleString("en-IN", {maximumFractionDigits:0});
}
function priceFormat(v) {
    if (v == null || v === "") return "-";
    return Number(v).toFixed(2);
}
function turnoverFormat(v) {
    if (v == null || v === "") return "-";
    v = Number(v);
    if (v >= 10000000) return (v / 10000000).toFixed(2) + " Cr";
    if (v >= 100000) return (v / 100000).toFixed(2) + " L";
    return numberFormat(v);
}
function timeCell(v, cls="time") {
    if (!v) return '<span class="no-time">—</span>';
    return '<span class="' + cls + '">' + v + '</span>';
}
function render(rows) {
    const body = document.getElementById("results");
    if (!rows || rows.length === 0) {
        body.innerHTML = '<tr><td colspan="28" style="text-align:center">No share meets the selected conditions.</td></tr>';
        return;
    }
    body.innerHTML = rows.slice(0,20).map((r, i) => {
        const volumeMultiple = Number(r.volume_multiple);
        const vratio = Number(r.previous_volume) > 0
            ? Number(r.today_volume) / Number(r.previous_volume) : 0;
        const blueRow = Number.isFinite(volumeMultiple) && Number.isFinite(vratio) && volumeMultiple > vratio;
        return `
    <tr class="${blueRow ? 'blue-volume-row' : ''}">
      <td class="rank">${i + 1}</td>
            <td class="symbol">${r.symbol || "-"}</td>
      <td class="score">${r.strength_score != null ? Number(r.strength_score).toFixed(2) : "-"}</td>
      <td class="gap">${r.opening_gap_pct != null ? Number(r.opening_gap_pct).toFixed(2) + "%" : "-"}</td>
      <td>${timeCell(r.detection_time,"detection")}</td>
      <td class="detect-price">${r.detection_price != null ? priceFormat(r.detection_price) : "-"}</td>
      <td>${priceFormat(r.previous_close)}</td>
      <td class="ltp-price">${priceFormat(r.ltp)}</td>
      <td class="open-price">${priceFormat(r.open)}</td>
      <td>${priceFormat(r.day_low)}</td>
      <td>${priceFormat(r.day_high)}</td>
      <td class="gain">${r.gain_pct != null ? Number(r.gain_pct).toFixed(2) + "%" : "-"}</td>
      <td class="multiple">${Number(r.volume_multiple).toFixed(2)}×</td>
      <td class="vratio">${Number(r.previous_volume) > 0 ? (Number(r.today_volume) / Number(r.previous_volume)).toFixed(2) + "×" : "-"}</td>
      <td class="gap">${r.open_low_gap_pct != null ? Number(r.open_low_gap_pct).toFixed(2) + "%" : "-"}</td>
      <td>${numberFormat(r.previous_volume)}</td><td>${numberFormat(r.today_volume)}</td>
      <td>${numberFormat(r.average_volume)}</td>
      <td>${turnoverFormat(r.average_turnover)}</td>
      <td>${timeCell(r.time_020)}</td><td>${timeCell(r.time_quarter)}</td><td>${timeCell(r.time_half)}</td>
      <td>${timeCell(r.time_1x,"one-x")}</td><td>${timeCell(r.time_2x)}</td><td>${timeCell(r.time_3x)}</td>
      <td>${timeCell(r.time_4x)}</td><td>${timeCell(r.time_5x)}</td><td>${timeCell(r.time_6x)}</td>
    </tr>`;
    }).join("");

}
function renderBlueTop(minusRows, plusRows) {
    const renderList = (elementId, rows, emptyText) => {
        const body = document.getElementById(elementId);
        if (!body) return;
        if (!rows || rows.length === 0) {
            body.innerHTML = `<tr><td colspan="12" style="text-align:center">${emptyText}</td></tr>`;
            return;
        }
        body.innerHTML = rows.slice(0, 5).map((r, i) => {
            const gap = r.opening_gap_pct != null ? Number(r.opening_gap_pct) : null;
            const volMultiple = Number(r.volume_multiple);
            const vratio = Number(r.previous_volume) > 0 ? Number(r.today_volume) / Number(r.previous_volume) : 0;
            const blueRow = Number.isFinite(volMultiple) && Number.isFinite(vratio) && volMultiple > vratio;
            return `<tr class="${blueRow ? 'blue-volume-row' : ''}">
              <td>${i + 1}</td><td>${r.symbol || "-"}</td>
              <td>${gap != null && Number.isFinite(gap) ? gap.toFixed(2) + "%" : "-"}</td>
              <td>${r.strength_score != null ? Number(r.strength_score).toFixed(2) : "-"}</td>
              <td>${r.detection_time || "-"}</td><td>${priceFormat(r.detection_price)}</td>
              <td>${priceFormat(r.previous_close)}</td><td>${priceFormat(r.ltp)}</td><td>${priceFormat(r.open)}</td>
              <td>${Number.isFinite(volMultiple) ? volMultiple.toFixed(2) + "×" : "-"}</td>
              <td>${Number.isFinite(vratio) ? vratio.toFixed(2) + "×" : "-"}</td>
              <td>${r.gain_pct != null ? Number(r.gain_pct).toFixed(2) + "%" : "-"}</td>
            </tr>`;
        }).join("");
    };
    renderList("minusBlueTopResults", minusRows, "Top 20 में कोई Negative Gain वाला शेयर नहीं मिला।");
    renderList("plusBlueTopResults", plusRows, "Top 20 में कोई Positive Gain वाला शेयर नहीं मिला।");
}

function rememberJob(jobId) {
    try { localStorage.setItem("nseManualVolumeScannerJobId", jobId); } catch (_) {}
}
function forgetJob(jobId) {
    try {
        if (!jobId || localStorage.getItem("nseManualVolumeScannerJobId") === jobId) {
            localStorage.removeItem("nseManualVolumeScannerJobId");
        }
    } catch (_) {}
}
function updateAutoStatus(text) {
    document.getElementById("autoStatus").innerText = text;
}
function updateScanButtonLabel() {
    const button = document.getElementById("scanBtn");
    if (!scanInProgress) {
        button.textContent = document.getElementById("autoScan").checked ? "SCAN NOW" : "SCAN";
    }
}
function stopAutoTimer() {
    if (autoTimer) clearTimeout(autoTimer);
    autoTimer = null;
}
function scheduleNextAutoScan() {
    stopAutoTimer();
    if (!document.getElementById("autoScan").checked) {
        updateAutoStatus("Auto Scan बंद है।");
        return;
    }
    const seconds = Number(document.getElementById("autoInterval").value) || 30;
    updateAutoStatus("अगला स्कैन लगभग " + seconds + " सेकंड बाद।");
    autoTimer = setTimeout(() => {
        if (!document.getElementById("autoScan").checked) return;
        if (!scanInProgress) {
            startScan(true);
        } else {
            scheduleNextAutoScan();
        }
    }, seconds * 1000);
}
function toggleAutoScan() {
    stopAutoTimer();
    updateScanButtonLabel();
    if (document.getElementById("autoScan").checked) {
        updateAutoStatus("Auto Scan चालू है। स्कैन शुरू हो रहा है।");
        if (!scanInProgress) startScan(true);
        else scheduleNextAutoScan();
    } else {
        updateAutoStatus("Auto Scan बंद है।");
    }
}
document.getElementById("autoScan").addEventListener("change", toggleAutoScan);
document.getElementById("autoInterval").addEventListener("change", () => {
    if (document.getElementById("autoScan").checked && !scanInProgress) scheduleNextAutoScan();
});

async function startScan(isAuto=false) {
    const btn = document.getElementById("scanBtn");
    const status = document.getElementById("status");
    const message = document.getElementById("message");
    const selectedDate = document.getElementById("scanDate").value;
    const multiplier = document.getElementById("multiplier").value;

    if (scanInProgress) return;
    if (!selectedDate) {
        status.innerText = "Please select a date.";
        return;
    }

    scanInProgress = true;
    lastRenderedResultsVersion = null;
    btn.disabled = true;
    btn.textContent = "SCANNING...";
    status.innerText = isAuto ? "Auto Scan शुरू हो रहा है..." : "Starting scan...";
    message.innerText = "Scanner server par kaam kar raha hai. App badalne par bhi server-side scan chalta rahega.";
    render([]);

    try {
        const response = await fetch(
            "/api/scan?multiplier=" + encodeURIComponent(multiplier) + "&date=" + encodeURIComponent(selectedDate),
            {cache:"no-store"}
        );
        const data = await response.json();
        if (!response.ok) throw new Error(data.error || "Unable to start scan.");
        currentJobId = data.job_id;
        rememberJob(data.job_id);
        await poll(data.job_id, 0);
    } catch (error) {
        status.innerText = "Connection issue";
        message.innerText = error.message + " Internet aane par dobara scan hoga.";
        scanInProgress = false;
        currentJobId = null;
        btn.disabled = false;
        updateScanButtonLabel();
        if (document.getElementById("autoScan").checked) scheduleNextAutoScan();
    }
}

async function poll(jobId, retryCount=0) {
    const btn = document.getElementById("scanBtn");
    const status = document.getElementById("status");
    const message = document.getElementById("message");
    try {
        const response = await fetch("/api/scan/status/" + encodeURIComponent(jobId), {cache:"no-store"});
        const data = await response.json();

        if (response.status === 404) {
            forgetJob(jobId);
            status.innerText = "Scan status unavailable";
            message.innerText = "Server restart hone se purana job record nahi mila. Auto Scan agla scan shuru karega.";
            scanInProgress = false;
            currentJobId = null;
            btn.disabled = false;
            updateScanButtonLabel();
            if (document.getElementById("autoScan").checked) {
                updateAutoStatus("Purana job nahi mila. Naya scan abhi shuru ho raha hai...");
                startScan(true);
            }
            return;
        }
        if (!response.ok) throw new Error(data.error || "Status request failed.");

        status.innerText =
            (data.status === "running" || data.status === "starting")
            ? "Scanner server par chal raha hai..."
            : data.status === "complete" ? "Scan complete." : data.status;
        message.innerText = data.message || "";

        if (data.results_ready && data.results_version !== lastRenderedResultsVersion) {
            render(data.results || []);
            renderBlueTop(data.minus_top5_results || [], data.plus_top5_results || []);
            lastRenderedResultsVersion = data.results_version;
        }

        if (data.status === "running" || data.status === "starting") {
            rememberJob(jobId);
            setTimeout(() => poll(jobId, 0), document.hidden ? 4000 : 1200);
            return;
        }

        if (data.status === "complete") {
            render(data.results || []);
            renderBlueTop(data.minus_top5_results || [], data.plus_top5_results || []);
            lastRenderedResultsVersion = data.results_version ?? lastRenderedResultsVersion;
        }
        if (data.status === "error") {
            message.innerText = data.error || data.message || "Unknown error";
            render([]);
        }

        forgetJob(jobId);
        scanInProgress = false;
        currentJobId = null;
        btn.disabled = false;
        updateScanButtonLabel();
        if (document.getElementById("autoScan").checked) scheduleNextAutoScan();
    } catch (error) {
        status.innerText = "Connection interrupted";
        message.innerText = "Scan server par chal sakta hai. Connection wapas aane par status phir check hoga.";
        const delay = Math.min(15000, 1500 * Math.pow(2, Math.min(retryCount, 3)));
        setTimeout(() => poll(jobId, retryCount + 1), delay);
    }
}

/* PAGE LOAD: Auto Scan default OFF; reconnect only to an existing job. */
window.addEventListener("load", () => {
    const autoScan = document.getElementById("autoScan");

    // Auto Scan default OFF on every page load.
    autoScan.checked = false;
    updateScanButtonLabel();

    let savedJob = null;
    try {
        savedJob = localStorage.getItem("nseManualVolumeScannerJobId");
    } catch (_) {}

    if (savedJob) {
        scanInProgress = true;
        currentJobId = savedJob;
        const btn = document.getElementById("scanBtn");
        btn.disabled = true;
        btn.textContent = "SCANNING...";
        document.getElementById("status").innerText =
            "Pichhle scan ka status dobara joda ja raha hai...";
        poll(savedJob, 0);
    } else {
        // Immediately run first scan without pressing SCAN NOW.
        toggleAutoScan();
    }
});
</script>
</body>
</html>
"""


# FLASK ROUTES
@app.route("/")
def home():
    return render_template_string(HTML, today_date=today_s())


@app.route("/api/scan", methods=["GET", "POST"])
def api_scan():
    if not TOKEN:
        return jsonify({"error": "UPSTOX_ACCESS_TOKEN Render ke Environment Variables mein set karein."}), 500
    body = request.get_json(silent=True) or {}
    try:
        multiplier = float(request.args.get("multiplier", body.get("multiplier", 0.20)))
    except (TypeError, ValueError):
        multiplier = 0.20
    if multiplier <= 0 or multiplier > 100:
        return jsonify({"error": "Multiplier 0 se bada aur 100 tak hona chahiye."}), 400
    date_text = request.args.get("date", body.get("date", today_s()))
    try:
        selected_date = datetime.strptime(date_text, "%Y-%m-%d").date()
    except (TypeError, ValueError):
        return jsonify({"error": "Date YYYY-MM-DD format mein honi chahiye."}), 400
    if selected_date > today():
        return jsonify({"error": "Future date ka scan nahi ho sakta."}), 400
    jid = str(uuid.uuid4())
    with JOBS_LOCK:
        JOBS[jid] = {"status": "starting", "message": "Scan start ho raha hai...", "results": [], "error": None}
    threading.Thread(target=run_scan, args=(jid, multiplier, selected_date), daemon=True).start()
    return jsonify({"job_id": jid})


@app.route("/api/scan/status/<jid>")
def scan_status(jid):
    with JOBS_LOCK:
        job = JOBS.get(jid)
        if job is None:
            return jsonify({"error": "Scan job nahi mila. Dobara scan karein."}), 404
        return jsonify(job)


@app.route("/health")
@app.route("/api/health")
def health():
    return jsonify({
        "status": "ok", "token_configured": bool(TOKEN),
        "time_ist": now_ist().strftime("%Y-%m-%d %H:%M:%S"),
    })


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.getenv("PORT", "10000")))
