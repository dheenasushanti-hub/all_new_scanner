"""
SENSEX Predictive Options Market Scanner â€” Market Structure Engine

What this version fixes:
- Uses completed/currently-available multi-timeframe SENSEX structure:
  3m, 15m, 30m, 60m, 120m, 180m Supertrend.
- Uses SENSEX futures price/OI regime as a primary directional factor.
- Uses Futures VWAP level + VWAP slope/position.
- Uses both option-chain OI concentration and Change-in-OI to derive
  dynamic support/resistance and directional pressure.
- Predicts direction before an option breakout; option momentum is a
  health/liquidity filter, not the primary market-direction trigger.
- Selects Bullish ATM-1/ATM-2 CE or Bearish ATM+1/ATM+2 PE, but ranks
  candidates by liquidity, delta, theta burden, spread, and structure.
- Builds T1/T2/SL dynamically from underlying ATR, Supertrend,
  option-chain support/resistance, and option Greeks.
- No order placement. The script only creates a signal, persists state,
  and sends email.
- Uses current Upstox endpoints: v2 for option chain/contracts/quotes/
  status/instrument search/OI/change-OI; v3 for candle data because the
  older v2 intraday candle API is deprecated.

Run:
    python market_scanner_new_refactored.py --self-test
    python market_scanner_new_refactored.py

Environment:
    UPSTOX_ANALYTICS_TOKEN   required
    SENSEX_INSTRUMENT_KEY     optional, default BSE_INDEX|SENSEX

Optional email:
    EMAIL_SENDER
    EMAIL_PASSWORD
    EMAIL_RECEIVER
    SMTP_HOST (default smtp.gmail.com)
    SMTP_PORT (default 465)

Optional tuning:
    STATE_FILE
    SIGNAL_THRESHOLD (default 60)
    MAX_HISTORY_DAYS (default 45)
"""

from __future__ import annotations

import hashlib
import html
import json
import logging
import math
import os
import smtplib
import sys
import time as time_module
import traceback
import urllib.parse
from dataclasses import asdict, dataclass
from datetime import date, datetime, time, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path
from typing import Any, Optional
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd
import requests


# =============================================================================
# CONFIG
# =============================================================================

IST = ZoneInfo("Asia/Kolkata")
BASE_URL = "https://api.upstox.com"

SENSEX_KEY = os.getenv("SENSEX_INSTRUMENT_KEY", "BSE_INDEX|SENSEX").strip()
UPSTOX_TOKEN = os.getenv("UPSTOX_ANALYTICS_TOKEN", "").strip()

EMAIL_SENDER = os.getenv("EMAIL_SENDER", "").strip()
EMAIL_PASSWORD = os.getenv("EMAIL_PASSWORD", "").strip()
EMAIL_RECEIVER = os.getenv("EMAIL_RECEIVER", "").strip()
SMTP_HOST = os.getenv("SMTP_HOST", "smtp.gmail.com").strip()
SMTP_PORT = int(os.getenv("SMTP_PORT", "465"))

REQUEST_TIMEOUT = int(os.getenv("REQUEST_TIMEOUT", "20"))
MAX_HISTORY_DAYS = int(os.getenv("MAX_HISTORY_DAYS", "45"))
SIGNAL_THRESHOLD = float(os.getenv("SIGNAL_THRESHOLD", "55"))
MIN_ENTRY_TIME = time(9, 18)
OPENING_RANGE_MINUTES = 3
OVEREXTENSION_ATR = float(os.getenv("OVEREXTENSION_ATR", "3.25"))

STATE_FILE = Path(os.getenv("STATE_FILE", "state/market_state.json"))

SCANNER_VERSION = "2026-09-29-MULTI-TF-MARKET-STRUCTURE-V6-OPENING-RESILIENT-PRICE-FIRST"

MARKET_START = time(9, 15)
MARKET_END = time(15, 30)

SUPERTREND_PERIOD = 10
SUPERTREND_FACTOR = 2.0
TIMEFRAMES = (3, 15, 30, 60, 120, 180)

ATR_PERIOD = 14
ATR_BUFFER_MULTIPLIER = 0.30

# Structure weights. Short/intermediate timeframes are most responsive;
# higher timeframes are stabilizers, not vetoes.
TF_WEIGHTS = {
    3: 1.40,
    15: 1.35,
    30: 1.15,
    60: 1.00,
    120: 0.85,
    180: 0.75,
}

# Directional score components.
W_VWAP_LEVEL = 2.0
W_VWAP_SLOPE = 1.25
W_FUTURES = 2.50
W_PRICE_STRUCTURE_3 = 1.20
W_PRICE_STRUCTURE_15 = 1.50
W_OPTION_OI = 1.70
W_OPTION_OI_CHANGE = 1.50
W_CHAIN_LEVELS = 1.30

# Predictive hard-confirmation thresholds. These are intentionally separate
# from the weighted score so Futures OI and option-chain structure cannot be
# drowned out by six Supertrend votes.
FUTURES_OI_MIN_PERSISTENCE = 0.50
FUTURES_OI_STRENGTH_THRESHOLD = 0.25
CHAIN_PREDICTIVE_STRENGTH_THRESHOLD = 0.15
CHAIN_WALL_PROXIMITY_ATR = 1.00
CHAIN_CHANGE_CONFIRM_THRESHOLD = 0.08
FUTURES_LIVE_OI_WEIGHT = 0.35

MIN_DIRECTIONAL_COMPONENTS = 4
ENTRY_SCORE = 4.50

# Trend-first decision engine.
# The scanner must not let a slowly changing option-chain wall or a higher
# timeframe Supertrend veto a clear intraday reversal.
INTRADAY_LOOKBACK_BARS = 8
INTRADAY_RECENT_BARS = 3
INTRADAY_TREND_TRIGGER = 0.75
CORE_BULL_TRIGGER = 2.50
CORE_BEAR_TRIGGER = -2.50
POSITIONING_HARD_OPPOSITE_STRENGTH = 0.65


# Strike health.
MIN_DELTA = 0.25
MAX_DELTA = 0.85
MAX_SPREAD_PCT = 0.12
# Theta is a ranking/risk factor for long-option selection, not a hard entry gate.
# Near expiry, theta can become very large and a rigid percentage cutoff can
# incorrectly reject every otherwise-tradable directional option.
EXPECTED_HOLDING_MINUTES = 60.0
THETA_WARNING_BURDEN = 0.10
MIN_OI = 100.0
MIN_VOLUME = 1.0

# Dynamic target and stop constraints.
MIN_T1_RISK_REWARD = 1.10
MIN_T2_RISK_REWARD = 1.60
OPTION_MAX_STOP_PCT = 0.30
OPTION_MIN_STOP_PCT = 0.15

# Trade monitoring.
REVERSAL_CONFIRMATIONS_REQUIRED = 1
STRUCTURE_REVERSAL_CONFIDENCE = 60.0

# URLs.
INSTRUMENT_SEARCH_URL = f"{BASE_URL}/v2/instruments/search"
OPTION_CONTRACT_URL = f"{BASE_URL}/v2/option/contract"
OPTION_CHAIN_URL = f"{BASE_URL}/v2/option/chain"
MARKET_QUOTE_URL = f"{BASE_URL}/v2/market-quote/quotes"
MARKET_STATUS_URL = f"{BASE_URL}/v2/market/status/BSE"
MARKET_HOLIDAY_URL = f"{BASE_URL}/v2/market/holidays"
MARKET_OI_URL = f"{BASE_URL}/v2/market/oi"
CHANGE_OI_URL = f"{BASE_URL}/v2/market/change-oi"
HISTORICAL_V3_URL = f"{BASE_URL}/v3/historical-candle"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
)
logger = logging.getLogger("sensex_scanner")


# =============================================================================
# DATA TYPES
# =============================================================================

@dataclass(frozen=True)
class FuturesContract:
    instrument_key: str
    trading_symbol: str
    expiry: str


@dataclass(frozen=True)
class OptionCandidate:
    instrument_key: str
    trading_symbol: str
    option_type: str
    strike: float
    expiry: str
    ltp: float
    oi: float
    prev_oi: float
    volume: float
    bid: float
    ask: float
    bid_qty: float
    ask_qty: float
    delta: float
    gamma: float
    theta: float
    iv: float
    spread_pct: float
    theta_burden_pct_day: float


@dataclass(frozen=True)
class StructureResult:
    direction: str
    score: float
    confidence: float
    interpretation: str
    components: dict[str, float]
    timeframe_directions: dict[str, int]
    vwap: float
    vwap_slope: float
    futures_regime: str
    futures_bias: int
    futures_oi_strength: float
    futures_oi_persistence: float
    futures_live_oi_change: float
    intraday_bias: int
    intraday_strength: float
    intraday_score: float
    chain_predictive_bias: int
    chain_predictive_strength: float
    chain_level_bias: int
    support_strength: float
    resistance_strength: float
    support_change_strength: float
    resistance_change_strength: float
    support_1: float
    support_2: float
    resistance_1: float
    resistance_2: float
    reasons: list[str]


@dataclass(frozen=True)
class Signal:
    timestamp: str
    direction: str
    regime: str
    confidence: float
    spot: float
    futures_state: str
    option_type: str
    strike: float
    trading_symbol: str
    instrument_key: str
    entry: float
    target_1: float
    target_2: float
    stop_loss: float
    underlying_stop: float
    underlying_target_1: float
    underlying_target_2: float
    delta: float
    gamma: float
    theta: float
    support_1: float
    support_2: float
    resistance_1: float
    resistance_2: float
    reasons: list[str]


class ScannerError(Exception):
    """Expected scanner/API failure."""


# =============================================================================
# BASIC HELPERS
# =============================================================================

def now_ist() -> datetime:
    return datetime.now(IST)


def safe_float(value: Any, default: float = 0.0) -> float:
    try:
        v = float(value)
        return v if math.isfinite(v) else default
    except (TypeError, ValueError):
        return default


def parse_date(raw: str) -> Optional[date]:
    try:
        return datetime.strptime(str(raw)[:10], "%Y-%m-%d").date()
    except (TypeError, ValueError):
        return None


def market_window_open() -> bool:
    now = now_ist()
    if now.weekday() >= 5:
        return False
    if is_bse_holiday(now):
        return False
    return MARKET_START <= now.time() <= MARKET_END


# =============================================================================
# UPSTOX HTTP
# =============================================================================

def api_headers() -> dict[str, str]:
    if not UPSTOX_TOKEN:
        raise ScannerError(
            "UPSTOX_ANALYTICS_TOKEN is missing. Set it in the environment."
        )
    return {
        "Accept": "application/json",
        "Content-Type": "application/json",
        "Authorization": f"Bearer {UPSTOX_TOKEN}",
    }


def api_get(
    url: str,
    params: Optional[dict[str, Any]] = None,
    retries: int = 3,
) -> dict[str, Any]:
    last_error = "Unknown Upstox error."

    for attempt in range(1, retries + 1):
        try:
            response = requests.get(
                url,
                params=params,
                headers=api_headers(),
                timeout=REQUEST_TIMEOUT,
            )
        except requests.RequestException as exc:
            last_error = f"Network error: {exc}"
            if attempt < retries:
                time_module.sleep(attempt)
                continue
            raise ScannerError(last_error) from exc

        if response.status_code == 200:
            try:
                payload = response.json()
            except ValueError as exc:
                raise ScannerError(
                    f"Upstox returned invalid JSON from {url}"
                ) from exc

            if not isinstance(payload, dict):
                raise ScannerError(f"Unexpected Upstox payload from {url}.")
            if str(payload.get("status", "")).lower() == "error":
                raise ScannerError(json.dumps(payload)[:2000])
            return payload

        last_error = (
            f"Upstox HTTP {response.status_code} | "
            f"{url} | {response.text[:1500]}"
        )

        transient = response.status_code in {429, 500, 502, 503, 504}
        if transient and attempt < retries:
            time_module.sleep(min(2 * attempt, 6))
            continue

        raise ScannerError(last_error)

    raise ScannerError(last_error)


# =============================================================================
# MARKET STATUS / HOLIDAYS
# =============================================================================

def is_bse_holiday(current: datetime) -> bool:
    url = f"{MARKET_HOLIDAY_URL}/{current.strftime('%Y-%m-%d')}"
    try:
        payload = api_get(url, retries=2)
    except ScannerError as exc:
        # Availability of holiday API should not create a false "closed" result.
        logger.warning("Holiday API unavailable: %s", exc)
        return False

    data = payload.get("data")
    if isinstance(data, dict):
        return bool(data)
    if isinstance(data, list):
        return bool(data)
    return False


def get_market_status() -> str:
    payload = api_get(MARKET_STATUS_URL, retries=3)
    data = payload.get("data", {})
    if isinstance(data, dict):
        status = str(data.get("status", "")).upper()
        if status in {"NORMAL_OPEN", "OPEN"}:
            return "OPEN"
        if status in {"NORMAL_CLOSE", "CLOSED"}:
            return "CLOSED"
        return status or "UNKNOWN"

    return "UNKNOWN"


# =============================================================================
# QUOTES
# =============================================================================

def get_quote(instrument_key: str) -> dict[str, Any]:
    payload = api_get(
        MARKET_QUOTE_URL,
        {"instrument_key": instrument_key},
        retries=3,
    )
    data = payload.get("data", {})
    if not isinstance(data, dict):
        raise ScannerError("Upstox quote data is not an object.")
    if instrument_key in data:
        return data[instrument_key]
    if len(data) == 1:
        return next(iter(data.values()))
    raise ScannerError(f"Quote not found for {instrument_key}.")


def extract_ltp(quote: dict[str, Any]) -> float:
    for key in ("last_price", "ltp", "lastPrice"):
        value = safe_float(quote.get(key), 0.0)
        if value > 0:
            return value
    raise ScannerError("LTP not present in quote.")


# =============================================================================
# INSTRUMENT DISCOVERY
# =============================================================================

def get_current_sensex_future() -> FuturesContract:
    candidates: list[dict[str, Any]] = []

    for expiry_filter in ("current_month", "next_month"):
        payload = api_get(
            INSTRUMENT_SEARCH_URL,
            {
                "query": "SENSEX",
                "exchanges": "BSE",
                "segments": "FO",
                "instrument_types": "FUT",
                "expiry": expiry_filter,
                "page_number": 1,
                "records": 30,
            },
        )
        rows = payload.get("data", [])
        if isinstance(rows, list):
            candidates.extend(x for x in rows if isinstance(x, dict))

    today = now_ist().date()
    valid: list[dict[str, Any]] = []

    for row in candidates:
        key = str(row.get("instrument_key", "")).strip()
        symbol = str(row.get("trading_symbol", "")).strip()
        expiry = parse_date(str(row.get("expiry", "")))
        underlying = str(row.get("underlying_symbol", "")).upper()

        if (
            key
            and symbol
            and expiry
            and expiry >= today
            and ("SENSEX" in underlying or "SENSEX" in symbol.upper())
        ):
            valid.append(row)

    if not valid:
        raise ScannerError("No active SENSEX futures found.")

    valid.sort(key=lambda x: parse_date(str(x["expiry"])) or date.max)
    selected = valid[0]

    logger.info(
        "Selected SENSEX future: %s | expiry=%s | key=%s",
        selected["trading_symbol"],
        selected["expiry"],
        selected["instrument_key"],
    )

    return FuturesContract(
        instrument_key=str(selected["instrument_key"]),
        trading_symbol=str(selected["trading_symbol"]),
        expiry=str(selected["expiry"])[:10],
    )


# =============================================================================
# CANDLES
# =============================================================================

def _parse_candles(candles: Any) -> pd.DataFrame:
    rows: list[dict[str, Any]] = []

    if not isinstance(candles, list):
        return pd.DataFrame()

    for row in candles:
        if not isinstance(row, (list, tuple)) or len(row) < 6:
            continue
        try:
            rows.append(
                {
                    "timestamp": row[0],
                    "open": float(row[1]),
                    "high": float(row[2]),
                    "low": float(row[3]),
                    "close": float(row[4]),
                    "volume": float(row[5]),
                    "oi": (
                        float(row[6])
                        if len(row) >= 7 and row[6] is not None
                        else np.nan
                    ),
                }
            )
        except (TypeError, ValueError):
            continue

    if not rows:
        return pd.DataFrame()

    df = pd.DataFrame(rows)
    df["timestamp"] = pd.to_datetime(
        df["timestamp"], utc=True, errors="coerce"
    )
    df = (
        df.dropna(subset=["timestamp"])
        .sort_values("timestamp")
        .drop_duplicates("timestamp")
        .reset_index(drop=True)
    )
    return df


def get_intraday_candles(
    instrument_key: str,
    interval_minutes: int,
    *,
    strict: bool = True,
) -> pd.DataFrame:
    """Fetch today's intraday candles without turning normal opening-data lag into a fatal error."""
    encoded = urllib.parse.quote(instrument_key, safe="")
    url = f"{HISTORICAL_V3_URL}/intraday/{encoded}/minutes/{interval_minutes}"

    try:
        payload = api_get(url, retries=3)
    except ScannerError:
        if strict:
            raise
        return pd.DataFrame()

    data = payload.get("data", {})
    df = _parse_candles(data.get("candles", []) if isinstance(data, dict) else [])
    if df.empty:
        if strict:
            raise ScannerError(f"No intraday {interval_minutes}m candles for {instrument_key}.")
        return pd.DataFrame()

    session_date = now_ist().date()
    local_dates = df["timestamp"].dt.tz_convert(IST).dt.date
    df = df.loc[local_dates == session_date].reset_index(drop=True)
    if df.empty and strict:
        raise ScannerError(f"No current-session {interval_minutes}m candles for {instrument_key}.")
    return df


def _resample_one_minute_to_three(df: pd.DataFrame) -> pd.DataFrame:
    """Build 3-minute bars from 1-minute data, preserving an incomplete opening bar."""
    if df is None or df.empty:
        return pd.DataFrame()
    work = df.copy().sort_values("timestamp").drop_duplicates("timestamp", keep="last")
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    work = work.dropna(subset=["timestamp"]).set_index("timestamp")
    for c in ("open", "high", "low", "close", "volume", "oi"):
        if c in work.columns:
            work[c] = pd.to_numeric(work[c], errors="coerce")
    agg = work.resample("3min", origin="start_day", offset="9h15min", label="left", closed="left").agg(
        open=("open", "first"), high=("high", "max"), low=("low", "min"),
        close=("close", "last"), volume=("volume", "sum"), oi=("oi", "last"),
    )
    return agg.dropna(subset=["open", "high", "low", "close"]).reset_index()


def get_current_session_futures_candles(instrument_key: str) -> pd.DataFrame:
    """Prefer native 3m data; fall back to 1m aggregation during opening/API lag."""
    native = get_intraday_candles(instrument_key, 3, strict=False)
    if not native.empty:
        logger.info("Current-session futures 3m candles: %d", len(native))
        return native

    one_min = get_intraday_candles(instrument_key, 1, strict=False)
    if not one_min.empty:
        rebuilt = _resample_one_minute_to_three(one_min)
        if not rebuilt.empty:
            logger.warning(
                "Native 3m futures candles unavailable; rebuilt %d 3m bars from 1m data.",
                len(rebuilt),
            )
            return rebuilt

    logger.warning("Current-session futures 3m/1m candles unavailable; using quote/historical fallbacks.")
    return pd.DataFrame()


def _subtract_months(d: date, months: int) -> date:
    """Subtract calendar months without exceeding the target month."""
    year = d.year
    month = d.month - months
    while month <= 0:
        month += 12
        year -= 1

    import calendar
    day = min(d.day, calendar.monthrange(year, month)[1])
    return date(year, month, day)


def get_historical_candles(
    instrument_key: str,
    interval_minutes: int,
    lookback_days: int = MAX_HISTORY_DAYS,
) -> pd.DataFrame:
    encoded = urllib.parse.quote(instrument_key, safe="")
    end = now_ist().date()

    # Upstox V3 historical-candle limits:
    #   1..15 minute intervals -> max 1 calendar month/request
    #   >15 minute minute intervals -> max 1 calendar quarter/request
    # Use calendar-month subtraction instead of a fixed day count.
    if interval_minutes <= 15:
        start = _subtract_months(end, 1)
    else:
        start = _subtract_months(end, 3)

    url = (
        f"{HISTORICAL_V3_URL}/{encoded}/minutes/{interval_minutes}"
        f"/{end.isoformat()}/{start.isoformat()}"
    )

    payload = api_get(url, retries=3)
    data = payload.get("data", {})
    df = _parse_candles(data.get("candles", []) if isinstance(data, dict) else [])

    if df.empty:
        raise ScannerError(
            f"No historical {interval_minutes}m candles for {instrument_key}."
        )
    return df


def merge_current_into_history(
    historical: pd.DataFrame,
    current: Optional[pd.DataFrame],
) -> pd.DataFrame:
    if current is None or current.empty:
        return historical
    combined = pd.concat([historical, current], ignore_index=True)
    return (
        combined.sort_values("timestamp")
        .drop_duplicates("timestamp", keep="last")
        .reset_index(drop=True)
    )


def get_timeframe_candles(
    instrument_key: str,
    interval_minutes: int,
    min_bars: int = 25,
) -> pd.DataFrame:
    """
    Use historical V3 data for indicator warm-up and merge today's intraday data.
    This is critical for 60/120/180m Supertrend: computing ST from only 1-3
    current-day candles is structurally invalid.
    """
    history_days = 35 if interval_minutes <= 15 else 60

    historical = get_historical_candles(
        instrument_key,
        interval_minutes,
        lookback_days=history_days,
    )

    current = None
    try:
        current = get_intraday_candles(instrument_key, interval_minutes)
    except ScannerError as exc:
        logger.info(
            "Current intraday %dm refresh unavailable; using historical data: %s",
            interval_minutes,
            exc,
        )

    merged = merge_current_into_history(historical, current)

    if len(merged) < min_bars:
        raise ScannerError(
            f"Insufficient {interval_minutes}m bars: {len(merged)} < {min_bars}."
        )

    return merged


def filter_completed_candles(
    df: pd.DataFrame,
    interval_minutes: int,
    now: Optional[datetime] = None,
) -> pd.DataFrame:
    """
    Keep only bars whose full interval has completed.

    Timestamp is assumed to be the candle start time, which is the standard
    representation of OHLC time series returned by Upstox.
    """
    if df.empty:
        return df

    current = now or now_ist()
    local_ts = df["timestamp"].dt.tz_convert(IST)
    interval = pd.to_timedelta(interval_minutes, unit="m")
    completed = local_ts + interval <= current

    result = df.loc[completed].copy()
    return result.reset_index(drop=True)


# =============================================================================
# INDICATORS
# =============================================================================

def calculate_atr(df: pd.DataFrame, period: int = ATR_PERIOD) -> pd.Series:
    previous = df["close"].shift(1)
    tr = pd.concat(
        [
            df["high"] - df["low"],
            (df["high"] - previous).abs(),
            (df["low"] - previous).abs(),
        ],
        axis=1,
    ).max(axis=1)

    return tr.ewm(
        alpha=1 / period,
        adjust=False,
        min_periods=1,
    ).mean()


def calculate_supertrend(
    df: pd.DataFrame,
    period: int = SUPERTREND_PERIOD,
    factor: float = SUPERTREND_FACTOR,
) -> pd.DataFrame:
    if df.empty:
        raise ScannerError("Cannot calculate Supertrend on empty data.")

    out = df.copy().reset_index(drop=True)
    atr = calculate_atr(out, period=period)
    out["atr"] = atr

    hl2 = (out["high"] + out["low"]) / 2.0
    upper_basic = hl2 + factor * atr
    lower_basic = hl2 - factor * atr

    upper = pd.Series(np.nan, index=out.index, dtype=float)
    lower = pd.Series(np.nan, index=out.index, dtype=float)
    direction = pd.Series(np.nan, index=out.index, dtype=float)
    st = pd.Series(np.nan, index=out.index, dtype=float)

    upper.iloc[0] = upper_basic.iloc[0]
    lower.iloc[0] = lower_basic.iloc[0]
    direction.iloc[0] = 1
    st.iloc[0] = lower.iloc[0]

    for i in range(1, len(out)):
        if (
            upper_basic.iloc[i] < upper.iloc[i - 1]
            or out["close"].iloc[i - 1] > upper.iloc[i - 1]
        ):
            upper.iloc[i] = upper_basic.iloc[i]
        else:
            upper.iloc[i] = upper.iloc[i - 1]

        if (
            lower_basic.iloc[i] > lower.iloc[i - 1]
            or out["close"].iloc[i - 1] < lower.iloc[i - 1]
        ):
            lower.iloc[i] = lower_basic.iloc[i]
        else:
            lower.iloc[i] = lower.iloc[i - 1]

        if out["close"].iloc[i] > upper.iloc[i - 1]:
            direction.iloc[i] = 1
        elif out["close"].iloc[i] < lower.iloc[i - 1]:
            direction.iloc[i] = -1
        else:
            direction.iloc[i] = direction.iloc[i - 1]

        st.iloc[i] = (
            lower.iloc[i] if direction.iloc[i] > 0 else upper.iloc[i]
        )

    out["supertrend"] = st
    out["direction"] = direction
    return out


def calculate_vwap(df: pd.DataFrame) -> pd.Series:
    if df.empty:
        return pd.Series(dtype=float)

    typical = (df["high"] + df["low"] + df["close"]) / 3.0
    volume = (
        pd.to_numeric(df["volume"], errors="coerce")
        .fillna(0.0)
        .clip(lower=0.0)
    )

    local_date = (
        pd.to_datetime(df["timestamp"], utc=True, errors="coerce")
        .dt.tz_convert(IST)
        .dt.date
    )

    cum_vol = volume.groupby(local_date).cumsum()
    cum_pv = (typical * volume).groupby(local_date).cumsum()

    vwap = cum_pv / cum_vol.replace(0, np.nan)

    if vwap.isna().all():
      vwap = typical.groupby(local_date).cummean()
    return vwap.ffill()

def trend_direction(
    df: pd.DataFrame,
    lookback: int = 6,
) -> int:
    if df is None or len(df) < 2:
        return 0

    closes = (
        pd.to_numeric(df["close"], errors="coerce")
        .dropna()
        .tail(max(2, lookback))
    )
    if len(closes) < 2:
        return 0

    diffs = np.diff(closes.to_numpy(dtype=float))
    net = float(closes.iloc[-1] - closes.iloc[0])
    pos = int(np.sum(diffs > 0))
    neg = int(np.sum(diffs < 0))

    if net > 0 and pos >= neg:
        return 1
    if net < 0 and neg >= pos:
        return -1
    return 1 if net > 0 else -1 if net < 0 else 0


def market_structure_state(
    df: pd.DataFrame,
    lookback: int = 8,
) -> str:
    if len(df) < 3:
        return "NEUTRAL"

    n = min(lookback, len(df))
    recent = df.tail(n)
    if len(recent) < 3:
        return "NEUTRAL"

    highs = recent["high"].to_numpy(dtype=float)
    lows = recent["low"].to_numpy(dtype=float)

    # Compare the latest third to the earliest third rather than one candle
    # against one candle; this is less noisy and captures HH/HL or LH/LL.
    split = max(1, len(recent) // 3)
    early_high = float(np.mean(highs[:split]))
    late_high = float(np.mean(highs[-split:]))
    early_low = float(np.mean(lows[:split]))
    late_low = float(np.mean(lows[-split:]))

    if late_high > early_high and late_low > early_low:
        return "BULLISH"
    if late_high < early_high and late_low < early_low:
        return "BEARISH"
    return "NEUTRAL"


# =============================================================================
# FUTURES PRICE/OI REGIME
# =============================================================================

def _extract_quote_oi(quote: Optional[dict[str, Any]]) -> float:
    """Extract live futures OI from the common Upstox v2 quote shapes."""
    if not isinstance(quote, dict):
        return float("nan")

    candidates = [
        quote.get("oi"),
        quote.get("open_interest"),
        (quote.get("eFeedDetails") or {}).get("oi")
        if isinstance(quote.get("eFeedDetails"), dict) else None,
    ]
    for value in candidates:
        parsed = safe_float(value, float("nan"))
        if math.isfinite(parsed) and parsed >= 0:
            return parsed
    return float("nan")


def futures_oi_structure(
    futures_3m: pd.DataFrame,
    live_quote: Optional[dict[str, Any]] = None,
) -> dict[str, Any]:
    """Build a predictive Futures price/OI regime.

    Unlike a single-candle OI test, this measures:
      - multi-candle price/OI direction,
      - directional OI persistence,
      - OI acceleration versus recent typical change, and
      - the live quote OI versus the most recent completed candle.

    The result is deliberately independent from the option-chain score.
    """
    if futures_3m is None or len(futures_3m) < 4:
        return {
            "regime": "UNAVAILABLE", "bias": 0, "price_delta": 0.0,
            "oi_delta": 0.0, "oi_strength": 0.0, "oi_persistence": 0.0,
            "live_oi_change": float("nan"), "oi_acceleration": 0.0,
        }

    recent = futures_3m.tail(12).copy()
    price = pd.to_numeric(recent["close"], errors="coerce")
    oi = pd.to_numeric(recent["oi"], errors="coerce")
    valid = pd.DataFrame({"price": price, "oi": oi}).dropna()

    if len(valid) < 4:
        pdir = trend_direction(recent, min(6, len(recent)))
        return {
            "regime": "PRICE_ONLY_BULLISH" if pdir > 0 else "PRICE_ONLY_BEARISH" if pdir < 0 else "NEUTRAL",
            "bias": pdir, "price_delta": float(price.dropna().iloc[-1] - price.dropna().iloc[0]) if price.notna().sum() >= 2 else 0.0,
            "oi_delta": 0.0, "oi_strength": 0.0, "oi_persistence": 0.0,
            "live_oi_change": float("nan"), "oi_acceleration": 0.0,
        }

    price_delta = float(valid["price"].iloc[-1] - valid["price"].iloc[0])
    oi_delta = float(valid["oi"].iloc[-1] - valid["oi"].iloc[0])
    price_dir = 1 if price_delta > 0 else -1 if price_delta < 0 else 0
    oi_dir = 1 if oi_delta > 0 else -1 if oi_delta < 0 else 0

    price_deltas = valid["price"].diff().dropna()
    oi_deltas = valid["oi"].diff().dropna()
    aligned = ((price_deltas < 0) & (oi_deltas > 0)) if price_dir < 0 else ((price_deltas > 0) & (oi_deltas > 0)) if price_dir > 0 else pd.Series(dtype=bool)
    opposing = ((price_deltas < 0) & (oi_deltas < 0)) if price_dir < 0 else ((price_deltas > 0) & (oi_deltas < 0)) if price_dir > 0 else pd.Series(dtype=bool)
    persistence = float(aligned.mean()) if len(aligned) else 0.0

    median_abs_oi_change = float(np.median(np.abs(oi_deltas.to_numpy(dtype=float)))) if len(oi_deltas) else 0.0
    last_oi_change = float(oi_deltas.iloc[-1]) if len(oi_deltas) else 0.0
    acceleration = (
        last_oi_change / median_abs_oi_change
        if median_abs_oi_change > 0 else 0.0
    )

    live_oi = _extract_quote_oi(live_quote)
    last_completed_oi = float(valid["oi"].iloc[-1])
    live_oi_change = live_oi - last_completed_oi if math.isfinite(live_oi) else float("nan")

    bullish_regime = price_dir > 0 and oi_dir > 0
    bearish_regime = price_dir < 0 and oi_dir > 0
    bullish_cover = price_dir > 0 and oi_dir < 0
    bearish_unwind = price_dir < 0 and oi_dir < 0

    if bearish_regime:
        regime, bias = "SHORT_BUILDUP", -1
    elif bullish_regime:
        regime, bias = "LONG_BUILDUP", 1
    elif bullish_cover:
        regime, bias = "SHORT_COVERING", 1
    elif bearish_unwind:
        regime, bias = "LONG_UNWINDING", -1
    elif price_dir < 0:
        regime, bias = "PRICE_ONLY_BEARISH", -1
    elif price_dir > 0:
        regime, bias = "PRICE_ONLY_BULLISH", 1
    else:
        regime, bias = "NEUTRAL", 0

    # Strength is intentionally dominated by persistence and OI magnitude.
    price_range = float(valid["price"].max() - valid["price"].min())
    price_component = min(abs(price_delta) / max(price_range, 1.0), 1.0)
    persistence_component = min(persistence / FUTURES_OI_MIN_PERSISTENCE, 1.0)
    acceleration_component = min(abs(acceleration) / 2.0, 1.0)
    live_component = (
        min(abs(live_oi_change) / max(median_abs_oi_change, 1.0), 1.0)
        if math.isfinite(live_oi_change) else 0.0
    )
    strength = 0.40 * persistence_component + 0.25 * price_component + 0.20 * acceleration_component + 0.15 * live_component

    # For short build-up, only a positive OI trend is predictive; an OI fall
    # while price falls is a different regime (long unwinding).
    if regime in {"SHORT_BUILDUP", "LONG_BUILDUP"} and persistence < FUTURES_OI_MIN_PERSISTENCE:
        strength *= 0.70

    logger.info(
        "FUTURES OI ENGINE: regime=%s bias=%+d price_delta=%+.2f oi_delta=%+.0f "
        "persistence=%.2f acceleration=%.2f live_oi_change=%+.0f strength=%.3f",
        regime, bias, price_delta, oi_delta, persistence, acceleration,
        live_oi_change if math.isfinite(live_oi_change) else float("nan"), strength,
    )

    return {
        "regime": regime,
        "bias": bias,
        "price_delta": price_delta,
        "oi_delta": oi_delta,
        "oi_strength": float(strength),
        "oi_persistence": persistence,
        "live_oi_change": live_oi_change,
        "oi_acceleration": float(acceleration),
        "opposing_fraction": float(opposing.mean()) if len(opposing) else 0.0,
    }


def futures_price_oi_regime(
    futures_3m: pd.DataFrame,
    live_quote: Optional[dict[str, Any]] = None,
) -> tuple[str, int, float, float]:
    result = futures_oi_structure(futures_3m, live_quote)
    return (
        str(result["regime"]),
        int(result["bias"]),
        float(result["price_delta"]),
        float(result["oi_delta"]),
    )


# =============================================================================
# OPTION CHAIN
# =============================================================================

def _nearest_active_option_expiry() -> str:
    """Return the nearest non-expired SENSEX option expiry available to Upstox."""
    payload = api_get(
        OPTION_CONTRACT_URL,
        {"instrument_key": SENSEX_KEY},
        retries=4,
    )
    contracts = payload.get("data", [])

    if not isinstance(contracts, list) or not contracts:
        raise ScannerError("No active SENSEX option contracts returned by Upstox.")

    today = now_ist().date()
    future_expiries: list[date] = []

    for contract in contracts:
        if not isinstance(contract, dict):
            continue
        expiry = parse_date(str(contract.get("expiry", "")))
        if expiry is not None and expiry >= today:
            future_expiries.append(expiry)

    if not future_expiries:
        raise ScannerError(
            f"No active SENSEX option expiry found on or after {today.isoformat()}."
        )

    selected = min(future_expiries)
    logger.info(
        "Selected nearest active SENSEX option expiry: %s",
        selected.isoformat(),
    )
    return selected.isoformat()


def get_option_chain() -> tuple[str, list[dict[str, Any]]]:
    """
    Load the nearest active SENSEX option expiry and then request its chain.

    We intentionally do not use Upstox's relative ``current_week`` keyword
    here. On the trading day immediately after a weekly expiry, that keyword
    can resolve to a completed week and the chain may be empty. Resolving the
    nearest active expiry from the option-contract endpoint makes the scanner
    roll automatically from (for example) 17-Sep to 24-Sep.
    """
    expiry = _nearest_active_option_expiry()

    payload = api_get(
        OPTION_CHAIN_URL,
        {
            "instrument_key": SENSEX_KEY,
            "expiry_date": expiry,
        },
        retries=4,
    )
    data = payload.get("data", [])

    if not isinstance(data, list) or not data:
        raise ScannerError(
            f"SENSEX option chain is empty for active expiry {expiry}."
        )

    # Guard against an unexpected mixed-expiry response.
    normalized_expiry = expiry[:10]
    filtered = [
        row
        for row in data
        if isinstance(row, dict)
        and str(row.get("expiry", ""))[:10] == normalized_expiry
    ]

    if filtered:
        data = filtered

    logger.info(
        "Loaded option chain: expiry=%s rows=%d",
        expiry,
        len(data),
    )
    return expiry, data


def chain_rows(chain: list[dict[str, Any]]) -> dict[float, dict[str, Any]]:
    out: dict[float, dict[str, Any]] = {}
    for row in chain:
        if not isinstance(row, dict):
            continue
        strike = safe_float(row.get("strike_price"), float("nan"))
        if math.isfinite(strike):
            out[strike] = row

    if not out:
        raise ScannerError("No valid strikes in option chain.")
    return out


def nearest_strike(spot: float, strikes: list[float]) -> float:
    if not strikes:
        raise ScannerError("No option strikes available.")
    return min(strikes, key=lambda x: abs(x - spot))


def strike_step(strikes: list[float]) -> float:
    unique = sorted(set(float(x) for x in strikes))
    diffs = [
        unique[i + 1] - unique[i]
        for i in range(len(unique) - 1)
        if unique[i + 1] > unique[i]
    ]
    if not diffs:
        raise ScannerError("Unable to determine strike interval.")
    return min(diffs)


def option_side_data(
    row: dict[str, Any],
    option_type: str,
) -> dict[str, Any]:
    key = "call_options" if option_type == "CE" else "put_options"
    block = row.get(key) or {}
    market = block.get("market_data") or {}
    greeks = block.get("option_greeks") or {}

    return {
        "instrument_key": block.get("instrument_key"),
        "ltp": safe_float(market.get("ltp")),
        "oi": safe_float(market.get("oi")),
        "prev_oi": safe_float(market.get("prev_oi")),
        "volume": safe_float(market.get("volume")),
        "bid": safe_float(market.get("bid_price")),
        "ask": safe_float(market.get("ask_price")),
        "bid_qty": safe_float(market.get("bid_qty")),
        "ask_qty": safe_float(market.get("ask_qty")),
        "delta": safe_float(greeks.get("delta"), float("nan")),
        "gamma": safe_float(greeks.get("gamma"), 0.0),
        "theta": safe_float(greeks.get("theta"), 0.0),
        "iv": safe_float(greeks.get("iv"), 0.0),
    }


def chain_oi_support_resistance(
    chain: list[dict[str, Any]],
    spot: float,
) -> dict[str, Any]:
    """Derive dynamic option-chain walls and predictive OI migration.

    Support = put-OI concentration below spot.
    Resistance = call-OI concentration above spot.

    The engine also measures how those walls are changing. A strong CE wall
    that is building while PE support weakens is predictive bearish evidence;
    the inverse is predictive bullish evidence.
    """
    rows = chain_rows(chain)
    strikes = sorted(rows)
    step = strike_step(strikes)
    atm = nearest_strike(spot, strikes)

    entries: list[dict[str, float]] = []
    for strike, row in rows.items():
        ce = option_side_data(row, "CE")
        pe = option_side_data(row, "PE")
        c_oi = max(safe_float(ce["oi"]), 0.0)
        p_oi = max(safe_float(pe["oi"]), 0.0)
        c_chg = safe_float(ce["oi"]) - safe_float(ce["prev_oi"])
        p_chg = safe_float(pe["oi"]) - safe_float(pe["prev_oi"])
        dist_steps = abs(strike - atm) / step if step > 0 else 0.0
        proximity = 1.0 / (1.0 + dist_steps)
        entries.append({
            "strike": float(strike), "call_oi": c_oi, "put_oi": p_oi,
            "call_change": c_chg, "put_change": p_chg,
            "proximity": proximity,
        })

    near_entries = [x for x in entries if abs(x["strike"] - atm) <= step * 10]
    max_call = max((x["call_oi"] for x in near_entries), default=1.0)
    max_put = max((x["put_oi"] for x in near_entries), default=1.0)

    support_rows = [x for x in entries if x["strike"] <= atm and x["put_oi"] > 0]
    resistance_rows = [x for x in entries if x["strike"] >= atm and x["call_oi"] > 0]

    def support_strength(x: dict[str, float]) -> float:
        oi = x["put_oi"] / max(max_put, 1.0)
        change = max(x["put_change"], 0.0) / max(max_put, 1.0)
        opposite = max(-x["call_change"], 0.0) / max(max_call, 1.0)
        return min(1.0, 0.55 * oi + 0.30 * change + 0.15 * opposite) * x["proximity"]

    def resistance_strength(x: dict[str, float]) -> float:
        oi = x["call_oi"] / max(max_call, 1.0)
        change = max(x["call_change"], 0.0) / max(max_call, 1.0)
        opposite = max(-x["put_change"], 0.0) / max(max_put, 1.0)
        return min(1.0, 0.55 * oi + 0.30 * change + 0.15 * opposite) * x["proximity"]

    supports_ranked = sorted(
        [(x, support_strength(x)) for x in support_rows],
        key=lambda z: (-z[1], abs(spot - z[0]["strike"])),
    )
    resistances_ranked = sorted(
        [(x, resistance_strength(x)) for x in resistance_rows],
        key=lambda z: (-z[1], abs(z[0]["strike"] - spot)),
    )

    support_levels = sorted(x[0]["strike"] for x in supports_ranked[:8])
    resistance_levels = sorted(x[0]["strike"] for x in resistances_ranked[:8])

    support_1 = min((x for x in support_levels if x < spot), key=lambda x: spot - x, default=spot)
    support_2 = max((x for x in support_levels if x < support_1), default=support_1)
    resistance_1 = min((x for x in resistance_levels if x > spot), key=lambda x: x - spot, default=spot)
    resistance_2 = min((x for x in resistance_levels if x > resistance_1), default=resistance_1)

    support1_row = next((x for x, _ in supports_ranked if abs(x["strike"] - support_1) < 0.01), None)
    resistance1_row = next((x for x, _ in resistances_ranked if abs(x["strike"] - resistance_1) < 0.01), None)

    support_strength_value = support_strength(support1_row) if support1_row else 0.0
    resistance_strength_value = resistance_strength(resistance1_row) if resistance1_row else 0.0
    support_change_strength = (
        max(support1_row["put_change"], 0.0) / max(max_put, 1.0) if support1_row else 0.0
    )
    resistance_change_strength = (
        max(resistance1_row["call_change"], 0.0) / max(max_call, 1.0) if resistance1_row else 0.0
    )

    # Local pressure around ATM, still useful but no longer the sole engine.
    nearby = [x for x in entries if abs(x["strike"] - atm) <= step * 5]
    bull_pressure = sum(x["proximity"] * (max(x["put_change"], 0.0) + max(-x["call_change"], 0.0)) for x in nearby)
    bear_pressure = sum(x["proximity"] * (max(x["call_change"], 0.0) + max(-x["put_change"], 0.0)) for x in nearby)
    pressure_den = bull_pressure + bear_pressure
    pressure_score = (bull_pressure - bear_pressure) / pressure_den if pressure_den > 0 else 0.0

    # Level/migration logic. This is intentionally predictive when a wall is
    # close enough to matter for the current ATR, not merely when spot crosses it.
    spot_ref_atr = max(
        safe_float(rows[atm].get("_scanner_atr"), 0.0),
        1.0,
    )
    res_dist = resistance_1 - spot if resistance_1 > spot else float("inf")
    sup_dist = spot - support_1 if support_1 < spot else float("inf")

    level_bias = 0
    if resistance_1 > spot and resistance_strength_value >= support_strength_value + 0.10:
        if res_dist <= CHAIN_WALL_PROXIMITY_ATR * max(spot_ref_atr, step):
            level_bias = -1
    if support_1 < spot and support_strength_value >= resistance_strength_value + 0.10:
        if sup_dist <= CHAIN_WALL_PROXIMITY_ATR * max(spot_ref_atr, step):
            level_bias = 1

    migration_bias = (
        -1 if resistance_change_strength - support_change_strength >= CHAIN_CHANGE_CONFIRM_THRESHOLD
        else 1 if support_change_strength - resistance_change_strength >= CHAIN_CHANGE_CONFIRM_THRESHOLD
        else 0
    )

    predictive_raw = 0.55 * pressure_score + 0.25 * (support_strength_value - resistance_strength_value) + 0.20 * migration_bias
    predictive_bias = 1 if predictive_raw >= CHAIN_PREDICTIVE_STRENGTH_THRESHOLD else -1 if predictive_raw <= -CHAIN_PREDICTIVE_STRENGTH_THRESHOLD else 0

    logger.info(
        "CHAIN PREDICTIVE ENGINE: S1=%.0f(%.3f) S2=%.0f R1=%.0f(%.3f) R2=%.0f "
        "support_chg=%.3f resistance_chg=%.3f pressure=%+.3f migration=%+d "
        "level_bias=%+d predictive=%+d raw=%+.3f",
        support_1, support_strength_value, support_2,
        resistance_1, resistance_strength_value, resistance_2,
        support_change_strength, resistance_change_strength,
        pressure_score, migration_bias, level_bias, predictive_bias, predictive_raw,
    )

    return {
        "support_1": float(support_1), "support_2": float(support_2),
        "resistance_1": float(resistance_1), "resistance_2": float(resistance_2),
        "pressure_score": float(pressure_score),
        "normalized_diff": float(pressure_score),
        "normalized_change": float(migration_bias),
        "oi_bias": int(1 if pressure_score > 0.08 else -1 if pressure_score < -0.08 else 0),
        "change_bias": int(migration_bias),
        "predictive_bias": int(predictive_bias),
        "predictive_strength": float(abs(predictive_raw)),
        "level_bias": int(level_bias),
        "support_strength": float(support_strength_value),
        "resistance_strength": float(resistance_strength_value),
        "support_change_strength": float(support_change_strength),
        "resistance_change_strength": float(resistance_change_strength),
    }


def get_daily_oi_confirmation(
    expiry: str,
) -> tuple[int, float]:
    """
    Optional v2 market/OI endpoint.
    The endpoint is date-based, so it is used as a secondary cross-check only.
    """
    today = now_ist().date().isoformat()

    try:
        payload = api_get(
            MARKET_OI_URL,
            {
                "instrument_key": SENSEX_KEY,
                "expiry": expiry,
                "date": today,
            },
            retries=2,
        )
    except ScannerError as exc:
        logger.info("Daily OI endpoint unavailable: %s", exc)
        return 0, 0.0

    data = payload.get("data", {})
    if not isinstance(data, dict):
        return 0, 0.0

    total_put = safe_float(data.get("total_puts"))
    total_call = safe_float(data.get("total_calls"))
    denominator = total_put + total_call

    if denominator <= 0:
        return 0, 0.0

    pcr = total_put / total_call if total_call > 0 else 999.0
    score = (total_put - total_call) / denominator
    bias = 1 if score > 0.05 else -1 if score < -0.05 else 0

    logger.info(
        "DAILY OI: puts=%.0f calls=%.0f PCR=%.3f score=%+.3f bias=%+d",
        total_put, total_call, pcr, score, bias,
    )
    return bias, score


def get_change_oi_confirmation(expiry: str) -> tuple[int, float]:
    """
    Upstox Change-in-OI is date-based, not an intraday timestamp API.
    It is therefore a secondary positioning confirmation.
    """
    today = now_ist().date().isoformat()

    try:
        payload = api_get(
            CHANGE_OI_URL,
            {
                "instrument_key": SENSEX_KEY,
                "expiry": expiry,
                "date": today,
                "interval": 1,
            },
            retries=2,
        )
    except ScannerError as exc:
        logger.info("Change-OI endpoint unavailable: %s", exc)
        return 0, 0.0

    data = payload.get("data", {})
    if not isinstance(data, dict):
        return 0, 0.0

    put_change = safe_float(data.get("total_put_change_oi"))
    call_change = safe_float(data.get("total_call_change_oi"))
    den = abs(put_change) + abs(call_change)

    if den <= 0:
        return 0, 0.0

    # Positive = PE buildup / CE unwinding => bullish.
    score = (put_change - call_change) / den
    bias = 1 if score > 0.10 else -1 if score < -0.10 else 0

    logger.info(
        "CHANGE-OI CONFIRMATION: put_change=%+.0f call_change=%+.0f "
        "score=%+.3f bias=%+d",
        put_change, call_change, score, bias,
    )
    return bias, score


# =============================================================================
# VWAP / TIMEFRAME STRUCTURE
# =============================================================================

def vwap_snapshot(
    futures_session: pd.DataFrame,
) -> tuple[float, float, int]:
    """Calculate session VWAP from whatever current-session bars are available.

    One opening bar is valid. A zero-volume opening feed falls back to a simple
    typical-price average rather than failing the entire scan.
    """
    if futures_session is None or futures_session.empty:
        raise ScannerError("Futures session candles unavailable for VWAP.")
    work = futures_session.copy()
    required = {"timestamp", "high", "low", "close"}
    missing = required.difference(work.columns)
    if missing:
        raise ScannerError(f"Futures session candles missing VWAP columns: {sorted(missing)}")
    for col in ("high", "low", "close", "volume"):
        if col not in work.columns:
            work[col] = 0.0
        work[col] = pd.to_numeric(work[col], errors="coerce")
    work = work.dropna(subset=["timestamp", "high", "low", "close"]).sort_values("timestamp").drop_duplicates("timestamp", keep="last")
    if work.empty:
        raise ScannerError("No valid Futures session candles available for VWAP.")
    vwap_series = calculate_vwap(work).replace([np.inf, -np.inf], np.nan).dropna()
    if vwap_series.empty:
        typical = (work["high"] + work["low"] + work["close"]) / 3.0
        vwap_series = typical.expanding().mean().dropna()
    current_vwap = float(vwap_series.iloc[-1])
    slope = float(vwap_series.iloc[-1] - vwap_series.iloc[-2]) if len(vwap_series) >= 2 else 0.0
    price = float(work["close"].iloc[-1])
    level_bias = 1 if price > current_vwap else -1 if price < current_vwap else 0
    logger.info("VWAP: price=%.2f vwap=%.2f slope=%+.2f level_bias=%+d bars=%d", price, current_vwap, slope, level_bias, len(vwap_series))
    return current_vwap, slope, level_bias


def intraday_trend_snapshot(
    futures_session: pd.DataFrame,
    vwap: float,
) -> tuple[int, float, float]:
    """
    Measure fast intraday direction independently of slow option walls.

    Inputs are current-session futures candles. The score combines:
      - 8-bar net price movement normalized by ATR,
      - very recent 3-bar movement,
      - higher-high / higher-low or lower-high / lower-low structure,
      - current price versus VWAP.

    Returns (bias, strength, raw_score).
    """
    if futures_session is None or futures_session.empty:
        return 0, 0.0, 0.0

    work = futures_session.copy()
    for col in ("high", "low", "close"):
        work[col] = pd.to_numeric(work[col], errors="coerce")

    work = work.dropna(subset=["high", "low", "close"]).sort_values("timestamp")
    closes = work["close"].tail(INTRADAY_LOOKBACK_BARS)
    if len(closes) < 3:
        return 0, 0.0, 0.0

    atr = calculate_atr(work).dropna()
    atr_value = max(
        float(atr.iloc[-1]) if not atr.empty and math.isfinite(float(atr.iloc[-1])) else 0.0,
        1.0,
    )

    net_move = float(closes.iloc[-1] - closes.iloc[0])
    recent_count = min(INTRADAY_RECENT_BARS + 1, len(closes))
    recent_move = float(closes.iloc[-1] - closes.iloc[-recent_count])

    recent = work.tail(min(INTRADAY_LOOKBACK_BARS, len(work)))
    split = max(1, len(recent) // 2)
    early = recent.iloc[:split]
    late = recent.iloc[-split:]

    higher_structure = (
        float(late["high"].mean()) > float(early["high"].mean())
        and float(late["low"].mean()) > float(early["low"].mean())
    )
    lower_structure = (
        float(late["high"].mean()) < float(early["high"].mean())
        and float(late["low"].mean()) < float(early["low"].mean())
    )

    price = float(closes.iloc[-1])
    vwap_bias = 1 if price > vwap else -1 if price < vwap else 0

    # Bounded contributions keep one abnormal move from dominating the engine.
    net_component = math.tanh(net_move / (1.25 * atr_value))
    recent_component = math.tanh(recent_move / (0.90 * atr_value))
    structure_component = 1.0 if higher_structure else -1.0 if lower_structure else 0.0

    raw_score = (
        1.55 * net_component
        + 1.25 * recent_component
        + 0.75 * structure_component
        + 0.60 * vwap_bias
    )

    bias = (
        1 if raw_score >= INTRADAY_TREND_TRIGGER
        else -1 if raw_score <= -INTRADAY_TREND_TRIGGER
        else 0
    )
    strength = min(abs(raw_score) / 3.50, 1.0)

    logger.info(
        "INTRADAY TREND: bias=%+d strength=%.3f score=%+.2f "
        "net_%dbars=%+.2f recent_%dbars=%+.2f structure=%s vwap_bias=%+d",
        bias,
        strength,
        raw_score,
        len(closes) - 1,
        net_move,
        recent_count - 1,
        recent_move,
        "HH_HL" if higher_structure else "LH_LL" if lower_structure else "MIXED",
        vwap_bias,
    )
    return bias, float(strength), float(raw_score)


def timeframe_snapshot(
    spot_key: str,
) -> tuple[dict[int, pd.DataFrame], dict[int, int]]:
    frames: dict[int, pd.DataFrame] = {}
    directions: dict[int, int] = {}

    for tf in TIMEFRAMES:
        bars = get_timeframe_candles(
            spot_key,
            tf,
            min_bars=35 if tf <= 15 else 30,
        )
        completed = filter_completed_candles(bars, tf)

        # At the very first scan of a session, higher TF completed candles may
        # intentionally come from the prior session. That is preferable to
        # manufacturing a Supertrend from 1-2 new candles.
        if len(completed) < 25:
            raise ScannerError(
                f"Too few completed {tf}m candles for a stable Supertrend."
            )

        st = calculate_supertrend(
            completed,
            period=SUPERTREND_PERIOD,
            factor=SUPERTREND_FACTOR,
        )

        frames[tf] = st

        latest_dir = safe_float(st["direction"].iloc[-1], 0.0)
        directions[tf] = 1 if latest_dir > 0 else -1 if latest_dir < 0 else 0

        logger.info(
            "TF %dm: Supertrend=%s level=%.2f structure=%s",
            tf,
            "BULLISH" if directions[tf] > 0 else "BEARISH" if directions[tf] < 0 else "NEUTRAL",
            safe_float(st["supertrend"].iloc[-1]),
            market_structure_state(st, 8),
        )

    return frames, directions


# =============================================================================
# MARKET STRUCTURE ENGINE
# =============================================================================

def build_market_structure(
    spot: float,
    futures_3m: pd.DataFrame,
    futures_session: pd.DataFrame,
    tf_frames: dict[int, pd.DataFrame],
    tf_directions: dict[int, int],
    chain_levels: dict[str, Any],
    daily_oi_bias: int,
    daily_oi_score: float,
    change_oi_bias: int,
    change_oi_score: float,
    futures_live_quote: Optional[dict[str, Any]] = None,
) -> StructureResult:
    """
    Trend-first market-structure engine.

    Design:
      1. Fast intraday price action + 3m/15m structure + VWAP establish the
         directional core.
      2. Futures OI, option-chain OI and daily/change-OI confirm or weaken it.
      3. 60/120/180m Supertrends provide context but do not veto a clear
         intraday reversal.
      4. A strong opposite chain wall is a caution, not an automatic veto.
    """
    vwap, vwap_slope, vwap_level_bias = vwap_snapshot(futures_session)
    intraday_bias, intraday_strength, intraday_score = intraday_trend_snapshot(
        futures_session,
        vwap,
    )
    futures_info = futures_oi_structure(futures_3m, futures_live_quote)
    if futures_3m is None or len(futures_3m) < 4:
        live_price = safe_float((futures_live_quote or {}).get("last_price"), spot)
        futures_info["regime"] = "OPENING_PRICE_ONLY"
        futures_info["bias"] = 1 if live_price > vwap else -1 if live_price < vwap else 0
        futures_info["oi_strength"] = 0.0
        futures_info["oi_persistence"] = 0.0
        futures_info["price_delta"] = 0.0
        futures_info["oi_delta"] = 0.0
        futures_info["live_oi_change"] = float("nan")
        futures_info["oi_acceleration"] = 0.0
    futures_regime = str(futures_info["regime"])
    futures_bias = int(futures_info["bias"])

    structure_3 = market_structure_state(tf_frames[3], 8)
    structure_15 = market_structure_state(tf_frames[15], 3)
    structure_3_bias = 1 if structure_3 == "BULLISH" else -1 if structure_3 == "BEARISH" else 0
    structure_15_bias = 1 if structure_15 == "BULLISH" else -1 if structure_15 == "BEARISH" else 0

    atr3 = max(safe_float(tf_frames[3]["atr"].iloc[-1]), 1.0)
    slope_threshold = max(0.20, atr3 * 0.03)
    vwap_slope_bias = (
        1 if vwap_slope > slope_threshold
        else -1 if vwap_slope < -slope_threshold
        else 0
    )

    chain_bias = int(chain_levels.get("oi_bias", 0))
    chain_change_bias = int(chain_levels.get("change_bias", 0))
    chain_predictive_bias = int(chain_levels.get("predictive_bias", 0))
    chain_predictive_strength = float(chain_levels.get("predictive_strength", 0.0))
    chain_level_bias = int(chain_levels.get("level_bias", 0))

    # -------------------------------------------------------------------------
    # Directional core: price/VWAP action is deliberately stronger than slow
    # positioning inputs.
    # -------------------------------------------------------------------------
    structure_30_bias = tf_directions.get(30, 0)
    core_components = {
        "intraday_trend": 3.40 * intraday_bias * max(0.55, intraday_strength),
        "vwap_level": 2.40 * vwap_level_bias,
        "vwap_slope": 1.40 * vwap_slope_bias,
        "structure_3m": 2.00 * structure_3_bias,
        "structure_15m": 1.80 * structure_15_bias,
        "structure_30m": 1.20 * structure_30_bias,
    }
    core_score = float(sum(core_components.values()))

    # -------------------------------------------------------------------------
    # Context/confirmation: useful, but cannot erase a strong intraday reversal
    # merely because a slow OI wall has not caught up yet.
    # -------------------------------------------------------------------------
    tf_component = sum(
        TF_WEIGHTS[tf] * tf_directions.get(tf, 0)
        for tf in TIMEFRAMES
    )
    futures_component = 2.00 * futures_bias * max(0.65, float(futures_info["oi_strength"]))
    chain_component = 1.10 * chain_predictive_bias * max(
        0.45, chain_predictive_strength
    )
    chain_level_component = 0.70 * chain_level_bias
    option_oi_component = 0.65 * chain_bias
    option_change_component = 0.65 * chain_change_bias
    daily_oi_component = 0.45 * int(daily_oi_bias)
    change_api_component = 0.45 * int(change_oi_bias)

    context_components = {
        "futures": futures_component,
        "multi_tf_supertrend": 0.55 * tf_component,
        "chain_predictive": chain_component,
        "chain_levels": chain_level_component,
        "option_oi": option_oi_component,
        "option_oi_change": option_change_component,
        "daily_oi": daily_oi_component,
        "change_oi_api": change_api_component,
        "chain_wall_imbalance": 0.75 * (
            float(chain_levels.get("support_strength", 0.0))
            - float(chain_levels.get("resistance_strength", 0.0))
        ),
    }

    components: dict[str, float] = {}
    components.update(core_components)
    components.update(context_components)
    components["futures_oi_strength"] = 0.80 * futures_info["oi_strength"] * futures_bias
    total_score = float(sum(components.values()))

    directional_groups = [
        intraday_bias,
        vwap_level_bias,
        vwap_slope_bias,
        structure_3_bias,
        structure_15_bias,
        futures_bias,
        *[tf_directions.get(tf, 0) for tf in TIMEFRAMES],
        chain_bias,
        chain_change_bias,
        chain_predictive_bias,
        chain_level_bias,
        daily_oi_bias,
        change_oi_bias,
    ]
    bullish_groups = sum(x > 0 for x in directional_groups)
    bearish_groups = sum(x < 0 for x in directional_groups)

    # -------------------------------------------------------------------------
    # Explicit core trigger.
    # A direction is eligible when the fast trend is aligned with VWAP or
    # VWAP slope and at least one of 3m/15m structure agrees.
    # -------------------------------------------------------------------------
    fast_bull_votes = sum(x > 0 for x in (structure_3_bias, structure_15_bias, structure_30_bias))
    fast_bear_votes = sum(x < 0 for x in (structure_3_bias, structure_15_bias, structure_30_bias))

    bull_price_core = (
        intraday_bias > 0
        and (fast_bull_votes >= 2 or (structure_3_bias > 0 and intraday_strength >= 0.50))
        and (vwap_level_bias > 0 or vwap_slope_bias > 0)
    )
    bear_price_core = (
        intraday_bias < 0
        and (fast_bear_votes >= 2 or (structure_3_bias < 0 and intraday_strength >= 0.50))
        and (vwap_level_bias < 0 or vwap_slope_bias < 0)
    )

    # Short-covering is explicitly bullish; long-unwinding is explicitly bearish.
    bullish_futures_confirmation = (
        futures_bias > 0
        and futures_info["oi_strength"] >= FUTURES_OI_STRENGTH_THRESHOLD
        and (
            futures_regime in {"LONG_BUILDUP", "SHORT_COVERING"}
            or futures_info["oi_persistence"] >= 0.35
        )
    )
    bearish_futures_confirmation = (
        futures_bias < 0
        and futures_info["oi_strength"] >= FUTURES_OI_STRENGTH_THRESHOLD
        and (
            futures_regime in {"SHORT_BUILDUP", "LONG_UNWINDING"}
            or futures_info["oi_persistence"] >= 0.35
        )
    )

    bullish_confirmation_count = sum(
        [
            bullish_futures_confirmation,
            chain_predictive_bias > 0 and chain_predictive_strength >= 0.15,
            chain_level_bias > 0,
            daily_oi_bias > 0,
            change_oi_bias > 0,
        ]
    )
    bearish_confirmation_count = sum(
        [
            bearish_futures_confirmation,
            chain_predictive_bias < 0 and chain_predictive_strength >= 0.15,
            chain_level_bias < 0,
            daily_oi_bias < 0,
            change_oi_bias < 0,
        ]
    )

    # A strong opposite positioning signal lowers confidence but does not veto
    # an already-established intraday price trend. The exception is a very
    # strong positioning conflict combined with weak price-core evidence.
    strong_opposite_to_bull = (
        chain_predictive_bias < 0
        and chain_predictive_strength >= POSITIONING_HARD_OPPOSITE_STRENGTH
        and intraday_strength < 0.70
        and structure_3_bias <= 0
    )
    strong_opposite_to_bear = (
        chain_predictive_bias > 0
        and chain_predictive_strength >= POSITIONING_HARD_OPPOSITE_STRENGTH
        and intraday_strength < 0.70
        and structure_3_bias >= 0
    )

    predictive_bull_surge = (
        vwap_level_bias > 0 
        and (
            (futures_regime == "LONG_BUILDUP" and futures_info["oi_acceleration"] >= 1.50)
            or (chain_predictive_bias > 0 and chain_predictive_strength >= 0.35)
        )
    )

    predictive_bear_surge = (
      vwap_level_bias < 0 
        and (
            (futures_regime == "SHORT_BUILDUP" and futures_info["oi_acceleration"] >= 1.50)
            or (chain_predictive_bias < 0 and chain_predictive_strength >= 0.35)
        )
    )
      
    bullish_trigger = (
        bull_price_core
        and (core_score >= CORE_BULL_TRIGGER or predictive_bull_surge)
        and (bullish_confirmation_count >= 1 or intraday_strength >= 0.62 or abs(core_score) >= 4.25 or predictive_bull_surge)
        and not strong_opposite_to_bull
    )
    bearish_trigger = (
        bear_price_core
        and (core_score <= CORE_BEAR_TRIGGER or predictive_bear_surge)
        and (bearish_confirmation_count >= 1 or intraday_strength >= 0.62 or abs(core_score) >= 4.25 or predictive_bear_surge)
        and not strong_opposite_to_bear
    )

    # Fallback for decisive multi-factor moves even when one core input is
    # temporarily stale/missing.
    if bullish_trigger:
        direction = "BULLISH"
    elif bearish_trigger:
        direction = "BEARISH"
    elif total_score >= ENTRY_SCORE and bullish_groups >= MIN_DIRECTIONAL_COMPONENTS and intraday_bias > 0:
        direction = "BULLISH"
    elif total_score <= -ENTRY_SCORE and bearish_groups >= MIN_DIRECTIONAL_COMPONENTS and intraday_bias < 0:
        direction = "BEARISH"
    else:
        direction = "NEUTRAL"

    # Confidence is based on evidence supporting the selected direction.
    selected_groups = bullish_groups if direction == "BULLISH" else bearish_groups if direction == "BEARISH" else max(bullish_groups, bearish_groups)
    alignment = selected_groups / max(len(directional_groups), 1)

    core_magnitude = min(abs(core_score) / 8.0, 1.0)
    total_magnitude = min(abs(total_score) / 12.0, 1.0)
    confirmation_factor = min(
        1.0,
        (
            bullish_confirmation_count if direction == "BULLISH"
            else bearish_confirmation_count if direction == "BEARISH"
            else 0
        ) / 3.0,
    )

    if direction != "NEUTRAL":
        confidence = (
            50.0
            + 25.0 * core_magnitude
            + 14.0 * intraday_strength
            + 7.0 * alignment
            + 8.0 * confirmation_factor
        )
    else:
        confidence = (
            15.0
            + 24.0 * core_magnitude
            + 16.0 * total_magnitude
            + 15.0 * alignment
        )

    confidence = min(99.0, max(0.0, confidence))

    interpretation = (
        "STRONG BEARISH MARKET STRUCTURE" if direction == "BEARISH" and confidence >= 80 else
        "BEARISH MARKET STRUCTURE" if direction == "BEARISH" else
        "STRONG BULLISH MARKET STRUCTURE" if direction == "BULLISH" and confidence >= 80 else
        "BULLISH MARKET STRUCTURE" if direction == "BULLISH" else
        "WAIT / MIXED MARKET STRUCTURE"
    )

    support_1 = float(chain_levels["support_1"])
    support_2 = float(chain_levels["support_2"])
    resistance_1 = float(chain_levels["resistance_1"])
    resistance_2 = float(chain_levels["resistance_2"])

    reasons: list[str] = [
        f"Intraday trend engine: bias={intraday_bias:+d}; strength={intraday_strength:.3f}; raw_score={intraday_score:+.2f}.",
        f"Fast directional core score={core_score:+.2f}; total market score={total_score:+.2f}.",
        f"Futures OI engine: regime={futures_regime}; price_delta={futures_info['price_delta']:+.2f}; OI_delta={futures_info['oi_delta']:+.0f}; persistence={futures_info['oi_persistence']:.2f}; strength={futures_info['oi_strength']:.3f}.",
        f"Futures live OI change versus last completed candle={futures_info['live_oi_change']:+.0f}.",
        f"Spot={spot:.2f}; Futures VWAP={vwap:.2f}; VWAP slope={vwap_slope:+.2f}.",
        f"Fast structure: 3m={structure_3}; 15m={structure_15}; 30m={'BULLISH' if structure_30_bias > 0 else 'BEARISH' if structure_30_bias < 0 else 'NEUTRAL'}.",
        "Multi-timeframe Supertrend=" + ", ".join(
            f"{tf}m:{'BULL' if tf_directions.get(tf,0)>0 else 'BEAR' if tf_directions.get(tf,0)<0 else 'NEUTRAL'}"
            for tf in TIMEFRAMES
        ),
        f"Option-chain walls: support={support_1:.0f}/{support_2:.0f}; resistance={resistance_1:.0f}/{resistance_2:.0f}.",
        f"Chain predictive bias={chain_predictive_bias:+d}; strength={chain_predictive_strength:.3f}; level_bias={chain_level_bias:+d}.",
        f"Daily OI API bias={daily_oi_bias:+d} score={daily_oi_score:+.3f}; Change-OI API bias={change_oi_bias:+d} score={change_oi_score:+.3f}.",
        f"Bull confirmations={bullish_confirmation_count}; bear confirmations={bearish_confirmation_count}.",
        f"Directional groups bullish={bullish_groups}, bearish={bearish_groups}.",
        "Decision hierarchy: intraday price/VWAP core first; derivatives positioning confirms and does not veto a strong intraday reversal unless price-core evidence is weak.",
    ]

    logger.info(
        "MARKET STRUCTURE V3: score=%+.2f core=%+.2f direction=%s confidence=%.1f | "
        "Intraday=%+d/%.3f Futures=%s/%.3f ChainPred=%+d/%.3f VWAP=%s | TF=%s | "
        "BullConf=%d BearConf=%d",
        total_score,
        core_score,
        direction,
        confidence,
        intraday_bias,
        intraday_strength,
        futures_regime,
        futures_info["oi_strength"],
        chain_predictive_bias,
        chain_predictive_strength,
        "ABOVE" if vwap_level_bias > 0 else "BELOW" if vwap_level_bias < 0 else "AT",
        ",".join(
            f"{tf}:{'B' if tf_directions.get(tf,0)>0 else 'S' if tf_directions.get(tf,0)<0 else 'N'}"
            for tf in TIMEFRAMES
        ),
        bullish_confirmation_count,
        bearish_confirmation_count,
    )

    return StructureResult(
        direction=direction,
        score=total_score,
        confidence=confidence,
        interpretation=interpretation,
        components=components,
        timeframe_directions={str(k): int(v) for k, v in tf_directions.items()},
        vwap=vwap,
        vwap_slope=vwap_slope,
        futures_regime=futures_regime,
        futures_bias=futures_bias,
        futures_oi_strength=float(futures_info["oi_strength"]),
        futures_oi_persistence=float(futures_info["oi_persistence"]),
        futures_live_oi_change=float(futures_info["live_oi_change"]),
        intraday_bias=int(intraday_bias),
        intraday_strength=float(intraday_strength),
        intraday_score=float(intraday_score),
        chain_predictive_bias=chain_predictive_bias,
        chain_predictive_strength=chain_predictive_strength,
        chain_level_bias=chain_level_bias,
        support_strength=float(chain_levels.get("support_strength", 0.0)),
        resistance_strength=float(chain_levels.get("resistance_strength", 0.0)),
        support_change_strength=float(chain_levels.get("support_change_strength", 0.0)),
        resistance_change_strength=float(chain_levels.get("resistance_change_strength", 0.0)),
        support_1=support_1,
        support_2=support_2,
        resistance_1=resistance_1,
        resistance_2=resistance_2,
        reasons=reasons,
    )


# =============================================================================
# OPTION SELECTION
# =============================================================================

def contract_lookup_from_chain(
    chain: list[dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in chain:
        if not isinstance(row, dict):
            continue
        strike = safe_float(row.get("strike_price"), float("nan"))
        if not math.isfinite(strike):
            continue

        for option_type in ("CE", "PE"):
            data = option_side_data(row, option_type)
            key = data.get("instrument_key")
            if key:
                out[str(key)] = {
                    "strike": strike,
                    "type": option_type,
                    "data": data,
                    "expiry": str(row.get("expiry", ""))[:10],
                }
    return out


def build_option_candidate(
    contract_meta: dict[str, Any],
    chain_data: dict[str, Any],
) -> OptionCandidate:
    # Accept either the wrapped contract-lookup object or raw option-side data.
    data = chain_data.get("data", chain_data)

    ltp = safe_float(data["ltp"])
    bid = safe_float(data["bid"])
    ask = safe_float(data["ask"])

    if ltp <= 0:
        raise ScannerError("Option LTP is invalid.")

    if bid > 0 and ask > 0 and ask >= bid:
        mid = (bid + ask) / 2.0
        spread_pct = (ask - bid) / mid if mid > 0 else 1.0
    else:
        spread_pct = 1.0

    theta = safe_float(data["theta"])
    theta_burden = abs(theta) / ltp if ltp > 0 else float("inf")

    delta = safe_float(data["delta"], float("nan"))
    if not math.isfinite(delta):
        raise ScannerError("Option delta unavailable.")

    return OptionCandidate(
        instrument_key=str(data["instrument_key"]),
        trading_symbol=str(
            data.get("trading_symbol")
            or contract_meta.get("trading_symbol")
            or data["instrument_key"]
        ),
        option_type=str(contract_meta["type"]),
        strike=float(contract_meta["strike"]),
        expiry=str(contract_meta["expiry"]),
        ltp=ltp,
        oi=safe_float(data["oi"]),
        prev_oi=safe_float(data["prev_oi"]),
        volume=safe_float(data["volume"]),
        bid=bid,
        ask=ask,
        bid_qty=safe_float(data["bid_qty"]),
        ask_qty=safe_float(data["ask_qty"]),
        delta=delta,
        gamma=safe_float(data["gamma"]),
        theta=theta,
        iv=safe_float(data["iv"]),
        spread_pct=spread_pct,
        theta_burden_pct_day=theta_burden,
    )


def option_health_score(
    option: OptionCandidate,
    atm: float,
    step: float,
) -> float:
    delta_abs = abs(option.delta)
    delta_score = max(
        0.0,
        1.0 - abs(delta_abs - 0.55) / 0.30,
    )

    spread_score = max(0.0, 1.0 - option.spread_pct / MAX_SPREAD_PCT)
    intraday_theta_burden = (
        option.theta_burden_pct_day
        * EXPECTED_HOLDING_MINUTES
        / 375.0
    )
    # Soft theta penalty: higher expected time-decay lowers the health score,
    # but does not make the candidate ineligible by itself. The formula is
    # monotonic and bounded, so even expiry-day options remain selectable when
    # the underlying, spread, liquidity and delta filters are healthy.
    theta_score = 1.0 / (1.0 + intraday_theta_burden / THETA_WARNING_BURDEN)

    liquidity_base = math.log1p(max(option.volume, 0.0))
    oi_base = math.log1p(max(option.oi, 0.0))
    liquidity_score = min(1.0, (liquidity_base + oi_base) / 20.0)

    distance_steps = abs(option.strike - atm) / step if step > 0 else 0.0
    distance_score = 1.0 if distance_steps <= 2.0 else 0.5

    return (
        0.30 * delta_score
        + 0.30 * spread_score
        + 0.20 * theta_score
        + 0.15 * liquidity_score
        + 0.05 * distance_score
    )


def select_directional_option(
    chain: list[dict[str, Any]],
    direction: str,
    spot: float,
) -> OptionCandidate:
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("Option selection requires BULLISH or BEARISH.")

    rows = chain_rows(chain)
    strikes = sorted(rows)
    step = strike_step(strikes)
    atm = nearest_strike(spot, strikes)

    candidate_strikes = (
        [atm - step, atm - 2 * step, atm]
        if direction == "BULLISH"
        else [atm + step, atm + 2 * step, atm]
    )
    option_type = "CE" if direction == "BULLISH" else "PE"

    candidates: list[OptionCandidate] = []
    rejection_log: list[str] = []

    for target in candidate_strikes:
        target = round(float(target), 2)

        # Never depend on exact float equality.
        row_key = min(strikes, key=lambda s: abs(s - target))
        if abs(row_key - target) > 0.01:
            rejection_log.append(f"{option_type} {target:.0f} absent from chain")
            continue

        data = option_side_data(rows[row_key], option_type)

        if not data["instrument_key"]:
            rejection_log.append(f"{option_type} {row_key:.0f}: no instrument key")
            continue

        if data["ltp"] <= 0:
            rejection_log.append(f"{option_type} {row_key:.0f}: invalid LTP")
            continue

        if data["oi"] < MIN_OI:
            rejection_log.append(
                f"{option_type} {row_key:.0f}: OI {data['oi']:.0f} below {MIN_OI:.0f}"
            )
            continue

        if data["volume"] < MIN_VOLUME:
            rejection_log.append(
                f"{option_type} {row_key:.0f}: volume {data['volume']:.0f} below {MIN_VOLUME:.0f}"
            )
            continue

        delta = safe_float(data["delta"], float("nan"))
        if not math.isfinite(delta):
            if option_type == "CE":
               delta = 0.50 + ((spot - target) / (2 * step)) * 0.15
            else:
                delta = -0.50 - ((target - spot) / (2 * step)) * 0.15
                delta = max(-0.95, min(0.95, delta))
            data["delta"] = delta

        bid = safe_float(data["bid"])
        ask = safe_float(data["ask"])
        if bid <= 0 or ask <= 0 or ask < bid:
            rejection_log.append(
                f"{option_type} {row_key:.0f}: invalid bid/ask"
            )
            continue

        mid = (bid + ask) / 2.0
        spread_pct = (ask - bid) / mid if mid > 0 else 1.0
        if spread_pct > MAX_SPREAD_PCT:
            rejection_log.append(
                f"{option_type} {row_key:.0f}: spread={spread_pct:.1%}"
            )
            continue

        theta = safe_float(data["theta"])
        theta_burden = abs(theta) / data["ltp"] if data["ltp"] > 0 else 999.0

        # Upstox exposes theta as a time-decay measure. For ranking a long
        # intraday option, we linearize it to the planned holding window only
        # as a risk estimate. This is intentionally NOT a hard rejection rule,
        # because theta is non-linear near expiry and can become very large.
        trading_day_minutes = 375.0  # 09:15-15:30 IST
        intraday_theta_burden = (
            theta_burden * EXPECTED_HOLDING_MINUTES / trading_day_minutes
        )
        if intraday_theta_burden > THETA_WARNING_BURDEN:
            logger.info(
                "OPTION HEALTH WARNING: %s %.0f has estimated %.1f%% theta burden for the planned holding window; ranking penalty only.",
                option_type, row_key, intraday_theta_burden * 100.0,
            )
        meta = {
            "strike": row_key,
            "type": option_type,
            "expiry": str(rows[row_key].get("expiry", ""))[:10],
        }
        candidate = build_option_candidate(meta, data)
        candidates.append(candidate)

    if not candidates:
        detail = "; ".join(rejection_log[-8:]) or "no valid candidates"
        raise ScannerError(
            f"No healthy directional {option_type} option. {detail}"
        )

    selected = max(
        candidates,
        key=lambda x: option_health_score(x, atm, step),
    )

    logger.info(
        "OPTION SELECT: direction=%s ATM=%.0f -> %s %.0f | "
        "LTP=%.2f OI=%.0f volume=%.0f delta=%.3f spread=%.2f%% "
        "theta=%.4f burden=%.2f%%/day",
        direction, atm, selected.trading_symbol, selected.strike,
        selected.ltp, selected.oi, selected.volume, selected.delta,
        selected.spread_pct * 100.0, selected.theta,
        selected.theta_burden_pct_day * 100.0,
    )
    return selected


# =============================================================================
# DYNAMIC LEVEL / GREEK TARGET ENGINE
# =============================================================================

def choose_underlying_levels(
    structure: StructureResult,
    spot: float,
    tf_frames: dict[int, pd.DataFrame],
) -> tuple[float, float, float]:
    """
    Returns:
        underlying_target_1,
        underlying_target_2,
        underlying_stop
    """
    atr3 = safe_float(tf_frames[3]["atr"].iloc[-1], 0.0)
    atr15 = safe_float(tf_frames[15]["atr"].iloc[-1], 0.0)

    max_allowed_atr = spot * 0.0025
    atr3 = min(max(atr3, 1.0), max_allowed_atr)
    atr15 = min(max(atr15, atr3), max_allowed_atr * 1.5)

    # Use 15m ST for invalidation, but never place it unrealistically close.
    st15 = safe_float(tf_frames[15]["supertrend"].iloc[-1], spot)

    if structure.direction == "BEARISH":
        support1 = structure.support_1
        support2 = structure.support_2

        # If the chain support is too close, project an ATR extension instead.
        t1_floor = spot - 0.55 * atr3
        t2_floor = spot - max(1.10 * atr15, 1.10 * atr3)

        if support1 < spot and (spot - support1) >= 0.40 * atr3:
            target1 = support1
        else:
            target1 = t1_floor

        if support2 < target1 and (spot - support2) >= 0.90 * atr3:
            target2 = support2
        else:
            target2 = min(t2_floor, target1 - 0.45 * atr15)

        # Bearish invalidation must clear normal intraday noise and sit above
        # VWAP/15m ST when those are on the wrong side.
        resistance_buffer = 0.35 * atr3
        stop_candidates = [
            structure.vwap + 0.25 * atr3,
            st15 + 0.20 * atr15,
            spot + 0.80 * atr3,
            structure.resistance_1 + resistance_buffer
            if structure.resistance_1 > spot else spot + 0.80 * atr3,
        ]
        underlying_stop = max(stop_candidates)

        if underlying_stop <= spot:
            underlying_stop = spot + 0.80 * atr3

    else:
        resistance1 = structure.resistance_1
        resistance2 = structure.resistance_2

        t1_ceiling = spot + 0.55 * atr3
        t2_ceiling = spot + max(1.10 * atr15, 1.10 * atr3)

        if resistance1 > spot and (resistance1 - spot) >= 0.40 * atr3:
            target1 = resistance1
        else:
            target1 = t1_ceiling

        if resistance2 > target1 and (resistance2 - spot) >= 0.90 * atr3:
            target2 = resistance2
        else:
            target2 = max(t2_ceiling, target1 + 0.45 * atr15)

        support_buffer = 0.35 * atr3
        stop_candidates = [
            structure.vwap - 0.25 * atr3,
            st15 - 0.20 * atr15,
            spot - 0.80 * atr3,
            structure.support_1 - support_buffer
            if structure.support_1 < spot else spot - 0.80 * atr3,
        ]
        underlying_stop = min(stop_candidates)

        if underlying_stop >= spot:
            underlying_stop = spot - 0.80 * atr3

    return float(target1), float(target2), float(underlying_stop)


def project_option_premium(
    entry: float,
    underlying_move: float,
    delta: float,
    gamma: float,
) -> float:
    """
    Second-order local Greek approximation:
        Î”premium â‰ˆ |delta| * |dS| + 0.5 * |gamma| * dSÂ²

    This is deliberately used only for target/stop estimation, not execution.
    """
    move = abs(float(underlying_move))
    change = abs(delta) * move + 0.5 * abs(gamma) * move * move
    return float(max(0.0, entry + change))


def create_dynamic_targets(
    option: OptionCandidate,
    structure: StructureResult,
    spot: float,
    tf_frames: dict[int, pd.DataFrame],
) -> tuple[float, float, float, float, float, float]:
    """Create option and underlying targets without allowing risk math to crash a valid signal.

    Important: the option is long, so an adverse underlying move must reduce
    premium. The previous implementation accidentally used the *positive*
    premium projection for the adverse move; with a high-delta/high-gamma
    option that could make ``adverse_premium >= entry`` and produce zero risk.
    """
    target_u1, target_u2, stop_u = choose_underlying_levels(
        structure, spot, tf_frames,
    )

    atr3 = max(safe_float(tf_frames[3]["atr"].iloc[-1], 0.0), 1.0)
    atr15 = max(safe_float(tf_frames[15]["atr"].iloc[-1], atr3), atr3)

    # Final defensive validation/fallback for unusual chain levels.
    if structure.direction == "BEARISH":
        if target_u1 >= spot:
            target_u1 = spot - 0.75 * atr3
        if target_u2 >= target_u1:
            target_u2 = target_u1 - max(0.75 * atr3, 0.50 * atr15)
        if stop_u <= spot:
            stop_u = spot + 0.80 * atr3
        move_t1 = spot - target_u1
        move_t2 = spot - target_u2
        adverse_move = stop_u - spot
    else:
        if target_u1 <= spot:
            target_u1 = spot + 0.75 * atr3
        if target_u2 <= target_u1:
            target_u2 = target_u1 + max(0.75 * atr3, 0.50 * atr15)
        if stop_u >= spot:
            stop_u = spot - 0.80 * atr3
        move_t1 = target_u1 - spot
        move_t2 = target_u2 - spot
        adverse_move = spot - stop_u

    if move_t1 <= 0:
        move_t1 = 0.75 * atr3
        target_u1 = spot + move_t1 if structure.direction == "BULLISH" else spot - move_t1
    if move_t2 <= move_t1:
        move_t2 = max(1.25 * atr15, move_t1 + 0.50 * atr3)
        target_u2 = spot + move_t2 if structure.direction == "BULLISH" else spot - move_t2
    if adverse_move <= 0:
        adverse_move = 0.80 * atr3
        stop_u = spot - adverse_move if structure.direction == "BULLISH" else spot + adverse_move

    target1 = project_option_premium(option.ltp, move_t1, option.delta, option.gamma)
    target2 = project_option_premium(option.ltp, move_t2, option.delta, option.gamma)

    # Correct signed adverse-premium estimate for a LONG option.
    # First order loses premium; gamma partially offsets that loss.
    delta_abs = abs(option.delta)
    gamma_abs = abs(option.gamma)
    estimated_loss = (delta_abs * adverse_move) - (0.5 * gamma_abs * adverse_move * adverse_move)
    estimated_loss = max(0.0, estimated_loss)

    # Always keep a real, bounded monetary risk. This is a safety bound, not
    # a directional veto. Near-expiry/high-gamma options can otherwise make
    # the second-order approximation mathematically negative.
    min_loss = option.ltp * OPTION_MIN_STOP_PCT
    max_loss = option.ltp * OPTION_MAX_STOP_PCT
    risk = min(max(estimated_loss, min_loss), max_loss)
    stop_loss = option.ltp - risk

    # Guarantee valid ordering without rejecting a structurally valid market
    # signal merely because the option's local Greek approximation is noisy.
    min_t1 = option.ltp + MIN_T1_RISK_REWARD * risk
    min_t2 = option.ltp + MIN_T2_RISK_REWARD * risk
    target1 = max(target1, min_t1)
    target2 = max(target2, min_t2, target1 + 0.25 * risk)

    if not (stop_loss < option.ltp < target1 < target2):
        raise ScannerError(
            f"Invalid option risk levels after fallback: entry={option.ltp:.2f}, "
            f"SL={stop_loss:.2f}, T1={target1:.2f}, T2={target2:.2f}."
        )

    logger.info(
        "OPTION RISK: entry=%.2f SL=%.2f risk=%.2f (%.1f%%) T1=%.2f T2=%.2f | "
        "underlying T1=%.2f T2=%.2f SL=%.2f",
        option.ltp, stop_loss, risk, 100.0 * risk / option.ltp,
        target1, target2, target_u1, target_u2, stop_u,
    )

    return (
        round(target1, 2), round(target2, 2), round(stop_loss, 2),
        round(stop_u, 2), round(target_u1, 2), round(target_u2, 2),
    )


# =============================================================================
# STATE
# =============================================================================

def load_state() -> dict[str, Any]:
    if not STATE_FILE.exists():
        return {}

    try:
        with STATE_FILE.open("r", encoding="utf-8") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else {}
    except Exception as exc:
        logger.warning("State load failed: %s", exc)
        return {}


def save_state(state: dict[str, Any]) -> None:
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    tmp = STATE_FILE.with_suffix(".tmp")

    with tmp.open("w", encoding="utf-8") as fh:
        json.dump(state, fh, indent=2, ensure_ascii=False)

    tmp.replace(STATE_FILE)


def active_trade_from_state(
    state: dict[str, Any],
) -> Optional[dict[str, Any]]:
    trade = state.get("active_trade")
    if not isinstance(trade, dict):
        return None

    if str(trade.get("status", "")).upper() != "ACTIVE":
        return None

    required = {
        "instrument_key",
        "trading_symbol",
        "direction",
        "entry",
        "target_1",
        "target_2",
        "stop_loss",
    }
    return trade if required.issubset(trade) else None


def signal_hash(signal: Signal) -> str:
    key = "|".join(
        [
            signal.direction,
            signal.instrument_key,
            str(signal.strike),
            signal.timestamp[:10],
        ]
    )
    return hashlib.sha256(key.encode("utf-8")).hexdigest()


# =============================================================================
# EMAIL
# =============================================================================

def send_email(subject: str, body: str) -> None:
    if not all([EMAIL_SENDER, EMAIL_PASSWORD, EMAIL_RECEIVER]):
        logger.info("Email not configured; skipping email.")
        return

    message = MIMEMultipart("alternative")
    message["From"] = EMAIL_SENDER
    message["To"] = EMAIL_RECEIVER
    message["Subject"] = subject
    message.attach(MIMEText(body, "html", "utf-8"))

    with smtplib.SMTP_SSL(
        SMTP_HOST,
        SMTP_PORT,
        timeout=30,
    ) as server:
        server.login(EMAIL_SENDER, EMAIL_PASSWORD)
        server.sendmail(
            EMAIL_SENDER,
            [EMAIL_RECEIVER],
            message.as_string(),
        )


def signal_email_body(signal: Signal) -> str:
    reasons = "".join(
        f"<li>{html.escape(reason)}</li>"
        for reason in signal.reasons
    )

    return f"""
<html>
<body>
<h2>SENSEX Predictive {html.escape(signal.direction)} Signal</h2>
<table border="1" cellpadding="6" cellspacing="0">
<tr><td><b>Time</b></td><td>{html.escape(signal.timestamp)}</td></tr>
<tr><td><b>Regime</b></td><td>{html.escape(signal.regime)}</td></tr>
<tr><td><b>Confidence</b></td><td>{signal.confidence:.1f}%</td></tr>
<tr><td><b>Spot</b></td><td>{signal.spot:.2f}</td></tr>
<tr><td><b>Futures Regime</b></td><td>{html.escape(signal.futures_state)}</td></tr>
<tr><td><b>Option</b></td><td>{html.escape(signal.trading_symbol)}</td></tr>
<tr><td><b>Strike</b></td><td>{signal.strike:.0f} {signal.option_type}</td></tr>
<tr><td><b>Entry</b></td><td>â‚¹{signal.entry:.2f}</td></tr>
<tr><td><b>Target 1</b></td><td>â‚¹{signal.target_1:.2f}</td></tr>
<tr><td><b>Target 2</b></td><td>â‚¹{signal.target_2:.2f}</td></tr>
<tr><td><b>Stop Loss</b></td><td>â‚¹{signal.stop_loss:.2f}</td></tr>
<tr><td><b>Underlying T1</b></td><td>{signal.underlying_target_1:.2f}</td></tr>
<tr><td><b>Underlying T2</b></td><td>{signal.underlying_target_2:.2f}</td></tr>
<tr><td><b>Underlying SL</b></td><td>{signal.underlying_stop:.2f}</td></tr>
<tr><td><b>Delta</b></td><td>{signal.delta:.4f}</td></tr>
<tr><td><b>Gamma</b></td><td>{signal.gamma:.6f}</td></tr>
<tr><td><b>Theta</b></td><td>{signal.theta:.4f}</td></tr>
<tr><td><b>Support</b></td><td>{signal.support_1:.0f} / {signal.support_2:.0f}</td></tr>
<tr><td><b>Resistance</b></td><td>{signal.resistance_1:.0f} / {signal.resistance_2:.0f}</td></tr>
</table>

<h3>Decision factors</h3>
<ul>{reasons}</ul>

<p>This is a rule-based market signal, not a guarantee of execution,
profitability, or future price movement. No order is placed by this script.</p>
</body>
</html>
"""


# =============================================================================
# ACTIVE TRADE MONITOR
# =============================================================================

def monitor_active_trade(
    state: dict[str, Any],
    structure: StructureResult,
) -> str:
    trade = active_trade_from_state(state)
    if trade is None:
        return "NO_ACTIVE"

    today = now_ist().date().isoformat()
    trade_date = str(trade.get("trade_date", ""))[:10]

    if trade_date and trade_date != today:
        state["last_completed_trade"] = dict(
            trade,
            status="CLOSED",
            outcome="SESSION_END_CLEANUP",
            closed_at=now_ist().isoformat(),
        )
        state["active_trade"] = None
        save_state(state)
        return "CLOSED"

    try:
        ltp = extract_ltp(get_quote(str(trade["instrument_key"])))
    except ScannerError as exc:
        logger.info("Active trade quote unavailable: %s", exc)
        return "ACTIVE"

    entry = safe_float(trade.get("entry"))
    target1 = safe_float(trade.get("target_1"))
    target2 = safe_float(trade.get("target_2"))
    stop = safe_float(trade.get("stop_loss"))

    if ltp >= target2:
        outcome = "TARGET_2"
    elif ltp >= target1:
        outcome = "TARGET_1"
    elif ltp <= stop:
        outcome = "STOP_LOSS"
    else:
        outcome = ""

    if outcome:
        closed = dict(trade)
        closed.update(
            {
                "status": "CLOSED",
                "outcome": outcome,
                "exit_ltp": round(ltp, 2),
                "closed_at": now_ist().isoformat(),
            }
        )
        state["active_trade"] = None
        state["last_completed_trade"] = closed
        save_state(state)

        send_email(
            f"SENSEX TRADE {outcome} - {trade['trading_symbol']}",
            (
                f"<p>{html.escape(str(trade['direction']))} trade closed.</p>"
                f"<p>Option: {html.escape(str(trade['trading_symbol']))}<br>"
                f"Entry: â‚¹{entry:.2f}<br>"
                f"Exit: â‚¹{ltp:.2f}<br>"
                f"Outcome: {outcome}</p>"
            ),
        )
        return "CLOSED"

    active_direction = str(trade.get("direction", "")).upper()
    last_opposite = int(trade.get("reversal_confirmations", 0) or 0)

    if structure.direction == active_direction:
        last_opposite = 0
    elif structure.direction in {"BULLISH", "BEARISH"}:
        last_opposite += 1
    else:
        last_opposite = 0

    trade["reversal_confirmations"] = last_opposite
    trade["last_ltp"] = round(ltp, 2)
    trade["last_market_direction"] = structure.direction
    trade["last_market_confidence"] = structure.confidence
    trade["last_monitored_at"] = now_ist().isoformat()

    if (
        structure.direction in {"BULLISH", "BEARISH"}
        and structure.direction != active_direction
        and structure.confidence >= STRUCTURE_REVERSAL_CONFIDENCE
        and last_opposite >= REVERSAL_CONFIRMATIONS_REQUIRED
    ):
        closed = dict(trade)
        closed.update(
            {
                "status": "CLOSED",
                "outcome": "STRUCTURE_REVERSAL",
                "exit_ltp": round(ltp, 2),
                "closed_at": now_ist().isoformat(),
            }
        )
        state["active_trade"] = None
        state["last_completed_trade"] = closed
        save_state(state)

        send_email(
            f"SENSEX STRUCTURE REVERSAL - {trade['trading_symbol']}",
            (
                f"<p>Trade exited on confirmed opposite market structure.</p>"
                f"<p>Active={active_direction}; current={structure.direction}; "
                f"confidence={structure.confidence:.1f}%.</p>"
            ),
        )
        return "CLOSED"

    state["active_trade"] = trade
    save_state(state)

    logger.info(
        "ACTIVE TRADE: %s LTP=%.2f T1=%.2f T2=%.2f SL=%.2f "
        "market=%s reversal=%d/%d",
        trade["trading_symbol"],
        ltp,
        target1,
        target2,
        stop,
        structure.direction,
        last_opposite,
        REVERSAL_CONFIRMATIONS_REQUIRED,
    )
    return "ACTIVE"


# =============================================================================
# SCAN
# =============================================================================

def execute_scan(
    state: Optional[dict[str, Any]] = None,
) -> Optional[Signal]:
    if not market_window_open():
        logger.info("Outside BSE market hours.")
        return None

    status = get_market_status()
    logger.info("BSE status=%s", status)
    if status != "OPEN":
        return None

    state = state if isinstance(state, dict) else {}
    now_time = now_ist().time()
    future = get_current_sensex_future()

    # Opening robustness: never require a completed 3m candle just to run the
    # scanner. Native 3m -> 1m-resampled 3m -> historical/quote fallback.
    futures_session = get_current_session_futures_candles(future.instrument_key)
    futures_live_quote = get_quote(future.instrument_key)
    spot = extract_ltp(get_quote(SENSEX_KEY))

    # If the current session feed is late, use recent historical 3m candles for
    # OI/ATR context and keep the live quote as the current price source.
    try:
        historical_futures = get_historical_candles(future.instrument_key, 3, lookback_days=10)
        historical_completed = filter_completed_candles(historical_futures, 3)
    except ScannerError as exc:
        logger.warning("Historical futures 3m fallback unavailable: %s", exc)
        historical_completed = pd.DataFrame()

    if futures_session.empty:
        futures_3m = historical_completed.tail(40).copy()
    else:
        completed_current = filter_completed_candles(futures_session, 3)
        futures_3m = pd.concat([historical_completed.tail(35), completed_current], ignore_index=True)
        futures_3m = futures_3m.sort_values("timestamp").drop_duplicates("timestamp", keep="last").reset_index(drop=True)

    # VWAP/trend uses the live session feed. If Upstox has not published it yet,
    # build a one-bar quote proxy so 09:15 does not crash the scanner.
    if futures_session.empty:
        q = futures_live_quote
        ltp = extract_ltp(q)
        opening_ts = pd.Timestamp(now_ist()).tz_convert("UTC")
        proxy = pd.DataFrame([{
            "timestamp": opening_ts,
            "open": ltp,
            "high": ltp,
            "low": ltp,
            "close": ltp,
            "volume": safe_float(q.get("volume"), 0.0),
            "oi": _extract_quote_oi(q),
        }])
        futures_session = proxy
        logger.warning("OPENING MODE: using live futures quote proxy until intraday candles arrive.")

    tf_frames, tf_directions = timeframe_snapshot(SENSEX_KEY)
    expiry, chain = get_option_chain()
    chain_levels = chain_oi_support_resistance(chain, spot)
    daily_oi_bias, daily_oi_score = get_daily_oi_confirmation(expiry)
    change_oi_bias, change_oi_score = get_change_oi_confirmation(expiry)

    structure = build_market_structure(
        spot=spot,
        futures_3m=futures_3m,
        futures_session=futures_session,
        tf_frames=tf_frames,
        tf_directions=tf_directions,
        chain_levels=chain_levels,
        daily_oi_bias=daily_oi_bias,
        daily_oi_score=daily_oi_score,
        change_oi_bias=change_oi_bias,
        change_oi_score=change_oi_score,
        futures_live_quote=futures_live_quote,
    )

    state["market_snapshot"] = {
        "timestamp": now_ist().isoformat(), "spot": round(spot, 2),
        "future": future.trading_symbol, "future_expiry": future.expiry,
        "futures_regime": structure.futures_regime, "futures_bias": structure.futures_bias,
        "futures_oi_strength": round(structure.futures_oi_strength, 4),
        "futures_oi_persistence": round(structure.futures_oi_persistence, 4),
        "futures_live_oi_change": round(structure.futures_live_oi_change, 2) if math.isfinite(structure.futures_live_oi_change) else None,
        "intraday_bias": structure.intraday_bias, "intraday_strength": round(structure.intraday_strength, 4),
        "intraday_score": round(structure.intraday_score, 4), "chain_predictive_bias": structure.chain_predictive_bias,
        "chain_predictive_strength": round(structure.chain_predictive_strength, 4), "chain_level_bias": structure.chain_level_bias,
        "support_strength": round(structure.support_strength, 4), "resistance_strength": round(structure.resistance_strength, 4),
        "support_change_strength": round(structure.support_change_strength, 4), "resistance_change_strength": round(structure.resistance_change_strength, 4),
        "vwap": round(structure.vwap, 2), "vwap_slope": round(structure.vwap_slope, 4),
        "direction": structure.direction, "score": round(structure.score, 3), "confidence": round(structure.confidence, 2),
        "support_1": structure.support_1, "support_2": structure.support_2,
        "resistance_1": structure.resistance_1, "resistance_2": structure.resistance_2,
        "timeframes": structure.timeframe_directions, "components": structure.components,
    }
    save_state(state)

    logger.info("PREDICTION: %s | %s | confidence=%.1f score=%+.2f", structure.direction, structure.interpretation, structure.confidence, structure.score)

    if active_trade_from_state(state) is not None:
        monitor_active_trade(state, structure)
        return None

    # Do not suppress the market engine during the opening. We only gate actual
    # option entry until the first 3-minute bar has completed, unless a decisive
    # opening move is already visible in 1m/resampled data.
    completed_session_bars = len(filter_completed_candles(futures_session, 3))
    opening_mode = now_time < MIN_ENTRY_TIME or completed_session_bars < 1
    if opening_mode:
        logger.info("OPENING MODE: completed_3m_bars=%d time=%s; monitoring structure without forcing a trade.", completed_session_bars, now_time.strftime("%H:%M:%S"))
        return None

    if structure.direction == "NEUTRAL":
        logger.info("No entry: market structure is neutral/mixed.")
        return None
    if structure.confidence < SIGNAL_THRESHOLD:
        logger.info("No entry: confidence %.1f < %.1f", structure.confidence, SIGNAL_THRESHOLD)
        return None

    atr3_val = max(safe_float(tf_frames[3]["atr"].iloc[-1], 50.0), 1.0)
    vwap_distance = abs(spot - structure.vwap)
    overextended = vwap_distance > (atr3_val * OVEREXTENSION_ATR)
    decisive_trend = structure.intraday_strength >= 0.78 and abs(structure.score) >= 5.5
    if overextended and not decisive_trend:
        logger.info("No entry: price is extended %.2f points from VWAP vs %.2f ATR; waiting for pullback.", vwap_distance, OVEREXTENSION_ATR)
        return None
    if overextended and decisive_trend:
        logger.info("TREND-EXTENSION MODE: %.2f points from VWAP, but price trend is decisive; extension is not a veto.", vwap_distance)

    option = select_directional_option(chain=chain, direction=structure.direction, spot=spot)
    target1, target2, stop_loss, underlying_stop, underlying_target1, underlying_target2 = create_dynamic_targets(
        option=option, structure=structure, spot=spot, tf_frames=tf_frames,
    )

    reasons = list(structure.reasons)
    reasons.extend([
        f"Entry mode: {'TREND-EXTENSION' if overextended else 'NORMAL'}; completed 3m bars={completed_session_bars}.",
        f"Directional strike rule: {'ATM-1/ATM-2 CE' if structure.direction == 'BULLISH' else 'ATM+1/ATM+2 PE'}.",
        f"Selected option health: spread={option.spread_pct:.2%}, theta burden={option.theta_burden_pct_day:.2%}/day, volume={option.volume:.0f}, OI={option.oi:.0f}, delta={option.delta:.3f}.",
        f"Dynamic underlying targets: T1={underlying_target1:.2f}, T2={underlying_target2:.2f}, SL={underlying_stop:.2f}.",
        f"Dynamic option targets: T1=â‚¹{target1:.2f}, T2=â‚¹{target2:.2f}, SL=â‚¹{stop_loss:.2f}.",
        "Market direction is established before option selection; option premium momentum is not the primary directional trigger.",
    ])

    return Signal(
        timestamp=now_ist().strftime("%Y-%m-%d %H:%M:%S IST"), direction=structure.direction,
        regime=structure.interpretation, confidence=structure.confidence, spot=spot,
        futures_state=structure.futures_regime, option_type=option.option_type, strike=option.strike,
        trading_symbol=option.trading_symbol, instrument_key=option.instrument_key, entry=option.ltp,
        target_1=target1, target_2=target2, stop_loss=stop_loss, underlying_stop=underlying_stop,
        underlying_target_1=underlying_target1, underlying_target_2=underlying_target2,
        delta=option.delta, gamma=option.gamma, theta=option.theta,
        support_1=structure.support_1, support_2=structure.support_2,
        resistance_1=structure.resistance_1, resistance_2=structure.resistance_2, reasons=reasons,
    )


# =============================================================================
# SELF TESTS
# =============================================================================

def _synthetic_candles(
    values: list[float],
    oi: Optional[list[float]] = None,
    start: str = "2026-09-10 09:15",
) -> pd.DataFrame:
    index = pd.date_range(start, periods=len(values), freq="3min", tz="Asia/Kolkata")
    df = pd.DataFrame(
        {
            "timestamp": index.tz_convert("UTC"),
            "open": values,
            "high": [x + 2 for x in values],
            "low": [x - 2 for x in values],
            "close": values,
            "volume": [1000.0] * len(values),
            "oi": oi if oi is not None else [np.nan] * len(values),
        }
    )
    return df


def self_test() -> None:
    # Supertrend should be directional on clear monotonic series.
    down = _synthetic_candles(
        [100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85]
    )
    st_down = calculate_supertrend(down, 10, 3.0)
    assert int(st_down["direction"].iloc[-1]) == -1

    up = _synthetic_candles(
        [85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100]
    )
    st_up = calculate_supertrend(up, 10, 3.0)
    assert int(st_up["direction"].iloc[-1]) == 1

    # Futures short build-up must remain bearish even if the most recent OI move
    # is small, because the regime is built from multiple candles.
    fut = _synthetic_candles(
        [100, 99, 98, 97, 96, 95, 94, 93],
        [1000, 1020, 1050, 1080, 1100, 1120, 1130, 1131],
    )
    regime, bias, price_delta, oi_delta = futures_price_oi_regime(fut)
    assert regime == "SHORT_BUILDUP"
    assert bias == -1
    assert price_delta < 0
    assert oi_delta > 0

    # The exact failure mode from the supplied logs:
    # below VWAP + bearish futures + bearish 3m structure must not become neutral
    # merely because the 15m ST is mixed.
    frames = {
        3: st_down,
        15: calculate_supertrend(
            _synthetic_candles(
                [100, 99.8, 99.5, 99.2, 98.8, 98.5, 98.2, 97.8,
                 97.5, 97.2, 96.8, 96.5, 96.2, 95.8, 95.5, 95.2]
            ), 10, 3.0
        ),
        30: st_down,
        60: st_down,
        120: st_down,
        180: st_down,
    }
    tf_dirs = {tf: -1 for tf in TIMEFRAMES}

    chain_levels = {
        "support_1": 74000.0,
        "support_2": 73800.0,
        "resistance_1": 74200.0,
        "resistance_2": 74400.0,
        "oi_bias": -1,
        "change_bias": -1,
    }

    structure = build_market_structure(
        spot=73900.0,
        futures_3m=fut,
        futures_session=fut,
        tf_frames=frames,
        tf_directions=tf_dirs,
        chain_levels=chain_levels,
        daily_oi_bias=-1,
        daily_oi_score=-0.20,
        change_oi_bias=-1,
        change_oi_score=-0.25,
    )
    assert structure.direction == "BEARISH", structure
    assert structure.score < -ENTRY_SCORE

    # Strike selection test.
    chain = []
    for strike in [74000, 74050, 74100, 74150, 74200]:
        chain.append(
            {
                "strike_price": strike,
                "expiry": "2026-09-17",
                "call_options": {
                    "instrument_key": f"CE{strike}",
                    "market_data": {
                        "ltp": 100.0,
                        "oi": 50000,
                        "prev_oi": 49000,
                        "volume": 10000,
                        "bid_price": 99.5,
                        "ask_price": 100.5,
                        "bid_qty": 100,
                        "ask_qty": 100,
                    },
                    "option_greeks": {
                        "delta": 0.55,
                        "gamma": 0.01,
                        "theta": -2.0,
                        "iv": 20,
                    },
                },
                "put_options": {
                    "instrument_key": f"PE{strike}",
                    "market_data": {
                        "ltp": 100.0,
                        "oi": 50000,
                        "prev_oi": 51000,
                        "volume": 10000,
                        "bid_price": 99.5,
                        "ask_price": 100.5,
                        "bid_qty": 100,
                        "ask_qty": 100,
                    },
                    "option_greeks": {
                        "delta": -0.55,
                        "gamma": 0.01,
                        "theta": -2.0,
                        "iv": 20,
                    },
                },
            }
        )

    # Chain S/R must independently recognize a nearby strengthening CE wall
    # and weakening PE support as bearish predictive evidence.
    chain_bear = []
    for strike in [74000, 74050, 74100, 74150, 74200, 74250]:
        chain_bear.append({
            "strike_price": strike,
            "expiry": "2026-09-17",
            "call_options": {
                "instrument_key": f"CEB{strike}",
                "market_data": {
                    "ltp": 100.0, "oi": 80000 if strike >= 74150 else 20000,
                    "prev_oi": 70000 if strike >= 74150 else 21000,
                    "volume": 10000, "bid_price": 99.5, "ask_price": 100.5,
                    "bid_qty": 100, "ask_qty": 100,
                },
                "option_greeks": {"delta": 0.55, "gamma": 0.01, "theta": -2.0, "iv": 20.0},
            },
            "put_options": {
                "instrument_key": f"PEB{strike}",
                "market_data": {
                    "ltp": 100.0, "oi": 15000 if strike <= 74050 else 20000,
                    "prev_oi": 20000 if strike <= 74050 else 21000,
                    "volume": 10000, "bid_price": 99.5, "ask_price": 100.5,
                    "bid_qty": 100, "ask_qty": 100,
                },
                "option_greeks": {"delta": -0.55, "gamma": 0.01, "theta": -2.0, "iv": 20.0},
            },
        })
    bear_chain_levels = chain_oi_support_resistance(chain_bear, 74100.0)
    assert bear_chain_levels["resistance_1"] == 74150.0
    assert bear_chain_levels["predictive_bias"] == -1
    assert bear_chain_levels["predictive_strength"] >= CHAIN_PREDICTIVE_STRENGTH_THRESHOLD

    selected_bull = select_directional_option(chain, "BULLISH", 74100)
    selected_bear = select_directional_option(chain, "BEARISH", 74100)
    assert selected_bull.strike in {74050.0, 74000.0}
    assert selected_bear.strike in {74150.0, 74200.0}
    assert selected_bear.option_type == "PE"

    # Regression test: the production failure had BOTH bearish candidates
    # above the old 10% intraday theta burden. They must still be considered;
    # the lower-theta candidate should win when all other health fields are equal.
    production_like_theta_chain = []
    theta_specs = {
        74400: {"ltp": 20.0, "theta": -41.56},   # ~207.8%/day -> ~33.25%/60m
        74500: {"ltp": 25.4, "theta": -40.386},  # ~159.0%/day -> ~25.44%/60m
    }
    for strike in [74400, 74500]:
        spec = theta_specs[strike]
        row = {
            "strike_price": strike,
            "expiry": "2026-09-17",
            "call_options": {
                "instrument_key": f"PCE{strike}",
                "market_data": {
                    "ltp": 100.0, "oi": 50000, "prev_oi": 49000,
                    "volume": 10000, "bid_price": 99.5, "ask_price": 100.5,
                    "bid_qty": 100, "ask_qty": 100,
                },
                "option_greeks": {"delta": 0.55, "gamma": 0.01, "theta": -2.0, "iv": 20},
            },
            "put_options": {
                "instrument_key": f"PP E{strike}".replace(" ", ""),
                "market_data": {
                    "ltp": spec["ltp"], "oi": 50000, "prev_oi": 49000,
                    "volume": 10000, "bid_price": spec["ltp"] - 0.5,
                    "ask_price": spec["ltp"] + 0.5,
                    "bid_qty": 100, "ask_qty": 100,
                },
                "option_greeks": {"delta": -0.55, "gamma": 0.01, "theta": spec["theta"], "iv": 20},
            },
        }
        production_like_theta_chain.append(row)
    selected_production_like = select_directional_option(
        production_like_theta_chain, "BEARISH", 74431.0
    )
    assert selected_production_like.strike == 74500.0, selected_production_like
    assert selected_production_like.option_type == "PE"

    # Regression test: first opening candle must still produce VWAP.
    opening_one_bar = _synthetic_candles([100.0])  # exactly one session value
    opening_vwap, opening_slope, opening_bias = vwap_snapshot(opening_one_bar)
    assert math.isfinite(opening_vwap)
    assert opening_slope == 0.0
    assert opening_bias == 0

    # Regression test: a clear intraday bullish reversal must not be vetoed by
    # slow bearish higher-timeframe context or a bearish option-chain wall.
    bull_session = _synthetic_candles(
        [100, 99.5, 99.8, 100.4, 101.2, 102.1, 103.0, 104.2, 105.0, 106.0, 106.8, 107.5],
        [1200, 1195, 1190, 1185, 1180, 1175, 1170, 1165, 1160, 1155, 1150, 1145],
    )
    bull_frames = {
        3: calculate_supertrend(_synthetic_candles([95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106]), 10, 3.0),
        15: calculate_supertrend(_synthetic_candles([95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106]), 10, 3.0),
        30: calculate_supertrend(_synthetic_candles([95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106]), 10, 3.0),
        60: st_down,
        120: st_down,
        180: st_down,
    }
    bull_tf_dirs = {3: 1, 15: 1, 30: 1, 60: -1, 120: -1, 180: -1}
    bull_chain_levels = {
        "support_1": 104.0,
        "support_2": 102.0,
        "resistance_1": 108.0,
        "resistance_2": 110.0,
        "oi_bias": -1,
        "change_bias": 0,
        "predictive_bias": -1,
        "predictive_strength": 0.36,
        "level_bias": -1,
        "support_strength": 0.20,
        "resistance_strength": 0.48,
        "support_change_strength": 0.10,
        "resistance_change_strength": 0.30,
    }
    bull_structure = build_market_structure(
        spot=107.5,
        futures_3m=bull_session,
        futures_session=bull_session,
        tf_frames=bull_frames,
        tf_directions=bull_tf_dirs,
        chain_levels=bull_chain_levels,
        daily_oi_bias=1,
        daily_oi_score=0.10,
        change_oi_bias=0,
        change_oi_score=0.0,
        futures_live_quote={"oi": 1140},
    )
    assert bull_structure.direction == "BULLISH", bull_structure
    assert bull_structure.intraday_bias == 1
    assert bull_structure.intraday_strength > 0.50

    # The supplied production logs show a bullish short-covering/reversal state:
    # 3m/15m/30m bullish + VWAP above + SHORT_COVERING. It must be eligible even
    # when a bearish chain wall is still present.
    # Regression test: the day after the 17-Sep weekly expiry,
    # "current_week" must not be allowed to resolve to an expired/empty week.
    # The scanner must discover and select the nearest active expiry instead.
    original_api_get = api_get
    original_now_ist = now_ist

    def _fake_expiry_api_get(
        url: str,
        params: Optional[dict[str, Any]] = None,
        retries: int = 3,
    ) -> dict[str, Any]:
        assert url == OPTION_CONTRACT_URL
        assert params == {"instrument_key": SENSEX_KEY}
        return {
            "status": "success",
            "data": [
                {"expiry": "2026-09-17", "instrument_type": "CE"},
                {"expiry": "2026-09-17", "instrument_type": "PE"},
                {"expiry": "2026-09-24", "instrument_type": "CE"},
                {"expiry": "2026-09-24", "instrument_type": "PE"},
                {"expiry": "2026-10-01", "instrument_type": "CE"},
            ],
        }

    def _fake_now_ist() -> datetime:
        return datetime(2026, 9, 18, 10, 11, tzinfo=IST)

    try:
        globals()["api_get"] = _fake_expiry_api_get
        globals()["now_ist"] = _fake_now_ist
        assert _nearest_active_option_expiry() == "2026-09-24"
    finally:
        globals()["api_get"] = original_api_get
        globals()["now_ist"] = original_now_ist

    # Opening-data regression: one current 3m bar is valid and must not raise.
    one_bar = _synthetic_candles([100.0])
    vv, ss, bb = vwap_snapshot(one_bar)
    assert math.isfinite(vv) and ss == 0.0 and bb == 0

    # Opening fallback regression: quote-only futures data must not make the
    # structure engine crash when completed 3m OI data is unavailable.
    quote_only = {"last_price": 101.0, "oi": 1000}
    opening_structure = build_market_structure(
        spot=101.0, futures_3m=pd.DataFrame(), futures_session=one_bar,
        tf_frames=frames, tf_directions=tf_dirs, chain_levels=chain_levels,
        daily_oi_bias=0, daily_oi_score=0.0, change_oi_bias=0, change_oi_score=0.0,
        futures_live_quote=quote_only,
    )
    assert opening_structure.direction in {"BULLISH", "BEARISH", "NEUTRAL"}

    logger.info("SELF-TEST PASSED.")


# =============================================================================
# MAIN
# =============================================================================

def main() -> int:
    logger.info("SENSEX SCANNER VERSION: %s", SCANNER_VERSION)

    if "--self-test" in sys.argv:
        self_test()
        return 0

    try:
        state = load_state()
        signal = execute_scan(state)

        if signal is None:
            logger.info("No actionable setup on this scan.")
            return 0

        active_trade = {
            "status": "ACTIVE",
            "trade_date": now_ist().date().isoformat(),
            "opened_at": signal.timestamp,
            "direction": signal.direction,
            "regime": signal.regime,
            "confidence": signal.confidence,
            "instrument_key": signal.instrument_key,
            "trading_symbol": signal.trading_symbol,
            "option_type": signal.option_type,
            "strike": signal.strike,
            "entry": signal.entry,
            "target_1": signal.target_1,
            "target_2": signal.target_2,
            "stop_loss": signal.stop_loss,
            "underlying_stop": signal.underlying_stop,
            "underlying_target_1": signal.underlying_target_1,
            "underlying_target_2": signal.underlying_target_2,
            "delta": signal.delta,
            "gamma": signal.gamma,
            "theta": signal.theta,
            "reversal_confirmations": 0,
            "last_market_direction": signal.direction,
            "last_market_confidence": signal.confidence,
            "last_ltp": signal.entry,
        }

        state["active_trade"] = active_trade
        state["last_signal"] = asdict(signal)
        state["last_signal_hash"] = signal_hash(signal)
        state["last_signal_timestamp"] = signal.timestamp
        save_state(state)

        send_email(
            f"SENSEX {signal.direction} {signal.trading_symbol}",
            signal_email_body(signal),
        )

        logger.info(
            "NEW SIGNAL LOCKED: %s | entry=%.2f T1=%.2f T2=%.2f SL=%.2f",
            signal.trading_symbol,
            signal.entry,
            signal.target_1,
            signal.target_2,
            signal.stop_loss,
        )
        return 0

    except ScannerError as exc:
        logger.error("Scanner error: %s", exc)
        return 1
    except Exception:
        logger.error("Fatal scanner failure:\n%s", traceback.format_exc())
        return 1


if __name__ == "__main__":
    sys.exit(main())