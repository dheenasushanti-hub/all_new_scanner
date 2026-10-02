"""
SENSEX Predictive Options Market Scanner — Market Structure Engine

What this version fixes:
- Uses the SENSEX INDEX as the primary market-price/VWAP/intraday structure feed.
- Uses SENSEX futures price/OI as a separate derivatives confirmation, not the price proxy.
- Uses completed/currently-available multi-timeframe SENSEX structure:
  3m, 15m, 30m, 60m, 120m, 180m Supertrend.
- Uses SENSEX futures price/OI regime as a confirmation and positioning factor.
- Uses INDEX VWAP level + VWAP slope/position.
- Uses both option-chain OI concentration and Change-in-OI to derive
  dynamic support/resistance and directional pressure.
- Separates market-state detection from trade-entry readiness.
- Detects continuous bullish/bearish states, weakening, sideways, and both reversal directions.
- Uses strict continuation confirmation plus an adaptive reversal gate so genuine turns are not suppressed by lagging cumulative positioning.
- Selects Bullish ATM-1/ATM-2 CE or Bearish ATM+1/ATM+2 PE, but ranks
  candidates by liquidity, delta, theta burden, spread, and structure.
- Builds T1/T2/SL dynamically from underlying ATR, Supertrend,
  option-chain support/resistance, and option Greeks.
- No order placement. The script only creates a signal, persists state,
  and sends email.
- Uses current Upstox endpoints: v2 for option chain/contracts/status/
  instrument search/OI/change-OI/PCR; v3 for Full Market Quotes and candle data because the
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
OVEREXTENSION_ATR = float(os.getenv("OVEREXTENSION_ATR", "2.25"))
# Entry timing controls: confirmation is necessary but not sufficient. These
# prevent chasing a move that is already materially displaced from VWAP.
ENTRY_FUTURES_MIN_PERSISTENCE = float(os.getenv("ENTRY_FUTURES_MIN_PERSISTENCE", "0.50"))
ENTRY_FUTURES_MIN_STRENGTH = float(os.getenv("ENTRY_FUTURES_MIN_STRENGTH", "0.35"))
ENTRY_PCR_BULL_THRESHOLD = float(os.getenv("ENTRY_PCR_BULL_THRESHOLD", "1.10"))
ENTRY_PCR_BEAR_THRESHOLD = float(os.getenv("ENTRY_PCR_BEAR_THRESHOLD", "0.90"))
ENTRY_CHANGE_OI_MIN_SCORE = float(os.getenv("ENTRY_CHANGE_OI_MIN_SCORE", "0.15"))
ENTRY_MAX_3M_MOVE_ATR = float(os.getenv("ENTRY_MAX_3M_MOVE_ATR", "1.35"))
ENTRY_BREAKOUT_LOOKBACK_BARS = int(os.getenv("ENTRY_BREAKOUT_LOOKBACK_BARS", "6"))
ENTRY_BREAKOUT_BUFFER_ATR = float(os.getenv("ENTRY_BREAKOUT_BUFFER_ATR", "0.10"))

# Adaptive reversal-entry controls. Continuation entries remain strict; reversal
# entries recognize that cumulative PCR and futures-OI positioning can lag a true
# intraday turn. They still require VWAP + Change-OI + non-hostile PCR + a
# non-strongly-opposed futures state, plus independent price-structure evidence.
REVERSAL_CHANGE_OI_MIN_SCORE = float(os.getenv("REVERSAL_CHANGE_OI_MIN_SCORE", "0.10"))
REVERSAL_PCR_NEUTRAL_FLOOR = float(os.getenv("REVERSAL_PCR_NEUTRAL_FLOOR", "0.90"))
REVERSAL_PCR_NEUTRAL_CEILING = float(os.getenv("REVERSAL_PCR_NEUTRAL_CEILING", "1.10"))
REVERSAL_FUTURES_MAX_OPPOSING_STRENGTH = float(os.getenv("REVERSAL_FUTURES_MAX_OPPOSING_STRENGTH", "0.30"))
REVERSAL_CHAIN_MAX_OPPOSING_STRENGTH = float(os.getenv("REVERSAL_CHAIN_MAX_OPPOSING_STRENGTH", "0.25"))
REVERSAL_MIN_INTRADAY_STRENGTH = float(os.getenv("REVERSAL_MIN_INTRADAY_STRENGTH", "0.45"))
REVERSAL_MIN_CORE_SCORE = float(os.getenv("REVERSAL_MIN_CORE_SCORE", "2.50"))
REVERSAL_MIN_RECENT_MOVE_ATR = float(os.getenv("REVERSAL_MIN_RECENT_MOVE_ATR", "0.20"))
EXPIRY_DAY_FORCE_ATM = os.getenv("EXPIRY_DAY_FORCE_ATM", "1").strip().lower() not in {"0", "false", "no"}

# Market-state memory. This prevents a neutral scan from erasing the last
# decisive directional regime.
STATE_HISTORY_LIMIT = int(os.getenv("STATE_HISTORY_LIMIT", "60"))

# Reversal detection is independent from option-entry confirmation. It uses
# completed 3m price history so a bullish/bearish turn can still be recognized
# when the immediately previous scan was NEUTRAL or there was a long scan gap.
REVERSAL_LOOKBACK_BARS = int(os.getenv("REVERSAL_LOOKBACK_BARS", "9"))
REVERSAL_RECENT_BARS = int(os.getenv("REVERSAL_RECENT_BARS", "3"))
REVERSAL_ENTRY_CONFIRMATIONS_REQUIRED = int(os.getenv("REVERSAL_ENTRY_CONFIRMATIONS_REQUIRED", "2"))
REVERSAL_STRIKE_MAX_DISTANCE_STEPS = float(os.getenv("REVERSAL_STRIKE_MAX_DISTANCE_STEPS", "1.25"))
REVERSAL_STRIKE_PREFERRED_DISTANCE_STEPS = float(os.getenv("REVERSAL_STRIKE_PREFERRED_DISTANCE_STEPS", "0.0"))

STATE_FILE = Path(os.getenv("STATE_FILE", "state/market_state.json"))

SCANNER_VERSION = "2026-10-02-SCENARIO-MATRIX-INTEGRATED-V8"

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

STATE_PCR_BULL_THRESHOLD = float(os.getenv("STATE_PCR_BULL_THRESHOLD", "1.20"))
STATE_PCR_BEAR_THRESHOLD = float(os.getenv("STATE_PCR_BEAR_THRESHOLD", "0.80"))
PCR_BUCKET_MINUTES = int(os.getenv("PCR_BUCKET_MINUTES", "15"))
PCR_PATTERN_MIN_MOVE = float(os.getenv("PCR_PATTERN_MIN_MOVE", "0.02"))
WALL_HEAVY_CHANGE_OI_RATIO = float(os.getenv("WALL_HEAVY_CHANGE_OI_RATIO", "0.08"))
WALL_HEAVY_CHANGE_MULTIPLIER = float(os.getenv("WALL_HEAVY_CHANGE_MULTIPLIER", "1.50"))
REVERSAL_WALL_PROXIMITY_ATR = float(os.getenv("REVERSAL_WALL_PROXIMITY_ATR", "0.75"))
REVERSAL_ACCEPTANCE_BARS = int(os.getenv("REVERSAL_ACCEPTANCE_BARS", "2"))
REVERSAL_VWAP_SLOPE_CHANGE_ATR = float(os.getenv("REVERSAL_VWAP_SLOPE_CHANGE_ATR", "0.05"))

MIN_DIRECTIONAL_COMPONENTS = 4
ENTRY_SCORE = 4.50

# Strict entry confirmation. A signal is emitted only when price structure
# agrees with the live derivatives/positioning picture. Missing/neutral
# confirmations are treated as WAIT rather than silently bypassed.
STRICT_ENTRY_CONFIRMATIONS = True
PCR_BULL_THRESHOLD = 1.05
PCR_BEAR_THRESHOLD = 0.95
MIN_ENTRY_CONFIRMATIONS = 4

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
REVERSAL_CONFIRMATIONS_REQUIRED = 2
STRUCTURE_REVERSAL_CONFIDENCE = 60.0

# Phase-aware state thresholds. These classify market movement separately from
# entry readiness, so conflicting derivatives can mark a weakening trend
# without falsely flipping the market direction.
WEAKENING_MIN_OPPOSITE_CONFIRMATIONS = 1
SIDEWAYS_CORE_THRESHOLD = 2.00

# URLs.
INSTRUMENT_SEARCH_URL = f"{BASE_URL}/v2/instruments/search"
OPTION_CONTRACT_URL = f"{BASE_URL}/v2/option/contract"
OPTION_CHAIN_URL = f"{BASE_URL}/v2/option/chain"
MARKET_QUOTE_URL = f"{BASE_URL}/v3/market-quote/quotes"
MARKET_STATUS_URL = f"{BASE_URL}/v2/market/status/BSE"
MARKET_HOLIDAY_URL = f"{BASE_URL}/v2/market/holidays"
MARKET_OI_URL = f"{BASE_URL}/v2/market/oi"
CHANGE_OI_URL = f"{BASE_URL}/v2/market/change-oi"
PCR_URL = f"{BASE_URL}/v2/market/pcr"
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
    market_phase: str
    entry_confirmed: bool
    reversal_confirmations: int
    confirmation_state: str
    pcr: float
    pcr_bias: int
    pcr_rate_15m: float
    pcr_higher_low: bool
    pcr_lower_high: bool
    false_breakout: bool
    trap_level: float
    entry_trigger: str
    invalidation_rule: str
    reasons: list[str]


@dataclass(frozen=True)
class Signal:
    timestamp: str
    direction: str
    regime: str
    market_state: str
    bias: str
    entry_trigger: str
    invalidation_rule: str
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
    # Full Market Quotes V3 uses a colon-delimited response key in some cases
    # (for example BSE_INDEX:SENSEX) even when the request used the pipe key.
    colon_key = instrument_key.replace("|", ":", 1)
    if colon_key in data:
        return data[colon_key]
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
        logger.info("Current-session 3m candles: %d", len(native))
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

    logger.warning("Current-session 3m/1m candles unavailable; using quote/historical fallbacks.")
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
        vwap = typical.groupby(local_date, sort=False).transform(
            lambda x: x.expanding().mean()
        )
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

    # Median is robust against one-off gaps/anomalous strikes. Using the raw
    # minimum can accidentally turn a 100-point chain into a 50-point chain and
    # corrupt ATM/adjacent-strike selection.
    return float(np.median(np.asarray(diffs, dtype=float)))


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
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
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
        api_change = (change_oi_by_strike or {}).get(float(strike), {})
        c_chg = safe_float(api_change.get("call_change"), safe_float(ce["oi"]) - safe_float(ce["prev_oi"]))
        p_chg = safe_float(api_change.get("put_change"), safe_float(pe["oi"]) - safe_float(pe["prev_oi"]))
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

    total_put_oi = sum(x["put_oi"] for x in entries)
    total_call_oi = sum(x["call_oi"] for x in entries)
    pcr = total_put_oi / total_call_oi if total_call_oi > 0 else float("nan")
    pcr_bias = (
        1 if math.isfinite(pcr) and pcr >= PCR_BULL_THRESHOLD
        else -1 if math.isfinite(pcr) and pcr <= PCR_BEAR_THRESHOLD
        else 0
    )

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

    major_support_row = max(support_rows, key=lambda x: x["put_oi"], default=None)
    major_resistance_row = max(resistance_rows, key=lambda x: x["call_oi"], default=None)
    abs_changes = [abs(x["call_change"]) for x in nearby] + [abs(x["put_change"]) for x in nearby]
    typical_abs_change = float(np.median(abs_changes)) if abs_changes else 0.0

    def heavy_positive(change: float, wall_oi: float) -> bool:
        threshold = max(WALL_HEAVY_CHANGE_OI_RATIO * max(wall_oi, 1.0), WALL_HEAVY_CHANGE_MULTIPLIER * typical_abs_change, 1.0)
        return change >= threshold

    def heavy_negative(change: float, wall_oi: float) -> bool:
        threshold = max(WALL_HEAVY_CHANGE_OI_RATIO * max(wall_oi, 1.0), WALL_HEAVY_CHANGE_MULTIPLIER * typical_abs_change, 1.0)
        return change <= -threshold

    major_support = float(major_support_row["strike"]) if major_support_row else float(support_1)
    major_resistance = float(major_resistance_row["strike"]) if major_resistance_row else float(resistance_1)
    major_support_put_change = float(major_support_row["put_change"]) if major_support_row else 0.0
    major_support_call_change = float(major_support_row["call_change"]) if major_support_row else 0.0
    major_resistance_call_change = float(major_resistance_row["call_change"]) if major_resistance_row else 0.0
    major_resistance_put_change = float(major_resistance_row["put_change"]) if major_resistance_row else 0.0

    put_writing_at_support = bool(major_support_row and heavy_positive(major_support_put_change, major_support_row["put_oi"]))
    put_unwinding_at_support = bool(major_support_row and heavy_negative(major_support_put_change, major_support_row["put_oi"]))
    call_writing_at_resistance = bool(major_resistance_row and heavy_positive(major_resistance_call_change, major_resistance_row["call_oi"]))
    call_unwinding_at_resistance = bool(major_resistance_row and heavy_negative(major_resistance_call_change, major_resistance_row["call_oi"]))

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
        "major_support": major_support,
        "major_resistance": major_resistance,
        "major_support_put_change": major_support_put_change,
        "major_support_call_change": major_support_call_change,
        "major_resistance_call_change": major_resistance_call_change,
        "major_resistance_put_change": major_resistance_put_change,
        "put_writing_at_support": put_writing_at_support,
        "put_unwinding_at_support": put_unwinding_at_support,
        "call_writing_at_resistance": call_writing_at_resistance,
        "call_unwinding_at_resistance": call_unwinding_at_resistance,
        "typical_abs_change": typical_abs_change,
        "pcr": float(pcr) if math.isfinite(pcr) else float("nan"),
        "pcr_bias": int(pcr_bias),
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


def get_change_oi_confirmation(
    expiry: str,
) -> tuple[int, float, dict[float, dict[str, float]]]:
    """Fetch aggregate and per-strike Change-in-OI in one API call."""
    today = now_ist().date().isoformat()
    by_strike: dict[float, dict[str, float]] = {}

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
        return 0, 0.0, by_strike

    data = payload.get("data", {})
    if not isinstance(data, dict):
        return 0, 0.0, by_strike

    put_change = safe_float(data.get("total_put_change_oi"))
    call_change = safe_float(data.get("total_call_change_oi"))

    detail_rows = data.get("call_put_oi_data_list", [])
    if isinstance(detail_rows, list):
        for item in detail_rows:
            if not isinstance(item, dict):
                continue
            strike = safe_float(item.get("strike_price"), float("nan"))
            if not math.isfinite(strike):
                continue
            by_strike[float(strike)] = {
                "call_change": safe_float(item.get("call_change_oi")),
                "put_change": safe_float(item.get("put_change_oi")),
            }

    den = abs(put_change) + abs(call_change)
    if den <= 0:
        return 0, 0.0, by_strike

    score = (put_change - call_change) / den
    bias = 1 if score > 0.10 else -1 if score < -0.10 else 0

    logger.info(
        "CHANGE-OI CONFIRMATION: put_change=%+.0f call_change=%+.0f score=%+.3f bias=%+d per_strike=%d",
        put_change, call_change, score, bias, len(by_strike),
    )
    return bias, score, by_strike


def get_intraday_pcr(expiry: str) -> tuple[float, float, int, bool, bool]:
    """Return current PCR, 15-minute change, trend, and local turning-pattern flags."""
    today = now_ist().date().isoformat()
    try:
        payload = api_get(
            PCR_URL,
            {
                "instrument_key": SENSEX_KEY,
                "expiry": expiry,
                "date": today,
                "bucket_interval": PCR_BUCKET_MINUTES,
            },
            retries=2,
        )
    except ScannerError as exc:
        logger.info("PCR endpoint unavailable: %s", exc)
        return float("nan"), 0.0, 0, False, False

    data = payload.get("data", {})
    if not isinstance(data, dict):
        return float("nan"), 0.0, 0, False, False

    fallback = safe_float(data.get("pcr"), float("nan"))
    values: list[float] = []
    insights = data.get("insights", [])
    if isinstance(insights, list):
        for row in insights:
            if not isinstance(row, dict):
                continue
            value = safe_float(row.get("pcr"), float("nan"))
            if math.isfinite(value):
                values.append(value)

    if not values:
        return fallback, 0.0, 0, False, False

    current = values[-1]
    previous = values[-2] if len(values) >= 2 else current
    rate = current - previous
    trend = 1 if rate > 0 else -1 if rate < 0 else 0

    higher_low = False
    lower_high = False
    if len(values) >= 4:
        prior = values[:-2]
        recent = values[-2:]
        higher_low = min(recent) >= min(prior) + PCR_PATTERN_MIN_MOVE
        lower_high = max(recent) <= max(prior) - PCR_PATTERN_MIN_MOVE

    logger.info(
        "PCR INTRADAY: current=%.3f rate_15m=%+.3f trend=%+d higher_low=%s lower_high=%s points=%d",
        current, rate, trend, higher_low, lower_high, len(values),
    )
    return current, rate, trend, higher_low, lower_high


# =============================================================================
# VWAP / TIMEFRAME STRUCTURE
# =============================================================================

def vwap_snapshot(
    price_session: pd.DataFrame,
) -> tuple[float, float, int]:
    """Calculate session VWAP from the SENSEX index price feed.

    Futures are deliberately excluded from the primary price/VWAP calculation;
    futures price/OI is treated separately as a derivatives confirmation.
    """
    if price_session is None or price_session.empty:
        raise ScannerError("Index session candles unavailable for VWAP.")

    work = price_session.copy()
    required = {"timestamp", "high", "low", "close"}
    missing = required.difference(work.columns)
    if missing:
        raise ScannerError(
            f"Index session candles missing VWAP columns: {sorted(missing)}"
        )

    for col in ("high", "low", "close"):
        work[col] = pd.to_numeric(work[col], errors="coerce")
    if "volume" not in work.columns:
        work["volume"] = 0.0
    work["volume"] = pd.to_numeric(work["volume"], errors="coerce").fillna(0.0)

    work = (
        work.dropna(subset=["timestamp", "high", "low", "close"])
        .sort_values("timestamp")
        .drop_duplicates("timestamp", keep="last")
    )
    if work.empty:
        raise ScannerError("No valid index session candles available for VWAP.")

    vwap_series = calculate_vwap(work).replace([np.inf, -np.inf], np.nan).dropna()
    if vwap_series.empty:
        typical = (work["high"] + work["low"] + work["close"]) / 3.0
        vwap_series = typical.expanding().mean().dropna()

    current_vwap = float(vwap_series.iloc[-1])
    slope = float(vwap_series.iloc[-1] - vwap_series.iloc[-2]) if len(vwap_series) >= 2 else 0.0
    price = float(work["close"].iloc[-1])
    level_bias = 1 if price > current_vwap else -1 if price < current_vwap else 0

    logger.info(
        "INDEX VWAP: price=%.2f vwap=%.2f slope=%+.2f level_bias=%+d bars=%d",
        price, current_vwap, slope, level_bias, len(vwap_series),
    )
    return current_vwap, slope, level_bias

def intraday_trend_snapshot(
    price_session: pd.DataFrame,
    vwap: float,
) -> tuple[int, float, float]:
    """Measure fast SENSEX-index intraday direction independently of derivatives.

    The index is the primary market-price series. Futures price/OI is consumed
    separately, preventing the futures basis from distorting price structure.
    """
    if price_session is None or price_session.empty:
        return 0, 0.0, 0.0

    work = price_session.copy().sort_values("timestamp")
    for col in ("high", "low", "close"):
        work[col] = pd.to_numeric(work[col], errors="coerce")
    work = work.dropna(subset=["high", "low", "close"])
    if len(work) < 3:
        return 0, 0.0, 0.0

    closes = work["close"].tail(INTRADAY_LOOKBACK_BARS)
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

    net_component = math.tanh(net_move / (1.25 * atr_value))
    recent_component = math.tanh(recent_move / (0.90 * atr_value))
    structure_component = 1.0 if higher_structure else -1.0 if lower_structure else 0.0

    raw_score = (
        1.55 * net_component
        + 1.35 * recent_component
        + 0.90 * structure_component
        + 0.75 * vwap_bias
    )

    bias = (
        1 if raw_score >= INTRADAY_TREND_TRIGGER
        else -1 if raw_score <= -INTRADAY_TREND_TRIGGER
        else 0
    )
    strength = min(abs(raw_score) / 4.0, 1.0)

    logger.info(
        "INDEX INTRADAY: bias=%+d strength=%.3f score=%+.2f "
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

def entry_timing_filter(
    price_session: pd.DataFrame,
    direction: str,
    vwap: float,
    atr3: float,
    market_phase: Optional[str] = None,
) -> tuple[bool, str, float, float]:
    """Reject stale/chased entries while allowing genuine reversal setups.

    Continuations need a fresh breakout or pullback/reclaim. A reversal may use
    the reversal impulse itself as the fresh setup, but it still cannot be
    extended from VWAP or have a blow-off 3m candle.
    """
    if price_session is None or price_session.empty or direction not in {"BULLISH", "BEARISH"}:
        return False, "INSUFFICIENT_DATA", float("inf"), float("inf")

    work = price_session.copy().sort_values("timestamp")
    work = filter_completed_candles(work, 3)
    if len(work) < max(ENTRY_BREAKOUT_LOOKBACK_BARS + 1, 7):
        return False, "INSUFFICIENT_COMPLETED_3M_BARS", float("inf"), float("inf")

    atr = max(float(atr3), 1.0)
    price = float(work["close"].iloc[-1])
    vwap_distance_atr = abs(price - vwap) / atr
    latest_move_atr = abs(float(work["close"].iloc[-1] - work["close"].iloc[-2])) / atr

    if vwap_distance_atr > OVEREXTENSION_ATR:
        return False, "VWAP_EXTENDED", vwap_distance_atr, latest_move_atr
    if latest_move_atr > ENTRY_MAX_3M_MOVE_ATR:
        return False, "LATEST_3M_BLOWOFF", vwap_distance_atr, latest_move_atr

    prior = work.iloc[-(ENTRY_BREAKOUT_LOOKBACK_BARS + 1):-1]
    last = work.iloc[-1]
    buffer = ENTRY_BREAKOUT_BUFFER_ATR * atr

    if direction == "BULLISH":
        prior_level = float(prior["high"].max())
        fresh_breakout = float(last["close"]) > prior_level + buffer
        reclaim = (
            float(last["close"]) > float(work["close"].iloc[-2])
            and float(last["low"]) <= float(work["low"].tail(4).min())
        )
    else:
        prior_level = float(prior["low"].min())
        fresh_breakout = float(last["close"]) < prior_level - buffer
        reclaim = (
            float(last["close"]) < float(work["close"].iloc[-2])
            and float(last["high"]) >= float(work["high"].tail(4).max())
        )

    is_reversal = str(market_phase or "").upper().startswith((
        "BEARISH_TO_BULLISH_REVERSAL", "BULLISH_TO_BEARISH_REVERSAL"
    ))

    if fresh_breakout:
        return True, "FRESH_BREAKOUT", vwap_distance_atr, latest_move_atr
    if reclaim:
        return True, "PULLBACK_RECLAIM", vwap_distance_atr, latest_move_atr

    if is_reversal:
        # For a reversal, a sustained recent directional impulse is the fresh
        # setup even before a six-bar breakout is printed.
        recent_count = min(4, len(work))
        recent_move = float(work["close"].iloc[-1] - work["close"].iloc[-recent_count]) / atr
        if (
            abs(recent_move) >= REVERSAL_MIN_RECENT_MOVE_ATR
            and ((direction == "BULLISH" and recent_move > 0) or
                 (direction == "BEARISH" and recent_move < 0))
        ):
            return True, "REVERSAL_IMPULSE", vwap_distance_atr, latest_move_atr

    return False, "NO_FRESH_ENTRY_SETUP", vwap_distance_atr, latest_move_atr

def infer_prior_session_direction(
    price_session: pd.DataFrame,
    current_direction: Optional[str] = None,
) -> tuple[Optional[str], str]:
    """Infer prior intraday direction from SENSEX-index 3m history.

    This works even when the saved market snapshot is NEUTRAL. The last decisive
    direction is reconstructed from earlier completed 3m bars rather than from
    a single previous scan.
    """
    if price_session is None or price_session.empty:
        return None, "NO_DATA"

    work = filter_completed_candles(price_session, 3)
    minimum = max(REVERSAL_LOOKBACK_BARS, REVERSAL_RECENT_BARS + 4)
    if len(work) < minimum:
        return None, "INSUFFICIENT_HISTORY"

    recent_count = min(REVERSAL_RECENT_BARS + 1, len(work) - 3)
    recent = work.tail(recent_count)
    prior_end = len(work) - recent_count
    prior_start = max(0, prior_end - REVERSAL_LOOKBACK_BARS)
    prior = work.iloc[prior_start:prior_end]

    if len(prior) < 4 or len(recent) < 3:
        return None, "INSUFFICIENT_WINDOWS"

    def window_score(window: pd.DataFrame) -> float:
        closes = pd.to_numeric(window["close"], errors="coerce").dropna()
        if len(closes) < 3:
            return 0.0
        atr = calculate_atr(window).dropna()
        atr_value = max(float(atr.iloc[-1]) if not atr.empty else 1.0, 1.0)
        net = float(closes.iloc[-1] - closes.iloc[0]) / atr_value
        return 1.40 * math.tanh(net / 1.4)

    prior_s = window_score(prior)
    recent_s = window_score(recent)

    if prior_s <= -0.35:
        prior_direction = "BEARISH"
    elif prior_s >= 0.35:
        prior_direction = "BULLISH"
    else:
        prior_direction = None

    current = (current_direction or "").upper()
    if current == "BULLISH" and prior_direction == "BEARISH" and recent_s >= 0.20:
        return prior_direction, "BEARISH_TO_BULLISH"
    if current == "BEARISH" and prior_direction == "BULLISH" and recent_s <= -0.20:
        return prior_direction, "BULLISH_TO_BEARISH"

    return prior_direction, "NO_CONFIRMED_TRANSITION"

def vwap_acceptance_context(
    price_session: pd.DataFrame,
    vwap: float,
    atr3: float,
) -> dict[str, Any]:
    """Measure completed-3m VWAP acceptance/rejection and slope change."""
    result = {
        "bull_acceptance": False, "bear_acceptance": False,
        "bull_cross": False, "bear_cross": False,
        "slope_change": 0.0, "current_slope": 0.0, "previous_slope": 0.0,
        "completed": 0,
    }
    if price_session is None or price_session.empty:
        return result
    work = filter_completed_candles(price_session.copy().sort_values("timestamp"), 3)
    if len(work) < 3:
        return result
    for c in ("close", "high", "low"):
        work[c] = pd.to_numeric(work[c], errors="coerce")
    work = work.dropna(subset=["close", "high", "low"])
    if len(work) < 3:
        return result
    v = calculate_vwap(work).replace([np.inf, -np.inf], np.nan).dropna()
    if len(v) < 3:
        return result
    current_slope = float(v.iloc[-1] - v.iloc[-2])
    previous_slope = float(v.iloc[-2] - v.iloc[-3])
    result.update({
        "current_slope": current_slope,
        "previous_slope": previous_slope,
        "slope_change": current_slope - previous_slope,
        "completed": len(work),
    })
    n = max(2, REVERSAL_ACCEPTANCE_BARS)
    c = work["close"].tail(n).to_numpy(dtype=float)
    vw = v.tail(n).to_numpy(dtype=float)
    result["bull_acceptance"] = bool(len(c) == n and np.all(c > vw))
    result["bear_acceptance"] = bool(len(c) == n and np.all(c < vw))
    result["bull_cross"] = float(work["close"].iloc[-2]) <= float(v.iloc[-2]) and float(work["close"].iloc[-1]) > float(v.iloc[-1])
    result["bear_cross"] = float(work["close"].iloc[-2]) >= float(v.iloc[-2]) and float(work["close"].iloc[-1]) < float(v.iloc[-1])
    return result


def detect_false_breakout_trap(
    price_session: pd.DataFrame,
    spot: float,
    vwap: float,
    atr3: float,
    chain_levels: dict[str, Any],
) -> dict[str, Any]:
    """Detect wall breach + adverse wall OI + fast VWAP failure/reclaim."""
    result = {"detected": False, "direction": 0, "level": 0.0, "kind": "", "reason": ""}
    if price_session is None or price_session.empty:
        return result
    work = filter_completed_candles(price_session.copy().sort_values("timestamp"), 3)
    if len(work) < 4:
        return result
    work = work.tail(6)
    atr = max(float(atr3), 1.0)
    buffer = ENTRY_BREAKOUT_BUFFER_ATR * atr
    ctx = vwap_acceptance_context(work, vwap, atr)
    r = safe_float(chain_levels.get("major_resistance"), float("nan"))
    s = safe_float(chain_levels.get("major_support"), float("nan"))

    if math.isfinite(r):
        breached = float(work["high"].iloc[:-1].max()) > r + buffer
        rejected = float(work["close"].iloc[-1]) < r and float(spot) < r
        vwap_failed = float(work["close"].iloc[-1]) < vwap and (ctx["bear_cross"] or float(spot) < vwap)
        if breached and rejected and vwap_failed and bool(chain_levels.get("call_writing_at_resistance")):
            return {
                "detected": True, "direction": -1, "level": r, "kind": "RESISTANCE_TRAP",
                "reason": f"Resistance {r:.2f} was breached, Call OI writing increased aggressively, and price failed back below VWAP.",
            }

    if math.isfinite(s):
        breached = float(work["low"].iloc[:-1].min()) < s - buffer
        rejected = float(work["close"].iloc[-1]) > s and float(spot) > s
        vwap_reclaimed = float(work["close"].iloc[-1]) > vwap and (ctx["bull_cross"] or float(spot) > vwap)
        if breached and rejected and vwap_reclaimed and bool(chain_levels.get("put_writing_at_support")):
            return {
                "detected": True, "direction": 1, "level": s, "kind": "SUPPORT_TRAP",
                "reason": f"Support {s:.2f} was breached, Put OI writing increased aggressively, and price reclaimed VWAP.",
            }

    return result


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
    previous_direction: Optional[str] = None,
    previous_phase: Optional[str] = None,
    previous_reversal_confirmations: int = 0,
    price_session: Optional[pd.DataFrame] = None,
    inferred_prior_direction: Optional[str] = None,
    transition_hint: Optional[str] = None,
    pcr_value: Optional[float] = None,
    pcr_rate_15m: float = 0.0,
    pcr_higher_low: bool = False,
    pcr_lower_high: bool = False,
) -> StructureResult:
    """Index-first, phase-aware market-structure and entry-state engine.

    Primary price structure:
        SENSEX index 3m/15m/30m structure + index VWAP + recent price action.
    Derivatives confirmation:
        futures price/OI + PCR + Change-OI + chain OI/pressure.

    Market-state classification never requires all derivatives to agree. Entry
    classification is stricter for continuation and adaptive for reversals so a
    genuine fast reversal is not suppressed solely by lagging cumulative PCR or
    a futures-OI unwind that is already losing strength.
    """
    primary_session = price_session if price_session is not None and not price_session.empty else futures_session
    vwap, vwap_slope, vwap_level_bias = vwap_snapshot(primary_session)
    intraday_bias, intraday_strength, intraday_score = intraday_trend_snapshot(primary_session, vwap)

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
    structure_15 = market_structure_state(tf_frames[15], 5)
    structure_3_bias = 1 if structure_3 == "BULLISH" else -1 if structure_3 == "BEARISH" else 0
    structure_15_bias = 1 if structure_15 == "BULLISH" else -1 if structure_15 == "BEARISH" else 0
    structure_30_bias = tf_directions.get(30, 0)

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
    chain_pcr = safe_float(chain_levels.get("pcr"), float("nan"))
    pcr = safe_float(pcr_value, chain_pcr) if pcr_value is not None else chain_pcr
    pcr_bias = (1 if math.isfinite(pcr) and pcr >= STATE_PCR_BULL_THRESHOLD
                else -1 if math.isfinite(pcr) and pcr <= STATE_PCR_BEAR_THRESHOLD
                else 0)

    # -------------------------------------------------------------------------
    # PRIMARY PRICE CORE
    # -------------------------------------------------------------------------
    core_components = {
        "intraday_trend": 3.60 * intraday_score,
        "vwap_level": 2.60 * vwap_level_bias,
        "vwap_slope": 1.50 * vwap_slope_bias,
        "structure_3m": 2.20 * structure_3_bias,
        "structure_15m": 1.90 * structure_15_bias,
        "structure_30m": 1.20 * structure_30_bias,
    }
    core_score = float(sum(core_components.values()))

    # Higher timeframes are context, not blockers.
    tf_component = sum(TF_WEIGHTS[tf] * tf_directions.get(tf, 0) for tf in TIMEFRAMES)
    context_components = {
        "futures": 1.90 * futures_bias * max(0.55, float(futures_info["oi_strength"])),
        "multi_tf_supertrend": 0.55 * tf_component,
        "chain_predictive": 1.20 * chain_predictive_bias * max(0.40, chain_predictive_strength),
        "chain_levels": 0.75 * chain_level_bias,
        "option_oi": 0.55 * chain_bias,
        "option_oi_change": 0.55 * chain_change_bias,
        "daily_oi": 0.40 * int(daily_oi_bias),
        "change_oi_api": 0.40 * int(change_oi_bias),
        "chain_wall_imbalance": 0.65 * (
            float(chain_levels.get("support_strength", 0.0))
            - float(chain_levels.get("resistance_strength", 0.0))
        ),
    }
    components: dict[str, float] = dict(core_components)
    components.update(context_components)
    components["futures_oi_strength"] = 0.70 * futures_info["oi_strength"] * futures_bias
    total_score = float(sum(components.values()))

    directional_groups = [
        1 if intraday_score > 0.30 else -1 if intraday_score < -0.30 else 0,
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
    # PRICE-REGIME DIRECTION (separate from entry confirmation)
    # -------------------------------------------------------------------------
    fast_bull_votes = sum(x > 0 for x in (structure_3_bias, structure_15_bias, structure_30_bias))
    fast_bear_votes = sum(x < 0 for x in (structure_3_bias, structure_15_bias, structure_30_bias))

    bull_price_core = (
        core_score >= CORE_BULL_TRIGGER
        and (
            intraday_score >= 0.25
            or vwap_level_bias > 0
            or structure_3_bias > 0
            or fast_bull_votes >= 2
        )
    )
    bear_price_core = (
        core_score <= CORE_BEAR_TRIGGER
        and (
            intraday_score <= -0.25
            or vwap_level_bias < 0
            or structure_3_bias < 0
            or fast_bear_votes >= 2
        )
    )

    raw_price_direction = (
        "BULLISH" if bull_price_core and not bear_price_core else
        "BEARISH" if bear_price_core and not bull_price_core else
        "BULLISH" if core_score >= CORE_BULL_TRIGGER + 1.0 else
        "BEARISH" if core_score <= CORE_BEAR_TRIGGER - 1.0 else
        None
    )

    # Reconstruct prior direction from price history when caller did not supply it.
    seed_direction = (previous_direction or inferred_prior_direction or "").upper() or None

    # -------------------------------------------------------------------------
    # DERIVATIVE CONFIRMATION
    # -------------------------------------------------------------------------
    bullish_futures_confirmation = (
        futures_bias > 0
        and futures_info["oi_strength"] >= ENTRY_FUTURES_MIN_STRENGTH
        and (
            (futures_regime == "LONG_BUILDUP" and futures_info["oi_persistence"] >= ENTRY_FUTURES_MIN_PERSISTENCE)
            or
            (futures_regime == "SHORT_COVERING" and futures_info["oi_delta"] < 0 and futures_info["oi_strength"] >= 0.25)
        )
    )
    bearish_futures_confirmation = (
        futures_bias < 0
        and futures_info["oi_strength"] >= ENTRY_FUTURES_MIN_STRENGTH
        and (
            (futures_regime == "SHORT_BUILDUP" and futures_info["oi_persistence"] >= ENTRY_FUTURES_MIN_PERSISTENCE)
            or
            (futures_regime == "LONG_UNWINDING" and futures_info["oi_delta"] < 0 and futures_info["oi_strength"] >= 0.25)
        )
    )

    bullish_confirmations = {
        "VWAP": vwap_level_bias > 0,
        "FUTURES_OI": bullish_futures_confirmation,
        "CHANGE_OI": change_oi_score >= ENTRY_CHANGE_OI_MIN_SCORE and change_oi_bias > 0,
        "PCR": math.isfinite(pcr) and pcr >= ENTRY_PCR_BULL_THRESHOLD,
        "CHAIN_OI": chain_predictive_bias > 0 and chain_predictive_strength >= CHAIN_PREDICTIVE_STRENGTH_THRESHOLD,
    }
    bearish_confirmations = {
        "VWAP": vwap_level_bias < 0,
        "FUTURES_OI": bearish_futures_confirmation,
        "CHANGE_OI": change_oi_score <= -ENTRY_CHANGE_OI_MIN_SCORE and change_oi_bias < 0,
        "PCR": math.isfinite(pcr) and pcr <= ENTRY_PCR_BEAR_THRESHOLD,
        "CHAIN_OI": chain_predictive_bias < 0 and chain_predictive_strength >= CHAIN_PREDICTIVE_STRENGTH_THRESHOLD,
    }
    bull_confirmed = sum(bullish_confirmations.values())
    bear_confirmed = sum(bearish_confirmations.values())

    full_bull_gate = (
        bull_price_core
        and bullish_confirmations["VWAP"]
        and bullish_confirmations["FUTURES_OI"]
        and bullish_confirmations["CHANGE_OI"]
        and bullish_confirmations["PCR"]
        and bull_confirmed >= MIN_ENTRY_CONFIRMATIONS
    )
    full_bear_gate = (
        bear_price_core
        and bearish_confirmations["VWAP"]
        and bearish_confirmations["FUTURES_OI"]
        and bearish_confirmations["CHANGE_OI"]
        and bearish_confirmations["PCR"]
        and bear_confirmed >= MIN_ENTRY_CONFIRMATIONS
    )

    # -------------------------------------------------------------------------
    # ADAPTIVE REVERSAL GATE
    # -------------------------------------------------------------------------
    # A reversal must be driven by price first. PCR is treated as a "not hostile"
    # filter because it is cumulative and can remain bearish during a bullish
    # intraday reversal. Futures-OI can also lag; a weak opposite unwind is allowed.
    effective_prior = (inferred_prior_direction or seed_direction or "").upper() or None
    effective_hint = (transition_hint or "").upper()

    inferred_reversal_bull = (
        effective_hint == "BEARISH_TO_BULLISH"
        or (
            effective_prior == "BEARISH"
            and raw_price_direction == "BULLISH"
            and intraday_strength >= REVERSAL_MIN_INTRADAY_STRENGTH
        )
    )
    inferred_reversal_bear = (
        effective_hint == "BULLISH_TO_BEARISH"
        or (
            effective_prior == "BULLISH"
            and raw_price_direction == "BEARISH"
            and intraday_strength >= REVERSAL_MIN_INTRADAY_STRENGTH
        )
    )

    bull_pcr_not_hostile = math.isfinite(pcr) and pcr >= REVERSAL_PCR_NEUTRAL_FLOOR
    bear_pcr_not_hostile = math.isfinite(pcr) and pcr <= REVERSAL_PCR_NEUTRAL_CEILING

    bull_futures_reversal_ok = (
        futures_bias > 0 and futures_info["oi_strength"] >= 0.20
    ) or (
        futures_bias < 0 and futures_info["oi_strength"] <= REVERSAL_FUTURES_MAX_OPPOSING_STRENGTH
        and futures_regime in {"LONG_UNWINDING", "SHORT_BUILDUP"}
    ) or futures_regime == "SHORT_COVERING"

    bear_futures_reversal_ok = (
        futures_bias < 0 and futures_info["oi_strength"] >= 0.20
    ) or (
        futures_bias > 0 and futures_info["oi_strength"] <= REVERSAL_FUTURES_MAX_OPPOSING_STRENGTH
        and futures_regime in {"SHORT_COVERING", "LONG_BUILDUP"}
    ) or futures_regime == "LONG_UNWINDING"

    bullish_reversal_gate = (
        inferred_reversal_bull
        and core_score >= REVERSAL_MIN_CORE_SCORE
        and intraday_strength >= REVERSAL_MIN_INTRADAY_STRENGTH
        and vwap_level_bias > 0
        and change_oi_score >= REVERSAL_CHANGE_OI_MIN_SCORE
        and change_oi_bias > 0
        and bull_pcr_not_hostile
        and bull_futures_reversal_ok
        and not (
            chain_predictive_bias < 0
            and chain_predictive_strength >= REVERSAL_CHAIN_MAX_OPPOSING_STRENGTH
        )
    )
    bearish_reversal_gate = (
        inferred_reversal_bear
        and core_score <= -REVERSAL_MIN_CORE_SCORE
        and intraday_strength >= REVERSAL_MIN_INTRADAY_STRENGTH
        and vwap_level_bias < 0
        and change_oi_score <= -REVERSAL_CHANGE_OI_MIN_SCORE
        and change_oi_bias < 0
        and bear_pcr_not_hostile
        and bear_futures_reversal_ok
        and not (
            chain_predictive_bias > 0
            and chain_predictive_strength >= REVERSAL_CHAIN_MAX_OPPOSING_STRENGTH
        )
    )

    # -------------------------------------------------------------------------
    # EXPLICIT SCENARIO MATRIX
    # -------------------------------------------------------------------------
    scenario_state = ""
    scenario_direction = 0
    scenario_entry = False
    scenario_trigger = "WAIT"
    scenario_invalidation = "No trade until a defined scenario is confirmed."
    scenario_reasons: list[str] = []

    major_support = safe_float(chain_levels.get("major_support"), safe_float(chain_levels.get("support_1"), spot))
    major_resistance = safe_float(chain_levels.get("major_resistance"), safe_float(chain_levels.get("resistance_1"), spot))
    put_writing_support = bool(chain_levels.get("put_writing_at_support"))
    put_unwinding_support = bool(chain_levels.get("put_unwinding_at_support"))
    call_writing_resistance = bool(chain_levels.get("call_writing_at_resistance"))
    call_unwinding_resistance = bool(chain_levels.get("call_unwinding_at_resistance"))

    vwap_ctx = vwap_acceptance_context(primary_session, vwap, atr3)
    prior_direction_matrix = (inferred_prior_direction or seed_direction or "").upper() or None

    continuous_bullish = (
        vwap_level_bias > 0 and vwap_slope_bias > 0 and
        math.isfinite(pcr) and pcr > STATE_PCR_BULL_THRESHOLD and pcr_rate_15m > 0 and
        put_writing_support and call_unwinding_resistance
    )
    continuous_bearish = (
        vwap_level_bias < 0 and vwap_slope_bias < 0 and
        math.isfinite(pcr) and pcr < STATE_PCR_BEAR_THRESHOLD and pcr_rate_15m < 0 and
        call_writing_resistance and put_unwinding_support
    )

    near_support = math.isfinite(major_support) and abs(spot - major_support) <= REVERSAL_WALL_PROXIMITY_ATR * max(atr3, 1.0)
    near_resistance = math.isfinite(major_resistance) and abs(spot - major_resistance) <= REVERSAL_WALL_PROXIMITY_ATR * max(atr3, 1.0)

    bull_reversal_matrix = (
        prior_direction_matrix == "BEARISH" and near_support and pcr_higher_low and put_writing_support and
        (vwap_ctx["bull_acceptance"] or vwap_ctx["bull_cross"]) and
        vwap_ctx["slope_change"] >= REVERSAL_VWAP_SLOPE_CHANGE_ATR * max(atr3, 1.0)
    )
    bear_reversal_matrix = (
        prior_direction_matrix == "BULLISH" and near_resistance and pcr_lower_high and call_writing_resistance and
        (vwap_ctx["bear_acceptance"] or vwap_ctx["bear_cross"]) and
        vwap_ctx["slope_change"] <= -REVERSAL_VWAP_SLOPE_CHANGE_ATR * max(atr3, 1.0)
    )
    trap = detect_false_breakout_trap(primary_session, spot, vwap, atr3, chain_levels)

    if trap["detected"]:
        scenario_state = "FALSE_BREAKOUT_TRAP"
        scenario_direction = int(trap["direction"])
        scenario_entry = True
        scenario_trigger = f"Take the counter-trend side only after the failed wall breach is confirmed by a completed 3m VWAP rejection/reclaim at {trap['level']:.2f}."
        scenario_invalidation = f"Invalidate if a completed 3m candle closes back beyond trap wall {trap['level']:.2f} in the breakout direction."
        scenario_reasons.append(trap["reason"])
    elif bull_reversal_matrix:
        scenario_state = "BEARISH_TO_BULLISH_REVERSAL"
        scenario_direction = 1
        scenario_reasons.append("Bearish prior regime + Put Support defense + PCR higher-low + bullish VWAP acceptance + positive VWAP slope change.")
        scenario_trigger = "Require the reversal confirmation sequence to remain above VWAP while Put Writing persists at the defended support wall."
        scenario_invalidation = "Invalidate on a completed 3m close below VWAP or a decisive break of the defended Put Support wall."
    elif bear_reversal_matrix:
        scenario_state = "BULLISH_TO_BEARISH_REVERSAL"
        scenario_direction = -1
        scenario_reasons.append("Bullish prior regime + Call Resistance defense + PCR lower-high + bearish VWAP acceptance + negative VWAP slope change.")
        scenario_trigger = "Require the reversal confirmation sequence to remain below VWAP while Call Writing persists at the defended resistance wall."
        scenario_invalidation = "Invalidate on a completed 3m close above VWAP or a decisive break of the defended Call Resistance wall."
    elif continuous_bullish:
        scenario_state = "CONTINUOUS_BULLISH"
        scenario_direction = 1
        scenario_entry = True
        scenario_trigger = "Price > rising VWAP; PCR > 1.20 and rising; heavy Put Writing at support; Call Unwinding at resistance."
        scenario_invalidation = "Invalidate on a completed 3m close below VWAP or loss of immediate Put Support."
    elif continuous_bearish:
        scenario_state = "CONTINUOUS_BEARISH"
        scenario_direction = -1
        scenario_entry = True
        scenario_trigger = "Price < falling VWAP; PCR < 0.80 and falling; heavy Call Writing at resistance; Put Unwinding at support."
        scenario_invalidation = "Invalidate on a completed 3m close above VWAP or loss of immediate Call Resistance."

    # -------------------------------------------------------------------------
    # MARKET DIRECTION + PHASE
    # -------------------------------------------------------------------------
    direction = raw_price_direction or (
        "BULLISH" if bull_confirmed >= 3 and core_score > 0 else
        "BEARISH" if bear_confirmed >= 3 and core_score < 0 else
        "NEUTRAL"
    )

    # Keep a direction through neutral/noisy scans when the new core is not strong
    # enough to override it. A strong opposite price core always wins.
    if direction == "NEUTRAL" and seed_direction in {"BULLISH", "BEARISH"}:
        direction = seed_direction

    opposite_confirmations = (
        bull_confirmed if direction == "BEARISH" else
        bear_confirmed if direction == "BULLISH" else 0
    )
    selected_confirmed = (
        bear_confirmed if direction == "BEARISH" else
        bull_confirmed if direction == "BULLISH" else 0
    )

    reversal_confirmations = 0
    transition_active = False
    if direction == "BULLISH":
        prior_phase_bull_reversal = previous_phase and str(previous_phase).upper().startswith("BEARISH_TO_BULLISH")
        if inferred_reversal_bull or (seed_direction == "BEARISH" and raw_price_direction == "BULLISH") or (prior_phase_bull_reversal and previous_direction == "BULLISH"):
            transition_active = True
            reversal_confirmations = (
                previous_reversal_confirmations + 1
                if prior_phase_bull_reversal and previous_direction == "BULLISH"
                else 1
            )
        if transition_active and reversal_confirmations < REVERSAL_ENTRY_CONFIRMATIONS_REQUIRED:
            market_phase = "BEARISH_TO_BULLISH_REVERSAL"
        elif transition_active:
            market_phase = "BEARISH_TO_BULLISH_REVERSAL_CONFIRMED"
        elif opposite_confirmations >= 1:
            market_phase = "BULLISH_WEAKENING"
        else:
            market_phase = "CONTINUOUS_BULLISH"
    elif direction == "BEARISH":
        prior_phase_bear_reversal = previous_phase and str(previous_phase).upper().startswith("BULLISH_TO_BEARISH")
        if inferred_reversal_bear or (seed_direction == "BULLISH" and raw_price_direction == "BEARISH") or (prior_phase_bear_reversal and previous_direction == "BEARISH"):
            transition_active = True
            reversal_confirmations = (
                previous_reversal_confirmations + 1
                if prior_phase_bear_reversal and previous_direction == "BEARISH"
                else 1
            )
        if transition_active and reversal_confirmations < REVERSAL_ENTRY_CONFIRMATIONS_REQUIRED:
            market_phase = "BULLISH_TO_BEARISH_REVERSAL"
        elif transition_active:
            market_phase = "BULLISH_TO_BEARISH_REVERSAL_CONFIRMED"
        elif opposite_confirmations >= 1:
            market_phase = "BEARISH_WEAKENING"
        else:
            market_phase = "CONTINUOUS_BEARISH"
    else:
        market_phase = "SIDEWAYS"

    # Full confirmation remains the continuation-grade entry. Reversal entries
    # use the adaptive reversal gate once the first reversal is structurally visible.
    full_entry_confirmed = full_bull_gate or full_bear_gate
    tactical_reversal = bullish_reversal_gate or bearish_reversal_gate
    entry_confirmed = bool(full_entry_confirmed or tactical_reversal)

    if market_phase in {"BEARISH_TO_BULLISH_REVERSAL", "BULLISH_TO_BEARISH_REVERSAL"}:
        # During the first reversal confirmation, the adaptive tactical gate may
        # act because it already requires price/VWAP/Change-OI/non-hostile PCR and
        # a non-strongly-opposed futures/chain state. A full continuation-grade
        # gate, however, does not bypass reversal persistence.
        entry_confirmed = bool(tactical_reversal and reversal_confirmations >= 1)
    elif market_phase.endswith("_CONFIRMED"):
        entry_confirmed = bool(full_entry_confirmed or tactical_reversal)

    if direction == "NEUTRAL":
        confirmation_state = "NEUTRAL"
    elif full_entry_confirmed:
        confirmation_state = "FULL"
    elif tactical_reversal:
        confirmation_state = "TACTICAL_REVERSAL"
    elif opposite_confirmations > 0:
        confirmation_state = "CONFLICT"
    else:
        confirmation_state = "PARTIAL"

    # Scenario matrix has precedence for the final state/entry decision.
    if scenario_direction > 0:
        direction = "BULLISH"
    elif scenario_direction < 0:
        direction = "BEARISH"

    if scenario_state in {"BEARISH_TO_BULLISH_REVERSAL", "BULLISH_TO_BEARISH_REVERSAL"}:
        expected_direction = "BULLISH" if scenario_state.startswith("BEARISH_TO_BULLISH") else "BEARISH"
        if previous_phase and str(previous_phase).startswith(scenario_state) and previous_direction == expected_direction:
            reversal_confirmations = previous_reversal_confirmations + 1
        else:
            reversal_confirmations = 1
        market_phase = scenario_state + ("_CONFIRMED" if reversal_confirmations >= REVERSAL_ENTRY_CONFIRMATIONS_REQUIRED else "")
        entry_confirmed = bool(scenario_entry and reversal_confirmations >= REVERSAL_ENTRY_CONFIRMATIONS_REQUIRED)
    elif scenario_state:
        market_phase = scenario_state
        entry_confirmed = bool(scenario_entry)
        reversal_confirmations = 0

    if scenario_state == "FALSE_BREAKOUT_TRAP":
        confirmation_state = "SCENARIO" if entry_confirmed else "PARTIAL"
    elif scenario_state:
        confirmation_state = "SCENARIO" if entry_confirmed else "PARTIAL"

    selected_groups = (
        bullish_groups if direction == "BULLISH"
        else bearish_groups if direction == "BEARISH"
        else max(bullish_groups, bearish_groups)
    )
    alignment = selected_groups / max(len(directional_groups), 1)
    core_magnitude = min(abs(core_score) / 10.0, 1.0)
    total_magnitude = min(abs(total_score) / 14.0, 1.0)
    confirmation_factor = selected_confirmed / 5.0

    if direction != "NEUTRAL":
        confidence = (
            35.0
            + 28.0 * core_magnitude
            + 20.0 * intraday_strength
            + 10.0 * alignment
            + 7.0 * min(confirmation_factor, 1.0)
        )
    else:
        confidence = 15.0 + 28.0 * core_magnitude + 16.0 * total_magnitude + 10.0 * alignment
    confidence = min(99.0, max(0.0, confidence))

    if scenario_state == "FALSE_BREAKOUT_TRAP":
        interpretation = "FALSE BREAKOUT TRAP — COUNTER-TREND REVERSAL SETUP"
    elif scenario_state == "BEARISH_TO_BULLISH_REVERSAL":
        interpretation = "BEARISH-TO-BULLISH REVERSAL — WAIT FOR CONFIRMATION"
    elif scenario_state == "BULLISH_TO_BEARISH_REVERSAL":
        interpretation = "BULLISH-TO-BEARISH REVERSAL — WAIT FOR CONFIRMATION"
    elif scenario_state == "CONTINUOUS_BULLISH":
        interpretation = "CONTINUOUS BULLISH — SCENARIO CONFIRMED"
    elif scenario_state == "CONTINUOUS_BEARISH":
        interpretation = "CONTINUOUS BEARISH — SCENARIO CONFIRMED"
    elif full_entry_confirmed:
        interpretation = "DERIVATIVE-CONFIRMED DIRECTIONAL STRUCTURE"
    elif direction == "BULLISH":
        interpretation = "BULLISH MARKET STRUCTURE — WAIT FOR SCENARIO CONFIRMATION"
    elif direction == "BEARISH":
        interpretation = "BEARISH MARKET STRUCTURE — WAIT FOR SCENARIO CONFIRMATION"
    else:
        interpretation = "SIDEWAYS / MIXED MARKET STRUCTURE"

    reasons = [
        f"Index-first price engine: intraday score={intraday_score:+.2f}, bias={intraday_bias:+d}, strength={intraday_strength:.3f}.",
        f"Index VWAP: price={'ABOVE' if vwap_level_bias > 0 else 'BELOW' if vwap_level_bias < 0 else 'AT'} VWAP={vwap:.2f}; slope={vwap_slope:+.2f}.",
        f"Price core score={core_score:+.2f}; total structure score={total_score:+.2f}.",
        f"Futures regime={futures_regime}; bias={futures_bias:+d}; OI strength={futures_info['oi_strength']:.3f}; persistence={futures_info['oi_persistence']:.3f}.",
        f"PCR={pcr:.3f} bias={pcr_bias:+d}; Change-OI score={change_oi_score:+.3f} bias={change_oi_bias:+d}.",
        f"Chain predictive bias={chain_predictive_bias:+d}; strength={chain_predictive_strength:.3f}; level bias={chain_level_bias:+d}.",
        f"Confirmations bullish={bull_confirmed}/5 bearish={bear_confirmed}/5; confirmation_state={confirmation_state}.",
        f"Prior direction={effective_prior or 'NONE'}; transition={effective_hint or 'NONE'}; reversal={reversal_confirmations}/{REVERSAL_ENTRY_CONFIRMATIONS_REQUIRED}.",
    ]

    if tactical_reversal:
        reasons.append("Adaptive reversal gate passed: price/VWAP + Change-OI + non-hostile PCR + non-strongly-opposed futures/chain.")
    elif transition_active:
        reasons.append("Reversal detected from index price history, but adaptive derivative/timing conditions are not yet complete.")

    if scenario_reasons:
        reasons.extend(scenario_reasons)
    reasons.append(
        f"Scenario matrix: state={scenario_state or 'UNCONFIRMED'}; PCR={pcr:.3f}; rate15m={pcr_rate_15m:+.3f}; "
        f"higher_low={pcr_higher_low}; lower_high={pcr_lower_high}; major_support={major_support:.2f}; "
        f"support_put_change={safe_float(chain_levels.get('major_support_put_change')):+.0f}; "
        f"major_resistance={major_resistance:.2f}; resistance_call_change={safe_float(chain_levels.get('major_resistance_call_change')):+.0f}."
    )

    logger.info(
        "MARKET STRUCTURE V7: score=%+.2f core=%+.2f direction=%s confidence=%.1f | "
        "Intraday=%+d/%.3f Futures=%s/%.3f ChainPred=%+d/%.3f VWAP=%s | "
        "TF=%s | BullConf=%d BearConf=%d Phase=%s Entry=%s",
        total_score, core_score, direction, confidence,
        intraday_bias, intraday_strength,
        futures_regime, futures_info["oi_strength"],
        chain_predictive_bias, chain_predictive_strength,
        "ABOVE" if vwap_level_bias > 0 else "BELOW" if vwap_level_bias < 0 else "AT",
        ",".join(
            f"{tf}:{'B' if tf_directions.get(tf,0)>0 else 'S' if tf_directions.get(tf,0)<0 else 'N'}"
            for tf in TIMEFRAMES
        ),
        bull_confirmed, bear_confirmed, market_phase, confirmation_state,
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
        support_1=safe_float(chain_levels.get("support_1"), spot),
        support_2=safe_float(chain_levels.get("support_2"), spot),
        resistance_1=safe_float(chain_levels.get("resistance_1"), spot),
        resistance_2=safe_float(chain_levels.get("resistance_2"), spot),
        market_phase=market_phase,
        entry_confirmed=entry_confirmed,
        reversal_confirmations=reversal_confirmations,
        confirmation_state=confirmation_state,
        pcr=pcr if math.isfinite(pcr) else float("nan"),
        pcr_bias=pcr_bias,
        pcr_rate_15m=float(pcr_rate_15m),
        pcr_higher_low=bool(pcr_higher_low),
        pcr_lower_high=bool(pcr_lower_high),
        false_breakout=bool(scenario_state == "FALSE_BREAKOUT_TRAP"),
        trap_level=safe_float(trap.get("level"), 0.0),
        entry_trigger=scenario_trigger,
        invalidation_rule=scenario_invalidation,
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
    distance_score = 1.0 if distance_steps <= 0.5 else 0.65 if distance_steps <= 1.0 else 0.20

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
    market_phase: Optional[str] = None,
) -> OptionCandidate:
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("Option selection requires BULLISH or BEARISH.")

    rows = chain_rows(chain)
    strikes = sorted(rows)
    step = strike_step(strikes)
    atm = nearest_strike(spot, strikes)
    atm_distance_steps = abs(atm - spot) / max(step, 1.0)

    # Fail safe rather than silently selecting a materially displaced strike.
    # This catches malformed/incomplete chains and prevents a stale chain from
    # converting an otherwise correct reversal into an obviously wrong option.
    if atm_distance_steps > 1.25:
        raise ScannerError(
            f"ATM strike sanity check failed: index spot={spot:.2f}, "
            f"nearest strike={atm:.0f}, step={step:.0f} "
            f"({atm_distance_steps:.2f} steps away)."
        )

    is_reversal = str(market_phase or "").upper() in {
        "BEARISH_TO_BULLISH_REVERSAL",
        "BEARISH_TO_BULLISH_REVERSAL_CONFIRMED",
        "BULLISH_TO_BEARISH_REVERSAL",
        "BULLISH_TO_BEARISH_REVERSAL_CONFIRMED",
    }

    expiry_dates = {
        parse_date(str(row.get("expiry", "")))
        for row in rows.values()
        if parse_date(str(row.get("expiry", ""))) is not None
    }
    expiry_day = now_ist().date() in expiry_dates

    if is_reversal:
        # Reversal entries use ATM first. On expiry day, ATM is mandatory unless
        # it is unavailable/invalid; this avoids paying for a displaced strike
        # exactly when gamma/theta are most sensitive.
        if EXPIRY_DAY_FORCE_ATM and expiry_day:
            candidate_strikes = [atm]
        else:
            candidate_strikes = (
                [atm, atm - step]
                if direction == "BULLISH"
                else [atm, atm + step]
            )
    else:
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

    if is_reversal:
        candidates = [
            x for x in candidates
            if abs(x.strike - spot) / max(step, 1.0) <= REVERSAL_STRIKE_MAX_DISTANCE_STEPS
        ]
        if not candidates:
            raise ScannerError(
                f"No reversal option within {REVERSAL_STRIKE_MAX_DISTANCE_STEPS:.2f} strike steps of index spot={spot:.2f}."
            )

    selected = max(
        candidates,
        key=lambda x: (
            option_health_score(x, atm, step)
            - (0.08 * abs(x.strike - atm) / max(step, 1.0) if is_reversal else 0.0)
        ),
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
    """Build T1/T2/SL from the next structural wall or 1.5x/3x ATR.

    T1 prefers the next major option-chain wall when it is sufficiently
    separated from spot; otherwise it falls back to 1.5 ATR. T2 prefers the
    second wall; otherwise it uses 3 ATR. The stop sits behind the nearest
    structural anchor, using VWAP, Supertrend and the opposite option wall.
    """
    atr3 = max(safe_float(tf_frames[3]["atr"].iloc[-1], 0.0), 1.0)
    atr15 = max(safe_float(tf_frames[15]["atr"].iloc[-1], atr3), atr3)

    # Keep the risk model realistic for unusually large ATR readings.
    max_allowed_atr = max(spot * 0.0025, 1.0)
    atr3 = min(atr3, max_allowed_atr)
    atr15 = min(max(atr15, atr3), max_allowed_atr * 1.5)

    st3 = safe_float(tf_frames[3]["supertrend"].iloc[-1], spot)
    st15 = safe_float(tf_frames[15]["supertrend"].iloc[-1], spot)

    is_bear = structure.direction == "BEARISH"
    if is_bear:
        wall1 = structure.support_1 if structure.support_1 < spot else float("nan")
        wall2 = structure.support_2 if structure.support_2 < spot else float("nan")
        wall1_dist = spot - wall1 if math.isfinite(wall1) else 0.0
        target1 = wall1 if wall1_dist >= 0.50 * atr3 else spot - 1.50 * atr3
        if math.isfinite(wall2) and wall2 < target1 and (spot - wall2) >= 1.00 * atr3:
            target2 = wall2
        else:
            target2 = spot - 3.00 * atr3

        stop_candidates = [
            structure.vwap + 0.25 * atr3,
            st3 + 0.20 * atr3,
            st15 + 0.20 * atr15,
        ]
        if structure.resistance_1 > spot:
            stop_candidates.append(structure.resistance_1 + 0.25 * atr3)
        # For a bearish trade the nearest valid anchor above spot is the stop.
        underlying_stop = min(x for x in stop_candidates if x > spot)
        if underlying_stop <= spot:
            underlying_stop = spot + 0.80 * atr3

        target1 = min(target1, spot - 0.25 * atr3)
        target2 = min(target2, target1 - 0.50 * atr3)
        return float(target1), float(target2), float(underlying_stop)

    wall1 = structure.resistance_1 if structure.resistance_1 > spot else float("nan")
    wall2 = structure.resistance_2 if structure.resistance_2 > spot else float("nan")
    wall1_dist = wall1 - spot if math.isfinite(wall1) else 0.0
    target1 = wall1 if wall1_dist >= 0.50 * atr3 else spot + 1.50 * atr3
    if math.isfinite(wall2) and wall2 > target1 and (wall2 - spot) >= 1.00 * atr3:
        target2 = wall2
    else:
        target2 = spot + 3.00 * atr3

    stop_candidates = [
        structure.vwap - 0.25 * atr3,
        st3 - 0.20 * atr3,
        st15 - 0.20 * atr15,
    ]
    if structure.support_1 < spot:
        stop_candidates.append(structure.support_1 - 0.25 * atr3)
    # For a bullish trade the nearest valid anchor below spot is the stop.
    underlying_stop = max(x for x in stop_candidates if x < spot)
    if underlying_stop >= spot:
        underlying_stop = spot - 0.80 * atr3

    target1 = max(target1, spot + 0.25 * atr3)
    target2 = max(target2, target1 + 0.50 * atr3)
    return float(target1), float(target2), float(underlying_stop)


def project_option_premium(
    entry: float,
    underlying_move: float,
    delta: float,
    gamma: float,
) -> float:
    """
    Second-order local Greek approximation:
        Δpremium ≈ |delta| * |dS| + 0.5 * |gamma| * dS²

    This is deliberately used only for target/stop estimation, not execution.
    """
    move = abs(float(underlying_move))
    change = abs(delta) * move + 0.5 * abs(gamma) * move * move
    return float(max(0.0, entry + change))


def project_option_premium_signed(
    entry: float,
    underlying_move: float,
    delta: float,
    gamma: float,
) -> float:
    """Signed second-order premium projection for trailing-stop estimation."""
    move = float(underlying_move)
    change = float(delta) * move + 0.5 * abs(float(gamma)) * move * move
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


def format_engine_output(signal: Signal) -> str:
    """Return the exact six-part scanner output requested by the strategy spec."""
    return (
        f"1. Market State: [{signal.market_state}]\n"
        f"2. Bias: [{signal.bias}]\n"
        f"3. Entry Trigger: [{signal.entry_trigger}]\n"
        f"4. Targets:\n"
        f"   - T1: {signal.target_1:.2f} (underlying {signal.underlying_target_1:.2f})\n"
        f"   - T2: {signal.target_2:.2f} (underlying {signal.underlying_target_2:.2f})\n"
        f"5. Stop Loss: {signal.stop_loss:.2f} (underlying {signal.underlying_stop:.2f})\n"
        f"6. Invalidation Rule: [{signal.invalidation_rule}]"
    )


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
<tr><td><b>Market State</b></td><td>{html.escape(signal.market_state)}</td></tr>
<tr><td><b>Regime</b></td><td>{html.escape(signal.regime)}</td></tr>
<tr><td><b>Entry Trigger</b></td><td>{html.escape(signal.entry_trigger)}</td></tr>
<tr><td><b>Invalidation</b></td><td>{html.escape(signal.invalidation_rule)}</td></tr>
<tr><td><b>Confidence</b></td><td>{signal.confidence:.1f}%</td></tr>
<tr><td><b>Spot</b></td><td>{signal.spot:.2f}</td></tr>
<tr><td><b>Futures Regime</b></td><td>{html.escape(signal.futures_state)}</td></tr>
<tr><td><b>Option</b></td><td>{html.escape(signal.trading_symbol)}</td></tr>
<tr><td><b>Strike</b></td><td>{signal.strike:.0f} {signal.option_type}</td></tr>
<tr><td><b>Entry</b></td><td>₹{signal.entry:.2f}</td></tr>
<tr><td><b>Target 1</b></td><td>₹{signal.target_1:.2f}</td></tr>
<tr><td><b>Target 2</b></td><td>₹{signal.target_2:.2f}</td></tr>
<tr><td><b>Stop Loss</b></td><td>₹{signal.stop_loss:.2f}</td></tr>
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
    tf_frames: Optional[dict[int, pd.DataFrame]] = None,
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
    t1_hit = bool(trade.get("t1_hit", False)) or ltp >= target1

    # T1 is a milestone, not a full exit. Once reached, the stop ratchets to
    # cost and then trails until T2 or a protective stop is reached.
    if ltp >= target2:
        outcome = "TARGET_2"
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
                f"Entry: ₹{entry:.2f}<br>"
                f"Exit: ₹{ltp:.2f}<br>"
                f"Outcome: {outcome}</p>"
            ),
        )
        return "CLOSED"

    # After T1, move the option stop to cost and then trail from the live
    # underlying Supertrend/ATR boundary. This ratchets risk only upward.
    if t1_hit:
        trade["t1_hit"] = True
        current_stop = safe_float(trade.get("stop_loss"), 0.0)
        if entry > current_stop:
            current_stop = entry
        trade["stop_loss"] = round(current_stop, 2)

        if tf_frames and 3 in tf_frames:
            try:
                atr3 = max(safe_float(tf_frames[3]["atr"].iloc[-1], 0.0), 1.0)
                st3 = safe_float(tf_frames[3]["supertrend"].iloc[-1], 0.0)
                snapshot = state.get("market_snapshot") if isinstance(state.get("market_snapshot"), dict) else {}
                spot_now = safe_float(snapshot.get("spot"), 0.0)
                base_spot = safe_float(trade.get("entry_underlying"), spot_now)
                direction = str(trade.get("direction", "")).upper()
                if spot_now > 0 and base_spot > 0 and st3 > 0:
                    trail_underlying = (
                        max(st3, spot_now - atr3)
                        if direction == "BULLISH"
                        else min(st3, spot_now + atr3)
                    )
                    signed_move = trail_underlying - base_spot
                    # Do not tighten beyond the entry-side direction: for a
                    # long CE, trail must remain above entry underlying; for a
                    # long PE, it must remain below entry underlying.
                    signed_move = signed_move if (
                        (direction == "BULLISH" and signed_move > 0)
                        or (direction == "BEARISH" and signed_move < 0)
                    ) else 0.0
                    trail_option = project_option_premium_signed(
                        entry, signed_move, safe_float(trade.get("delta")), safe_float(trade.get("gamma"))
                    )
                    # A long option stop must remain below the current premium.
                    trail_option = min(trail_option, max(0.0, ltp - 0.01))
                    trade["stop_loss"] = round(max(safe_float(trade.get("stop_loss")), trail_option), 2)
            except (KeyError, IndexError, TypeError, ValueError) as exc:
                logger.info("Trailing-stop update skipped: %s", exc)

    if t1_hit and not bool(trade.get("t1_notified", False)):
        trade["t1_notified"] = True
        send_email(
            f"SENSEX T1 HIT - {trade['trading_symbol']}",
            (
                f"<p>T1 reached; trade remains active for T2.</p>"
                f"<p>Option: {html.escape(str(trade['trading_symbol']))}<br>"
                f"Entry: ₹{entry:.2f}<br>"
                f"Current: ₹{ltp:.2f}<br>"
                f"New protective SL: ₹{safe_float(trade.get('stop_loss')):.2f}</p>"
            ),
        )

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

    # -------------------------------------------------------------------------
    # PRIMARY MARKET PRICE FEED = SENSEX INDEX
    # -------------------------------------------------------------------------
    index_session = get_current_session_futures_candles(SENSEX_KEY)
    index_live_quote = get_quote(SENSEX_KEY)
    spot = extract_ltp(index_live_quote)

    # -------------------------------------------------------------------------
    # DERIVATIVES FEED = SENSEX FUTURES PRICE/OI
    # -------------------------------------------------------------------------
    futures_session = get_current_session_futures_candles(future.instrument_key)
    futures_live_quote = get_quote(future.instrument_key)
    futures_ltp_now = extract_ltp(futures_live_quote)

    logger.info(
        "UNDERLYING PRICES: index_spot=%.2f futures_ltp=%.2f basis=%+.2f",
        spot, futures_ltp_now, futures_ltp_now - spot,
    )

    # If the current index feed is late, use the current-session slice from the
    # regular V3 timeframe path; only then fall back to a live quote proxy.
    if index_session.empty:
        try:
            index_history = get_timeframe_candles(SENSEX_KEY, 3, min_bars=25)
            local_dates = index_history["timestamp"].dt.tz_convert(IST).dt.date
            index_session = index_history.loc[local_dates == now_ist().date()].copy()
        except ScannerError as exc:
            logger.warning("Index 3m session fallback unavailable: %s", exc)

    if index_session.empty:
        ltp = spot
        opening_ts = pd.Timestamp(now_ist()).tz_convert("UTC")
        index_session = pd.DataFrame([{
            "timestamp": opening_ts,
            "open": ltp,
            "high": ltp,
            "low": ltp,
            "close": ltp,
            "volume": safe_float(index_live_quote.get("volume"), 0.0),
            "oi": np.nan,
        }])
        logger.warning("INDEX SESSION: using live index quote proxy until candles arrive.")

    if futures_session.empty:
        ltp = futures_ltp_now
        opening_ts = pd.Timestamp(now_ist()).tz_convert("UTC")
        futures_session = pd.DataFrame([{
            "timestamp": opening_ts,
            "open": ltp,
            "high": ltp,
            "low": ltp,
            "close": ltp,
            "volume": safe_float(futures_live_quote.get("volume"), 0.0),
            "oi": _extract_quote_oi(futures_live_quote),
        }])
        logger.warning("FUTURES SESSION: using live futures quote proxy until candles arrive.")

    # Historical futures bars are only for OI warm-up; historical index bars are
    # only used if the live current-session index feed is too short.
    try:
        historical_futures = get_historical_candles(
            future.instrument_key, 3, lookback_days=10
        )
        historical_completed = filter_completed_candles(historical_futures, 3)
    except ScannerError as exc:
        logger.warning("Historical futures 3m fallback unavailable: %s", exc)
        historical_completed = pd.DataFrame()

    if futures_session.empty:
        futures_3m = historical_completed.tail(40).copy()
    else:
        completed_current = filter_completed_candles(futures_session, 3)
        futures_3m = pd.concat(
            [historical_completed.tail(35), completed_current],
            ignore_index=True,
        )
        if not futures_3m.empty:
            futures_3m = (
                futures_3m.sort_values("timestamp")
                .drop_duplicates("timestamp", keep="last")
                .reset_index(drop=True)
            )

    # Multi-timeframe structures are already computed from the SENSEX index.
    tf_frames, tf_directions = timeframe_snapshot(SENSEX_KEY)
    expiry, chain = get_option_chain()
    daily_oi_bias, daily_oi_score = get_daily_oi_confirmation(expiry)
    change_oi_bias, change_oi_score, change_oi_by_strike = get_change_oi_confirmation(expiry)
    pcr_value, pcr_rate_15m, pcr_trend, pcr_higher_low, pcr_lower_high = get_intraday_pcr(expiry)
    chain_levels = chain_oi_support_resistance(chain, spot, change_oi_by_strike)
    chain_levels["pcr_trend"] = pcr_trend

    previous_snapshot = state.get("market_snapshot") if isinstance(state.get("market_snapshot"), dict) else {}
    previous_direction = str(previous_snapshot.get("direction", "")).upper() or None
    persistent_direction = str(
        state.get("persistent_direction")
        or previous_snapshot.get("persistent_direction", "")
    ).upper() or None
    previous_phase = str(previous_snapshot.get("market_phase", "")).upper() or None
    previous_reversal_confirmations = int(previous_snapshot.get("reversal_confirmations", 0) or 0)

    # Provisional index direction for history reconstruction.
    vwap_seed, _, _ = vwap_snapshot(index_session)
    provisional_intraday_bias, _, provisional_intraday_score = intraday_trend_snapshot(
        index_session, vwap_seed
    )
    provisional_current_direction = (
        "BULLISH" if provisional_intraday_score >= CORE_BULL_TRIGGER
        else "BEARISH" if provisional_intraday_score <= CORE_BEAR_TRIGGER
        else persistent_direction or previous_direction or "NEUTRAL"
    )

    inferred_prior_direction, transition_hint = infer_prior_session_direction(
        index_session, provisional_current_direction
    )

    seed_direction = persistent_direction or previous_direction
    if inferred_prior_direction and transition_hint in {
        "BEARISH_TO_BULLISH", "BULLISH_TO_BEARISH"
    }:
        seed_direction = inferred_prior_direction
    elif not seed_direction and inferred_prior_direction:
        seed_direction = inferred_prior_direction

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
        previous_direction=seed_direction,
        previous_phase=previous_phase,
        previous_reversal_confirmations=previous_reversal_confirmations,
        price_session=index_session,
        inferred_prior_direction=inferred_prior_direction,
        transition_hint=transition_hint,
        pcr_value=pcr_value,
        pcr_rate_15m=pcr_rate_15m,
        pcr_higher_low=pcr_higher_low,
        pcr_lower_high=pcr_lower_high,
    )

    state_history = state.get("market_history")
    if not isinstance(state_history, list):
        state_history = []
    history_item = {
        "timestamp": now_ist().isoformat(),
        "spot": round(spot, 2),
        "direction": structure.direction,
        "phase": structure.market_phase,
        "score": round(structure.score, 3),
        "core": round(structure.components.get("intraday_trend", 0.0) + structure.components.get("vwap_level", 0.0), 3),
        "confidence": round(structure.confidence, 2),
        "confirmation_state": structure.confirmation_state,
        "reversal_confirmations": structure.reversal_confirmations,
    }
    state_history.append(history_item)
    state["market_history"] = state_history[-STATE_HISTORY_LIMIT:]

    state["market_snapshot"] = {
        "timestamp": now_ist().isoformat(),
        "spot": round(spot, 2),
        "futures_ltp": round(futures_ltp_now, 2),
        "basis": round(futures_ltp_now - spot, 2),
        "future": future.trading_symbol,
        "future_expiry": future.expiry,
        "futures_regime": structure.futures_regime,
        "futures_bias": structure.futures_bias,
        "futures_oi_strength": round(structure.futures_oi_strength, 4),
        "futures_oi_persistence": round(structure.futures_oi_persistence, 4),
        "futures_live_oi_change": round(structure.futures_live_oi_change, 2) if math.isfinite(structure.futures_live_oi_change) else None,
        "intraday_bias": structure.intraday_bias,
        "intraday_strength": round(structure.intraday_strength, 4),
        "intraday_score": round(structure.intraday_score, 4),
        "chain_predictive_bias": structure.chain_predictive_bias,
        "chain_predictive_strength": round(structure.chain_predictive_strength, 4),
        "chain_level_bias": structure.chain_level_bias,
        "support_strength": round(structure.support_strength, 4),
        "resistance_strength": round(structure.resistance_strength, 4),
        "support_change_strength": round(structure.support_change_strength, 4),
        "resistance_change_strength": round(structure.resistance_change_strength, 4),
        "vwap": round(structure.vwap, 2),
        "vwap_slope": round(structure.vwap_slope, 4),
        "direction": structure.direction,
        "persistent_direction": (
            structure.direction if structure.direction in {"BULLISH", "BEARISH"}
            else seed_direction
        ),
        "inferred_prior_direction": inferred_prior_direction or "",
        "transition_hint": transition_hint,
        "score": round(structure.score, 3),
        "confidence": round(structure.confidence, 2),
        "market_phase": structure.market_phase,
        "entry_confirmed": structure.entry_confirmed,
        "reversal_confirmations": structure.reversal_confirmations,
        "confirmation_state": structure.confirmation_state,
        "pcr": structure.pcr if math.isfinite(structure.pcr) else None,
        "pcr_bias": structure.pcr_bias,
        "pcr_rate_15m": round(structure.pcr_rate_15m, 4),
        "pcr_higher_low": structure.pcr_higher_low,
        "pcr_lower_high": structure.pcr_lower_high,
        "false_breakout": structure.false_breakout,
        "trap_level": structure.trap_level,
        "entry_trigger": structure.entry_trigger,
        "invalidation_rule": structure.invalidation_rule,
        "support_1": structure.support_1,
        "support_2": structure.support_2,
        "resistance_1": structure.resistance_1,
        "resistance_2": structure.resistance_2,
        "timeframes": structure.timeframe_directions,
        "components": structure.components,
    }
    state["persistent_direction"] = (
        structure.direction if structure.direction in {"BULLISH", "BEARISH"}
        else (seed_direction or "")
    ) or None
    save_state(state)

    logger.info(
        "REVERSAL CONTEXT: persisted=%s inferred_prior=%s hint=%s immediate_previous=%s",
        state.get("persistent_direction") or "NONE",
        inferred_prior_direction or "NONE",
        transition_hint,
        previous_direction or "NONE",
    )
    logger.info(
        "PREDICTION: %s | %s | confidence=%.1f score=%+.2f",
        structure.direction,
        structure.interpretation,
        structure.confidence,
        structure.score,
    )

    if active_trade_from_state(state) is not None:
        monitor_active_trade(state, structure, tf_frames)
        return None

    completed_session_bars = len(filter_completed_candles(index_session, 3))
    opening_mode = now_time < MIN_ENTRY_TIME or completed_session_bars < 1
    if opening_mode:
        logger.info(
            "OPENING MODE: completed_index_3m_bars=%d time=%s; monitoring structure without forcing a trade.",
            completed_session_bars,
            now_time.strftime("%H:%M:%S"),
        )
        return None

    if structure.direction == "NEUTRAL":
        logger.info(
            "No entry: market structure is neutral/mixed; phase=%s.",
            structure.market_phase,
        )
        return None

    allowed_matrix_states = {
        "CONTINUOUS_BULLISH",
        "CONTINUOUS_BEARISH",
        "FALSE_BREAKOUT_TRAP",
        "BEARISH_TO_BULLISH_REVERSAL",
        "BULLISH_TO_BEARISH_REVERSAL",
    }
    matrix_state = (
        structure.market_phase[:-10]
        if structure.market_phase.endswith("_CONFIRMED")
        else structure.market_phase
    )
    if matrix_state not in allowed_matrix_states:
        logger.info(
            "No entry: scenario matrix state not confirmed: %s",
            structure.market_phase,
        )
        return None

    if not structure.entry_confirmed:
        logger.info(
            "No entry: confirmation/tactical gate failed. direction=%s phase=%s state=%s reversal=%d/%d PCR_bias=%+d",
            structure.direction,
            structure.market_phase,
            structure.confirmation_state,
            structure.reversal_confirmations,
            REVERSAL_ENTRY_CONFIRMATIONS_REQUIRED,
            structure.pcr_bias,
        )
        return None

    if structure.confidence < SIGNAL_THRESHOLD:
        logger.info(
            "No entry: confidence %.1f < %.1f",
            structure.confidence,
            SIGNAL_THRESHOLD,
        )
        return None

    atr3_val = max(safe_float(tf_frames[3]["atr"].iloc[-1], 50.0), 1.0)
    timing_ok, timing_state, vwap_distance_atr, latest_3m_move_atr = entry_timing_filter(
        price_session=index_session,
        direction=structure.direction,
        vwap=structure.vwap,
        atr3=atr3_val,
        market_phase=structure.market_phase,
    )
    logger.info(
        "ENTRY TIMING: state=%s vwap_distance=%.2f ATR latest_3m_move=%.2f ATR",
        timing_state,
        vwap_distance_atr,
        latest_3m_move_atr,
    )
    if not timing_ok:
        logger.info(
            "No entry: directional gate passed but timing filter rejected setup: %s.",
            timing_state,
        )
        return None

    option = select_directional_option(
        chain=chain,
        direction=structure.direction,
        spot=spot,
        market_phase=structure.market_phase,
    )
    target1, target2, stop_loss, underlying_stop, underlying_target1, underlying_target2 = create_dynamic_targets(
        option=option,
        structure=structure,
        spot=spot,
        tf_frames=tf_frames,
    )

    setup_label = (
        "FULL-CONFIRMATION ENTRY" if structure.confirmation_state == "FULL"
        else "TACTICAL REVERSAL ENTRY"
    )
    reasons = list(structure.reasons)
    reasons.extend([
        f"Setup type: {setup_label}.",
        f"Entry timing: {timing_state}; index VWAP distance={vwap_distance_atr:.2f} ATR; latest 3m move={latest_3m_move_atr:.2f} ATR; completed index 3m bars={completed_session_bars}.",
        f"Strike rule: {'REVERSAL/EXPIRY-DAY ATM CE' if structure.direction == 'BULLISH' and structure.market_phase.startswith('BEARISH_TO_BULLISH') else 'REVERSAL/EXPIRY-DAY ATM PE' if structure.direction == 'BEARISH' and structure.market_phase.startswith('BULLISH_TO_BEARISH') else 'ATM-1/ATM-2 CE' if structure.direction == 'BULLISH' else 'ATM+1/ATM+2 PE'}.",
        f"Index spot used for option ATM selection={spot:.2f}; futures LTP={futures_ltp_now:.2f}; futures/index basis={futures_ltp_now - spot:+.2f}.",
        f"Selected option health: spread={option.spread_pct:.2%}, theta burden={option.theta_burden_pct_day:.2%}/day, volume={option.volume:.0f}, OI={option.oi:.0f}, delta={option.delta:.3f}.",
        f"Dynamic underlying targets: T1={underlying_target1:.2f}, T2={underlying_target2:.2f}, SL={underlying_stop:.2f}.",
        f"Dynamic option targets: T1=₹{target1:.2f}, T2=₹{target2:.2f}, SL=₹{stop_loss:.2f}.",
        "Market direction is determined from the SENSEX index. Futures price/OI and option-chain data confirm or qualify the entry; option premium momentum is not the directional trigger.",
    ])

    return Signal(
        timestamp=now_ist().strftime("%Y-%m-%d %H:%M:%S IST"),
        direction=structure.direction,
        regime=structure.interpretation,
        market_state=(structure.market_phase[:-10] if structure.market_phase.endswith("_CONFIRMED") else structure.market_phase),
        bias="Bullish" if structure.direction == "BULLISH" else "Bearish" if structure.direction == "BEARISH" else "Neutral",
        entry_trigger=structure.entry_trigger,
        invalidation_rule=structure.invalidation_rule,
        confidence=structure.confidence,
        spot=spot,
        futures_state=structure.futures_regime,
        option_type=option.option_type,
        strike=option.strike,
        trading_symbol=option.trading_symbol,
        instrument_key=option.instrument_key,
        entry=option.ltp,
        target_1=target1,
        target_2=target2,
        stop_loss=stop_loss,
        underlying_stop=underlying_stop,
        underlying_target_1=underlying_target1,
        underlying_target_2=underlying_target2,
        delta=option.delta,
        gamma=option.gamma,
        theta=option.theta,
        support_1=structure.support_1,
        support_2=structure.support_2,
        resistance_1=structure.resistance_1,
        resistance_2=structure.resistance_2,
        reasons=reasons,
    )

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

    # Reversal-history regression: a current bullish move following a prior
    # bearish completed 3m window must be detected even without prior state.
    reversal_values = [110, 109, 108, 107, 106, 105, 104, 103, 104, 106, 108, 110]
    reversal_df = _synthetic_candles(reversal_values)
    prior_dir, hint = infer_prior_session_direction(reversal_df, "BULLISH")
    assert prior_dir == "BEARISH", (prior_dir, hint)
    assert hint == "BEARISH_TO_BULLISH", (prior_dir, hint)

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

    # New matrix regression: false breakout trap must fire only after the wall
    # breach is followed by rejection and VWAP failure with adverse wall OI.
    trap_df = _synthetic_candles([100, 101, 104, 106, 107, 103, 102])
    trap_vwap, _, _ = vwap_snapshot(trap_df)
    trap_atr = float(calculate_atr(trap_df).iloc[-1])
    trap_result = detect_false_breakout_trap(
        trap_df, 102.0, trap_vwap, trap_atr,
        {
            "major_resistance": 105.0,
            "major_support": 95.0,
            "call_writing_at_resistance": True,
            "put_writing_at_support": False,
        },
    )
    assert trap_result["detected"] is True, trap_result
    assert trap_result["direction"] == -1, trap_result
    assert trap_result["kind"] == "RESISTANCE_TRAP", trap_result

    # New risk regression: underlying T1/T2 use the requested 1.5x/3x ATR
    # fallback, while a real option wall is preferred when it is far enough away.
    selected_reversal = select_directional_option(
        chain, "BULLISH", 74100, market_phase="BEARISH_TO_BULLISH_REVERSAL"
    )
    assert selected_reversal.strike in {74050.0, 74100.0}

    selected_bull = select_directional_option(chain, "BULLISH", 74100)
    selected_bear = select_directional_option(chain, "BEARISH", 74100)
    assert selected_bull.strike in {74100.0, 74050.0, 74000.0}
    assert selected_bear.strike in {74100.0, 74150.0, 74200.0}
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
    assert bull_structure.market_phase == "BULLISH_WEAKENING", bull_structure
    assert not bull_structure.entry_confirmed, bull_structure
    assert bull_structure.confirmation_state == "CONFLICT", bull_structure

    # Phase-aware regression: a strong bearish core with bullish Change-OI/PCR
    # conflict remains BEARISH, but is explicitly marked as weakening. It must
    # not flip bullish and must not produce an option-entry confirmation.
    weakening_chain = dict(chain_levels)
    weakening_chain.update({
        "pcr": 1.08,
        "pcr_bias": 1,
        "predictive_bias": 0,
        "predictive_strength": 0.10,
        "level_bias": 0,
        "change_bias": 0,
    })
    weakening = build_market_structure(
        spot=93.0,
        futures_3m=fut,
        futures_session=fut,
        tf_frames=frames,
        tf_directions=tf_dirs,
        chain_levels=weakening_chain,
        daily_oi_bias=-1,
        daily_oi_score=-0.20,
        change_oi_bias=1,
        change_oi_score=0.24,
    )
    assert weakening.direction == "BEARISH", weakening
    assert weakening.market_phase == "BEARISH_WEAKENING", weakening
    assert weakening.confirmation_state == "CONFLICT", weakening
    assert not weakening.entry_confirmed, weakening

    # Strict-entry regression: all four mandatory confirmations aligned with
    # the price core must allow an entry; chain OI is an additional confirmation.
    confirmed_chain = dict(bull_chain_levels)
    confirmed_chain.update({
        "oi_bias": 1, "change_bias": 1, "predictive_bias": 1,
        "predictive_strength": 0.30, "level_bias": 1,
        "pcr": 1.10, "pcr_bias": 1,
    })
    confirmed = build_market_structure(
        spot=107.5,
        futures_3m=bull_session,
        futures_session=bull_session,
        tf_frames=bull_frames,
        tf_directions=bull_tf_dirs,
        chain_levels=confirmed_chain,
        daily_oi_bias=1,
        daily_oi_score=0.20,
        change_oi_bias=1,
        change_oi_score=0.25,
        futures_live_quote={"oi": 1140},
    )
    assert confirmed.direction == "BULLISH", confirmed
    assert confirmed.entry_confirmed, confirmed
    assert confirmed.confirmation_state == "FULL", confirmed

    # Reversal persistence regression: the first bullish scan after a bearish
    # regime is labelled as a reversal but cannot trigger an option entry. The
    # second consecutive confirming scan is required before entry is allowed.
    reversal_1 = build_market_structure(
        spot=107.5, futures_3m=bull_session, futures_session=bull_session,
        tf_frames=bull_frames, tf_directions=bull_tf_dirs,
        chain_levels=confirmed_chain, daily_oi_bias=1, daily_oi_score=0.20,
        change_oi_bias=1, change_oi_score=0.25, futures_live_quote={"oi": 1140},
        previous_direction="BEARISH", previous_phase="CONTINUOUS_BEARISH",
        previous_reversal_confirmations=0,
    )
    assert reversal_1.market_phase == "BEARISH_TO_BULLISH_REVERSAL", reversal_1
    assert reversal_1.reversal_confirmations == 1, reversal_1
    assert reversal_1.entry_confirmed, reversal_1

    reversal_2 = build_market_structure(
        spot=107.5, futures_3m=bull_session, futures_session=bull_session,
        tf_frames=bull_frames, tf_directions=bull_tf_dirs,
        chain_levels=confirmed_chain, daily_oi_bias=1, daily_oi_score=0.20,
        change_oi_bias=1, change_oi_score=0.25, futures_live_quote={"oi": 1140},
        previous_direction="BULLISH", previous_phase="BEARISH_TO_BULLISH_REVERSAL",
        previous_reversal_confirmations=1,
    )
    assert reversal_2.market_phase == "BEARISH_TO_BULLISH_REVERSAL_CONFIRMED", reversal_2
    assert reversal_2.reversal_confirmations == 2, reversal_2
    assert reversal_2.entry_confirmed, reversal_2

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

    # Entry-timing regression: an already-displaced trend must be rejected even
    # when directional structure is strong. A fresh breakout within the VWAP
    # distance limit remains eligible.
    extended = _synthetic_candles(
        [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
    )
    ok, state, dist_atr, move_atr = entry_timing_filter(
        extended, "BULLISH", vwap=100.0, atr3=2.0
    )
    assert not ok, (ok, state, dist_atr, move_atr)
    assert state == "VWAP_EXTENDED", state

    breakout = _synthetic_candles(
        [100, 100.2, 100.1, 100.3, 100.2, 100.4, 100.3, 100.5, 100.7, 100.6, 100.8, 103.3]
    )
    ok, state, _, _ = entry_timing_filter(
        breakout, "BULLISH", vwap=100.2, atr3=3.0
    )
    assert ok, (ok, state)
    assert state in {"FRESH_BREAKOUT", "PULLBACK_RECLAIM"}, state

    # Oct-1-style index reversal regression:
    # bearish early structure, then strong recent index recovery + VWAP reclaim +
    # bullish Change-OI should become a tactical reversal rather than remain
    # permanently SIDEWAYS because cumulative PCR/futures positioning lag.
    oct1_like = _synthetic_candles(
        [100.0, 99.6, 99.3, 99.1, 99.0, 99.2, 99.8, 100.5, 101.0, 101.4,
         101.8, 102.1, 102.4, 102.7],
        [1000, 990, 980, 970, 960, 950, 940, 930, 920, 910, 900, 890, 880, 870],
    )
    oct_frames = {
        3: calculate_supertrend(oct1_like, 10, 2.0),
        15: calculate_supertrend(oct1_like, 10, 2.0),
        30: calculate_supertrend(oct1_like, 10, 2.0),
        60: calculate_supertrend(oct1_like, 10, 2.0),
        120: calculate_supertrend(oct1_like, 10, 2.0),
        180: calculate_supertrend(oct1_like, 10, 2.0),
    }
    oct1_dirs = {3: 1, 15: -1, 30: -1, 60: -1, 120: -1, 180: -1}
    oct_chain = {
        "support_1": 102.0, "support_2": 101.0,
        "resistance_1": 104.0, "resistance_2": 105.0,
        "oi_bias": 0, "change_bias": 1,
        "predictive_bias": 0, "predictive_strength": 0.05,
        "level_bias": 0, "support_strength": 0.30,
        "resistance_strength": 0.30, "support_change_strength": 0.30,
        "resistance_change_strength": 0.30, "pcr": 1.02, "pcr_bias": 0,
    }
    oct_structure = build_market_structure(
        spot=102.7,
        futures_3m=oct1_like,
        futures_session=oct1_like,
        price_session=oct1_like,
        tf_frames=oct_frames,
        tf_directions=oct1_dirs,
        chain_levels=oct_chain,
        daily_oi_bias=0,
        daily_oi_score=0.0,
        change_oi_bias=1,
        change_oi_score=0.18,
        futures_live_quote={"last_price": 102.7, "oi": 940},
        previous_direction="BEARISH",
        previous_phase="CONTINUOUS_BEARISH",
        previous_reversal_confirmations=0,
        inferred_prior_direction="BEARISH",
        transition_hint="BEARISH_TO_BULLISH",
    )
    assert oct_structure.direction == "BULLISH", oct_structure
    assert oct_structure.market_phase.startswith("BEARISH_TO_BULLISH"), oct_structure
    assert oct_structure.confirmation_state in {"TACTICAL_REVERSAL", "FULL"}, oct_structure
    assert oct_structure.entry_confirmed, oct_structure

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
            "entry_underlying": signal.spot,
            "t1_hit": False,
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

        print(format_engine_output(signal))

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
