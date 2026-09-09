"""
SENSEX Predictive Options Market Scanner

Strategy:
- SENSEX 3-minute and 15-minute Supertrend: (10, 3)
- Full current-session VWAP + price structure
- Dynamic current-month SENSEX futures discovery
- Futures price/OI regime
- Current-week option-chain OI / previous OI
- Strike-level CE/PE OI differential with proximity weighting
- Option price/OI confirmation for the selected contract
- Pre-breakout prediction instead of waiting for an option breakout
- Reversal detection
- Directional ITM option selection:
      bullish -> ATM-1 CE, fallback ATM-2 CE
      bearish -> ATM+1 PE, fallback ATM+2 PE
- No option-extension rejection for predictive entries
- T1 based on projected 3-minute breakout level
- T2 based on projected 15-minute resistance/support
- Option premium targets translated using live option Delta/Gamma
- Stop loss = 10% below entry premium
- Duplicate signal suppression via persisted state
- Email notifications only for new actionable signals

No order placement is performed.
"""

from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import smtplib
import sys
import traceback
import urllib.parse
import time as time_module
from dataclasses import dataclass, asdict
from datetime import datetime, time
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path
from typing import Any, Optional
from zoneinfo import ZoneInfo


import numpy as np
import pandas as pd
import requests


# =============================================================================
# CONFIGURATION
# =============================================================================

IST = ZoneInfo("Asia/Kolkata")

BASE_URL = "https://api.upstox.com"

SENSEX_KEY = os.getenv(
    "SENSEX_INSTRUMENT_KEY",
    "BSE_INDEX|SENSEX",
).strip()

UPSTOX_TOKEN = os.getenv(
    "UPSTOX_ANALYTICS_TOKEN",
    "",
).strip()

EMAIL_SENDER = os.getenv(
    "EMAIL_SENDER",
    "",
).strip()

EMAIL_PASSWORD = os.getenv(
    "EMAIL_PASSWORD",
    "",
).strip()

EMAIL_RECEIVER = os.getenv(
    "EMAIL_RECEIVER",
    "",
).strip()

SMTP_HOST = os.getenv(
    "SMTP_HOST",
    "smtp.gmail.com",
).strip()

SMTP_PORT = int(
    os.getenv(
        "SMTP_PORT",
        "465",
    )
)

REQUEST_TIMEOUT = int(
    os.getenv(
        "REQUEST_TIMEOUT",
        "20",
    )
)

SCANNER_VERSION = "2026-09-09-MARKET-STRUCTURE-OVERHAUL-V2"

STATE_FILE = Path(
    os.getenv(
        "STATE_FILE",
        "state/market_state.json",
    )
)

SIGNAL_THRESHOLD = float(
    os.getenv(
        "SIGNAL_THRESHOLD",
        "40",
    )
)

PREDICTION_MIN_CONFLUENCE = 3
MIN_DIRECTIONAL_GROUPS = 3
LOCK_SETUP_MINUTES = 45
MARKET_SCORE_ENTRY = 5.0
MARKET_SCORE_STRONG = 7.0
REVERSAL_CONFIRMATIONS_REQUIRED = 2
NEUTRAL_DOES_NOT_EXIT = True
ACTIVE_TRADE_SL_PCT = 0.10
ACTIVE_TRADE_SL_FACTOR = 1.0 - ACTIVE_TRADE_SL_PCT

MARKET_START = time(9, 15)
MARKET_END = time(15, 30)

SUPERTREND_PERIOD = 10
SUPERTREND_FACTOR = 3.0

STRUCTURE_LOOKBACK_3M = 8
STRUCTURE_LOOKBACK_15M = 6

OPTION_MIN_DELTA = 0.35
OPTION_MAX_DELTA = 0.85

# BUY-ONLY option momentum guardrails. A strike must show positive premium
# momentum before it can be selected or locked.
BUY_OPTION_LOOKBACK = 6
BUY_OPTION_MIN_CANDLES = 5
BUY_OPTION_MIN_RETURN_PCT = 0.10

# Noise controls for a 5-minute workflow.
VWAP_FLAT_SLOPE_EPSILON = 0.10
FUTURES_BASIS_EPSILON_POINTS = 1.00
FUTURES_REGIME_MIN_PRICE_MOVE = 0.50
FUTURES_REGIME_MIN_OI_CHANGE = 1.0

MAX_SIGNAL_AGE_MINUTES = 15
VWAP_TRANSITION_LOOKBACK_CANDLES = 5

# Do not select an option that is already materially collapsing at entry.
# This is a strike-health preference, not a bullish/bearish market filter.
OPTION_ENTRY_MAX_DRAWNDOWN_PCT = float(os.getenv("OPTION_ENTRY_MAX_DRAWDOWN_PCT", "0.50"))
OPTION_ENTRY_MAX_PEAK_PULLBACK_PCT = float(os.getenv("OPTION_ENTRY_MAX_PEAK_PULLBACK_PCT", "0.75"))
OPTION_ENTRY_MIN_3M_RETURN_PCT = float(os.getenv("OPTION_ENTRY_MIN_3M_RETURN_PCT", "0.10"))

# Chart-driven OI-difference thresholds.
# OI difference = weighted (PE OI - CE OI) around ATM.
OI_DIFF_POSITIVE_THRESHOLD = 0.03
OI_DIFF_CHANGE_THRESHOLD = 0.01
VWAP_RECLAIM_TOLERANCE_PCT = 0.0015
CAP_CE_CHANGE_THRESHOLD = 0.10

# =============================================================================
# SIDEWAYS / RANGE MARKET FILTER
# =============================================================================

SIDEWAYS_LOOKBACK_3M = 12
SIDEWAYS_LOOKBACK_15M = 6

# Total high-low range relative to ATR.
SIDEWAYS_MAX_RANGE_ATR_3M = 3.0
SIDEWAYS_MAX_RANGE_ATR_15M = 2.5

# Net movement from first close to latest close relative to ATR.
SIDEWAYS_MAX_NET_MOVE_ATR_3M = 0.75
SIDEWAYS_MAX_NET_MOVE_ATR_15M = 0.75

# Number of directional Supertrend flips allowed inside the lookback.
SIDEWAYS_MAX_SUPERTREND_FLIPS = 2

# OI score near zero means positioning is balanced.
SIDEWAYS_CHAIN_OI_SCORE = 0.05
SIDEWAYS_CHANGE_OI_SCORE = 0.10

# =============================================================================
# ENDPOINTS
# =============================================================================

INSTRUMENT_SEARCH_URL = (
    f"{BASE_URL}/v2/instruments/search"
)

OPTION_CHAIN_URL = (
    f"{BASE_URL}/v2/option/chain"
)

OPTION_CONTRACT_URL = (
    f"{BASE_URL}/v2/option/contract"
)

CHANGE_OI_URL = (
    f"{BASE_URL}/v2/market/change-oi"
)

MARKET_STATUS_URL = (
    f"{BASE_URL}/v2/market/status/BSE"
)

QUOTE_URL = (
    f"{BASE_URL}/v2/market-quote/quotes"
)
HISTORICAL_CANDLE_URL = (
    f"{BASE_URL}/v3/historical-candle"
)

# =============================================================================
# LOGGING
# =============================================================================

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
)

logger = logging.getLogger("sensex_scanner")


# =============================================================================
# DATA CLASSES
# =============================================================================

@dataclass
class FuturesContract:
    instrument_key: str
    trading_symbol: str
    expiry: str


@dataclass
class OptionCandidate:
    instrument_key: str
    trading_symbol: str
    option_type: str
    strike: float
    expiry: str
    ltp: float
    oi: float
    prev_oi: float
    delta: float
    gamma: float
    iv: float


@dataclass
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
    underlying_trigger_3m: float
    underlying_target_15m: float
    delta: float
    gamma: float
    reasons: list[str]


# =============================================================================
# EXCEPTIONS
# =============================================================================

class ScannerError(Exception):
    pass


# =============================================================================
# TIME HELPERS
# =============================================================================

def now_ist() -> datetime:
    return datetime.now(IST)


def market_window_open() -> bool:

    current = now_ist()

    if current.weekday() >= 5:
        return False

    if is_bse_holiday(current):
        logger.info(
            "BSE holiday: %s. Scanner will not run.",
            current.strftime("%Y-%m-%d"),
        )
        return False

    return (
        MARKET_START
        <= current.time()
        <= MARKET_END
    )


# =============================================================================
# API HELPERS
# =============================================================================

def api_headers() -> dict[str, str]:
    if not UPSTOX_TOKEN:
        raise ScannerError(
            "UPSTOX_ANALYTICS_TOKEN is missing."
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

    last_error = None

    for attempt in range(1, retries + 1):

        try:
            response = requests.get(
                url,
                params=params,
                headers=api_headers(),
                timeout=REQUEST_TIMEOUT,
            )

        except requests.RequestException as exc:

            last_error = f"Network request failed: {exc}"

            if attempt < retries:
                wait_seconds = attempt * 2

                logger.warning(
                    "Request failed. Retry %d/%d in %d seconds: %s",
                    attempt,
                    retries,
                    wait_seconds,
                    last_error,
                )

                time_module.sleep(wait_seconds)
                continue

            raise ScannerError(last_error) from exc

        if response.status_code == 200:

            try:
                payload = response.json()

            except ValueError as exc:
                raise ScannerError(
                    "Upstox returned invalid JSON."
                ) from exc

            if not isinstance(payload, dict):
                raise ScannerError(
                    "Unexpected Upstox response structure."
                )

            if payload.get("status") == "error":
                raise ScannerError(
                    json.dumps(payload)[:1500]
                )

            return payload

        last_error = (
            f"Upstox HTTP {response.status_code}: "
            f"{response.text[:1000]}"
        )

        transient_error = response.status_code in {
            500,
            502,
            503,
            504,
        }

        logger.warning(
            "Upstox request failed | attempt=%d/%d | "
            "status=%s | url=%s | params=%s | response=%s",
            attempt,
            retries,
            response.status_code,
            url,
            params,
            response.text[:1000],
        )

        if transient_error and attempt < retries:

            wait_seconds = attempt * 2

            logger.info(
                "Transient Upstox server error. Retrying in %d seconds...",
                wait_seconds,
            )

            time_module.sleep(wait_seconds)
            continue

        raise ScannerError(last_error)

    raise ScannerError(
        last_error or "Unknown Upstox API error."
    )

# =============================================================================
# MARKET HOLIDAY
# =============================================================================

def is_bse_holiday(
    current_date: datetime,
) -> bool:
    """
    Uses Upstox's market-holiday API to determine whether
    BSE is closed on the current IST date.
    """

    date_string = current_date.strftime(
        "%Y-%m-%d"
    )

    url = (
        f"{BASE_URL}/v2/market/holidays/{date_string}"
    )

    try:
        payload = api_get(url)

        data = payload.get(
            "data"
        )

        # Upstox returns holiday information when the
        # requested date is a holiday.
        if isinstance(data, dict):
            return bool(data)

        if isinstance(data, list):
            return len(data) > 0

        return False

    except ScannerError as exc:
        logger.warning(
            "Holiday API unavailable: %s",
            exc,
        )

        # Do not silently assume a trading holiday when
        # the holiday service itself is unavailable.
        return False

# =============================================================================
# MARKET STATUS
# =============================================================================

def get_market_status() -> str:

    payload = api_get(
        MARKET_STATUS_URL
    )

    serialized = json.dumps(
        payload,
        default=str,
    ).lower()

    if '"open"' in serialized or "open" in serialized:
        return "OPEN"

    if "closed" in serialized:
        return "CLOSED"

    return "UNKNOWN"


# =============================================================================
# SENSEX QUOTE
# =============================================================================

def get_quote(
    instrument_key: str,
) -> dict[str, Any]:

    payload = api_get(
        QUOTE_URL,
        {
            "instrument_key": instrument_key,
        },
    )

    data = payload.get(
        "data",
        {},
    )

    if not isinstance(data, dict):
        raise ScannerError(
            "Quote response data is not an object."
        )

    if instrument_key in data:
        return data[instrument_key]

    if len(data) == 1:
        return next(iter(data.values()))

    raise ScannerError(
        f"Quote not found for {instrument_key}."
    )


def extract_ltp(
    quote: dict[str, Any],
) -> float:

    for field in (
        "last_price",
        "ltp",
        "lastPrice",
    ):
        value = quote.get(field)

        if value is not None:
            price = float(value)

            if price > 0:
                return price

    raise ScannerError(
        "LTP not present in quote."
    )


# =============================================================================
# INSTRUMENT DISCOVERY
# =============================================================================
def get_current_sensex_future() -> FuturesContract:

    all_contracts = []

    # Try current month first, then next month.
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

        contracts = payload.get("data", [])

        if isinstance(contracts, list):
            all_contracts.extend(contracts)

    if not all_contracts:
        raise ScannerError(
            "No active SENSEX futures returned by Upstox."
        )

    valid = []

    for contract in all_contracts:

        if not (
            contract.get("instrument_key")
            and contract.get("trading_symbol")
            and contract.get("expiry")
        ):
            continue

        underlying = str(
            contract.get(
                "underlying_symbol",
                ""
            )
        ).upper()

        symbol = str(
            contract.get(
                "trading_symbol",
                ""
            )
        ).upper()

        if (
            "SENSEX" in underlying
            or "SENSEX" in symbol
        ):
            valid.append(contract)

    if not valid:
        logger.error(
            "Upstox futures response: %s",
            json.dumps(
                all_contracts,
                default=str,
            ),
        )

        raise ScannerError(
            "No valid SENSEX future found."
        )

    # Sort by expiry and select nearest available future.
    valid.sort(
        key=lambda x: str(
            x.get("expiry")
        )
    )

    selected = valid[0]

    logger.info(
        "Selected SENSEX future: %s | Expiry: %s | Key: %s",
        selected["trading_symbol"],
        selected["expiry"],
        selected["instrument_key"],
    )

    return FuturesContract(
        instrument_key=selected["instrument_key"],
        trading_symbol=selected["trading_symbol"],
        expiry=str(selected["expiry"]),
    )

def get_current_week_contracts() -> list[dict[str, Any]]:
    """
    Load SENSEX option contracts for the exact weekly Thursday expiry.
    """
    exact_expiry = get_active_sensex_expiry()

    logger.info(
        "Using exact dynamically selected SENSEX weekly expiry for option contracts: %s",
        exact_expiry,
    )

    payload = api_get(
        OPTION_CONTRACT_URL,
        {
            "instrument_key": SENSEX_KEY,
            "expiry_date": exact_expiry,
        },
    )

    contracts = payload.get("data", [])

    if not isinstance(contracts, list) or not contracts:
        raise ScannerError(
            "No SENSEX option contracts returned for selected expiry "
            f"{exact_expiry}."
        )

    return contracts


# =============================================================================
# CANDLE DATA
# =============================================================================

def get_intraday_candles(
    instrument_key: str,
    interval_minutes: int,
    max_candles: Optional[int] = None,
    min_candles: int = 2,
) -> pd.DataFrame:

    encoded_key = urllib.parse.quote(
        instrument_key,
        safe="",
    )

    # Use Upstox V3 intraday candles for the current trading session.
    # This is the correct V3 endpoint for current-day data and supports
    # custom minute intervals such as 3 and 15 minutes.
    url = (
        f"{HISTORICAL_CANDLE_URL}/intraday/"
        f"{encoded_key}/minutes/{interval_minutes}"
    )

    payload = api_get(url)

    data = payload.get(
        "data",
        {},
    )

    candles = data.get(
        "candles",
        [],
    )

    if not isinstance(candles, list) or not candles:
        raise ScannerError(
            f"No {interval_minutes}-minute candles returned for {instrument_key}."
        )

    records = []

    for row in candles:
        if not isinstance(row, (list, tuple)) or len(row) < 6:
            continue

        try:
            records.append(
                {
                    "timestamp": row[0],
                    "open": float(row[1]),
                    "high": float(row[2]),
                    "low": float(row[3]),
                    "close": float(row[4]),
                    "volume": float(row[5]),
                    "oi": (
                        float(row[6])
                        if len(row) > 6 and row[6] is not None
                        else np.nan
                    ),
                }
            )
        except (TypeError, ValueError):
            continue

    df = pd.DataFrame(records)

    if df.empty:
        raise ScannerError(
            f"No valid {interval_minutes}-minute candles after parsing."
        )

    df["timestamp"] = pd.to_datetime(
        df["timestamp"],
        utc=True,
        errors="coerce",
    )

    df = (
        df
        .dropna(subset=["timestamp"])
        .sort_values("timestamp")
        .drop_duplicates(subset=["timestamp"])
        .reset_index(drop=True)
    )

    # Keep only current-session records. The V3 intraday endpoint is current-day
    # data, but this explicit filter protects the VWAP calculation.
    session_date = now_ist().date()
    session_dates = df["timestamp"].dt.tz_convert(IST).dt.date
    df = df.loc[session_dates == session_date].reset_index(drop=True)

    if len(df) < min_candles:
        raise ScannerError(
            f"Insufficient current-session {interval_minutes}-minute candles: "
            f"got {len(df)}, need at least {min_candles}."
        )

    if max_candles is not None and len(df) > max_candles:
        df = df.tail(max_candles).reset_index(drop=True)

    logger.info(
        "Loaded %d current-session %d-minute candles for %s",
        len(df),
        interval_minutes,
        instrument_key,
    )

    return df


def get_session_candles_for_vwap(
    instrument_key: str,
    interval_minutes: int = 3,
    min_candles: int = 20,
) -> pd.DataFrame:
    """Fetch and return the complete current-session candle set for VWAP.

    This function intentionally does not accept max_candles. It prevents the
    short Futures regime window (2-3 candles) from ever being reused as the
    VWAP source.
    """
    df = get_intraday_candles(
        instrument_key,
        interval_minutes,
        max_candles=None,
        min_candles=min_candles,
    )

    usable_volume = pd.to_numeric(
        df["volume"], errors="coerce"
    ).fillna(0.0).clip(lower=0.0)

    if len(df) < min_candles or float(usable_volume.sum()) <= 0.0:
        raise ScannerError(
            f"Insufficient usable Futures session data for VWAP: "
            f"candles={len(df)}, volume={float(usable_volume.sum()):.0f}."
        )

    logger.info(
        "VWAP source: SENSEX Futures | current-session candles=%d | volume=%0.f",
        len(df),
        float(usable_volume.sum()),
    )
    return df


# =============================================================================
# INDICATORS
# =============================================================================

def calculate_atr(
    df: pd.DataFrame,
    period: int,
) -> pd.Series:

    previous_close = df["close"].shift(1)

    true_range = pd.concat(
        [
            df["high"] - df["low"],
            (
                df["high"]
                - previous_close
            ).abs(),
            (
                df["low"]
                - previous_close
            ).abs(),
        ],
        axis=1,
    ).max(axis=1)

    return true_range.ewm(
        alpha=1 / period,
        adjust=False,
        min_periods=1,
    ).mean()


def calculate_supertrend(
    df: pd.DataFrame,
    period: int = SUPERTREND_PERIOD,
    factor: float = SUPERTREND_FACTOR,
) -> pd.DataFrame:

    result = df.copy()

    result["atr"] = calculate_atr(
        result,
        period,
    )

    hl2 = (
        result["high"]
        + result["low"]
    ) / 2.0

    basic_upper = (
        hl2
        + factor * result["atr"]
    )

    basic_lower = (
        hl2
        - factor * result["atr"]
    )

    final_upper = pd.Series(
        np.nan,
        index=result.index,
        dtype=float,
    )

    final_lower = pd.Series(
        np.nan,
        index=result.index,
        dtype=float,
    )

    direction = pd.Series(
        np.nan,
        index=result.index,
        dtype=float,
    )

    supertrend = pd.Series(
        np.nan,
        index=result.index,
        dtype=float,
    )

    if result.empty:
        raise ScannerError(
            "Unable to calculate Supertrend: no candles available."
        )

    first_valid = result["atr"].first_valid_index()

    if first_valid is None:
        raise ScannerError(
            f"Unable to calculate Supertrend: ATR contains no valid values "
            f"(candles={len(result)}, period={period})."
        )

    start = result.index.get_loc(
        first_valid
    )

    final_upper.iloc[start] = (
        basic_upper.iloc[start]
    )

    final_lower.iloc[start] = (
        basic_lower.iloc[start]
    )

    direction.iloc[start] = 1

    supertrend.iloc[start] = (
        final_lower.iloc[start]
    )

    for i in range(
        start + 1,
        len(result),
    ):

        prev = i - 1

        if (
            basic_upper.iloc[i]
            < final_upper.iloc[prev]
            or result["close"].iloc[prev]
            > final_upper.iloc[prev]
        ):
            final_upper.iloc[i] = (
                basic_upper.iloc[i]
            )
        else:
            final_upper.iloc[i] = (
                final_upper.iloc[prev]
            )

        if (
            basic_lower.iloc[i]
            > final_lower.iloc[prev]
            or result["close"].iloc[prev]
            < final_lower.iloc[prev]
        ):
            final_lower.iloc[i] = (
                basic_lower.iloc[i]
            )
        else:
            final_lower.iloc[i] = (
                final_lower.iloc[prev]
            )

        if (
            result["close"].iloc[i]
            > final_upper.iloc[prev]
        ):
            direction.iloc[i] = 1

        elif (
            result["close"].iloc[i]
            < final_lower.iloc[prev]
        ):
            direction.iloc[i] = -1

        else:
            direction.iloc[i] = (
                direction.iloc[prev]
            )

        supertrend.iloc[i] = (
            final_lower.iloc[i]
            if direction.iloc[i] == 1
            else final_upper.iloc[i]
        )

    result["supertrend"] = supertrend
    result["direction"] = direction

    return result


def calculate_vwap(
    df: pd.DataFrame,
) -> pd.Series:
    """Calculate session VWAP and fail explicitly when usable volume is absent."""
    if df.empty:
        return pd.Series(np.nan, index=df.index, dtype=float)

    typical = (
        df["high"]
        + df["low"]
        + df["close"]
    ) / 3.0

    volume = pd.to_numeric(df["volume"], errors="coerce").fillna(0.0).clip(lower=0.0)
    session = pd.to_datetime(
        df["timestamp"], utc=True, errors="coerce"
    ).dt.tz_convert(IST).dt.date

    cumulative_volume = volume.groupby(session).cumsum()
    cumulative_pv = (typical * volume).groupby(session).cumsum()

    vwap = cumulative_pv / cumulative_volume.replace(0, np.nan)

    # Index candles can legitimately have zero volume. In that case this is
    # not a real VWAP. The scanner uses SENSEX futures candles for VWAP instead.
    return vwap


# =============================================================================
# MARKET STRUCTURE
# =============================================================================

def structure_state(
    df: pd.DataFrame,
    lookback: int,
) -> str:

    if len(df) < lookback:
        return "NEUTRAL"

    recent = df.tail(
        lookback
    )

    highs = recent[
        "high"
    ].to_numpy()

    lows = recent[
        "low"
    ].to_numpy()

    bullish = (
        highs[-1] > highs[0]
        and lows[-1] > lows[0]
    )

    bearish = (
        highs[-1] < highs[0]
        and lows[-1] < lows[0]
    )

    if bullish:
        return "BULLISH"

    if bearish:
        return "BEARISH"

    return "NEUTRAL"

def market_regime(
    spot_3m: pd.DataFrame,
    spot_15m: pd.DataFrame,
    chain_bias: str,
    chain_bias_score: float,
    change_oi_bias_value: str,
    change_oi_score: float,
) -> tuple[str, list[str]]:

    """
    Classify the current market as TRENDING or SIDEWAYS.

    The goal is to prevent a single Futures regime + VWAP position
    from manufacturing a directional prediction while price action
    is actually compressed inside a range.
    """

    reasons: list[str] = []

    if (
        len(spot_3m) < SIDEWAYS_LOOKBACK_3M
        or len(spot_15m) < SIDEWAYS_LOOKBACK_15M
    ):
        return (
            "UNKNOWN",
            ["Insufficient candles for sideways/range classification."]
        )

    recent_3m = spot_3m.tail(
        SIDEWAYS_LOOKBACK_3M
    ).copy()

    recent_15m = spot_15m.tail(
        SIDEWAYS_LOOKBACK_15M
    ).copy()

    latest_3m = recent_3m.iloc[-1]
    latest_15m = recent_15m.iloc[-1]

    atr_3m = float(latest_3m.get("atr", np.nan))
    atr_15m = float(latest_15m.get("atr", np.nan))

    if (
        not math.isfinite(atr_3m)
        or not math.isfinite(atr_15m)
        or atr_3m <= 0
        or atr_15m <= 0
    ):
        return (
            "UNKNOWN",
            ["ATR unavailable for sideways/range classification."]
        )

    # -------------------------------------------------------------
    # 3-minute range measurements
    # -------------------------------------------------------------

    range_3m = float(
        recent_3m["high"].max()
        - recent_3m["low"].min()
    )

    net_move_3m = abs(
        float(recent_3m["close"].iloc[-1])
        - float(recent_3m["close"].iloc[0])
    )

    range_atr_3m = range_3m / atr_3m
    net_move_atr_3m = net_move_3m / atr_3m

    # -------------------------------------------------------------
    # 15-minute range measurements
    # -------------------------------------------------------------

    range_15m = float(
        recent_15m["high"].max()
        - recent_15m["low"].min()
    )

    net_move_15m = abs(
        float(recent_15m["close"].iloc[-1])
        - float(recent_15m["close"].iloc[0])
    )

    range_atr_15m = range_15m / atr_15m
    net_move_atr_15m = net_move_15m / atr_15m

    # -------------------------------------------------------------
    # Supertrend flip count
    # -------------------------------------------------------------

    direction_3m = (
        pd.to_numeric(
            recent_3m["direction"],
            errors="coerce"
        )
        .dropna()
        .astype(int)
    )

    direction_15m = (
        pd.to_numeric(
            recent_15m["direction"],
            errors="coerce"
        )
        .dropna()
        .astype(int)
    )

    flips_3m = int(
        direction_3m.ne(
            direction_3m.shift()
        ).sum() - 1
    ) if len(direction_3m) > 1 else 0

    flips_15m = int(
        direction_15m.ne(
            direction_15m.shift()
        ).sum() - 1
    ) if len(direction_15m) > 1 else 0

    # -------------------------------------------------------------
    # Price structure
    # -------------------------------------------------------------

    structure_3m = structure_state(
        recent_3m,
        min(
            STRUCTURE_LOOKBACK_3M,
            len(recent_3m)
        ),
    )

    structure_15m = structure_state(
        recent_15m,
        min(
            STRUCTURE_LOOKBACK_15M,
            len(recent_15m)
        ),
    )

    # -------------------------------------------------------------
    # Sideways conditions
    # -------------------------------------------------------------

    compressed_3m = (
        range_atr_3m <= SIDEWAYS_MAX_RANGE_ATR_3M
    )

    compressed_15m = (
        range_atr_15m <= SIDEWAYS_MAX_RANGE_ATR_15M
    )

    low_net_move_3m = (
        net_move_atr_3m <= SIDEWAYS_MAX_NET_MOVE_ATR_3M
    )

    low_net_move_15m = (
        net_move_atr_15m <= SIDEWAYS_MAX_NET_MOVE_ATR_15M
    )

    unstable_3m = (
        flips_3m >= SIDEWAYS_MAX_SUPERTREND_FLIPS
    )

    unstable_15m = (
        flips_15m >= SIDEWAYS_MAX_SUPERTREND_FLIPS
    )

    oi_balanced = (
        abs(float(chain_bias_score))
        <= SIDEWAYS_CHAIN_OI_SCORE
        and abs(float(change_oi_score))
        <= SIDEWAYS_CHANGE_OI_SCORE
    )

    neutral_structure = (
        structure_3m == "NEUTRAL"
        or structure_15m == "NEUTRAL"
        or structure_3m != structure_15m
    )

    sideways_score = 0

    if compressed_3m:
        sideways_score += 1

    if low_net_move_3m:
        sideways_score += 1

    if compressed_15m:
        sideways_score += 1

    if low_net_move_15m:
        sideways_score += 1

    if unstable_3m:
        sideways_score += 1

    if unstable_15m:
        sideways_score += 1

    if oi_balanced:
        sideways_score += 2

    if neutral_structure:
        sideways_score += 1

    logger.info(
        "Market regime check: "
        "3m_range_ATR=%.2f "
        "3m_net_ATR=%.2f "
        "15m_range_ATR=%.2f "
        "15m_net_ATR=%.2f "
        "3m_flips=%d "
        "15m_flips=%d "
        "structure_3m=%s "
        "structure_15m=%s "
        "chain_OI=%.3f "
        "change_OI=%.3f "
        "sideways_score=%d",
        range_atr_3m,
        net_move_atr_3m,
        range_atr_15m,
        net_move_atr_15m,
        flips_3m,
        flips_15m,
        structure_3m,
        structure_15m,
        float(chain_bias_score),
        float(change_oi_score),
        sideways_score,
    )

    # -----------------------------------------------------------------
    # STRONG SIDEWAYS / RANGE DETECTION
    # -----------------------------------------------------------------

    # The market can be sideways even if the 3-minute candles show
    # temporary directional movement. Give greater importance to the
    # 15-minute net movement because it represents the broader intraday
    # structure.
    strong_15m_compression = (
        compressed_15m
        and low_net_move_15m
    )

    timeframe_conflict = (
        structure_3m in {"BULLISH", "BEARISH"}
        and structure_15m in {"BULLISH", "BEARISH"}
        and structure_3m != structure_15m
    )

    # Strong sideways condition:
    # 1. 15-minute market remains compressed.
    # 2. Net movement is small.
    # 3. 3m and 15m structures disagree.
    if strong_15m_compression and timeframe_conflict:
        sideways_score = max(sideways_score, 5)
        reasons.append(
            "Strong sideways condition: compressed 15-minute range "
            "with minimal net movement and conflicting 3m/15m structure."
        )

    # -----------------------------------------------------------------
    # NORMAL SIDEWAYS CLASSIFICATION
    # -----------------------------------------------------------------
    if sideways_score >= 5:
        reasons.extend([
            "Market classified as SIDEWAYS/RANGE.",
            (
                f"3m range={range_atr_3m:.2f} ATR, "
                f"net move={net_move_atr_3m:.2f} ATR."
            ),
            (
                f"15m range={range_atr_15m:.2f} ATR, "
                f"net move={net_move_atr_15m:.2f} ATR."
            ),
            (
                f"3m structure={structure_3m}, "
                f"15m structure={structure_15m}."
            ),
            (
                f"Supertrend flips: "
                f"3m={flips_3m}, 15m={flips_15m}."
            ),
            (
                f"OI positioning: localized={chain_bias}, "
                f"Change-OI={change_oi_bias_value}."
            ),
        ])
        return "SIDEWAYS", reasons

    reasons.extend([
        "Market classified as TRENDING/EXPANDING.",
        (
            f"3m range={range_atr_3m:.2f} ATR, "
            f"net move={net_move_atr_3m:.2f} ATR."
        ),
        (
            f"15m range={range_atr_15m:.2f} ATR, "
            f"net move={net_move_atr_15m:.2f} ATR."
        ),
        (
            f"3m structure={structure_3m}, "
            f"15m structure={structure_15m}."
        ),
    ])

    return "TRENDING", reasons

def recent_swing_high(
    df: pd.DataFrame,
    lookback: int,
) -> float:

    if len(df) < lookback:
        raise ScannerError(
            "Insufficient data for swing high."
        )

    return float(
        df["high"]
        .iloc[
            -lookback:
            -1
        ]
        .max()
    )


def recent_swing_low(
    df: pd.DataFrame,
    lookback: int,
) -> float:

    if len(df) < lookback:
        raise ScannerError(
            "Insufficient data for swing low."
        )

    return float(
        df["low"]
        .iloc[
            -lookback:
            -1
        ]
        .min()
    )


# =============================================================================
# OPTION CHAIN ANALYSIS
# =============================================================================

def get_active_sensex_expiry() -> str:
    """
    Dynamically select the nearest non-expired SENSEX option expiry.

    The option-contract endpoint is queried without a relative expiry filter,
    then all valid expiry dates returned by Upstox are parsed and the nearest
    active date is selected.
    """
    payload = api_get(
        OPTION_CONTRACT_URL,
        {"instrument_key": SENSEX_KEY},
    )

    contracts = payload.get("data", [])

    if not isinstance(contracts, list) or not contracts:
        raise ScannerError(
            "No SENSEX option contracts returned for dynamic expiry discovery."
        )

    today = now_ist().date()
    weekly_expiries = set()

    for contract in contracts:
        if not isinstance(contract, dict):
            continue

        raw_expiry = str(contract.get("expiry", "")).strip()

        try:
            expiry_date = datetime.strptime(
                raw_expiry[:10],
                "%Y-%m-%d",
            ).date()
        except (TypeError, ValueError):
            continue

        if expiry_date < today:
            continue

        if bool(contract.get("weekly")):
            weekly_expiries.add(expiry_date)

    if not weekly_expiries:
        raise ScannerError(
            "No valid non-expired SENSEX weekly option expiry was found."
        )

    expiries = weekly_expiries

    selected_expiry = min(expiries).isoformat()

    logger.info(
        "Dynamically selected active SENSEX expiry: %s",
        selected_expiry,
    )

    return selected_expiry


def get_chain() -> list[dict[str, Any]]:
    """
    Load the SENSEX option chain using a dynamically discovered
    active expiry.
    """

    exact_expiry = get_active_sensex_expiry()

    logger.info(
        "Using dynamically selected SENSEX expiry for option chain: %s",
        exact_expiry,
    )

    # Verify the selected expiry through the option contracts endpoint
    # before requesting the option chain.
    contracts_payload = api_get(
        OPTION_CONTRACT_URL,
        {
            "instrument_key": SENSEX_KEY,
            "expiry_date": exact_expiry,
        },
    )

    contracts = contracts_payload.get("data", [])

    if not isinstance(contracts, list) or not contracts:

        raise ScannerError(
            "Selected SENSEX expiry was discovered but no active option "
            f"contracts were returned for expiry {exact_expiry}."
        )

    returned_expiries = sorted(
        {
            str(contract.get("expiry", "")).strip()[:10]
            for contract in contracts
            if isinstance(contract, dict)
            and contract.get("expiry")
        }
    )

    logger.info(
        "Verified SENSEX option contracts: expiry=%s | contracts=%d",
        exact_expiry,
        len(contracts),
    )

    if exact_expiry not in returned_expiries:

        raise ScannerError(
            f"Expiry validation failed. Requested={exact_expiry}, "
            f"returned={returned_expiries}"
        )

    payload = api_get(
        OPTION_CHAIN_URL,
        {
            "instrument_key": SENSEX_KEY,
            "expiry_date": exact_expiry,
        },
        retries=4,
    )

    data = payload.get("data", [])

    if not isinstance(data, list) or not data:

        raise ScannerError(
            "SENSEX option chain is empty for expiry "
            f"{exact_expiry}."
        )

    logger.info(
        "Loaded SENSEX option chain: expiry=%s | rows=%d",
        exact_expiry,
        len(data),
    )

    return data


def chain_spot(
    chain: list[dict[str, Any]],
) -> float:

    values = []

    for row in chain:

        value = row.get(
            "underlying_spot_price"
        )

        if value is not None:
            try:
                values.append(
                    float(value)
                )
            except (
                TypeError,
                ValueError,
            ):
                continue

    if not values:
        raise ScannerError(
            "Underlying spot unavailable in option chain."
        )

    return float(
        np.median(values)
    )


def chain_rows(
    chain: list[dict[str, Any]],
) -> dict[float, dict[str, Any]]:

    result = {}

    for row in chain:

        strike = row.get(
            "strike_price"
        )

        if strike is None:
            continue

        try:
            result[
                float(strike)
            ] = row
        except (
            TypeError,
            ValueError,
        ):
            continue

    if not result:
        raise ScannerError(
            "No valid option strikes in chain."
        )

    return result


def nearest_atm_strike(
    spot: float,
    strikes: list[float],
) -> float:

    return min(
        strikes,
        key=lambda x: abs(
            x - spot
        ),
    )


def strike_interval(
    strikes: list[float],
) -> float:

    unique = sorted(
        set(strikes)
    )

    differences = [
        unique[i + 1] - unique[i]
        for i in range(
            len(unique) - 1
        )
        if unique[i + 1] > unique[i]
    ]

    if not differences:
        raise ScannerError(
            "Unable to determine option strike interval."
        )

    return min(
        differences
    )


def option_market_data(
    row: dict[str, Any],
    option_type: str,
) -> dict[str, Any]:

    key = (
        "call_options"
        if option_type == "CE"
        else "put_options"
    )

    data = row.get(
        key,
        {},
    )

    market = data.get(
        "market_data",
        {},
    )

    greeks = data.get(
        "option_greeks",
        {},
    )

    return {
        "instrument_key": data.get(
            "instrument_key"
        ),
        "ltp": market.get(
            "ltp"
        ),
        "oi": market.get(
            "oi"
        ),
        "prev_oi": market.get(
            "prev_oi"
        ),
        "delta": greeks.get(
            "delta"
        ),
        "gamma": greeks.get(
            "gamma"
        ),
        "iv": greeks.get(
            "iv"
        ),
    }


def oi_structure(
    chain: list[dict[str, Any]],
    spot: float,
) -> tuple[str, float, dict[float, dict[str, float]]]:
    """
    Build a localized option-positioning bias around ATM.

    Bullish pressure:
      - PE OI increasing
      - CE OI decreasing (unwinding)

    Bearish pressure:
      - CE OI increasing
      - PE OI decreasing (unwinding)

    The calculation is proximity-weighted so strikes nearest ATM have
    more influence than distant strikes. This is intentionally different
    from a simple aggregate CE-minus-PE total.
    """
    rows = chain_rows(chain)
    strikes = sorted(rows.keys())

    atm = nearest_atm_strike(spot, strikes)
    step = strike_interval(strikes)

    relevant = [
        strike
        for strike in strikes
        if abs(strike - atm) <= step * 3
    ]

    strike_data: dict[float, dict[str, float]] = {}

    bullish_pressure = 0.0
    bearish_pressure = 0.0

    for strike in relevant:
        row = rows[strike]

        call = option_market_data(row, "CE")
        put = option_market_data(row, "PE")

        call_oi = float(call["oi"] or 0)
        call_prev = float(call["prev_oi"] or 0)
        put_oi = float(put["oi"] or 0)
        put_prev = float(put["prev_oi"] or 0)

        call_change = call_oi - call_prev
        put_change = put_oi - put_prev

        # Near-ATM strikes matter more than distant strikes.
        distance_steps = abs(strike - atm) / step if step > 0 else 0.0
        weight = 1.0 / (1.0 + distance_steps)

        # Bullish = put buildup + call unwinding.
        bullish_pressure += weight * (
            max(put_change, 0.0) + max(-call_change, 0.0)
        )

        # Bearish = call buildup + put unwinding.
        bearish_pressure += weight * (
            max(call_change, 0.0) + max(-put_change, 0.0)
        )

        strike_data[strike] = {
            "call_oi": call_oi,
            "put_oi": put_oi,
            "call_change": call_change,
            "put_change": put_change,
            "weight": weight,
        }

    denominator = bullish_pressure + bearish_pressure

    if denominator <= 0:
        score = 0.0
    else:
        score = (bullish_pressure - bearish_pressure) / denominator

    # Keep the threshold modest because this is a localized pressure
    # measurement, while Futures and VWAP provide the primary directional filter.
    if score >= 0.08:
        bias = "BULLISH"
    elif score <= -0.08:
        bias = "BEARISH"
    else:
        bias = "NEUTRAL"

    logger.info(
        "Localized OI: ATM=%.0f bullish_pressure=%.0f bearish_pressure=%.0f score=%.3f bias=%s",
        atm,
        bullish_pressure,
        bearish_pressure,
        score,
        bias,
    )

    return bias, float(score), strike_data


# =============================================================================
# OI CHANGE FROM LIVE OPTION CHAIN
# =============================================================================

def get_change_oi_from_chain(
    chain: list[dict[str, Any]],
) -> dict[str, Any]:
    """
    Calculate current-session Change-in-OI directly from the live option-chain
    market_data. Upstox exposes both `oi` and `prev_oi` on each option, so this
    avoids relying on a separate aggregate endpoint during every scan.
    """
    total_call_change = 0.0
    total_put_change = 0.0
    strike_changes: list[dict[str, float]] = []
    valid_rows = 0

    for row in chain:
        if not isinstance(row, dict):
            continue

        try:
            strike_value = float(row.get("strike_price"))
        except (TypeError, ValueError):
            continue

        call = option_market_data(row, "CE")
        put = option_market_data(row, "PE")

        try:
            call_oi = float(call.get("oi") or 0.0)
            call_prev_oi = float(call.get("prev_oi") or 0.0)
            put_oi = float(put.get("oi") or 0.0)
            put_prev_oi = float(put.get("prev_oi") or 0.0)
        except (TypeError, ValueError):
            continue

        call_change = call_oi - call_prev_oi
        put_change = put_oi - put_prev_oi
        total_call_change += call_change
        total_put_change += put_change
        strike_changes.append({
            "strike_price": strike_value,
            "call_change_oi": call_change,
            "put_change_oi": put_change,
        })
        valid_rows += 1

    if valid_rows == 0:
        raise ScannerError(
            "No valid current/previous OI values were found in the option chain."
        )

    logger.info(
        "Chain Change-OI: rows=%d total_call_change=%+.0f total_put_change=%+.0f",
        valid_rows,
        total_call_change,
        total_put_change,
    )

    return {
        "total_call_change_oi": total_call_change,
        "total_put_change_oi": total_put_change,
        "call_put_oi_data_list": strike_changes,
    }



def change_oi_bias(
    data: dict[str, Any],
) -> tuple[str, float]:

    if not data:
        return (
            "UNAVAILABLE",
            0.0,
        )

    call_change = float(
        data.get(
            "total_call_change_oi",
            0,
        )
    )

    put_change = float(
        data.get(
            "total_put_change_oi",
            0,
        )
    )

    denominator = (
        abs(call_change)
        + abs(put_change)
    )

    if denominator == 0:
        return (
            "NEUTRAL",
            0.0,
        )

    score = (
        put_change
        - call_change
    ) / denominator

    if score >= 0.15:
        return (
            "BULLISH",
            float(score),
        )

    if score <= -0.15:
        return (
            "BEARISH",
            float(score),
        )

    return (
        "NEUTRAL",
        float(score),
    )


# =============================================================================
# FUTURES ANALYSIS
# =============================================================================

def futures_regime(
    future: FuturesContract,
    candles: Optional[pd.DataFrame] = None,
) -> str:
    """Classify Futures positioning with a small noise filter.

    The latest move and the aggregate move across the supplied recent candles
    must agree. A mixed/tiny move is NEUTRAL instead of being forced into a
    regime, which reduces one-candle OI whipsaws.
    """
    if candles is None:
        candles = get_intraday_candles(
            future.instrument_key,
            3,
            max_candles=3,
            min_candles=3,
        )

    if len(candles) < 3:
        return "UNAVAILABLE"

    recent = candles.tail(3).copy()
    closes = pd.to_numeric(recent["close"], errors="coerce")
    ois = pd.to_numeric(recent["oi"], errors="coerce")
    if closes.isna().any() or ois.isna().any():
        return "UNAVAILABLE"

    latest_price_delta = float(closes.iloc[-1] - closes.iloc[-2])
    latest_oi_delta = float(ois.iloc[-1] - ois.iloc[-2])
    aggregate_price_delta = float(closes.iloc[-1] - closes.iloc[0])
    aggregate_oi_delta = float(ois.iloc[-1] - ois.iloc[0])

    if (
        abs(latest_price_delta) < FUTURES_REGIME_MIN_PRICE_MOVE
        or abs(aggregate_price_delta) < FUTURES_REGIME_MIN_PRICE_MOVE
        or abs(latest_oi_delta) < FUTURES_REGIME_MIN_OI_CHANGE
        or abs(aggregate_oi_delta) < FUTURES_REGIME_MIN_OI_CHANGE
    ):
        return "NEUTRAL"

    price_sign = (
        latest_price_delta > 0 and aggregate_price_delta > 0
    ) or (
        latest_price_delta < 0 and aggregate_price_delta < 0
    )
    oi_sign = (
        latest_oi_delta > 0 and aggregate_oi_delta > 0
    ) or (
        latest_oi_delta < 0 and aggregate_oi_delta < 0
    )

    if not (price_sign and oi_sign):
        logger.info(
            "Futures regime noise/mixed: latest_price=%.2f aggregate_price=%.2f latest_oi=%.0f aggregate_oi=%.0f",
            latest_price_delta,
            aggregate_price_delta,
            latest_oi_delta,
            aggregate_oi_delta,
        )
        return "NEUTRAL"

    if latest_price_delta > 0 and latest_oi_delta > 0:
        return "LONG_BUILDUP"
    if latest_price_delta < 0 and latest_oi_delta > 0:
        return "SHORT_BUILDUP"
    if latest_price_delta > 0 and latest_oi_delta < 0:
        return "SHORT_COVERING"
    if latest_price_delta < 0 and latest_oi_delta < 0:
        return "LONG_UNWINDING"

    return "NEUTRAL"


# =============================================================================
# OPTION CONTRACT SELECTION
# =============================================================================

def option_buying_momentum(
    option: OptionCandidate,
) -> tuple[bool, dict[str, Any]]:
    """Strict premium-expansion gate for BUY-only entries.

    A directionally correct market is NOT enough to buy an option.  The option
    itself must already be expanding in price, have a positive EMA slope, avoid
    a recent peak-to-current drawdown, and show a buy-side OI regime.
    """
    try:
        candles = get_intraday_candles(
            option.instrument_key,
            3,
            max_candles=BUY_OPTION_LOOKBACK,
            min_candles=BUY_OPTION_MIN_CANDLES,
        )
    except ScannerError as exc:
        return False, {
            "reason": f"option candles unavailable: {exc}",
            "regime": "UNAVAILABLE",
        }

    closes = pd.to_numeric(candles["close"], errors="coerce").dropna()
    if len(closes) < BUY_OPTION_MIN_CANDLES:
        return False, {
            "reason": f"only {len(closes)} usable option candles",
            "regime": "UNAVAILABLE",
        }

    latest = float(closes.iloc[-1])
    previous = float(closes.iloc[-2])
    lookback_close = float(closes.iloc[-BUY_OPTION_MIN_CANDLES])
    recent_peak = float(closes.tail(min(5, len(closes))).max())

    ema5_series = closes.ewm(span=5, adjust=False).mean()
    ema5 = float(ema5_series.iloc[-1])
    ema5_prev = float(ema5_series.iloc[-2])

    oi_latest = candles["oi"].iloc[-1]
    oi_previous = candles["oi"].iloc[-2]
    price_delta = latest - previous
    oi_delta = (
        float(oi_latest) - float(oi_previous)
        if pd.notna(oi_latest) and pd.notna(oi_previous)
        else 0.0
    )

    if price_delta > 0 and oi_delta > 0:
        regime = "LONG_BUILDUP"
    elif price_delta > 0 and oi_delta < 0:
        regime = "SHORT_COVERING"
    elif price_delta < 0 and oi_delta > 0:
        regime = "SHORT_BUILDUP"
    elif price_delta < 0 and oi_delta < 0:
        regime = "LONG_UNWINDING"
    else:
        regime = "NEUTRAL"

    multi_return_pct = (
        (latest - lookback_close) / lookback_close * 100.0
        if lookback_close > 0
        else 0.0
    )
    ltp_vs_last_pct = (
        (option.ltp - latest) / latest * 100.0
        if latest > 0
        else -100.0
    )
    peak_pullback_pct = (
        (recent_peak - option.ltp) / recent_peak * 100.0
        if recent_peak > 0
        else 100.0
    )

    recent_closes = closes.tail(3).tolist()
    no_recent_rollover = (
        len(recent_closes) < 3
        or recent_closes[-1] >= recent_closes[-2] >= recent_closes[-3]
    )

    premium_rising = price_delta > 0 and option.ltp >= latest
    trend_positive = latest > lookback_close
    ema_positive = latest >= ema5 and ema5 > ema5_prev
    regime_positive = regime in {"LONG_BUILDUP", "SHORT_COVERING"}
    live_price_ok = ltp_vs_last_pct >= 0.0
    pullback_ok = peak_pullback_pct <= OPTION_ENTRY_MAX_PEAK_PULLBACK_PCT
    recent_structure_ok = no_recent_rollover

    valid = (
        premium_rising
        and trend_positive
        and ema_positive
        and regime_positive
        and multi_return_pct >= OPTION_ENTRY_MIN_3M_RETURN_PCT
        and live_price_ok
        and pullback_ok
        and recent_structure_ok
    )

    failed = []
    if not premium_rising:
        failed.append("latest premium is not rising")
    if not trend_positive:
        failed.append("short lookback trend is not positive")
    if not ema_positive:
        failed.append("EMA5 slope is not positive")
    if not regime_positive:
        failed.append(f"option regime={regime} is not buy-side")
    if multi_return_pct < OPTION_ENTRY_MIN_3M_RETURN_PCT:
        failed.append(f"3m momentum={multi_return_pct:.2f}% below minimum")
    if not live_price_ok:
        failed.append(f"LTP vs last close={ltp_vs_last_pct:+.2f}%")
    if not pullback_ok:
        failed.append(f"peak pullback={peak_pullback_pct:.2f}% too large")
    if not recent_structure_ok:
        failed.append("recent premium candles show rollover/decay")

    reason = (
        "premium-expansion gate passed"
        if valid
        else "; ".join(failed)
    )

    metrics = {
        "reason": reason,
        "regime": regime,
        "latest_close": latest,
        "previous_close": previous,
        "ema5": ema5,
        "ema5_prev": ema5_prev,
        "multi_return_pct": multi_return_pct,
        "ltp_vs_last_pct": ltp_vs_last_pct,
        "peak_pullback_pct": peak_pullback_pct,
        "premium_score": (
            max(multi_return_pct, 0.0)
            + max(ltp_vs_last_pct, 0.0)
            + max((ema5 - ema5_prev) / ema5 * 100.0 if ema5 > 0 else 0.0, 0.0)
        ),
    }

    logger.info(
        "BUY PREMIUM GATE: %s regime=%s LTP=%.2f last3m=%.2f 3m_return=%+.2f%% "
        "EMA5=%.2f slope=%+.4f%% peak_pullback=%.2f%% no_rollover=%s valid=%s",
        option.trading_symbol,
        regime,
        option.ltp,
        latest,
        multi_return_pct,
        ema5,
        ((ema5 - ema5_prev) / ema5_prev * 100.0) if ema5_prev > 0 else 0.0,
        peak_pullback_pct,
        no_recent_rollover,
        valid,
    )
    return valid, metrics

def select_directional_option(
    contracts: list[dict[str, Any]],
    chain: list[dict[str, Any]],
    direction: str,
    spot: float,
    preferred_strike: Optional[float] = None,
) -> OptionCandidate:
    """Select the required directional ITM strike from the CURRENT ATM.

    Bullish -> ATM-1 CE, fallback ATM-2 CE.
    Bearish -> ATM+1 PE, fallback ATM+2 PE.

    Market direction is decided upstream. This function only validates that
    the requested strike exists and has usable option market data.
    """
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("Cannot select an option for NEUTRAL direction.")

    rows = chain_rows(chain)
    chain_strikes = sorted(rows.keys())
    if not chain_strikes:
        raise ScannerError("Option chain contains no strikes.")

    atm = nearest_atm_strike(spot, chain_strikes)
    step = strike_interval(chain_strikes)

    if direction == "BULLISH":
        candidates = [atm - step, atm - 2 * step]
        option_type = "CE"
    else:
        candidates = [atm + step, atm + 2 * step]
        option_type = "PE"

    if preferred_strike is not None:
        candidates = [float(preferred_strike)]

    rejection_reasons: list[str] = []

    for target_strike in candidates:
        row = rows.get(float(target_strike))
        if row is None:
            rejection_reasons.append(
                f"Strike {target_strike:.0f} not present in option chain"
            )
            continue

        matches = []
        for contract in contracts:
            try:
                strike = float(contract.get("strike_price", -1))
            except (TypeError, ValueError):
                continue
            if (
                str(contract.get("instrument_type", "")).upper() == option_type
                and abs(strike - float(target_strike)) < 0.01
                and contract.get("instrument_key")
                and contract.get("trading_symbol")
            ):
                matches.append(contract)

        if not matches:
            rejection_reasons.append(
                f"No {option_type} contract found at {target_strike:.0f}"
            )
            continue

        market = option_market_data(row, option_type)
        try:
            ltp = float(market.get("ltp") or 0.0)
            oi = float(market.get("oi") or 0.0)
            prev_oi = float(market.get("prev_oi") or 0.0)
            delta = float(market.get("delta"))
            gamma = float(market.get("gamma") or 0.0)
            iv = float(market.get("iv") or 0.0)
        except (TypeError, ValueError):
            rejection_reasons.append(
                f"Invalid market data at {target_strike:.0f}"
            )
            continue

        if not math.isfinite(ltp) or ltp <= 0:
            rejection_reasons.append(f"Invalid LTP at {target_strike:.0f}")
            continue
        if not math.isfinite(oi) or oi < 0:
            rejection_reasons.append(f"Invalid OI at {target_strike:.0f}")
            continue
        if not math.isfinite(delta) or not (OPTION_MIN_DELTA <= abs(delta) <= OPTION_MAX_DELTA):
            rejection_reasons.append(
                f"Delta {delta!r} outside {OPTION_MIN_DELTA:.2f}-{OPTION_MAX_DELTA:.2f} at {target_strike:.0f}"
            )
            continue
        if not math.isfinite(gamma):
            gamma = 0.0
        if not math.isfinite(iv):
            iv = 0.0

        selected = OptionCandidate(
            instrument_key=str(matches[0]["instrument_key"]),
            trading_symbol=str(matches[0]["trading_symbol"]),
            option_type=option_type,
            strike=float(target_strike),
            expiry=str(matches[0].get("expiry", "")),
            ltp=ltp,
            oi=oi,
            prev_oi=prev_oi,
            delta=delta,
            gamma=gamma,
            iv=iv,
        )

        logger.info(
            "SELECTED DIRECTIONAL OPTION: direction=%s ATM=%.0f -> %s %.0f %s LTP=%.2f OI=%.0f Delta=%.3f",
            direction, atm, selected.trading_symbol, selected.strike,
            selected.option_type, selected.ltp, selected.oi, selected.delta,
        )
        return selected

    details = "; ".join(rejection_reasons[-6:]) or "no valid directional strike"
    raise ScannerError(
        f"No valid {option_type} strike available for direction={direction}: {details}"
    )


# =============================================================================
# OPTION EXTENSION FILTER
# =============================================================================

def option_is_extended(
    option: OptionCandidate,
) -> bool:
    # Disabled deliberately: the scanner must not reject an otherwise
    # valid predictive setup because the option has already started moving.
    return False


def option_price_oi_regime(option: OptionCandidate) -> str:
    """Return the selected option's latest 3-minute price/OI regime.

    This is a confirmation field only. It never becomes the primary
    prediction trigger because the goal is to identify the move before
    the option premium is already extended.
    """
    try:
        candles = get_intraday_candles(option.instrument_key, 3, max_candles=3, min_candles=2)

        if len(candles) < 3:
            return "UNAVAILABLE"

        latest = candles.iloc[-1]
        previous = candles.iloc[-2]

        if pd.isna(latest["oi"]) or pd.isna(previous["oi"]):
            return "UNAVAILABLE"

        price_delta = float(latest["close"] - previous["close"])
        oi_delta = float(latest["oi"] - previous["oi"])

        if price_delta > 0 and oi_delta > 0:
            return "LONG_BUILDUP"

        if price_delta > 0 and oi_delta < 0:
            return "SHORT_COVERING"

        if price_delta < 0 and oi_delta > 0:
            return "SHORT_BUILDUP"

        if price_delta < 0 and oi_delta < 0:
            return "LONG_UNWINDING"

        return "NEUTRAL"

    except ScannerError as exc:
        logger.info(
            "Option price/OI confirmation unavailable for %s: %s",
            option.trading_symbol,
            exc,
        )
        return "UNAVAILABLE"


def final_entry_direction_confirmation(
    direction: str,
    interpretation: str,
    spot_3m: pd.DataFrame,
    futures_vwap_candles: pd.DataFrame,
) -> tuple[bool, list[str]]:
    """Confirm direction without requiring a completed breakout candle.

    This is deliberately a lightweight safety check. Market direction has
    already been established by the weighted structure engine. A bullish setup
    needs price above VWAP; a bearish setup needs price below VWAP. Near-VWAP
    transitions are allowed when the 3m price is moving in the signal direction.
    """
    if spot_3m is None or len(spot_3m) < 2:
        return False, ["SENSEX 3-minute candles unavailable."]
    if futures_vwap_candles is None or futures_vwap_candles.empty:
        return False, ["SENSEX Futures VWAP candles unavailable."]

    vwap_series = calculate_vwap(futures_vwap_candles).dropna()
    if vwap_series.empty:
        return False, ["SENSEX Futures session VWAP unavailable."]

    price = float(spot_3m["close"].iloc[-1])
    prev_price = float(spot_3m["close"].iloc[-2])
    vwap = float(vwap_series.iloc[-1])
    distance_pct = abs(price - vwap) / vwap * 100.0 if vwap else 0.0

    bullish = direction == "BULLISH"
    bearish = direction == "BEARISH"
    above = price >= vwap
    below = price <= vwap

    # Permit a very recent reclaim/break transition, but never permit a
    # directional signal that is clearly on the wrong side of VWAP.
    if bullish:
        ok = above or (price > prev_price and distance_pct <= 0.20)
    elif bearish:
        ok = below or (price < prev_price and distance_pct <= 0.20)
    else:
        ok = False

    reasons = [
        f"Market interpretation={interpretation}.",
        f"SENSEX price={price:.2f}; Futures VWAP={vwap:.2f}; distance={distance_pct:.3f}%.",
        f"Price position={'ABOVE' if price > vwap else 'BELOW' if price < vwap else 'AT VWAP'}.",
        f"Pre-breakout VWAP confirmation={'PASS' if ok else 'FAIL'}.",
    ]

    logger.info(
        "FINAL PRE-BREAKOUT CONFIRMATION: direction=%s interpretation=%s price=%.2f VWAP=%.2f "
        "distance=%.3f%% prev_price=%.2f OK=%s",
        direction, interpretation, price, vwap, distance_pct, prev_price, ok,
    )
    return ok, reasons


def futures_premium_discount_state(
    futures_candles: pd.DataFrame,
    spot_3m: pd.DataFrame,
    live_spot: float,
    epsilon_points: float = FUTURES_BASIS_EPSILON_POINTS,
) -> tuple[str, float, float]:
    """Classify Futures premium/discount behavior for the sentiment matrix.

    Matrix mapping:
      LONG_BUILDUP   -> widening premium is supportive.
      SHORT_BUILDUP  -> deepening discount is supportive.
      SHORT_COVERING -> shrinking premium / narrowing discount is supportive.
      LONG_UNWINDING -> shrinking premium / narrowing discount is supportive.
    """
    if futures_candles is None or spot_3m is None or futures_candles.empty or spot_3m.empty:
        return "UNAVAILABLE", float("nan"), float("nan")
    if len(futures_candles) < 2 or len(spot_3m) < 2:
        return "UNAVAILABLE", float("nan"), float("nan")

    try:
        fut_latest = float(futures_candles["close"].iloc[-1])
        fut_previous = float(futures_candles["close"].iloc[-2])
        spot_previous = float(spot_3m["close"].iloc[-2])
        current_basis = fut_latest - float(live_spot)
        previous_basis = fut_previous - spot_previous
        basis_change = current_basis - previous_basis
    except (TypeError, ValueError, KeyError, IndexError):
        return "UNAVAILABLE", float("nan"), float("nan")

    if not all(math.isfinite(v) for v in (current_basis, previous_basis, basis_change)):
        return "UNAVAILABLE", float("nan"), float("nan")

    if current_basis >= 0:
        if basis_change > epsilon_points:
            state = "WIDENING_PREMIUM"
        elif basis_change < -epsilon_points:
            state = "SHRINKING_PREMIUM"
        else:
            state = "FLAT_PREMIUM"
    else:
        if basis_change < -epsilon_points:
            state = "DEEPENING_DISCOUNT"
        elif basis_change > epsilon_points:
            state = "NARROWING_DISCOUNT"
        else:
            state = "FLAT_DISCOUNT"

    logger.info(
        "Futures premium/discount: current_basis=%.2f previous_basis=%.2f change=%.2f state=%s",
        current_basis,
        previous_basis,
        basis_change,
        state,
    )
    return state, current_basis, basis_change


# =============================================================================
# PRE-BREAKOUT ENGINE
# =============================================================================

def option_oi_difference(
    chain: list[dict[str, Any]],
    spot: float,
) -> tuple[float, float, float, str, str, float, float]:
    """Calculate the chart's PE-CE OI difference around the live ATM strike.

    Returns:
        raw_diff: weighted PE OI - CE OI
        raw_change: weighted change in (PE OI - CE OI) from previous OI
        normalized_diff: raw_diff / weighted total OI
        direction: BULLISH/BEARISH/NEUTRAL
        trend: INCREASING/DECREASING/FLAT
        ce_change: weighted CE change-OI
        ce_change_normalized: weighted CE change-OI / weighted CE OI
    """
    rows = chain_rows(chain)
    strikes = sorted(rows.keys())
    atm = nearest_atm_strike(float(spot), strikes)
    step = strike_interval(strikes)
    relevant = [strike for strike in strikes if abs(strike - atm) <= step * 3]
    if not relevant:
        raise ScannerError("No option strikes available around ATM.")

    diff = 0.0
    diff_change = 0.0
    weighted_total = 0.0
    weighted_ce_oi = 0.0
    ce_change = 0.0

    for strike in relevant:
        row = rows[strike]
        call = option_market_data(row, "CE")
        put = option_market_data(row, "PE")

        call_oi = float(call.get("oi") or 0.0)
        call_prev = float(call.get("prev_oi") or 0.0)
        put_oi = float(put.get("oi") or 0.0)
        put_prev = float(put.get("prev_oi") or 0.0)

        distance_steps = abs(strike - atm) / step if step > 0 else 0.0
        weight = 1.0 / (1.0 + distance_steps)

        diff += weight * (put_oi - call_oi)
        diff_change += weight * ((put_oi - put_prev) - (call_oi - call_prev))
        weighted_total += weight * (put_oi + call_oi)
        weighted_ce_oi += weight * call_oi
        ce_change += weight * (call_oi - call_prev)

    normalized_diff = diff / weighted_total if weighted_total > 0 else 0.0
    normalized_change = diff_change / weighted_total if weighted_total > 0 else 0.0
    ce_change_normalized = ce_change / weighted_ce_oi if weighted_ce_oi > 0 else 0.0

    if normalized_diff >= OI_DIFF_POSITIVE_THRESHOLD:
        oi_direction = "BULLISH"
    elif normalized_diff <= -OI_DIFF_POSITIVE_THRESHOLD:
        oi_direction = "BEARISH"
    else:
        oi_direction = "NEUTRAL"

    if normalized_change >= OI_DIFF_CHANGE_THRESHOLD:
        oi_trend = "INCREASING"
    elif normalized_change <= -OI_DIFF_CHANGE_THRESHOLD:
        oi_trend = "DECREASING"
    else:
        oi_trend = "FLAT"

    logger.info(
        "Chart OI Difference: ATM=%.0f PE-CE=%+.0f normalized=%.3f "
        "change=%+.0f change_normalized=%.3f direction=%s trend=%s CE_change=%+.0f CE_change_norm=%.3f",
        atm, diff, normalized_diff, diff_change, normalized_change,
        oi_direction, oi_trend, ce_change, ce_change_normalized,
    )
    return (
        float(diff), float(diff_change), float(normalized_diff),
        oi_direction, oi_trend, float(ce_change), float(ce_change_normalized),
    )


def _sign(value: float, threshold: float = 0.0) -> int:
    if not math.isfinite(float(value)):
        return 0
    if value > threshold:
        return 1
    if value < -threshold:
        return -1
    return 0


def _trend_direction(df: pd.DataFrame, lookback: int = 5) -> int:
    """Return direction from recent closes using both net and majority movement."""
    if df is None or len(df) < 2:
        return 0
    closes = pd.to_numeric(df["close"], errors="coerce").dropna().tail(max(2, lookback))
    if len(closes) < 2:
        return 0
    net = float(closes.iloc[-1] - closes.iloc[0])
    diffs = np.diff(closes.to_numpy(dtype=float))
    pos = int(np.sum(diffs > 0))
    neg = int(np.sum(diffs < 0))
    if net > 0 and pos >= neg:
        return 1
    if net < 0 and neg >= pos:
        return -1
    return _sign(net)


def _supertrend_direction(df: pd.DataFrame) -> int:
    if df is None or df.empty or "direction" not in df:
        return 0
    try:
        value = float(pd.to_numeric(df["direction"], errors="coerce").dropna().iloc[-1])
        return 1 if value > 0 else -1 if value < 0 else 0
    except (IndexError, TypeError, ValueError):
        return 0


def _market_structure_snapshot(
    spot_3m: pd.DataFrame,
    spot_15m: pd.DataFrame,
    futures_3m: pd.DataFrame,
    futures_vwap_candles: pd.DataFrame,
    live_spot: float,
    option_oi_diff: float,
    option_oi_diff_change: float,
) -> dict[str, Any]:
    """Build one coherent market view. No single input can manufacture direction."""
    vwap_series = calculate_vwap(futures_vwap_candles).dropna()
    if vwap_series.empty:
        raise ScannerError("Futures VWAP unavailable for market structure.")
    vwap = float(vwap_series.iloc[-1])
    price_vs_vwap = _sign(float(live_spot) - vwap, max(abs(vwap) * 0.00015, 1.0))

    st3 = _supertrend_direction(spot_3m)
    st15 = _supertrend_direction(spot_15m)
    structure3 = structure_state(spot_3m, min(STRUCTURE_LOOKBACK_3M, len(spot_3m))) if len(spot_3m) >= 3 else "NEUTRAL"
    structure15 = structure_state(spot_15m, min(STRUCTURE_LOOKBACK_15M, len(spot_15m))) if len(spot_15m) >= 3 else "NEUTRAL"
    price3 = _trend_direction(spot_3m, 6)
    price15 = _trend_direction(spot_15m, 4)

    fut_close = pd.to_numeric(futures_3m["close"], errors="coerce").dropna()
    fut_oi = pd.to_numeric(futures_3m["oi"], errors="coerce").dropna()
    fut_price_dir = _trend_direction(futures_3m, 6)
    fut_oi_dir = _trend_direction(futures_3m.assign(close=futures_3m["oi"]), 6)
    latest_fut_price_change = float(fut_close.iloc[-1] - fut_close.iloc[-2]) if len(fut_close) >= 2 else 0.0
    latest_fut_oi_change = float(fut_oi.iloc[-1] - fut_oi.iloc[-2]) if len(fut_oi) >= 2 else 0.0

    # Futures price/OI interpretation. This is intentionally separate from
    # the old 3-candle hard gate: stale/flat OI on the last candle must not erase
    # a clearly directional multi-candle move.
    if fut_price_dir < 0 and fut_oi_dir > 0:
        futures_bias, futures_regime = -1, "SHORT_BUILDUP"
    elif fut_price_dir > 0 and fut_oi_dir > 0:
        futures_bias, futures_regime = 1, "LONG_BUILDUP"
    elif fut_price_dir < 0 and fut_oi_dir < 0:
        futures_bias, futures_regime = -1, "LONG_UNWINDING"
    elif fut_price_dir > 0 and fut_oi_dir < 0:
        futures_bias, futures_regime = 1, "SHORT_COVERING"
    else:
        futures_bias, futures_regime = fut_price_dir, "PRICE_ONLY_BIAS" if fut_price_dir else "NEUTRAL"

    oi_dir = _sign(option_oi_diff, max(abs(option_oi_diff) * 0.05, 1.0))
    oi_change_dir = _sign(option_oi_diff_change, max(abs(option_oi_diff) * 0.05, 1.0))

    # PE-CE OI difference: positive supports bulls, negative supports bears.
    score = 0.0
    reasons: list[str] = []

    if price_vs_vwap > 0:
        score += 2.0; reasons.append("SENSEX is above Futures VWAP.")
    elif price_vs_vwap < 0:
        score -= 2.0; reasons.append("SENSEX is below Futures VWAP.")

    if st3 > 0:
        score += 1.5; reasons.append("3m Supertrend is bullish.")
    elif st3 < 0:
        score -= 1.5; reasons.append("3m Supertrend is bearish.")

    if st15 > 0:
        score += 2.0; reasons.append("15m Supertrend is bullish.")
    elif st15 < 0:
        score -= 2.0; reasons.append("15m Supertrend is bearish.")

    if structure3 == "BULLISH": score += 1.0
    elif structure3 == "BEARISH": score -= 1.0
    if structure15 == "BULLISH": score += 1.5
    elif structure15 == "BEARISH": score -= 1.5

    if futures_bias > 0:
        score += 2.0; reasons.append(f"Futures structure is bullish ({futures_regime}).")
    elif futures_bias < 0:
        score -= 2.0; reasons.append(f"Futures structure is bearish ({futures_regime}).")

    if oi_dir > 0:
        score += 1.5; reasons.append("PE-CE OI difference is bullish.")
    elif oi_dir < 0:
        score -= 1.5; reasons.append("PE-CE OI difference is bearish.")

    if oi_change_dir > 0:
        score += 1.5; reasons.append("PE-CE OI difference is improving toward bulls.")
    elif oi_change_dir < 0:
        score -= 1.5; reasons.append("PE-CE OI difference is deteriorating toward bears.")

    # Require alignment across independent groups, not merely a high raw score.
    bullish_groups = sum(x > 0 for x in (price_vs_vwap, st3, st15, price3, price15, futures_bias, oi_dir, oi_change_dir))
    bearish_groups = sum(x < 0 for x in (price_vs_vwap, st3, st15, price3, price15, futures_bias, oi_dir, oi_change_dir))

    if score >= MARKET_SCORE_ENTRY and bullish_groups >= PREDICTION_MIN_CONFLUENCE:
        direction = "BULLISH"
    elif score <= -MARKET_SCORE_ENTRY and bearish_groups >= PREDICTION_MIN_CONFLUENCE:
        direction = "BEARISH"
    else:
        direction = "NEUTRAL"

    confidence = min(99.0, max(0.0, 50.0 + abs(score) * 5.5)) if direction != "NEUTRAL" else min(49.0, abs(score) * 5.0)
    interpretation = (
        "STRONG BULLISH MARKET STRUCTURE" if direction == "BULLISH" and score >= MARKET_SCORE_STRONG
        else "BULLISH MARKET STRUCTURE" if direction == "BULLISH"
        else "STRONG BEARISH MARKET STRUCTURE" if direction == "BEARISH" and score <= -MARKET_SCORE_STRONG
        else "BEARISH MARKET STRUCTURE" if direction == "BEARISH"
        else "WAIT / MIXED MARKET STRUCTURE"
    )

    logger.info(
        "MARKET STRUCTURE: score=%+.1f direction=%s confidence=%.1f | VWAP=%s 3mST=%s 15mST=%s "
        "3mStructure=%s 15mStructure=%s Futures=%s FutPriceDir=%+d FutOIDir=%+d PE-CE=%+.0f PE-CEchg=%+.0f",
        score, direction, confidence,
        "ABOVE" if price_vs_vwap > 0 else "BELOW" if price_vs_vwap < 0 else "AT",
        "BULL" if st3 > 0 else "BEAR" if st3 < 0 else "NA",
        "BULL" if st15 > 0 else "BEAR" if st15 < 0 else "NA",
        structure3, structure15, futures_regime, fut_price_dir, fut_oi_dir,
        option_oi_diff, option_oi_diff_change,
    )

    return {
        "score": score, "direction": direction, "confidence": confidence,
        "interpretation": interpretation, "reasons": reasons,
        "vwap": vwap, "price_vs_vwap": price_vs_vwap,
        "st3": st3, "st15": st15, "structure3": structure3, "structure15": structure15,
        "futures_bias": futures_bias, "futures_regime": futures_regime,
        "fut_price_dir": fut_price_dir, "fut_oi_dir": fut_oi_dir,
        "latest_fut_price_change": latest_fut_price_change,
        "latest_fut_oi_change": latest_fut_oi_change,
        "oi_dir": oi_dir, "oi_change_dir": oi_change_dir,
    }


def predictive_direction(
    spot_3m: pd.DataFrame,
    spot_15m: pd.DataFrame,
    chain_bias: str,
    chain_bias_score: float,
    change_oi_bias_value: str,
    change_oi_score: float,
    futures_state: str,
    live_spot: float,
    futures_3m: Optional[pd.DataFrame] = None,
    futures_vwap_candles: Optional[pd.DataFrame] = None,
    previous_snapshot: Optional[dict[str, Any]] = None,
    option_oi_diff: Optional[float] = None,
    option_oi_diff_change: Optional[float] = None,
    option_oi_direction: Optional[str] = None,
    option_oi_trend: Optional[str] = None,
    ce_change_oi: Optional[float] = None,
    ce_change_oi_normalized: Optional[float] = None,
) -> tuple[str, str, float, list[str], float]:
    """Overhauled prediction engine: market structure first, option second.

    The previous literal matrix rejected many valid combinations and returned
    NEUTRAL whenever one column did not match a predefined row. This engine
    requires multi-factor directional agreement instead.
    """
    if futures_3m is None or len(futures_3m) < 3:
        raise ScannerError("Insufficient Futures candles for market structure.")
    if futures_vwap_candles is None or futures_vwap_candles.empty:
        raise ScannerError("Futures VWAP candles unavailable.")
    snap = _market_structure_snapshot(
        spot_3m, spot_15m, futures_3m, futures_vwap_candles, live_spot,
        float(option_oi_diff or 0.0), float(option_oi_diff_change or 0.0),
    )
    reasons = list(snap["reasons"])
    reasons.extend([
        f"Market structure score={snap['score']:+.1f}.",
        f"Price vs VWAP={'ABOVE' if snap['price_vs_vwap'] > 0 else 'BELOW' if snap['price_vs_vwap'] < 0 else 'AT'}.",
        f"Futures regime={snap['futures_regime']} with price direction={snap['fut_price_dir']:+d} and OI direction={snap['fut_oi_dir']:+d}.",
        f"PE-CE OI={float(option_oi_diff or 0.0):+.0f}; change={float(option_oi_diff_change or 0.0):+.0f}.",
        f"Legacy localized OI={chain_bias} ({float(chain_bias_score):+.3f}); chain Change-OI={change_oi_bias_value} ({float(change_oi_score):+.3f}).",
        "Prediction is based on the combined market structure, not a single matrix row.",
    ])
    return snap["direction"], snap["interpretation"], float(snap["confidence"]), reasons, float(snap["score"])

def validate_prebreakout(
    spot_3m: pd.DataFrame,
    spot_15m: pd.DataFrame,
    direction: str,
    option: OptionCandidate,
) -> tuple[bool, float, float, list[str]]:
    """Build target levels without requiring a future breakout to occur first."""

    if spot_3m.empty or spot_15m.empty:
        return False, 0.0, 0.0, ["Underlying candles unavailable."]

    latest_3 = spot_3m.iloc[-1]
    latest_15 = spot_15m.iloc[-1]
    spot = float(latest_3["close"])

    atr_3 = float(latest_3.get("atr", np.nan))
    atr_15 = float(latest_15.get("atr", np.nan))
    if not (math.isfinite(atr_3) and atr_3 > 0):
        atr_3 = max(float(spot_3m["high"].iloc[-1] - spot_3m["low"].iloc[-1]), 1.0)
    if not (math.isfinite(atr_15) and atr_15 > 0):
        atr_15 = max(float(spot_15m["high"].iloc[-1] - spot_15m["low"].iloc[-1]), atr_3)

    # Use available structure; early-session scans do not fail just because
    # there are fewer than the preferred 8/6 candles.
    n3 = max(1, min(STRUCTURE_LOOKBACK_3M, len(spot_3m) - 1))
    n15 = max(1, min(STRUCTURE_LOOKBACK_15M, len(spot_15m) - 1))

    if direction == "BULLISH":
        if n3 >= 1:
            recent_trigger = float(spot_3m["high"].iloc[-n3-1:-1].max()) if len(spot_3m) > 1 else float(latest_3["high"])
        else:
            recent_trigger = float(latest_3["high"])
        trigger_3m = max(
            recent_trigger,
            spot + max(atr_3 * 0.25, 1.0),
        )

        recent_15 = (
            float(spot_15m["high"].iloc[-n15-1:-1].max())
            if len(spot_15m) > 1
            else float(latest_15["high"])
        )
        supertrend_15 = float(latest_15.get("supertrend", np.nan))
        st_level = supertrend_15 if math.isfinite(supertrend_15) else recent_15
        target_15m = max(
            recent_15,
            st_level,
            trigger_3m + max(atr_15 * 0.50, atr_3 * 0.50),
        )
    else:
        recent_trigger = (
            float(spot_3m["low"].iloc[-n3-1:-1].min())
            if len(spot_3m) > 1
            else float(latest_3["low"])
        )
        trigger_3m = min(
            recent_trigger,
            spot - max(atr_3 * 0.25, 1.0),
        )

        recent_15 = (
            float(spot_15m["low"].iloc[-n15-1:-1].min())
            if len(spot_15m) > 1
            else float(latest_15["low"])
        )
        supertrend_15 = float(latest_15.get("supertrend", np.nan))
        st_level = supertrend_15 if math.isfinite(supertrend_15) else recent_15
        target_15m = min(
            recent_15,
            st_level,
            trigger_3m - max(atr_15 * 0.50, atr_3 * 0.50),
        )

    return (
        True,
        float(trigger_3m),
        float(target_15m),
        [
            "Pre-breakout entry: market interpretation occurs before the 3m breakout.",
            f"3m projected trigger={trigger_3m:.2f}.",
            f"15m projected target/resistance={target_15m:.2f}.",
            f"Selected ITM option={option.strike:.0f} {option.option_type}.",
        ],
    )


# =============================================================================
# PREMIUM TARGET ENGINE
# =============================================================================

def premium_target_from_underlying_move(
    entry: float,
    current_underlying: float,
    target_underlying: float,
    delta: float,
    gamma: float,
    direction: str,
) -> float:

    if direction == "BULLISH":
        move = (
            target_underlying
            - current_underlying
        )
    else:
        move = (
            current_underlying
            - target_underlying
        )

    if move <= 0:
        raise ScannerError(
            "Underlying target is not beyond current price."
        )

    absolute_delta = abs(delta)

    first_order = (
        absolute_delta
        * move
    )

    second_order = (
        0.5
        * abs(gamma)
        * move
        * move
    )

    premium_change = (
        first_order
        + second_order
    )

    # Prevent a pathological Greek-derived projection
    # from creating a mathematically extreme alert.
    premium_change = min(
        premium_change,
        entry * 2.0,
    )

    return round(
        entry + premium_change,
        2,
    )


def create_targets(
    option: OptionCandidate,
    spot: float,
    trigger_3m: float,
    target_15m: float,
    direction: str,
) -> tuple[float, float, float]:

    entry = option.ltp

    target_1 = premium_target_from_underlying_move(
        entry=entry,
        current_underlying=spot,
        target_underlying=trigger_3m,
        delta=option.delta,
        gamma=option.gamma,
        direction=direction,
    )

    target_2 = premium_target_from_underlying_move(
        entry=entry,
        current_underlying=spot,
        target_underlying=target_15m,
        delta=option.delta,
        gamma=option.gamma,
        direction=direction,
    )

    if target_2 <= target_1:
        raise ScannerError(
            "Target 2 must exceed Target 1."
        )

    stop_loss = round(
        entry * ACTIVE_TRADE_SL_FACTOR,
        2,
    )

    return (
        target_1,
        target_2,
        stop_loss,
    )


# =============================================================================
# ACTIVE TRADE / PERSISTENT STATE
# =============================================================================

def active_trade_from_state(state: dict[str, Any]) -> Optional[dict[str, Any]]:
    trade = state.get("active_trade")
    if not isinstance(trade, dict):
        return None
    if str(trade.get("status", "")).upper() != "ACTIVE":
        return None
    required = {
        "instrument_key",
        "trading_symbol",
        "direction",
        "option_type",
        "strike",
        "entry",
        "target_1",
        "target_2",
        "stop_loss",
    }
    if not required.issubset(trade):
        logger.warning("Ignoring incomplete active trade state.")
        return None
    return trade


def market_logic_signature(
    direction: str,
    interpretation: str,
    price_vs_vwap: str,
    futures_state: str,
    oi_direction: str,
    oi_trend: str,
    final_gate: bool,
) -> str:
    """Stable signature for the discrete market logic that owns an active strike."""
    parts = [
        str(direction).upper(),
        str(interpretation).upper(),
        str(price_vs_vwap).upper(),
        str(futures_state).upper(),
        str(oi_direction).upper(),
        str(oi_trend).upper(),
        "GATE_PASS" if final_gate else "GATE_FAIL",
    ]
    return "|".join(parts)


def close_active_trade(
    state: dict[str, Any],
    trade: dict[str, Any],
    outcome: str,
    exit_ltp: Optional[float] = None,
    reason: str = "",
) -> None:
    closed = dict(trade)
    closed["status"] = "CLOSED"
    closed["outcome"] = outcome
    if exit_ltp is not None:
        closed["exit_ltp"] = round(float(exit_ltp), 2)
    closed["closed_at"] = now_ist().isoformat()
    if reason:
        closed["invalidation_reason"] = reason
    state["active_trade"] = None
    state["last_completed_trade"] = closed
    save_state(state)


def monitor_active_trade(
    state: dict[str, Any],
    current_direction: str,
    current_interpretation: str,
    current_confidence: float,
    final_confirmed: bool,
    selected_option: Optional[OptionCandidate],
    current_logic_signature: str,
) -> str:
    """Monitor an active trade without treating normal market noise as an exit.

    Exit hierarchy:
      1. T2 / T1 / hard option SL.
      2. Confirmed opposite market structure on two consecutive scans.
      3. Neutral or temporary disagreement NEVER exits the trade.

    The old implementation exited on any signature change, which caused a
    bearish trade to be invalidated merely because Futures OI moved from
    INCREASING to DECREASING on the next 3-minute scan.
    """
    trade = active_trade_from_state(state)
    if trade is None:
        return "NO_ACTIVE"

    try:
        ltp = extract_ltp(get_quote(str(trade["instrument_key"])))
    except ScannerError as exc:
        logger.info("ACTIVE TRADE MONITOR: quote unavailable: %s", exc)
        return "ACTIVE"

    entry = float(trade["entry"])
    target_1 = float(trade["target_1"])
    target_2 = float(trade["target_2"])
    stop_loss = round(entry * ACTIVE_TRADE_SL_FACTOR, 2)
    trade["stop_loss"] = stop_loss
    trade["last_ltp"] = round(ltp, 2)
    trade["last_monitored_at"] = now_ist().isoformat()

    active_direction = str(trade.get("direction", "")).upper()
    reversal_count = int(trade.get("reversal_confirmations", 0) or 0)

    # Targets/SL are actual option-level exits and remain authoritative.
    outcome = None
    if ltp >= target_2:
        outcome = "TARGET_2"
    elif ltp >= target_1:
        outcome = "TARGET_1"
    elif ltp <= stop_loss:
        outcome = "STOP_LOSS"

    if outcome:
        close_active_trade(state, trade, outcome, exit_ltp=ltp)
        logger.info("ACTIVE TRADE CLOSED: %s | outcome=%s exit_ltp=%.2f", trade["trading_symbol"], outcome, ltp)
        try:
            send_email(
                f"SENSEX TRADE {outcome} - {trade['trading_symbol']}",
                f"SENSEX {trade['direction']} trade closed.<br>Option: {trade['trading_symbol']}<br>Entry: ₹{entry:.2f}<br>Exit: ₹{ltp:.2f}<br>Outcome: {outcome}<br>Exit was triggered by the option target/stop policy.",
            )
        except ScannerError as exc:
            logger.warning("Trade outcome email failed: %s", exc)
        return "CLOSED"

    # Neutral is not an exit. Neither is a temporary VWAP/structure disagreement.
    if current_direction == active_direction:
        reversal_count = 0
    elif current_direction in {"BULLISH", "BEARISH"}:
        reversal_count += 1
    else:
        reversal_count = 0

    trade["reversal_confirmations"] = reversal_count
    trade["last_market_direction"] = current_direction
    trade["last_market_interpretation"] = current_interpretation
    trade["last_market_confidence"] = float(current_confidence)

    logger.info(
        "ACTIVE TRADE STRUCTURE MONITOR: %s | active=%s current=%s confidence=%.1f "
        "reversal_confirmations=%d/%d | LTP=%.2f T1=%.2f T2=%.2f SL=%.2f",
        trade["trading_symbol"], active_direction, current_direction, float(current_confidence),
        reversal_count, REVERSAL_CONFIRMATIONS_REQUIRED, ltp, target_1, target_2, stop_loss,
    )

    # Only a strong opposite direction confirmed on consecutive scans can force
    # a structural exit. A NEUTRAL result is explicitly ignored.
    if (
        current_direction in {"BULLISH", "BEARISH"}
        and current_direction != active_direction
        and float(current_confidence) >= 70.0
        and reversal_count >= REVERSAL_CONFIRMATIONS_REQUIRED
    ):
        reason = (
            f"confirmed opposite market structure: active={active_direction}, "
            f"current={current_direction}, confidence={float(current_confidence):.1f}, "
            f"confirmations={reversal_count}"
        )
        close_active_trade(state, trade, "STRUCTURE_REVERSAL", exit_ltp=ltp, reason=reason)
        try:
            send_email(
                f"SENSEX TRADE STRUCTURE REVERSAL - {trade['trading_symbol']}",
                f"SENSEX {trade['direction']} trade exited on confirmed opposite market structure.<br>Option: {trade['trading_symbol']}<br>Entry: ₹{entry:.2f}<br>Exit: ₹{ltp:.2f}<br>Reason: {reason}",
            )
        except ScannerError as exc:
            logger.warning("Structure reversal email failed: %s", exc)
        return "CLOSED"

    state["active_trade"] = trade
    save_state(state)
    return "ACTIVE"


# =============================================================================
# STATE
# =============================================================================

def load_state() -> dict[str, Any]:
    if not STATE_FILE.exists():
        logger.info("State file not found: %s", STATE_FILE)
        return {}

    try:
        with STATE_FILE.open("r", encoding="utf-8") as file:
            data = json.load(file)

        if isinstance(data, dict):
            snapshot = data.get("market_snapshot")
            logger.info(
                "Loaded state from %s | previous_snapshot=%s | active_trade=%s",
                STATE_FILE,
                "YES" if isinstance(snapshot, dict) else "NO",
                "YES" if active_trade_from_state(data) is not None else "NO",
            )
            return data

        logger.warning("State file contains invalid root data: %s", STATE_FILE)
        return {}

    except Exception as exc:
        logger.warning("State read failed: %s", exc)
        return {}


def save_state(
    state: dict[str, Any],
) -> None:

    STATE_FILE.parent.mkdir(
        parents=True,
        exist_ok=True,
    )

    temp_file = STATE_FILE.with_suffix(
        ".tmp"
    )

    with temp_file.open(
        "w",
        encoding="utf-8",
    ) as file:

        json.dump(
            state,
            file,
            indent=2,
            ensure_ascii=False,
        )

    temp_file.replace(
        STATE_FILE
    )
    logger.info("State saved: %s", STATE_FILE)


def signal_hash(
    signal: Signal,
) -> str:

    key = "|".join(
        [
            signal.direction,
            signal.instrument_key,
            str(
                signal.strike
            ),
            signal.regime,
        ]
    )

    return hashlib.sha256(
        key.encode(
            "utf-8"
        )
    ).hexdigest()


# =============================================================================
# EMAIL
# =============================================================================

def send_email(
    subject: str,
    body: str,
) -> None:

    required = {
        "EMAIL_SENDER": EMAIL_SENDER,
        "EMAIL_PASSWORD": EMAIL_PASSWORD,
        "EMAIL_RECEIVER": EMAIL_RECEIVER,
    }

    missing = [
        name
        for name, value in required.items()
        if not value
    ]

    if missing:
        raise ScannerError(
            "Missing email configuration: "
            + ", ".join(missing)
        )

    message = MIMEMultipart(
        "alternative"
    )

    message["From"] = EMAIL_SENDER
    message["To"] = EMAIL_RECEIVER
    message["Subject"] = subject

    message.attach(
        MIMEText(
            body,
            "html",
            "utf-8",
        )
    )

    with smtplib.SMTP_SSL(
        SMTP_HOST,
        SMTP_PORT,
        timeout=30,
    ) as server:

        server.login(
            EMAIL_SENDER,
            EMAIL_PASSWORD,
        )

        server.sendmail(
            EMAIL_SENDER,
            [EMAIL_RECEIVER],
            message.as_string(),
        )


def email_body(
    signal: Signal,
) -> str:

    reason_html = "".join(
        f"<li>{reason}</li>"
        for reason in signal.reasons
    )

    return f"""
<html>
<body>

<h2>
SENSEX Predictive {signal.direction} Signal
</h2>

<table border="1"
       cellpadding="7"
       cellspacing="0">

<tr>
<td><b>Time</b></td>
<td>{signal.timestamp}</td>
</tr>

<tr>
<td><b>Regime</b></td>
<td>{signal.regime}</td>
</tr>

<tr>
<td><b>Confidence</b></td>
<td>{signal.confidence:.1f}%</td>
</tr>

<tr>
<td><b>SENSEX Spot</b></td>
<td>{signal.spot:.2f}</td>
</tr>

<tr>
<td><b>Futures Regime</b></td>
<td>{signal.futures_state}</td>
</tr>

<tr>
<td><b>Option</b></td>
<td>{signal.trading_symbol}</td>
</tr>

<tr>
<td><b>Option Type</b></td>
<td>{signal.option_type}</td>
</tr>

<tr>
<td><b>Strike</b></td>
<td>{signal.strike:.0f}</td>
</tr>

<tr>
<td><b>Entry</b></td>
<td>₹{signal.entry:.2f}</td>
</tr>

<tr>
<td><b>Target 1</b></td>
<td>₹{signal.target_1:.2f}</td>
</tr>

<tr>
<td><b>Target 2</b></td>
<td>₹{signal.target_2:.2f}</td>
</tr>

<tr>
<td><b>Stop Loss</b></td>
<td>₹{signal.stop_loss:.2f}</td>
</tr>

<tr>
<td><b>3m Breakout Trigger</b></td>
<td>{signal.underlying_trigger_3m:.2f}</td>
</tr>

<tr>
<td><b>15m Target Level</b></td>
<td>{signal.underlying_target_15m:.2f}</td>
</tr>

<tr>
<td><b>Delta</b></td>
<td>{signal.delta:.4f}</td>
</tr>

<tr>
<td><b>Gamma</b></td>
<td>{signal.gamma:.6f}</td>
</tr>

</table>

<h3>Prediction Factors</h3>

<ul>
{reason_html}
</ul>

<p>
This is a rule-based market signal. It does not guarantee
future price movement or profitability.
</p>

</body>
</html>
"""


# =============================================================================
# MAIN SCANNER — CLEAN EXECUTION PIPELINE
# =============================================================================

def execute_scan(state: Optional[dict[str, Any]] = None) -> Optional[Signal]:
    """Run one complete SENSEX scan.

    Pipeline:
        Market Structure -> Direction -> Confirmation -> Strike Selection
        -> Entry -> Monitoring -> Exit

    Existing active trades are monitored BEFORE any new strike is selected.
    This prevents a valid active trade from being invalidated by a transient
    option-chain/Greek/strike-selection condition on the same scan.
    """
    if not market_window_open():
        logger.info("Outside BSE market hours.")
        return None

    status = get_market_status()
    logger.info("BSE status: %s", status)
    if status != "OPEN":
        logger.info("BSE is not OPEN. No signal generated.")
        return None

    state = state if isinstance(state, dict) else {}
    previous_snapshot = state.get("market_snapshot")
    if not isinstance(previous_snapshot, dict):
        previous_snapshot = {}

    try:
        future = get_current_sensex_future()
        futures_3m = get_intraday_candles(future.instrument_key, 3, max_candles=12, min_candles=3)
        futures_vwap = get_session_candles_for_vwap(future.instrument_key, interval_minutes=3, min_candles=5)

        spot_3m = get_intraday_candles(SENSEX_KEY, 3, max_candles=80, min_candles=3)
        spot_15m = get_intraday_candles(SENSEX_KEY, 15, max_candles=80, min_candles=2)
        spot_3m = calculate_supertrend(spot_3m, SUPERTREND_PERIOD, SUPERTREND_FACTOR)
        spot_15m = calculate_supertrend(spot_15m, SUPERTREND_PERIOD, SUPERTREND_FACTOR)

        spot = extract_ltp(get_quote(SENSEX_KEY))
        chain = get_chain()
        contracts = get_current_week_contracts()

        chain_spot_value = chain_spot(chain)
        if abs(chain_spot_value - spot) > 100:
            raise ScannerError(
                f"Option-chain spot mismatch: chain={chain_spot_value:.2f}, live={spot:.2f}."
            )

        # Option OI difference is a confirmation input to market structure;
        # it is not allowed to replace price/VWAP/Supertrend structure.
        (
            oi_diff,
            oi_diff_change,
            oi_diff_normalized,
            oi_diff_direction,
            oi_diff_trend,
            ce_change_oi,
            ce_change_oi_normalized,
        ) = option_oi_difference(chain, spot)

        chain_bias, chain_bias_score, _ = oi_structure(chain, spot)
        change_data = get_change_oi_from_chain(chain)
        change_bias, change_bias_score = change_oi_bias(change_data)

        direction, interpretation, confidence, reasons, market_score = predictive_direction(
            spot_3m=spot_3m,
            spot_15m=spot_15m,
            chain_bias=chain_bias,
            chain_bias_score=chain_bias_score,
            change_oi_bias_value=change_bias,
            change_oi_score=change_bias_score,
            futures_state="STRUCTURE_ENGINE",
            live_spot=spot,
            futures_3m=futures_3m,
            futures_vwap_candles=futures_vwap,
            previous_snapshot=previous_snapshot,
            option_oi_diff=oi_diff,
            option_oi_diff_change=oi_diff_change,
            option_oi_direction=oi_diff_direction,
            option_oi_trend=oi_diff_trend,
            ce_change_oi=ce_change_oi,
            ce_change_oi_normalized=ce_change_oi_normalized,
        )

        snap = _market_structure_snapshot(
            spot_3m, spot_15m, futures_3m, futures_vwap, spot,
            float(oi_diff), float(oi_diff_change),
        )
        vwap = float(snap["vwap"])
        price_vs_vwap = "ABOVE" if spot > vwap else "BELOW" if spot < vwap else "AT_VWAP"

        state["market_snapshot"] = {
            "timestamp": now_ist().isoformat(),
            "sensex_spot": round(float(spot), 2),
            "futures_price": round(float(futures_3m["close"].iloc[-1]), 2),
            "futures_state": snap["futures_regime"],
            "price_vs_vwap": price_vs_vwap,
            "futures_vwap": round(vwap, 4),
            "option_oi_difference": round(float(oi_diff), 2),
            "option_oi_difference_change": round(float(oi_diff_change), 2),
            "option_oi_difference_normalized": round(float(oi_diff_normalized), 6),
            "option_oi_direction": oi_diff_direction,
            "option_oi_trend": oi_diff_trend,
            "prediction_direction": direction,
            "prediction_regime": interpretation,
            "prediction_confidence": round(float(confidence), 2),
            "market_structure_score": round(float(market_score), 3),
            "three_min_supertrend": "BULLISH" if snap["st3"] > 0 else "BEARISH" if snap["st3"] < 0 else "NEUTRAL",
            "fifteen_min_supertrend": "BULLISH" if snap["st15"] > 0 else "BEARISH" if snap["st15"] < 0 else "NEUTRAL",
            "futures_price_direction": int(snap["fut_price_dir"]),
            "futures_oi_direction": int(snap["fut_oi_dir"]),
        }
        save_state(state)

        logger.info(
            "PREDICTION: direction=%s regime=%s confidence=%.1f score=%+.2f",
            direction, interpretation, confidence, market_score,
        )

        # ------------------------------------------------------------------
        # ACTIVE TRADE: monitor first. Never re-select or invalidate it merely
        # because current entry conditions are temporarily unavailable.
        # ------------------------------------------------------------------
        active = active_trade_from_state(state)
        if active is not None:
            trade_date = str(active.get("trade_date", ""))[:10]
            today = now_ist().date().isoformat()
            if trade_date and trade_date != today:
                logger.info("Clearing stale previous-session active trade: %s", active.get("trading_symbol", ""))
                state["last_completed_trade"] = dict(active, status="CLOSED", outcome="SESSION_END_CLEANUP")
                state["active_trade"] = None
                save_state(state)
            else:
                monitor_result = monitor_active_trade(
                    state=state,
                    current_direction=direction,
                    current_interpretation=interpretation,
                    current_confidence=confidence,
                    final_confirmed=(direction != "NEUTRAL"),
                    selected_option=None,
                    current_logic_signature="",
                )
                # An existing trade owns this scan. Do not create a second trade.
                return None

        if direction == "NEUTRAL":
            logger.info("No entry: market structure is neutral/mixed.")
            return None

        if confidence < SIGNAL_THRESHOLD:
            logger.info("No entry: confidence %.1f < %.1f.", confidence, SIGNAL_THRESHOLD)
            return None

        # Pre-breakout confirmation: direction must already be established,
        # but the breakout itself must NOT have occurred.
        confirmed, confirmation_reasons = final_entry_direction_confirmation(
            direction, interpretation, spot_3m, futures_vwap
        )
        if not confirmed:
            logger.info("No entry: pre-breakout VWAP confirmation failed.")
            return None

        option = select_directional_option(
            contracts=contracts,
            chain=chain,
            direction=direction,
            spot=spot,
            preferred_strike=None,
        )

        valid, trigger_3m, target_15m, validation_reasons = validate_prebreakout(
            spot_3m, spot_15m, direction, option
        )
        if not valid:
            logger.info("No entry: pre-breakout structural validation failed.")
            return None

        target_1, target_2, stop_loss = create_targets(
            option, spot, trigger_3m, target_15m, direction
        )

        all_reasons = list(reasons) + list(confirmation_reasons) + list(validation_reasons) + [
            f"Market structure score={market_score:+.2f}.",
            f"PE-CE OI difference={oi_diff:+.0f}; change={oi_diff_change:+.0f}.",
            f"Futures regime={snap['futures_regime']}.",
            f"Strike rule={'ATM-1 CE, fallback ATM-2 CE' if direction == 'BULLISH' else 'ATM+1 PE, fallback ATM+2 PE'}.",
            "Entry is predictive and pre-breakout; no completed breakout candle is required.",
            "Active trade exits only at T1/T2/SL or after two consecutive strong opposite-structure confirmations.",
        ]

        return Signal(
            timestamp=now_ist().strftime("%Y-%m-%d %H:%M:%S IST"),
            direction=direction,
            regime=interpretation,
            confidence=float(confidence),
            spot=float(spot),
            futures_state=str(snap["futures_regime"]),
            option_type=option.option_type,
            strike=float(option.strike),
            trading_symbol=option.trading_symbol,
            instrument_key=option.instrument_key,
            entry=float(option.ltp),
            target_1=float(target_1),
            target_2=float(target_2),
            stop_loss=float(stop_loss),
            underlying_trigger_3m=float(trigger_3m),
            underlying_target_15m=float(target_15m),
            delta=float(option.delta),
            gamma=float(option.gamma),
            reasons=all_reasons,
        )

    except ScannerError as exc:
        logger.info("Scanner cycle skipped safely: %s", exc)
        return None
    except Exception:
        logger.error("Unexpected scan failure:\n%s", traceback.format_exc())
        return None


def self_test() -> None:
    """Offline deterministic tests for core decision/state logic."""
    def candles(values: list[float], oi: Optional[list[float]] = None) -> pd.DataFrame:
        idx = pd.date_range("2026-09-09 09:15", periods=len(values), freq="3min")
        df = pd.DataFrame({
            "timestamp": idx,
            "open": values,
            "high": [v + 2 for v in values],
            "low": [v - 2 for v in values],
            "close": values,
            "volume": [1000] * len(values),
        }, index=idx)
        if oi is not None:
            df["oi"] = oi
        return df

    # Direction engine: strongly bearish and bullish synthetic structures.
    bear3 = calculate_supertrend(candles([100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89]), 10, 3.0)
    bear15 = calculate_supertrend(candles([100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89]), 10, 3.0)
    fut_bear = candles([100, 99, 98, 97, 96, 95], [1000, 1020, 1040, 1060, 1080, 1100])
    vwap_bear = fut_bear.copy()
    bear = _market_structure_snapshot(bear3, bear15, fut_bear, vwap_bear, 89.0, -1000.0, -100.0)
    assert bear["direction"] == "BEARISH", f"bearish test failed: {bear}"

    bull3 = calculate_supertrend(candles([90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]), 10, 3.0)
    bull15 = calculate_supertrend(candles([90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101]), 10, 3.0)
    fut_bull = candles([90, 91, 92, 93, 94, 95], [1000, 1020, 1040, 1060, 1080, 1100])
    vwap_bull = fut_bull.copy()
    bull = _market_structure_snapshot(bull3, bull15, fut_bull, vwap_bull, 101.0, 1000.0, 100.0)
    assert bull["direction"] == "BULLISH", f"bullish test failed: {bull}"

    # Strike selection: deterministic ATM +/- one, fallback +/- two.
    chain = []
    contracts = []
    for strike in [74000, 74050, 74100, 74150, 74200]:
        chain.append({"strike_price": strike,
                      "call_options": {"instrument_key": f"CE{strike}", "market_data": {"ltp": 100, "oi": 1000, "prev_oi": 900}, "option_greeks": {"delta": .5, "gamma": .01, "iv": 20}},
                      "put_options": {"instrument_key": f"PE{strike}", "market_data": {"ltp": 100, "oi": 1000, "prev_oi": 900}, "option_greeks": {"delta": -.5, "gamma": .01, "iv": 20}}})
        contracts.extend([
            {"instrument_key": f"CE{strike}", "trading_symbol": f"SENSEX{strike}CE", "instrument_type": "CE", "strike_price": strike, "expiry": "2026-09-15"},
            {"instrument_key": f"PE{strike}", "trading_symbol": f"SENSEX{strike}PE", "instrument_type": "PE", "strike_price": strike, "expiry": "2026-09-15"},
        ])
    selected_bull = select_directional_option(contracts, chain, "BULLISH", 74100)
    selected_bear = select_directional_option(contracts, chain, "BEARISH", 74100)
    assert selected_bull.strike == 74050 and selected_bull.option_type == "CE"
    assert selected_bear.strike == 74150 and selected_bear.option_type == "PE"

    # Target ordering and SL.
    t1, t2, sl = create_targets(selected_bull, 74100, 74150, 74250, "BULLISH")
    assert t2 > t1 > selected_bull.ltp and sl < selected_bull.ltp

    logger.info("SELF-TEST PASSED: market direction, strike selection, and target engine.")


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
            "underlying_trigger_3m": signal.underlying_trigger_3m,
            "underlying_target_15m": signal.underlying_target_15m,
            "delta": signal.delta,
            "gamma": signal.gamma,
            "last_ltp": signal.entry,
            "reversal_confirmations": 0,
            "last_market_direction": signal.direction,
            "last_market_confidence": signal.confidence,
        }
        state["active_trade"] = active_trade
        state["last_signal"] = asdict(signal)
        state["last_signal_timestamp"] = signal.timestamp
        state["last_signal_hash"] = signal_hash(signal)
        save_state(state)

        send_email(
            f"SENSEX {signal.direction} {signal.trading_symbol}",
            email_body(signal),
        )
        logger.info("NEW ACTIVE TRADE LOCKED: %s", signal.trading_symbol)
        return 0

    except ScannerError as exc:
        logger.error("Scanner error: %s", exc)
        return 1
    except Exception:
        logger.error("Fatal scanner failure:\n%s", traceback.format_exc())
        return 1


if __name__ == "__main__":
    sys.exit(main())
