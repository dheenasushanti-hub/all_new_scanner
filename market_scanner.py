"""
NIFTY Predictive Options Market Scanner

Strategy:
- NIFTY 3-minute and 15-minute Supertrend: (10, 3)
- Full current-session VWAP + price structure
- Dynamic current-month NIFTY futures discovery
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
- Stop loss = 15% below entry premium
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

NIFTY_KEY = os.getenv(
    "NIFTY_INSTRUMENT_KEY",
    "NSE_INDEX|Nifty 50",
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

STATE_FILE = Path(
    os.getenv(
        "STATE_FILE",
        "state/market_state.json",
    )
)

SIGNAL_THRESHOLD = float(
    os.getenv(
        "SIGNAL_THRESHOLD",
        "60",
    )
)

PREDICTION_MIN_CONFLUENCE = 2
LOCK_SETUP_MINUTES = 45

MARKET_START = time(9, 15)
MARKET_END = time(15, 30)

SUPERTREND_PERIOD = 10
SUPERTREND_FACTOR = 3.0

STRUCTURE_LOOKBACK_3M = 8
STRUCTURE_LOOKBACK_15M = 6

OPTION_MIN_DELTA = 0.35
OPTION_MAX_DELTA = 0.85

MAX_SIGNAL_AGE_MINUTES = 15


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
    f"{BASE_URL}/v2/market/status/NSE"
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

logger = logging.getLogger("nifty_scanner")


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

    if is_nse_holiday(current):
        logger.info(
            "NSE holiday: %s. Scanner will not run.",
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
) -> dict[str, Any]:

    try:
        response = requests.get(
            url,
            params=params,
            headers=api_headers(),
            timeout=REQUEST_TIMEOUT,
        )
    except requests.RequestException as exc:
        raise ScannerError(
            f"Network request failed: {exc}"
        ) from exc

    if response.status_code != 200:
        raise ScannerError(
            f"Upstox HTTP {response.status_code}: "
            f"{response.text[:1000]}"
        )

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

# =============================================================================
# MARKET HOLIDAY
# =============================================================================

def is_nse_holiday(
    current_date: datetime,
) -> bool:
    """
    Uses Upstox's market-holiday API to determine whether
    NSE is closed on the current IST date.
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
# NIFTY QUOTE
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
def get_current_nifty_future() -> FuturesContract:

    all_contracts = []

    # Try current month first, then next month.
    for expiry_filter in ("current_month", "next_month"):

        payload = api_get(
            INSTRUMENT_SEARCH_URL,
            {
                "query": "NIFTY",
                "exchanges": "NSE",
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
            "No active NIFTY futures returned by Upstox."
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
            "NIFTY" in underlying
            or "NIFTY" in symbol
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
            "No valid NIFTY future found."
        )

    # Sort by expiry and select nearest available future.
    valid.sort(
        key=lambda x: str(
            x.get("expiry")
        )
    )

    selected = valid[0]

    logger.info(
        "Selected NIFTY future: %s | Expiry: %s | Key: %s",
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

    payload = api_get(
        OPTION_CONTRACT_URL,
        {
            "instrument_key": NIFTY_KEY,
            "expiry_date": "current_week",
        },
    )

    contracts = payload.get(
        "data",
        [],
    )

    if not isinstance(
        contracts,
        list,
    ) or not contracts:
        raise ScannerError(
            "No current-week NIFTY option contracts returned."
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
        "VWAP source: NIFTY Futures | current-session candles=%d | volume=%0.f",
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
        min_periods=period,
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

    first_valid = result["atr"].first_valid_index()

    if first_valid is None:
        raise ScannerError(
            "Unable to calculate Supertrend."
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
    # not a real VWAP. The scanner uses NIFTY futures candles for VWAP instead.
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

def get_chain() -> list[dict[str, Any]]:

    payload = api_get(
        OPTION_CHAIN_URL,
        {
            "instrument_key": NIFTY_KEY,
            "expiry_date": "current_week",
        },
    )

    data = payload.get(
        "data",
        [],
    )

    if not isinstance(
        data,
        list,
    ) or not data:
        raise ScannerError(
            "Current-week option chain is empty."
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
# OI CHANGE API
# =============================================================================

def get_change_oi() -> dict[str, Any]:

    current_date = now_ist().strftime(
        "%Y-%m-%d"
    )

    try:

        payload = api_get(
            CHANGE_OI_URL,
            {
                "instrument_key": NIFTY_KEY,
                "expiry": "current_week",
                "date": current_date,
                "interval": 1,
            },
        )

        data = payload.get(
            "data",
            {}
        )

        if not isinstance(
            data,
            dict,
        ):
            raise ScannerError(
                "Invalid Change-in-OI data."
            )

        return data

    except ScannerError as exc:

        logger.warning(
            "Change-in-OI unavailable: %s",
            exc,
        )

        return {}


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

    if candles is None:
        candles = get_intraday_candles(
            future.instrument_key,
            3,
            max_candles=3,
            min_candles=2,
        )

    if len(candles) < 3:
        return "UNAVAILABLE"

    latest = candles.iloc[-1]
    previous = candles.iloc[-2]

    if (
        pd.isna(latest["oi"])
        or pd.isna(previous["oi"])
    ):
        return "UNAVAILABLE"

    price_delta = (
        latest["close"]
        - previous["close"]
    )

    oi_delta = (
        latest["oi"]
        - previous["oi"]
    )

    if price_delta > 0 and oi_delta > 0:
        return "LONG_BUILDUP"

    if price_delta < 0 and oi_delta > 0:
        return "SHORT_BUILDUP"

    if price_delta > 0 and oi_delta < 0:
        return "SHORT_COVERING"

    if price_delta < 0 and oi_delta < 0:
        return "LONG_UNWINDING"

    return "NEUTRAL"


# =============================================================================
# OPTION CONTRACT SELECTION
# =============================================================================

def select_directional_option(
    contracts: list[dict[str, Any]],
    chain: list[dict[str, Any]],
    direction: str,
    spot: float,
    preferred_strike: Optional[float] = None,
) -> OptionCandidate:

    rows = chain_rows(chain)
    chain_strikes = sorted(rows.keys())

    atm = nearest_atm_strike(spot, chain_strikes)
    step = strike_interval(chain_strikes)

    # For bullish moves, buy ITM CE: ATM-1, then ATM-2.
    # For bearish moves, buy ITM PE: ATM+1, then ATM+2.
    if direction == "BULLISH":
        candidates = [atm - step, atm - 2 * step]
        option_type = "CE"
    else:
        candidates = [atm + step, atm + 2 * step]
        option_type = "PE"

    if preferred_strike is not None:
        candidates = [float(preferred_strike)] + [
            strike for strike in candidates
            if float(strike) != float(preferred_strike)
        ]

    for target_strike in candidates:
        if target_strike not in rows:
            continue

        matches = [
            contract
            for contract in contracts
            if (
                str(contract.get("instrument_type", "")).upper() == option_type
                and float(contract.get("strike_price", -1)) == float(target_strike)
            )
        ]

        if not matches:
            continue

        contract = matches[0]
        market = option_market_data(rows[target_strike], option_type)
        ltp = float(market["ltp"] or 0)
        delta = market["delta"]

        if ltp <= 0 or delta is None:
            continue

        logger.info(
            "ITM option selected: direction=%s ATM=%.0f strike=%.0f type=%s LTP=%.2f Delta=%.3f",
            direction, atm, target_strike, option_type, ltp, float(delta),
        )

        return OptionCandidate(
            instrument_key=contract["instrument_key"],
            trading_symbol=contract["trading_symbol"],
            option_type=option_type,
            strike=float(target_strike),
            expiry=str(contract["expiry"]),
            ltp=ltp,
            oi=float(market["oi"] or 0),
            prev_oi=float(market["prev_oi"] or 0),
            delta=float(delta),
            gamma=float(market["gamma"] or 0),
            iv=float(market["iv"] or 0),
        )

    raise ScannerError(
        f"No valid ITM {option_type} contract found for ATM={atm:.0f}."
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


# =============================================================================
# PRE-BREAKOUT ENGINE
# =============================================================================

def predictive_direction(
    spot_3m: pd.DataFrame,
    spot_15m: pd.DataFrame,
    chain_bias: str,
    change_oi_bias_value: str,
    futures_state: str,
    live_spot: float,
    futures_3m: Optional[pd.DataFrame] = None,
) -> tuple[str, str, float, list[str]]:
    """
    Predict direction before the breakout.

    Core trigger:
      1. Futures price/OI regime
      2. Localized option OI pressure OR Upstox Change-OI bias
      3. NIFTY price relative to session VWAP and VWAP slope

    Supertrend is deliberately NOT required for entry prediction.
    It remains a confirmation/target framework.
    """
    latest_3 = spot_3m.iloc[-1]
    previous_3 = spot_3m.iloc[-2]
    latest_15 = spot_15m.iloc[-1]

    bullish_score = 0.0
    bearish_score = 0.0
    bullish_reasons: list[str] = []
    bearish_reasons: list[str] = []

    # -------------------------------------------------------------------------
    # 1. FUTURES — primary directional signal
    # -------------------------------------------------------------------------
    bullish_futures = futures_state in ("LONG_BUILDUP", "SHORT_COVERING")
    bearish_futures = futures_state in ("SHORT_BUILDUP", "LONG_UNWINDING")

    if bullish_futures:
        bullish_score += 40
        bullish_reasons.append(
            f"Futures confirms bullish positioning: {futures_state}"
        )
    elif bearish_futures:
        bearish_score += 40
        bearish_reasons.append(
            f"Futures confirms bearish positioning: {futures_state}"
        )

    # -------------------------------------------------------------------------
    # 2. OPTION OI — localized strike pressure + Upstox change-OI
    #
    # Localized chain bias is primary. The Change-OI endpoint is a second
    # confirmation source and is never required when unavailable.
    # -------------------------------------------------------------------------
    bullish_oi = chain_bias == "BULLISH" or change_oi_bias_value == "BULLISH"
    bearish_oi = chain_bias == "BEARISH" or change_oi_bias_value == "BEARISH"

    if chain_bias == "BULLISH":
        bullish_score += 30
        bullish_reasons.append(
            "Localized option OI pressure is bullish"
        )
    elif chain_bias == "BEARISH":
        bearish_score += 30
        bearish_reasons.append(
            "Localized option OI pressure is bearish"
        )

    if change_oi_bias_value == "BULLISH":
        bullish_score += 10
        bullish_reasons.append(
            "Upstox Change-OI confirms bullish direction"
        )
    elif change_oi_bias_value == "BEARISH":
        bearish_score += 10
        bearish_reasons.append(
            "Upstox Change-OI confirms bearish direction"
        )

    # -------------------------------------------------------------------------
    # 3. VWAP — primary price confirmation
    # -------------------------------------------------------------------------
    # NIFTY index candles may have no exchange-traded volume, which makes an
    # index VWAP undefined. Use the complete current-session NIFTY futures
    # candles for the session VWAP.
    if futures_3m is None or futures_3m.empty:
        raise ScannerError("NIFTY futures candle data unavailable for VWAP.")

    vwap_series = calculate_vwap(futures_3m)
    valid_vwap = vwap_series.dropna()

    if len(valid_vwap) < 2:
        raise ScannerError(
            "Session VWAP unavailable: NIFTY futures volume is zero/missing."
        )

    session_vwap = float(valid_vwap.iloc[-1])
    previous_vwap = float(valid_vwap.iloc[-2])
    vwap_slope = session_vwap - previous_vwap
    above_vwap = float(live_spot) > session_vwap

    # Price location relative to VWAP is the primary VWAP signal.
    # VWAP slope is a confidence/context factor, not a hard direction gate.
    bullish_vwap = above_vwap
    bearish_vwap = not above_vwap

    logger.info(
        "VWAP check: NIFTY=%.2f VWAP=%.2f slope=%.4f position=%s",
        live_spot,
        session_vwap,
        vwap_slope,
        "ABOVE" if above_vwap else "BELOW",
    )

    if bullish_vwap:
        bullish_score += 20
        bullish_reasons.append(
            f"NIFTY {live_spot:.2f} is above session VWAP {session_vwap:.2f}; slope={vwap_slope:.4f}"
        )
        if vwap_slope > 0:
            bullish_score += 5
            bullish_reasons.append("VWAP slope is rising")
    else:
        bearish_score += 20
        bearish_reasons.append(
            f"NIFTY {live_spot:.2f} is below session VWAP {session_vwap:.2f}; slope={vwap_slope:.4f}"
        )
        if vwap_slope < 0:
            bearish_score += 5
            bearish_reasons.append("VWAP slope is falling")

    # -------------------------------------------------------------------------
    # 4. Supertrend — confirmation only
    # -------------------------------------------------------------------------
    if latest_15["direction"] == 1:
        bullish_score += 5
        bullish_reasons.append(
            "15-minute Supertrend supports bullish continuation"
        )
    elif latest_15["direction"] == -1:
        bearish_score += 5
        bearish_reasons.append(
            "15-minute Supertrend supports bearish continuation"
        )

    # -------------------------------------------------------------------------
    # FINAL PREDICTIVE CONFLUENCE
    # Futures + OI + VWAP must align.
    # -------------------------------------------------------------------------
    if (
        bullish_futures
        and bullish_oi
        and bullish_vwap
        and bullish_score > bearish_score
    ):
        return (
            "BULLISH",
            "BULLISH_PREDICTIVE",
            min(100.0, bullish_score),
            bullish_reasons,
        )

    if (
        bearish_futures
        and bearish_oi
        and bearish_vwap
        and bearish_score > bullish_score
    ):
        return (
            "BEARISH",
            "BEARISH_PREDICTIVE",
            min(100.0, bearish_score),
            bearish_reasons,
        )

    return (
        "NEUTRAL",
        "NEUTRAL",
        0.0,
        [
            "Futures + localized OI/Change-OI + VWAP did not reach predictive confluence."
        ],
    )


# =============================================================================
# PRE-BREAKOUT VALIDATION
# =============================================================================

def validate_prebreakout(
    spot_3m: pd.DataFrame,
    spot_15m: pd.DataFrame,
    direction: str,
    option: OptionCandidate,
) -> tuple[bool, float, float, list[str]]:

    latest_3 = spot_3m.iloc[-1]
    latest_15 = spot_15m.iloc[-1]
    spot = float(latest_3["close"])

    atr_3 = float(latest_3["atr"])
    atr_15 = float(latest_15["atr"])
    if not (math.isfinite(atr_3) and math.isfinite(atr_15) and atr_3 > 0 and atr_15 > 0):
        return False, 0.0, 0.0, ["ATR unavailable."]

    if direction == "BULLISH":
        recent_trigger = recent_swing_high(spot_3m, STRUCTURE_LOOKBACK_3M)
        trigger_3m = max(
            recent_trigger,
            spot + max(atr_3 * 0.25, 1.0),
        )

        recent_15 = recent_swing_high(spot_15m, STRUCTURE_LOOKBACK_15M)
        target_15m = max(
            recent_15,
            float(latest_15["supertrend"]),
            trigger_3m + max(atr_15 * 0.50, atr_3 * 0.50),
        )
    else:
        recent_trigger = recent_swing_low(spot_3m, STRUCTURE_LOOKBACK_3M)
        trigger_3m = min(
            recent_trigger,
            spot - max(atr_3 * 0.25, 1.0),
        )

        recent_15 = recent_swing_low(spot_15m, STRUCTURE_LOOKBACK_15M)
        target_15m = min(
            recent_15,
            float(latest_15["supertrend"]),
            trigger_3m - max(atr_15 * 0.50, atr_3 * 0.50),
        )

    if not (OPTION_MIN_DELTA <= abs(option.delta) <= OPTION_MAX_DELTA):
        return (
            False,
            trigger_3m,
            target_15m,
            [f"Rejected: selected option Delta={option.delta:.3f} is outside the trading range."],
        )

    return (
        True,
        trigger_3m,
        target_15m,
        [
            "Prediction is based on Futures + OI difference + VWAP.",
            "3-minute Supertrend is used for target/confirmation, not as the entry trigger.",
            f"ITM option selected at {option.strike:.0f} ({option.option_type}).",
            f"Option Delta={option.delta:.3f}.",
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
        entry * 0.85,
        2,
    )

    return (
        target_1,
        target_2,
        stop_loss,
    )


# =============================================================================
# STATE
# =============================================================================

def load_state() -> dict[str, Any]:

    if not STATE_FILE.exists():
        return {}

    try:

        with STATE_FILE.open(
            "r",
            encoding="utf-8",
        ) as file:

            data = json.load(
                file
            )

        return (
            data
            if isinstance(data, dict)
            else {}
        )

    except Exception as exc:

        logger.warning(
            "State read failed: %s",
            exc,
        )

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
NIFTY Predictive {signal.direction} Signal
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
<td><b>NIFTY Spot</b></td>
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
# MAIN SCANNER
# =============================================================================

def execute_scan(state: Optional[dict[str, Any]] = None) -> Optional[Signal]:
    if not market_window_open():
        logger.info("Outside NSE market hours.")
        return None

    status = get_market_status()
    logger.info("NSE status: %s", status)

    if status != "OPEN":
        logger.info("NSE is not OPEN. No signal generated.")
        return None

    state = state if isinstance(state, dict) else {}

    future = get_current_nifty_future()

    # -------------------------------------------------------------------------
    # Underlying market data
    # -------------------------------------------------------------------------
    # Separate datasets by purpose. The latest 3 candles are used only for
    # Futures price/OI regime. A complete current-session Futures dataset is
    # fetched separately for the session VWAP and is never truncated.
    futures_recent = get_intraday_candles(
        future.instrument_key,
        3,
        max_candles=3,
        min_candles=3,
    )
    futures_state = futures_regime(future, candles=futures_recent)

    futures_vwap_candles = get_session_candles_for_vwap(
        future.instrument_key,
        interval_minutes=3,
        min_candles=20,
    )

    logger.info(
        "Futures regime: %s | regime candles=%d | VWAP candles=%d",
        futures_state,
        len(futures_recent),
        len(futures_vwap_candles),
    )

    spot_3m = get_intraday_candles(NIFTY_KEY, 3)
    spot_3m = calculate_supertrend(
        spot_3m,
        SUPERTREND_PERIOD,
        SUPERTREND_FACTOR,
    )
    spot_15m = get_intraday_candles(NIFTY_KEY, 15)
    spot_15m = calculate_supertrend(
        spot_15m,
        SUPERTREND_PERIOD,
        SUPERTREND_FACTOR,
    )

    spot_quote = get_quote(NIFTY_KEY)
    spot = extract_ltp(spot_quote)

    # -------------------------------------------------------------------------
    # Option chain / OI
    # -------------------------------------------------------------------------
    chain = get_chain()
    chain_spot_value = chain_spot(chain)

    if abs(chain_spot_value - spot) > 100:
        raise ScannerError(
            "Option-chain spot differs materially from current quote."
        )

    contracts = get_current_week_contracts()

    chain_bias, chain_bias_score, strike_data = oi_structure(
        chain,
        spot,
    )

    change_data = get_change_oi()
    change_bias, change_bias_score = change_oi_bias(change_data)

    direction, regime, confidence, reasons = predictive_direction(
        spot_3m,
        spot_15m,
        chain_bias,
        change_bias,
        futures_state,
        live_spot=spot,
        futures_3m=futures_vwap_candles,
    )

    logger.info(
        "Prediction: direction=%s regime=%s confidence=%.2f",
        direction,
        regime,
        confidence,
    )

    if direction == "NEUTRAL":
        return None

    if confidence < SIGNAL_THRESHOLD:
        logger.info(
            "Rejected: confidence %.2f < %.2f",
            confidence,
            SIGNAL_THRESHOLD,
        )
        return None

    # -------------------------------------------------------------------------
    # Futures must never contradict the predictive direction.
    # -------------------------------------------------------------------------
    bullish_future = futures_state in (
        "LONG_BUILDUP",
        "SHORT_COVERING",
    )
    bearish_future = futures_state in (
        "SHORT_BUILDUP",
        "LONG_UNWINDING",
    )

    if direction == "BULLISH" and bearish_future:
        logger.info(
            "Rejected: futures explicitly bearish (%s).",
            futures_state,
        )
        return None

    if direction == "BEARISH" and bullish_future:
        logger.info(
            "Rejected: futures explicitly bullish (%s).",
            futures_state,
        )
        return None

    # -------------------------------------------------------------------------
    # Strike lock
    #
    # Once a predictive setup first produces an ITM strike, keep that strike
    # for LOCK_SETUP_MINUTES. This prevents chasing a later ATM shift.
    # -------------------------------------------------------------------------
    locked_direction = state.get("locked_direction")
    locked_strike = state.get("locked_strike")
    locked_timestamp = state.get("locked_timestamp")

    preferred_strike: Optional[float] = None

    if (
        locked_direction == direction
        and locked_strike is not None
        and locked_timestamp
    ):
        try:
            locked_at = datetime.fromisoformat(locked_timestamp)
            locked_age = (
                now_ist() - locked_at
            ).total_seconds() / 60.0

            if 0 <= locked_age <= LOCK_SETUP_MINUTES:
                preferred_strike = float(locked_strike)
                logger.info(
                    "Using locked predictive strike: %s %.0f (age %.1f min).",
                    direction,
                    preferred_strike,
                    locked_age,
                )
            else:
                logger.info(
                    "Previous %s strike lock expired (age %.1f min).",
                    locked_direction,
                    locked_age,
                )
        except (TypeError, ValueError):
            preferred_strike = None

    option = select_directional_option(
        contracts,
        chain,
        direction,
        spot,
        preferred_strike=preferred_strike,
    )

    # If this is a new predictive setup, lock the chosen strike immediately.
    # This records the strike at the moment the Futures/OI/VWAP prediction is
    # detected, rather than after the market has already moved.
    if preferred_strike is None:
        state["locked_direction"] = direction
        state["locked_strike"] = option.strike
        state["locked_option_type"] = option.option_type
        state["locked_timestamp"] = now_ist().isoformat()
        save_state(state)

        logger.info(
            "NEW predictive strike locked: %s %.0f %s.",
            direction,
            option.strike,
            option.option_type,
        )

    logger.info(
        "Candidate option: %s | strike=%.0f | LTP=%.2f | OI=%.0f | prev_OI=%.0f",
        option.trading_symbol,
        option.strike,
        option.ltp,
        option.oi,
        option.prev_oi,
    )

    option_regime = option_price_oi_regime(option)
    logger.info(
        "Selected option price/OI confirmation: %s = %s",
        option.trading_symbol,
        option_regime,
    )

    valid, trigger_3m, target_15m, validation_reasons = validate_prebreakout(
        spot_3m,
        spot_15m,
        direction,
        option,
    )

    if not valid:
        logger.info("Pre-breakout validation rejected.")
        return None

    target_1, target_2, stop_loss = create_targets(
        option,
        spot,
        trigger_3m,
        target_15m,
        direction,
    )

    all_reasons = (
        reasons
        + validation_reasons
        + [
            f"Localized option OI score={chain_bias_score:.3f}.",
            f"Upstox Change-OI score={change_bias_score:.3f}.",
            f"Selected option price/OI confirmation={option_regime}.",
            "Prediction trigger = Futures + localized OI/Change-OI + VWAP.",
            "3-minute Supertrend is confirmation/target framework, not entry trigger.",
            "ITM strike is locked at first predictive detection to avoid chasing ATM.",
        ]
    )

    return Signal(
        timestamp=now_ist().strftime("%Y-%m-%d %H:%M:%S IST"),
        direction=direction,
        regime=regime,
        confidence=confidence,
        spot=spot,
        futures_state=futures_state,
        option_type=option.option_type,
        strike=option.strike,
        trading_symbol=option.trading_symbol,
        instrument_key=option.instrument_key,
        entry=option.ltp,
        target_1=target_1,
        target_2=target_2,
        stop_loss=stop_loss,
        underlying_trigger_3m=trigger_3m,
        underlying_target_15m=target_15m,
        delta=option.delta,
        gamma=option.gamma,
        reasons=all_reasons,
    )


# =============================================================================
# PROGRAM ENTRY
# =============================================================================

def main() -> int:

    try:

        state = load_state()

        signal = execute_scan(state)

        if signal is None:
            logger.info(
                "No actionable predictive setup."
            )
            return 0

        current_hash = signal_hash(
            signal
        )

        previous_hash = state.get(
            "last_signal_hash"
        )

        if current_hash == previous_hash:

            logger.info(
                "Duplicate signal suppressed."
            )

            return 0

        send_email(
            (
                f"NIFTY {signal.direction} "
                f"{signal.trading_symbol}"
            ),
            email_body(
                signal
            ),
        )

        state[
            "last_signal_hash"
        ] = current_hash

        state[
            "locked_direction"
        ] = signal.direction

        state[
            "locked_strike"
        ] = signal.strike

        state[
            "locked_option_type"
        ] = signal.option_type

        state[
            "locked_timestamp"
        ] = now_ist().isoformat()

        state[
            "last_signal"
        ] = asdict(
            signal
        )

        state[
            "last_signal_timestamp"
        ] = signal.timestamp

        save_state(
            state
        )

        logger.info(
            "NEW SIGNAL EMAILED: %s",
            signal.trading_symbol,
        )

        return 0

    except ScannerError as exc:

        logger.error(
            "Scanner error: %s",
            exc,
        )

        return 1

    except Exception:

        logger.error(
            "Unexpected scanner failure:\n%s",
            traceback.format_exc(),
        )

        return 1


if __name__ == "__main__":
    sys.exit(
        main()
    )
