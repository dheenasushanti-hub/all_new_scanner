"""
NIFTY 50 Predictive Options Scanner — V45 Structure-Authoritative Regime and Entry Guard

What this version fixes:
- Uses the NIFTY INDEX as the primary market-price/VWAP/intraday structure feed.
- Uses NIFTY futures price/OI as a separate derivatives confirmation, not the price proxy.
- Uses completed 3-minute NIFTY price action for structural persistence and risk.
- Uses NIFTY futures price/OI regime as a confirmation and positioning factor.
- Uses INDEX VWAP level + VWAP slope/position.
- Compares Call OI vs Put OI at every strike; emits per-strike support/resistance,
  reliability and breakout/breakdown watches; the four market scenarios use futures price + futures OI.
- Uses option-chain OI concentration and Change-in-OI to derive dynamic structural walls.
- Uses ATM +/-4 as the decision scope for local aggregate Change-OI, rolling/cumulative
  COI confirmation, OI guard events, support/resistance, targets, stops, and strike ranking.
  One full-chain response/snapshot is retained for history; no per-strike API calls are added.
- From 09:15-09:45, cumulative COI from the earliest valid same-session snapshot is weighted
  at 0.35; until a baseline exists, only local ATM-window API/chain Change-OI is the fallback.
  From 09:45, valid local 15-30 minute velocity is primary; a neutral valid window is not
  overridden by a day-total score.
- Checks the selected futures contract's symbol/expiry and explicit quote timestamps. Stale
  futures quotes are excluded from secondary derivatives confirmation; unavailable timestamps
  are marked unverified. Basis outliers warn for inspection but never override NIFTY structure.
- Supports early-session classification from at least five completed 3-minute bars when
  indicator-history seeding is unavailable but live VWAP/price structure is aligned.
- Detects confirmed completed-bar breaks of prior OI levels, including a permitted
  opposite-direction re-entry when derivatives confirm the break.
- Blocks new entries when the opposing OI wall leaves insufficient directional runway.
- Separates market-state detection from trade-entry readiness.
- Detects continuous bullish/bearish states, weakening, sideways, and directional watch states; entries are limited to continuous structure.
- Uses persistent continuous-structure entries plus a separately gated, high-confirmation exhaustion reversal scalp; ordinary pullbacks cannot flip an established trend.
- Classifies Direction x Intensity (NORMAL / STRONG / EXHAUSTION / SIDEWAYS).
- Applies time-of-day gates, expiry-day OTM bans, option-premium VWAP filters,
  15-30 minute OI velocity, delta floors, moneyness weighting, and a 5% safety override.
- Enforces a +0.500 minimum score, hard vetoes active OI walls, and disqualifies OI pins.
- Forces new-entry cutoff at 15:15 IST and uses a continuation-aware stagnation guard;
  logs index and futures candle feeds separately.
- Builds NIFTY T1/T2/SL directly from price action + option OI; option Greeks
  are ranking/context only and are not used to forecast target premiums.
- No order placement. The script only creates a signal, persists state,
  and sends email.
- Uses current Upstox endpoints: v2 for option chain/contracts/status/
  instrument search/change-OI/option-chain; v3 for Full Market Quotes and candle data because the
  older v2 intraday candle API is deprecated.

Run:
    python market_scanner_v45_structural_entry_risk_guard.py --self-test
    python market_scanner_v45_structural_entry_risk_guard.py

Environment:
    UPSTOX_ANALYTICS_TOKEN   required
    NIFTY_INSTRUMENT_KEY     optional, default NSE_INDEX|Nifty 50

Optional email:
    EMAIL_SENDER
    EMAIL_PASSWORD
    EMAIL_RECEIVER
    SMTP_HOST (default smtp.gmail.com)
    SMTP_PORT (default 465)

Optional tuning:
    STATE_FILE
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
from dataclasses import asdict, dataclass, field, replace
from datetime import date, datetime, time
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path
from typing import Any, Optional
from zoneinfo import ZoneInfo

import numpy as np
import pandas as pd
import requests

HTTP_SESSION = requests.Session()


# =============================================================================
# CONFIG
# =============================================================================

IST = ZoneInfo("Asia/Kolkata")
BASE_URL = "https://api.upstox.com"

NIFTY_KEY = os.getenv("NIFTY_INSTRUMENT_KEY", "NSE_INDEX|Nifty 50").strip()
UPSTOX_TOKEN = os.getenv("UPSTOX_ANALYTICS_TOKEN", "").strip()

EMAIL_SENDER = os.getenv("EMAIL_SENDER", "").strip()
EMAIL_PASSWORD = os.getenv("EMAIL_PASSWORD", "").strip()
EMAIL_RECEIVER = os.getenv("EMAIL_RECEIVER", "").strip()
SMTP_HOST = os.getenv("SMTP_HOST", "smtp.gmail.com").strip()
SMTP_PORT = int(os.getenv("SMTP_PORT", "465"))

REQUEST_TIMEOUT = int(os.getenv("REQUEST_TIMEOUT", "12"))

# Price-action regime thresholds.
REGIME_SIDEWAYS_RANGE_ATR = float(os.getenv("REGIME_SIDEWAYS_RANGE_ATR", "2.40"))
REGIME_SIDEWAYS_NET_ATR = float(os.getenv("REGIME_SIDEWAYS_NET_ATR", "0.45"))
REGIME_SIDEWAYS_VWAP_DISTANCE_ATR = float(os.getenv("REGIME_SIDEWAYS_VWAP_DISTANCE_ATR", "0.90"))
REGIME_SIDEWAYS_ALTERNATION = float(os.getenv("REGIME_SIDEWAYS_ALTERNATION", "0.35"))
MIN_ENTRY_TIME = time(9, 18)
OPENING_MIN_COMPLETED_BARS = max(4, int(os.getenv("OPENING_MIN_COMPLETED_BARS", "5")))
MIN_OPPOSING_WALL_CLEARANCE_STEPS = max(0.5, float(os.getenv("MIN_OPPOSING_WALL_CLEARANCE_STEPS", "1.5")))
OI_DOMINANCE_RELIABILITY_RATIO = max(1.01, float(os.getenv("OI_DOMINANCE_RELIABILITY_RATIO", "1.20")))
LOCAL_BREAK_MIN_PRESSURE = min(-0.05, float(os.getenv("LOCAL_BREAK_MIN_PRESSURE", "-0.20")))
# Counter-trend OI-wall rejection entries must still have enough structural runway.
MIN_STRUCTURAL_ENTRY_REWARD_RISK_RATIO = max(1.0, float(os.getenv("MIN_STRUCTURAL_ENTRY_REWARD_RISK_RATIO", os.getenv("LOCAL_REJECTION_MIN_REWARD_RISK_RATIO", "1.25"))))

# Hard limit for all primary option-strike decisions: ATM plus/minus four strike steps.
ATM_ANALYSIS_RADIUS_LEVELS = 4
COI_WINDOW_MIN_COVERAGE_FRACTION = min(1.0, max(0.50, float(os.getenv("COI_WINDOW_MIN_COVERAGE_FRACTION", "0.60"))))
FUTURES_QUOTE_MAX_AGE_SECONDS = max(30, int(os.getenv("FUTURES_QUOTE_MAX_AGE_SECONDS", "180")))
FUTURES_BASIS_WARNING_PCT = max(0.001, float(os.getenv("FUTURES_BASIS_WARNING_PCT", "0.004")))
# A weakening nearby OI wall can arm a breakout watch, but never substitutes for
# a price-confirmed breakout. The scan reports the watch explicitly rather than
# silently treating the setup as an executable breakout.
BREAKOUT_WATCH_MAX_DISTANCE_STEPS = max(
    0.5, float(os.getenv("BREAKOUT_WATCH_MAX_DISTANCE_STEPS", "1.5"))
)


# Market-state memory. This prevents a neutral scan from erasing the last
# decisive directional regime.
STATE_HISTORY_LIMIT = int(os.getenv("STATE_HISTORY_LIMIT", "60"))


# Anchor the default state path to this script, not the process working directory.
# Scheduler jobs and interactive runs must load the same OI history unless STATE_FILE
# explicitly points elsewhere. Relative overrides are resolved against this script.
_state_file_override = os.getenv("STATE_FILE", "").strip()
if _state_file_override:
    _state_path = Path(_state_file_override).expanduser()
    STATE_FILE = _state_path if _state_path.is_absolute() else (Path.cwd() / _state_path).resolve()
else:
    STATE_FILE = Path(__file__).resolve().parent / "state" / "market_state.json"

SCANNER_VERSION = "2026-10-15-STRUCTURE-V45-ADX-STRENGTH-ONLY-PERSISTENCE-REGIME-ALIGNMENT-ATM4"
# PA/OI target construction is unchanged; keep the V30 target engine identifier so
# existing live trades are not needlessly re-migrated by entry-filter-only changes.
OPTION_TARGET_ENGINE_VERSION = "V30_DYNAMIC_COI_MATRIX_PA_OI"

MARKET_START = time(9, 15)
MARKET_END = time(15, 30)
NEW_ENTRY_CUTOFF = time(15, 15)
OPENING_END = time(10, 30)
MIDDAY_END = time(13, 30)

ATR_PERIOD = 14
ADX_PERIOD = int(os.getenv("ADX_PERIOD", "14"))
REGIME_INDICATOR_HISTORY_BARS = max(2 * ADX_PERIOD + 30, int(os.getenv("REGIME_INDICATOR_HISTORY_BARS", "300")))
REGIME_INDICATOR_CACHE_RETRY_SECONDS = max(60, int(os.getenv("REGIME_INDICATOR_CACHE_RETRY_SECONDS", "300")))
REGIME_INDICATOR_CACHE_KEY = "regime_indicator_history_cache"
FUTURES_HISTORY_CACHE_KEY = "futures_oi_history_cache"
FUTURES_HISTORY_CACHE_BARS = 60
ADX_SIDEWAYS_THRESHOLD = float(os.getenv("ADX_SIDEWAYS_THRESHOLD", "20"))
ADX_STRONG_THRESHOLD = float(os.getenv("ADX_STRONG_THRESHOLD", "25"))
MIDDAY_MIN_ADX = float(os.getenv("MIDDAY_MIN_ADX", "23"))
# Retained as a backward-compatible environment setting for older deployments.
# It is intentionally not used as an extra hard veto for a PA/OI-confirmed
# continuous trend; structural confirmation is authoritative and direction flips
# use a separate, explicit two-bar confirmation policy below.
MIDDAY_MIN_PERSISTENCE = int(os.getenv("MIDDAY_MIN_PERSISTENCE", "3"))
STRONG_VOLUME_MULTIPLIER = float(os.getenv("STRONG_VOLUME_MULTIPLIER", "1.20"))
OPTION_OI_MIN_AGE_MINUTES = int(os.getenv("OPTION_OI_MIN_AGE_MINUTES", "15"))
OPTION_OI_MAX_AGE_MINUTES = int(os.getenv("OPTION_OI_MAX_AGE_MINUTES", "30"))
OPTION_OI_HISTORY_KEEP_MINUTES = int(os.getenv("OPTION_OI_HISTORY_KEEP_MINUTES", "60"))
COI_COLD_START_END = time(9, 45)
COI_COLD_START_WEIGHT = float(os.getenv("COI_COLD_START_WEIGHT", "0.35"))
COI_STRONG_CHANGE_PCT = float(os.getenv("COI_STRONG_CHANGE_PCT", "0.01"))
COI_PUSH_MAX_POINTS = float(os.getenv("COI_PUSH_MAX_POINTS", "1.0"))
COI_FLOOR_MAX_POINTS = float(os.getenv("COI_FLOOR_MAX_POINTS", "1.0"))
COI_ROLL_MAX_POINTS = float(os.getenv("COI_ROLL_MAX_POINTS", "1.5"))
COI_WALL_MAX_PENALTY = float(os.getenv("COI_WALL_MAX_PENALTY", "1.5"))
COI_UNDERLYING_MOVE_PCT = float(os.getenv("COI_UNDERLYING_MOVE_PCT", "0.001"))
STAGNATION_RANGE_PCT = float(os.getenv("STAGNATION_RANGE_PCT", "0.001"))
STAGNATION_REQUIRED_BARS = int(os.getenv("STAGNATION_REQUIRED_BARS", "3"))
# A directional move of at least this fraction over the three 5m bars can suppress
# the stagnation exit, but only when the active trade direction, index VWAP and COI agree.
STAGNATION_MIN_FAVORABLE_PROGRESS_PCT = max(0.0, float(os.getenv("STAGNATION_MIN_FAVORABLE_PROGRESS_PCT", "0.0001")))
OPENING_MAX_SPREAD_PCT = float(os.getenv("OPENING_MAX_SPREAD_PCT", "0.08"))
MIN_EXECUTION_SCORE = min(1.0, max(0.0, float(os.getenv("MIN_EXECUTION_SCORE", "0.500"))))

# Option-flow classification threshold.
STRUCTURE_ACTIVITY_PRICE_NOISE_PCT = float(os.getenv("STRUCTURE_ACTIVITY_PRICE_NOISE_PCT", "0.002"))
PCR_BULL_THRESHOLD = 1.10
PCR_BEAR_THRESHOLD = 0.90

# Futures price/OI is secondary context only; this threshold is never used
# to decide the primary NIFTY market direction.
FUTURES_OI_MIN_PERSISTENCE = float(os.getenv("FUTURES_OI_MIN_PERSISTENCE", "0.50"))

# PRIMARY MARKET-STRUCTURE ENGINE
# The hierarchy is intentionally explicit:
#   1) NIFTY price relative to VWAP defines the directional environment
#   2) Option OI + Change-OI define authoritative structural support/resistance
#   3) Multi-window NIFTY price movement establishes persistence
#   4) Change-OI confirms the same direction
#   5) A support/resistance break strengthens the signal but is not required
#      for an already-established continuous trend
# Futures price/OI and PCR are context only; neither can override PA/VWAP/Change-OI structure.
STRUCTURE_BREAK_BUFFER_ATR = float(os.getenv("STRUCTURE_BREAK_BUFFER_ATR", "0.08"))
STRUCTURE_HOLD_BARS = int(os.getenv("STRUCTURE_HOLD_BARS", "2"))
STRUCTURE_CHANGE_OI_CONFIRM = float(os.getenv("STRUCTURE_CHANGE_OI_CONFIRM", "0.08"))
STRUCTURE_CHANGE_OI_STRONG = float(os.getenv("STRUCTURE_CHANGE_OI_STRONG", "0.20"))
STRUCTURE_CHANGE_OI_CONFLICT = float(os.getenv("STRUCTURE_CHANGE_OI_CONFLICT", "0.35"))
# A strong opposite futures price/OI regime blocks a fresh option entry; it does
# not independently reverse the NIFTY structure.
STRUCTURE_FUTURES_CONFLICT_STRENGTH = float(os.getenv("STRUCTURE_FUTURES_CONFLICT_STRENGTH", "0.50"))
STRUCTURE_VWAP_RECLAIM_BUFFER_ATR = float(os.getenv("STRUCTURE_VWAP_RECLAIM_BUFFER_ATR", "0.05"))
# Structural levels are option-OI levels. Price swings are retained only as
# secondary context for risk/targets and are never silently substituted into
# the authoritative support/resistance decision.
# Continuous-trend classification: a small countertrend move is a pullback,
# not a regime reversal, while a material multi-bar recovery can weaken the
# directional state.

# Entry confirmation controls. One scanner pass is sufficient once the overall
# market is aligned; forcing two polls would delay fast reversal/continuation entries.
# Require the same directional regime on two distinct completed 3-minute bars.
# This suppresses one-scan opening noise and rapid CE/PE reversals.
CONTINUATION_CONFIRMATIONS_REQUIRED = int(
    os.getenv("CONTINUATION_CONFIRMATIONS_REQUIRED", "2")
)

# Active-trade protection uses 1m OHLC when available so an intrabar stop/target
# is not silently missed between the normal scanner polls.
ACTIVE_TRADE_INTRABAR_MONITOR = os.getenv(
    "ACTIVE_TRADE_INTRABAR_MONITOR", "1"
).strip().lower() not in {"0", "false", "no"}
# A 1m option stop is only allowed to close a trade when the NIFTY index itself
# has breached the structural stop. This keeps the option SL subordinate to the
# underlying market structure instead of allowing IV/theta/option noise to
# terminate a structurally-valid NIFTY trend.
ACTIVE_TRADE_REQUIRE_UNDERLYING_CONFIRMATION = os.getenv(
    "ACTIVE_TRADE_REQUIRE_UNDERLYING_CONFIRMATION", "1"
).strip().lower() not in {"0", "false", "no"}
# Number of recent 1m bars inspected on each scan. The monitor additionally
# filters these bars to the period after the trade was opened / last checked.
ACTIVE_TRADE_INTRABAR_LOOKBACK = int(
    os.getenv("ACTIVE_TRADE_INTRABAR_LOOKBACK", "15")
)
MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED = int(
    os.getenv("MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED", "2")
)

# Do not immediately re-enter the same direction after a completed trade.
# A fresh completed 3m bar is required, and the short cooldown prevents
# stop -> new strike -> stop churn when ATM moves between two strikes.
REENTRY_COOLDOWN_MINUTES = int(os.getenv("REENTRY_COOLDOWN_MINUTES", "6"))
REENTRY_REQUIRE_NEW_3M_BAR = os.getenv("REENTRY_REQUIRE_NEW_3M_BAR", "1").strip().lower() not in {"0", "false", "no"}
STRUCTURAL_STOP_CONFIRM_BARS = int(os.getenv("STRUCTURAL_STOP_CONFIRM_BARS", "1"))



# Strike health.
MAX_SPREAD_PCT = 0.12
# Theta burden is retained for reporting/diagnostics only; it is not a direct
# score term or hard gate. Price structure and execution-quality gates remain primary.
MIN_OI = 100.0
MIN_VOLUME = 1.0

# Price-action + OI structural trade levels. These levels are authoritative;
# option Greeks are not used to manufacture T1/T2/SL prices.
PA_OI_SWING_LOOKBACK = int(os.getenv("PA_OI_SWING_LOOKBACK", "12"))
PA_OI_STOP_BUFFER_STEPS = float(os.getenv("PA_OI_STOP_BUFFER_STEPS", "0.25"))
PA_OI_SECONDARY_OI_RATIO = float(os.getenv("PA_OI_SECONDARY_OI_RATIO", "0.30"))

# T1/T2/SL are no longer option-Greek-derived.
# They are authoritative NIFTY structural levels from current PA + OI.

# Trade monitoring.

# Phase-aware state thresholds. These classify market movement separately from
# entry readiness, so conflicting derivatives can mark a weakening trend
# without falsely flipping the market direction.

# URLs.
INSTRUMENT_SEARCH_URL = f"{BASE_URL}/v2/instruments/search"
OPTION_CONTRACT_URL = f"{BASE_URL}/v2/option/contract"
OPTION_CHAIN_URL = f"{BASE_URL}/v2/option/chain"
MARKET_QUOTE_URL = f"{BASE_URL}/v3/market-quote/quotes"
MARKET_STATUS_URL = f"{BASE_URL}/v2/market/status/NSE"
CHANGE_OI_URL = f"{BASE_URL}/v2/market/change-oi"
HISTORICAL_V3_URL = f"{BASE_URL}/v3/historical-candle"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
)
logger = logging.getLogger("nifty_scanner")


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
    theta: float
    spread_pct: float
    theta_burden_pct_day: float
    premium_vwap: float = float("nan")
    flow_score: float = float("nan")
    vwap_score: float = float("nan")
    oi_momentum_score: float = float("nan")
    delta_weight: float = float("nan")
    call_oi_change_pct_15m: float = float("nan")
    put_oi_change_pct_15m: float = float("nan")
    oi_velocity_baseline_minutes: float = float("nan")
    market_intensity: str = "UNKNOWN"
    coi_push_score: float = 0.0
    coi_floor_score: float = 0.0
    coi_roll_score: float = 0.0
    coi_wall_penalty: float = 0.0
    coi_matrix_label: str = "UNAVAILABLE"
    coi_baseline_mode: str = "UNAVAILABLE"
    total_score: float = float("nan")


def execution_veto_reason(
    total_score: Optional[float],
    *,
    coi_label: str = "",
    wall_penalty: float = 0.0,
    disqualified: bool = False,
) -> str:
    """Return a hard execution veto reason; empty string means the candidate passes."""
    label = str(coi_label or "").upper()
    if disqualified or "PIN_DISQUALIFICATION" in label or "PIN_DISQUALIFIED" in label:
        return "PIN_DISQUALIFICATION"
    if safe_float(wall_penalty, 0.0) > 0.0 or "WALL_PENALTY" in label:
        return "WALL_PENALTY_VETO"
    if total_score is not None:
        score = safe_float(total_score, float("nan"))
        if not math.isfinite(score) or score < MIN_EXECUTION_SCORE:
            return f"MINIMUM_QUALITY_SCORE_VETO score={score:.3f} required>={MIN_EXECUTION_SCORE:.3f}"
    return ""


@dataclass(frozen=True)
class StructureResult:
    direction: str
    score: float
    confidence: float
    interpretation: str
    components: dict[str, Any]
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
    theta: float
    support_1: float
    support_2: float
    resistance_1: float
    resistance_2: float
    reasons: list[str]
    market_intensity: str = "NORMAL"


@dataclass
class MarketSnapshot:
    """Typed view of a persisted market snapshot with unknown fields preserved."""
    timestamp: str = ""
    spot: Optional[float] = None
    direction: str = "NEUTRAL"
    market_phase: str = ""
    persistent_direction: Optional[str] = None
    latest_completed_3m_bar: str = ""
    extra: dict[str, Any] = field(default_factory=dict, repr=False)
    present_keys: set[str] = field(default_factory=set, repr=False)
    raw_spot_value: Any = field(default=None, repr=False)

    @classmethod
    def from_mapping(cls, raw: Any) -> "MarketSnapshot":
        data = raw if isinstance(raw, dict) else {}
        known = {"timestamp", "spot", "direction", "market_phase", "persistent_direction", "latest_completed_3m_bar"}
        raw_spot = data.get("spot")
        spot_value: Optional[float]
        try:
            spot_value = float(raw_spot) if raw_spot is not None and math.isfinite(float(raw_spot)) else None
        except (TypeError, ValueError, OverflowError):
            spot_value = None
        return cls(
            timestamp=str(data.get("timestamp", "")), spot=spot_value,
            direction=str(data.get("direction", "NEUTRAL")),
            market_phase=str(data.get("market_phase", "")),
            persistent_direction=(str(data["persistent_direction"]) if data.get("persistent_direction") is not None else None),
            latest_completed_3m_bar=str(data.get("latest_completed_3m_bar", "")),
            extra={key: value for key, value in data.items() if key not in known},
            present_keys=set(data), raw_spot_value=raw_spot,
        )

    def to_mapping(self) -> dict[str, Any]:
        # Preserve malformed historical values byte-for-byte at the JSON-value
        # level; scanners still consume the typed finite value (None on failure).
        spot_output = self.spot
        if self.spot is None and "spot" in self.present_keys:
            spot_output = self.raw_spot_value
        values = {
            "timestamp": self.timestamp, "spot": spot_output, "direction": self.direction,
            "market_phase": self.market_phase, "persistent_direction": self.persistent_direction,
            "latest_completed_3m_bar": self.latest_completed_3m_bar,
        }
        result = dict(self.extra)
        defaults = {"timestamp": "", "spot": None, "direction": "NEUTRAL", "market_phase": "", "persistent_direction": None, "latest_completed_3m_bar": ""}
        for key, value in values.items():
            if key in self.present_keys or value != defaults[key]:
                result[key] = value
        return result


@dataclass
class ActiveTradeState:
    """Typed view of an active trade; extra keys preserve older/newer state versions."""
    status: str = ""
    trade_date: str = ""
    opened_at: str = ""
    direction: str = ""
    instrument_key: str = ""
    trading_symbol: str = ""
    entry: Optional[float] = None
    target_1: Optional[float] = None
    target_2: Optional[float] = None
    stop_loss: Optional[float] = None
    extra: dict[str, Any] = field(default_factory=dict, repr=False)
    present_keys: set[str] = field(default_factory=set, repr=False)
    raw_numeric_values: dict[str, Any] = field(default_factory=dict, repr=False)

    @classmethod
    def from_mapping(cls, raw: Any) -> "ActiveTradeState":
        data = raw if isinstance(raw, dict) else {}
        known = {"status", "trade_date", "opened_at", "direction", "instrument_key", "trading_symbol", "entry", "target_1", "target_2", "stop_loss"}
        def optional_number(key: str) -> Optional[float]:
            try:
                value = float(data[key])
                return value if math.isfinite(value) else None
            except (KeyError, TypeError, ValueError, OverflowError):
                return None
        numeric_keys = {"entry", "target_1", "target_2", "stop_loss"}
        parsed_numeric = {key: optional_number(key) for key in numeric_keys}
        raw_numeric = {
            key: data[key] for key in numeric_keys
            if key in data and parsed_numeric[key] is None and data[key] is not None
        }
        return cls(
            status=str(data.get("status", "")), trade_date=str(data.get("trade_date", "")),
            opened_at=str(data.get("opened_at", "")), direction=str(data.get("direction", "")),
            instrument_key=str(data.get("instrument_key", "")), trading_symbol=str(data.get("trading_symbol", "")),
            entry=parsed_numeric["entry"], target_1=parsed_numeric["target_1"],
            target_2=parsed_numeric["target_2"], stop_loss=parsed_numeric["stop_loss"],
            extra={key: value for key, value in data.items() if key not in known},
            present_keys=set(data), raw_numeric_values=raw_numeric,
        )

    def to_mapping(self) -> dict[str, Any]:
        values = {
            "status": self.status, "trade_date": self.trade_date, "opened_at": self.opened_at,
            "direction": self.direction, "instrument_key": self.instrument_key,
            "trading_symbol": self.trading_symbol, "entry": self.entry,
            "target_1": self.target_1, "target_2": self.target_2, "stop_loss": self.stop_loss,
        }
        result = dict(self.extra)
        for key, value in values.items():
            if key in self.raw_numeric_values and value is None:
                result[key] = self.raw_numeric_values[key]
            elif key in self.present_keys or value not in (None, ""):
                result[key] = value
        return result


@dataclass
class MarketMemory:
    """Typed view of persistent direction and rolling market history."""
    market_history: list[dict[str, Any]] = field(default_factory=list)
    persistent_direction: Optional[str] = None
    continuation_phase: str = ""
    continuation_count: int = 0
    continuation_last_bar: str = ""
    scanner_version: str = ""

    @classmethod
    def from_state(cls, state: dict[str, Any]) -> "MarketMemory":
        history_raw = state.get("market_history")
        history = [dict(item) for item in history_raw if isinstance(item, dict)] if isinstance(history_raw, list) else []
        try:
            count = max(0, int(state.get("continuation_count", 0)))
        except (TypeError, ValueError, OverflowError):
            count = 0
        direction = str(state.get("persistent_direction", "")).upper() or None
        return cls(
            market_history=history, persistent_direction=direction,
            continuation_phase=str(state.get("continuation_phase", "")),
            continuation_count=count, continuation_last_bar=str(state.get("continuation_last_bar", "")),
            scanner_version=str(state.get("scanner_version", "")),
        )

    def append_history(self, item: dict[str, Any], limit: int = STATE_HISTORY_LIMIT) -> None:
        self.market_history.append(dict(item))
        self.market_history = self.market_history[-max(1, int(limit)):]


class ScannerError(Exception):
    """Expected scanner/API failure."""


class UpstoxDataProvider:
    """Owns HTTP access and response normalization for Upstox data endpoints."""

    def __init__(
        self,
        token: Optional[str] = None,
        *,
        session: Optional[requests.Session] = None,
        timeout: int = REQUEST_TIMEOUT,
    ) -> None:
        self.token = (UPSTOX_TOKEN if token is None else token).strip()
        self.session = session if session is not None else HTTP_SESSION
        self.timeout = max(1, int(timeout))

    def api_headers(self) -> dict[str, str]:
        if not self.token:
            raise ScannerError("UPSTOX_ANALYTICS_TOKEN is missing. Set it in the environment.")
        return {
            "Accept": "application/json",
            "Content-Type": "application/json",
            "Authorization": f"Bearer {self.token}",
        }

    def api_get(
        self,
        url: str,
        params: Optional[dict[str, Any]] = None,
        retries: int = 3,
    ) -> dict[str, Any]:
        last_error = "Unknown Upstox error."
        attempts = max(1, int(retries))
        for attempt in range(1, attempts + 1):
            try:
                response = self.session.get(
                    url, params=params, headers=self.api_headers(), timeout=self.timeout
                )
            except requests.RequestException as exc:
                last_error = f"Network error: {exc}"
                if attempt < attempts:
                    time_module.sleep(attempt)
                    continue
                raise ScannerError(last_error) from exc
            if response.status_code == 200:
                try:
                    payload = response.json()
                except ValueError as exc:
                    raise ScannerError(f"Upstox returned invalid JSON from {url}") from exc
                if not isinstance(payload, dict):
                    raise ScannerError(f"Unexpected Upstox payload from {url}.")
                if str(payload.get("status", "")).lower() == "error":
                    raise ScannerError(json.dumps(payload)[:2000])
                return payload
            last_error = f"Upstox HTTP {response.status_code} | {url} | {response.text[:1500]}"
            if response.status_code in {429, 500, 502, 503, 504} and attempt < attempts:
                time_module.sleep(min(2 * attempt, 6))
                continue
            raise ScannerError(last_error)
        raise ScannerError(last_error)

    def get_quote(self, instrument_key: str) -> dict[str, Any]:
        payload = self.api_get(MARKET_QUOTE_URL, {"instrument_key": instrument_key}, retries=3)
        data = payload.get("data", {})
        if not isinstance(data, dict):
            raise ScannerError("Upstox quote data is not an object.")
        if instrument_key in data:
            return data[instrument_key]
        colon_key = instrument_key.replace("|", ":", 1)
        if colon_key in data:
            return data[colon_key]
        if len(data) == 1:
            only_quote = next(iter(data.values()))
            if isinstance(only_quote, dict):
                return only_quote
        raise ScannerError(f"Quote not found for {instrument_key}.")

    def get_intraday_candles(
        self,
        instrument_key: str,
        interval_minutes: int,
        *,
        strict: bool = True,
    ) -> pd.DataFrame:
        interval = int(interval_minutes)
        if interval <= 0:
            raise ValueError("interval_minutes must be positive")
        encoded = urllib.parse.quote(instrument_key, safe="")
        url = f"{HISTORICAL_V3_URL}/intraday/{encoded}/minutes/{interval}"
        try:
            payload = self.api_get(url, retries=3)
        except ScannerError:
            if strict:
                raise
            return pd.DataFrame()
        data = payload.get("data", {})
        df = _parse_candles(data.get("candles", []) if isinstance(data, dict) else [])
        if df.empty:
            if strict:
                raise ScannerError(f"No intraday {interval}m candles for {instrument_key}.")
            return pd.DataFrame()
        session_date = now_ist().date()
        local_dates = df["timestamp"].dt.tz_convert(IST).dt.date
        df = df.loc[local_dates == session_date].reset_index(drop=True)
        if df.empty and strict:
            raise ScannerError(f"No current-session {interval}m candles for {instrument_key}.")
        return df

    def _nearest_active_option_expiry(self) -> str:
        payload = self.api_get(OPTION_CONTRACT_URL, {"instrument_key": NIFTY_KEY}, retries=4)
        contracts = payload.get("data", [])
        if not isinstance(contracts, list) or not contracts:
            raise ScannerError("No active NIFTY option contracts returned by Upstox.")
        today = now_ist().date()
        expiries: list[date] = []
        for contract in contracts:
            if not isinstance(contract, dict):
                continue
            expiry = parse_date(str(contract.get("expiry", "")))
            if expiry is not None and expiry >= today:
                expiries.append(expiry)
        if not expiries:
            raise ScannerError(f"No active NIFTY option expiry found on or after {today.isoformat()}.")
        selected = min(expiries).isoformat()
        logger.info("Selected nearest active NIFTY option expiry: %s", selected)
        return selected

    def get_option_chain(
        self,
        state: Optional[dict[str, Any]] = None,
    ) -> tuple[str, list[dict[str, Any]]]:
        expiry: Optional[str] = None
        today = now_ist().date()
        if isinstance(state, dict):
            cached_expiry = parse_date(str(state.get("option_expiry", "")))
            if cached_expiry and cached_expiry >= today:
                expiry = cached_expiry.isoformat()
        if not expiry:
            expiry = self._nearest_active_option_expiry()
            if isinstance(state, dict):
                state["option_expiry"] = expiry
        payload = self.api_get(
            OPTION_CHAIN_URL,
            {"instrument_key": NIFTY_KEY, "expiry_date": expiry},
            retries=4,
        )
        data = payload.get("data", [])
        if not isinstance(data, list) or not data:
            raise ScannerError(f"NIFTY option chain is empty for active expiry {expiry}.")
        filtered = [
            row for row in data
            if isinstance(row, dict) and str(row.get("expiry", ""))[:10] == expiry[:10]
        ]
        if filtered:
            data = filtered
        logger.info("Loaded option chain: expiry=%s rows=%d", expiry, len(data))
        return expiry, data


DEFAULT_DATA_PROVIDER = UpstoxDataProvider()


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


def classify_price_oi_scenario(price_delta: Any, oi_delta: Any) -> str:
    """Map directional price/OI changes to the standard four derivatives scenarios."""
    p = safe_float(price_delta, 0.0)
    o = safe_float(oi_delta, 0.0)
    if p > 0 and o > 0:
        return "LONG_BUILDUP"
    if p < 0 and o > 0:
        return "SHORT_BUILDUP"
    if p > 0 and o < 0:
        return "SHORT_COVERING"
    if p < 0 and o < 0:
        return "LONG_UNWINDING"
    return "NEUTRAL"


def classify_strike_oi_state(
    strike: float,
    spot: float,
    call_oi: float,
    put_oi: float,
    call_oi_change: float,
    put_oi_change: float,
    underlying_move: float,
    step: float,
    min_call_oi: float = 0.0,
    min_put_oi: float = 0.0,
) -> dict[str, Any]:
    """Classify a single strike by OI dominance and change-OI/price confirmation.

    OI dominance sets the strike's base role. A wall can be called reliable only
    when the dominant-side OI is material relative to the chain. Classic market
    scenarios are NOT inferred from spot movement plus an option's OI change;
    those refer to different instruments. A confirmed potential breakout/breakdown
    may be labelled Short Covering / Long Unwinding as a strike-level watch only.
    """
    c_oi = max(safe_float(call_oi), 0.0)
    p_oi = max(safe_float(put_oi), 0.0)
    c_chg = safe_float(call_oi_change)
    p_chg = safe_float(put_oi_change)
    step_value = max(safe_float(step, 50.0), 1.0)
    near_level = abs(safe_float(spot) - safe_float(strike)) <= 1.5 * step_value

    reliable_call_wall = c_oi >= max(0.0, safe_float(min_call_oi, 0.0))
    reliable_put_wall = p_oi >= max(0.0, safe_float(min_put_oi, 0.0))
    if c_oi > p_oi:
        dominant_role = "RESISTANCE"
        dominance_ratio = c_oi / max(p_oi, 1.0)
        call_unwinding = c_chg < -max(1.0, 0.002 * c_oi)
        if reliable_call_wall and underlying_move > 0 and call_unwinding and (near_level or spot >= strike):
            state = "POTENTIAL_BREAKOUT_SHORT_COVERING"
            reliability = "BREAKOUT_WATCH"
            scenario = "SHORT_COVERING"
        elif reliable_call_wall and dominance_ratio >= OI_DOMINANCE_RELIABILITY_RATIO and c_chg >= -max(1.0, 0.002 * c_oi):
            state = "RELIABLE_RESISTANCE"
            reliability = "HIGH"
            scenario = "UNCONFIRMED"
        else:
            state = "RESISTANCE"
            reliability = "MODERATE"
            scenario = "UNCONFIRMED"
    elif p_oi > c_oi:
        dominant_role = "SUPPORT"
        dominance_ratio = p_oi / max(c_oi, 1.0)
        put_unwinding = p_chg < -max(1.0, 0.002 * p_oi)
        if reliable_put_wall and underlying_move < 0 and put_unwinding and (near_level or spot <= strike):
            state = "POTENTIAL_BREAKDOWN_LONG_UNWINDING"
            reliability = "BREAKDOWN_WATCH"
            scenario = "LONG_UNWINDING"
        elif reliable_put_wall and dominance_ratio >= OI_DOMINANCE_RELIABILITY_RATIO and p_chg >= -max(1.0, 0.002 * p_oi):
            state = "RELIABLE_SUPPORT"
            reliability = "HIGH"
            scenario = "UNCONFIRMED"
        else:
            state = "SUPPORT"
            reliability = "MODERATE"
            scenario = "UNCONFIRMED"
    else:
        dominant_role = "BALANCED"
        dominance_ratio = 1.0 if c_oi > 0 else 0.0
        state = "BALANCED_OI"
        reliability = "LOW"
        scenario = "UNCONFIRMED"

    return {
        "strike": float(strike),
        "call_oi": c_oi,
        "put_oi": p_oi,
        "call_oi_change": c_chg,
        "put_oi_change": p_chg,
        "dominant_role": dominant_role,
        "dominance_ratio": float(dominance_ratio),
        "state": state,
        "reliability": reliability,
        "scenario": scenario,
    }


def _oi_role_row(oi_structure_by_strike: Optional[dict[str, Any]], level: float) -> dict[str, Any]:
    """Return the current-window OI classification row for an exact strike."""
    mapping = oi_structure_by_strike if isinstance(oi_structure_by_strike, dict) else {}
    direct = mapping.get(f"{float(level):.0f}")
    if isinstance(direct, dict):
        return direct
    for key, row in mapping.items():
        if isinstance(row, dict) and abs(safe_float(key, float("nan")) - float(level)) <= 0.01:
            return row
    return {}


def _oi_role_is_confirmed(
    oi_structure_by_strike: Optional[dict[str, Any]], level: float, role: str
) -> bool:
    """Only allow remembered walls to trigger if the current chain still validates that role."""
    row = _oi_role_row(oi_structure_by_strike, level)
    wanted = str(role or "").upper()
    dominant = str(row.get("dominant_role", "")).upper()
    state = str(row.get("state", "")).upper()
    reliability = str(row.get("reliability", "")).upper()
    if wanted == "SUPPORT":
        return dominant == "SUPPORT" and (
            state in {"RELIABLE_SUPPORT", "POTENTIAL_BREAKDOWN_LONG_UNWINDING"}
            or reliability == "HIGH"
        )
    if wanted == "RESISTANCE":
        return dominant == "RESISTANCE" and (
            state in {"RELIABLE_RESISTANCE", "POTENTIAL_BREAKOUT_SHORT_COVERING"}
            or reliability == "HIGH"
        )
    return False


def detect_confirmed_local_oi_break(
    price_session: pd.DataFrame,
    *,
    spot: float,
    support: float,
    resistance: float,
    previous_snapshot: Optional[dict[str, Any]],
    chain_levels: dict[str, Any],
    futures_regime: str,
    pressure_score: float,
    oi_structure_by_strike: Optional[dict[str, Any]] = None,
    strike_step_value: float = 50.0,
) -> dict[str, Any]:
    """Confirm a real break of a valid support/resistance level, not a stale weak level.

    Current-window support is only a bearish breakdown candidate and current-window
    resistance only a bullish breakout candidate. Remembered prior levels are allowed
    only when the current OI map still confirms their role with high reliability.
    A held-break recovery requires two completed closes beyond a material buffer.
    """
    empty = {
        "confirmed": False, "direction": "NEUTRAL", "level": float("nan"),
        "kind": "", "reason": "NO_CONFIRMED_BREAK_OR_INSUFFICIENT_BARS",
    }
    completed = (
        filter_completed_candles(price_session, 3)
        if price_session is not None and not price_session.empty else pd.DataFrame()
    )
    if len(completed) < 2:
        return empty
    work = completed.sort_values("timestamp").drop_duplicates("timestamp", keep="last").reset_index(drop=True)
    prev, last = work.iloc[-2], work.iloc[-1]
    prev_close = safe_float(prev.get("close"), float("nan"))
    last_close = safe_float(last.get("close"), float("nan"))
    last_open = safe_float(last.get("open"), float("nan"))
    spot_value = safe_float(spot, float("nan"))
    if not all(math.isfinite(x) for x in (prev_close, last_close, last_open, spot_value)):
        return empty

    window_low = safe_float(chain_levels.get("window_lower_bound"), float("nan"))
    window_high = safe_float(chain_levels.get("window_upper_bound"), float("nan"))
    has_window = math.isfinite(window_low) and math.isfinite(window_high) and window_low <= window_high

    def in_window(level: float) -> bool:
        return math.isfinite(level) and level > 0 and (
            not has_window or window_low - 0.01 <= level <= window_high + 0.01
        )

    current_support = safe_float(support, float("nan"))
    current_resistance = safe_float(resistance, float("nan"))
    support_levels: list[float] = []
    resistance_levels: list[float] = []
    if in_window(current_support) and current_support < spot_value:
        support_levels.append(current_support)
    if in_window(current_resistance) and current_resistance > spot_value:
        resistance_levels.append(current_resistance)

    prior_support_levels: list[float] = []
    prior_resistance_levels: list[float] = []
    for raw in (
        safe_float((previous_snapshot or {}).get("support_1"), float("nan")),
        safe_float(chain_levels.get("previous_support_1"), float("nan")),
    ):
        value = safe_float(raw, float("nan"))
        if (in_window(value) and _oi_role_is_confirmed(oi_structure_by_strike, value, "SUPPORT")
                and all(abs(value - old) > 0.01 for old in prior_support_levels)):
            prior_support_levels.append(value)
            if all(abs(value - old) > 0.01 for old in support_levels):
                support_levels.append(value)
    for raw in (
        safe_float((previous_snapshot or {}).get("resistance_1"), float("nan")),
        safe_float(chain_levels.get("previous_resistance_1"), float("nan")),
    ):
        value = safe_float(raw, float("nan"))
        if (in_window(value) and _oi_role_is_confirmed(oi_structure_by_strike, value, "RESISTANCE")
                and all(abs(value - old) > 0.01 for old in prior_resistance_levels)):
            prior_resistance_levels.append(value)
            if all(abs(value - old) > 0.01 for old in resistance_levels):
                resistance_levels.append(value)

    if not support_levels and not resistance_levels:
        return empty
    atr_series = calculate_atr(work, ATR_PERIOD)
    atr = safe_float(atr_series.iloc[-1], 0.0) if not atr_series.empty else 0.0
    step = max(safe_float(strike_step_value, 50.0), 1.0)
    # Require a meaningful close beyond the wall; a fraction-of-a-point breach is not enough.
    buffer = max(0.10 * atr, 0.10 * step, spot_value * 0.00008, 2.0)
    pressure = safe_float(pressure_score)
    fut = str(futures_regime or "").upper()
    bearish_confirm = pressure <= LOCAL_BREAK_MIN_PRESSURE or fut in {"LONG_UNWINDING", "SHORT_BUILDUP"}
    bullish_confirm = pressure >= abs(LOCAL_BREAK_MIN_PRESSURE) or fut in {"LONG_BUILDUP", "SHORT_COVERING"}

    bearish_levels = [
        level for level in support_levels
        if prev_close >= level - buffer and last_close < level - buffer
    ]
    if (bearish_levels and last_close < last_open and last_close < prev_close
            and spot_value < max(bearish_levels) and bearish_confirm):
        level = max(bearish_levels, key=lambda x: (prev_close - x, x))
        return {
            "confirmed": True, "direction": "BEARISH", "level": float(level), "kind": "BREAKDOWN",
            "reason": f"COMPLETED_3M_BREAKDOWN level={level:.2f} displacement={level-last_close:.2f} "
                      f"buffer={buffer:.2f} pressure={pressure:+.3f} futures={fut}",
        }

    bullish_levels = [
        level for level in resistance_levels
        if prev_close <= level + buffer and last_close > level + buffer
    ]
    if (bullish_levels and last_close > last_open and last_close > prev_close
            and spot_value > min(bullish_levels) and bullish_confirm):
        level = min(bullish_levels, key=lambda x: (x - prev_close, x))
        return {
            "confirmed": True, "direction": "BULLISH", "level": float(level), "kind": "BREAKOUT",
            "reason": f"COMPLETED_3M_BREAKOUT level={level:.2f} displacement={last_close-level:.2f} "
                      f"buffer={buffer:.2f} pressure={pressure:+.3f} futures={fut}",
        }

    held_bearish = [
        level for level in prior_support_levels
        if prev_close < level - buffer and last_close < level - buffer
        and spot_value < level and last_close <= prev_close
    ]
    if held_bearish and last_close < last_open and bearish_confirm:
        level = min(held_bearish, key=lambda x: x - last_close)
        return {
            "confirmed": True, "direction": "BEARISH", "level": float(level), "kind": "BREAKDOWN",
            "reason": f"TWO_COMPLETED_3M_BARS_HOLD_BELOW_VALID_PRIOR_SUPPORT level={level:.2f} "
                      f"prev_close={prev_close:.2f} close={last_close:.2f} buffer={buffer:.2f} "
                      f"pressure={pressure:+.3f} futures={fut}",
        }

    held_bullish = [
        level for level in prior_resistance_levels
        if prev_close > level + buffer and last_close > level + buffer
        and spot_value > level and last_close >= prev_close
    ]
    if held_bullish and last_close > last_open and bullish_confirm:
        level = max(held_bullish, key=lambda x: x - prev_close)
        return {
            "confirmed": True, "direction": "BULLISH", "level": float(level), "kind": "BREAKOUT",
            "reason": f"TWO_COMPLETED_3M_BARS_HOLD_ABOVE_VALID_PRIOR_RESISTANCE level={level:.2f} "
                      f"prev_close={prev_close:.2f} close={last_close:.2f} buffer={buffer:.2f} "
                      f"pressure={pressure:+.3f} futures={fut}",
        }
    return empty


def detect_confirmed_local_oi_rejection(
    price_session: pd.DataFrame,
    *,
    spot: float,
    support: float,
    resistance: float,
    chain_levels: dict[str, Any],
    oi_structure_by_strike: Optional[dict[str, Any]],
    futures_regime: str,
    pressure_score: float,
    strike_step_value: float = 50.0,
    futures_oi_strength: float = 0.0,
) -> dict[str, Any]:
    """Detect a completed-candle rejection of an OI wall or bounce off OI support.

    Merely approaching a wall is not a signal. The last completed candle must test
    the wall, close back away from it, and show a directional candle with volume at
    least equal to the trailing 21-bar median. Strong option Change-OI confirmation
    can outweigh a conflicting futures regime; only an extreme futures conflict
    remains a hard veto.
    """
    empty = {
        "confirmed": False, "direction": "NEUTRAL", "level": float("nan"),
        "kind": "", "reason": "NO_CONFIRMED_OI_WALL_REJECTION_OR_SUPPORT_BOUNCE",
    }
    completed = (
        filter_completed_candles(price_session, 3)
        if price_session is not None and not price_session.empty else pd.DataFrame()
    )
    if len(completed) < 2:
        return empty
    work = completed.sort_values("timestamp").drop_duplicates("timestamp", keep="last").reset_index(drop=True)
    prev, last = work.iloc[-2], work.iloc[-1]
    prev_close = safe_float(prev.get("close"), float("nan"))
    opn = safe_float(last.get("open"), float("nan"))
    high = safe_float(last.get("high"), float("nan"))
    low = safe_float(last.get("low"), float("nan"))
    close = safe_float(last.get("close"), float("nan"))
    spot_value = safe_float(spot, float("nan"))
    if not all(math.isfinite(x) for x in (prev_close, opn, high, low, close, spot_value)):
        return empty

    step = max(safe_float(strike_step_value, 50.0), 1.0)
    atr_series = calculate_atr(work, ATR_PERIOD)
    atr = safe_float(atr_series.iloc[-1], 0.0) if not atr_series.empty else 0.0
    rejection_buffer = max(0.08 * atr, 0.10 * step, spot_value * 0.00005, 2.0)

    # Wall-test tolerance responds to live dispersion around VWAP's 1-sigma bands,
    # but remains tightly capped relative to the strike step to avoid accepting
    # shallow near-misses as institutional wall tests.
    vwap_now, vwap_upper_1sd, vwap_lower_1sd = calculate_vwap_bands(work)
    upper_sigma = abs(vwap_upper_1sd - vwap_now) if all(
        math.isfinite(value) for value in (vwap_now, vwap_upper_1sd)
    ) else float("nan")
    lower_sigma = abs(vwap_now - vwap_lower_1sd) if all(
        math.isfinite(value) for value in (vwap_now, vwap_lower_1sd)
    ) else float("nan")
    valid_sigmas = [value for value in (upper_sigma, lower_sigma) if math.isfinite(value) and value >= 0.0]
    vwap_sigma = max(valid_sigmas) if valid_sigmas else 0.0
    vwap_tolerance_component = 0.10 * vwap_sigma
    test_tolerance = min(max(0.03 * atr, 0.04 * step, vwap_tolerance_component, 1.0), 0.08 * step)

    # Use the median of the previous 21 completed candles; exclude the rejection
    # candle itself so an unusually large candle cannot inflate its own threshold.
    volume_series = pd.to_numeric(work.get("volume", pd.Series(dtype=float)), errors="coerce")
    prior_volumes = volume_series.iloc[-22:-1].dropna().clip(lower=0.0)
    median_volume = safe_float(prior_volumes.median(), 0.0) if not prior_volumes.empty else 0.0
    current_volume = safe_float(last.get("volume"), 0.0)
    volume_confirmed = median_volume > 0.0 and current_volume >= median_volume

    pressure = safe_float(pressure_score)
    fut = str(futures_regime or "").upper()
    futures_strength = min(1.0, max(0.0, safe_float(futures_oi_strength, 0.0)))
    bearish_futures = fut in {"SHORT_BUILDUP", "LONG_UNWINDING"}
    bullish_futures = fut in {"LONG_BUILDUP", "SHORT_COVERING"}
    flow_threshold = abs(min(LOCAL_BREAK_MIN_PRESSURE, -0.20))
    bearish_flow = pressure <= -flow_threshold
    bullish_flow = pressure >= flow_threshold
    bearish_flow_strong = pressure <= -0.45
    bullish_flow_strong = pressure >= 0.45

    # Strong options COI alignment is primary. A conflicting futures state warns
    # and reduces confidence; only a near-maximal futures conflict without extreme
    # aligned COI retains a hard veto.
    extreme_futures_conflict_strength = max(0.95, STRUCTURE_FUTURES_CONFLICT_STRENGTH + 0.40)
    extreme_bullish_conflict = bullish_futures and futures_strength >= extreme_futures_conflict_strength and not bearish_flow_strong
    extreme_bearish_conflict = bearish_futures and futures_strength >= extreme_futures_conflict_strength and not bullish_flow_strong
    bearish_soft_futures_conflict = bearish_flow and bullish_futures and not extreme_bullish_conflict
    bullish_soft_futures_conflict = bullish_flow and bearish_futures and not extreme_bearish_conflict

    window_low = safe_float(chain_levels.get("window_lower_bound"), float("nan"))
    window_high = safe_float(chain_levels.get("window_upper_bound"), float("nan"))
    has_window = math.isfinite(window_low) and math.isfinite(window_high) and window_low <= window_high

    # A resistance rejection can support PE; a support bounce can support CE.
    resistance_value = safe_float(resistance, float("nan"))
    if (math.isfinite(resistance_value) and resistance_value > 0
            and 0.0 <= resistance_value - spot_value <= BREAKOUT_WATCH_MAX_DISTANCE_STEPS * step
            and (not has_window or window_low - 0.01 <= resistance_value <= window_high + 0.01)):
        row = _oi_role_row(oi_structure_by_strike, resistance_value)
        valid_wall = str(row.get("dominant_role", "")).upper() == "RESISTANCE"
        tested = high >= resistance_value - test_tolerance
        rejected = close <= resistance_value - rejection_buffer and close < opn and close < prev_close
        bearish_confirmation = (bearish_flow or bearish_futures) and not extreme_bullish_conflict
        if valid_wall and tested and rejected and volume_confirmed and bearish_confirmation:
            conflict_note = (
                f" FUTURES_CONFLICT_SOFTENED strength={futures_strength:.3f} confidence_penalty=8"
                if bearish_soft_futures_conflict else ""
            )
            return {
                "confirmed": True, "direction": "BEARISH", "level": resistance_value,
                "kind": "RESISTANCE_REJECTION",
                "confidence_penalty": 8.0 if bearish_soft_futures_conflict else 0.0,
                "warnings": ["CONFLICTING_FUTURES_CONTEXT"] if bearish_soft_futures_conflict else [],
                "volume": current_volume, "median_volume": median_volume,
                "vwap": vwap_now, "vwap_upper_1sd": vwap_upper_1sd,
                "vwap_lower_1sd": vwap_lower_1sd, "test_tolerance": test_tolerance,
                "reason": f"CONFIRMED_RESISTANCE_REJECTION level={resistance_value:.2f} high={high:.2f} "
                          f"close={close:.2f} rejection={resistance_value-close:.2f} "
                          f"volume={current_volume:.0f} median21={median_volume:.0f} "
                          f"vwap_sigma={vwap_sigma:.3f} tolerance={test_tolerance:.2f} "
                          f"pressure={pressure:+.3f} futures={fut}{conflict_note}",
            }
        resistance_check = (
            f"RESISTANCE_REJECTION_NOT_CONFIRMED level={resistance_value:.2f} "
            f"valid_wall={valid_wall} tested={tested} bearish_candle_rejection={rejected} "
            f"volume_confirmed={volume_confirmed} volume={current_volume:.0f} median21={median_volume:.0f} "
            f"derivatives_confirm={bearish_confirmation} extreme_futures_conflict={extreme_bullish_conflict} "
            f"pressure={pressure:+.3f} futures={fut}"
        )
    else:
        resistance_check = "RESISTANCE_REJECTION_NOT_CHECKED: no current in-window resistance near spot"

    support_value = safe_float(support, float("nan"))
    if (math.isfinite(support_value) and support_value > 0
            and 0.0 <= spot_value - support_value <= BREAKOUT_WATCH_MAX_DISTANCE_STEPS * step
            and (not has_window or window_low - 0.01 <= support_value <= window_high + 0.01)):
        row = _oi_role_row(oi_structure_by_strike, support_value)
        valid_wall = str(row.get("dominant_role", "")).upper() == "SUPPORT"
        tested = low <= support_value + test_tolerance
        bounced = close >= support_value + rejection_buffer and close > opn and close > prev_close
        bullish_confirmation = (bullish_flow or bullish_futures) and not extreme_bearish_conflict
        if valid_wall and tested and bounced and volume_confirmed and bullish_confirmation:
            conflict_note = (
                f" FUTURES_CONFLICT_SOFTENED strength={futures_strength:.3f} confidence_penalty=8"
                if bullish_soft_futures_conflict else ""
            )
            return {
                "confirmed": True, "direction": "BULLISH", "level": support_value,
                "kind": "SUPPORT_BOUNCE",
                "confidence_penalty": 8.0 if bullish_soft_futures_conflict else 0.0,
                "warnings": ["CONFLICTING_FUTURES_CONTEXT"] if bullish_soft_futures_conflict else [],
                "volume": current_volume, "median_volume": median_volume,
                "vwap": vwap_now, "vwap_upper_1sd": vwap_upper_1sd,
                "vwap_lower_1sd": vwap_lower_1sd, "test_tolerance": test_tolerance,
                "reason": f"CONFIRMED_SUPPORT_BOUNCE level={support_value:.2f} low={low:.2f} "
                          f"close={close:.2f} reclaim={close-support_value:.2f} "
                          f"volume={current_volume:.0f} median21={median_volume:.0f} "
                          f"vwap_sigma={vwap_sigma:.3f} tolerance={test_tolerance:.2f} "
                          f"pressure={pressure:+.3f} futures={fut}{conflict_note}",
            }
        support_check = (
            f"SUPPORT_BOUNCE_NOT_CONFIRMED level={support_value:.2f} "
            f"valid_wall={valid_wall} tested={tested} bullish_candle_bounce={bounced} "
            f"volume_confirmed={volume_confirmed} volume={current_volume:.0f} median21={median_volume:.0f} "
            f"derivatives_confirm={bullish_confirmation} extreme_futures_conflict={extreme_bearish_conflict} "
            f"pressure={pressure:+.3f} futures={fut}"
        )
    else:
        support_check = "SUPPORT_BOUNCE_NOT_CHECKED: no current in-window support near spot"
    empty["reason"] = f"{resistance_check}; {support_check}"
    return empty


def evaluate_local_breakout_watch(
    *,
    direction: str,
    spot: float,
    current_close: float,
    vwap: float,
    support: float,
    resistance: float,
    strike_step_value: float,
    structure_phase: str,
    structure_entry_confirmed: bool,
    effective_change_oi: float,
    futures_regime: str,
    oi_structure_by_strike: Optional[dict[str, Any]],
    market_intensity: str,
) -> dict[str, Any]:
    """Describe a near-wall breakout setup without mislabelling it as confirmed."""
    side = str(direction or "").upper()
    phase = str(structure_phase or "").upper()
    intensity = str(market_intensity or "UNKNOWN").upper()
    fut = str(futures_regime or "").upper()
    levels = oi_structure_by_strike if isinstance(oi_structure_by_strike, dict) else {}
    step = max(safe_float(strike_step_value, 50.0), 1.0)
    spot_v = safe_float(spot, float("nan"))
    close_v = safe_float(current_close, float("nan"))
    vwap_v = safe_float(vwap, float("nan"))
    flow = safe_float(effective_change_oi, 0.0)
    wall = safe_float(resistance if side == "BULLISH" else support, float("nan"))
    if (side not in {"BULLISH", "BEARISH"} or intensity in {"SIDEWAYS", "UNKNOWN"}
            or not structure_entry_confirmed
            or phase not in {"CONTINUOUS_BULLISH", "CONTINUOUS_BEARISH"}
            or not all(math.isfinite(x) for x in (spot_v, close_v, vwap_v, wall))):
        return {"armed": False, "confirmed": False, "direction": side, "level": wall, "reason": "STRUCTURE_NOT_READY"}
    distance = wall - spot_v if side == "BULLISH" else spot_v - wall
    if distance < 0.0 or distance > BREAKOUT_WATCH_MAX_DISTANCE_STEPS * step:
        return {"armed": False, "confirmed": False, "direction": side, "level": wall, "reason": "WALL_NOT_NEAR_OR_ALREADY_CROSSED"}
    vwap_aligned = close_v > vwap_v if side == "BULLISH" else close_v < vwap_v
    flow_aligned = flow >= STRUCTURE_CHANGE_OI_CONFIRM if side == "BULLISH" else flow <= -STRUCTURE_CHANGE_OI_CONFIRM
    fut_aligned = fut in ({"LONG_BUILDUP", "SHORT_COVERING"} if side == "BULLISH" else {"SHORT_BUILDUP", "LONG_UNWINDING"})
    wall_row: dict[str, Any] = {}
    for raw_key, raw_value in levels.items():
        if abs(safe_float(raw_key, float("nan")) - wall) <= 0.01 and isinstance(raw_value, dict):
            wall_row = raw_value
            break
    wall_state = str(wall_row.get("state", "")).upper()
    if side == "BULLISH":
        wall_weakening = wall_state == "POTENTIAL_BREAKOUT_SHORT_COVERING"
    else:
        wall_weakening = wall_state == "POTENTIAL_BREAKDOWN_LONG_UNWINDING"
    armed = bool(wall_weakening and vwap_aligned and flow_aligned and fut_aligned)
    reasons = []
    if not wall_weakening: reasons.append("OI_WALL_NOT_CONFIRMED_WEAKENING")
    if not vwap_aligned: reasons.append("VWAP_NOT_ALIGNED")
    if not flow_aligned: reasons.append("CHANGE_OI_NOT_ALIGNED")
    if not fut_aligned: reasons.append("FUTURES_CONTEXT_NOT_ALIGNED")
    return {
        "armed": armed, "confirmed": False, "direction": side, "level": wall,
        "distance": distance, "wall_state": wall_state,
        "reason": "ALL_PRE_BREAKOUT_FILTERS_ALIGNED" if armed else ";".join(reasons),
    }


def parse_date(raw: str) -> Optional[date]:
    try:
        return datetime.strptime(str(raw)[:10], "%Y-%m-%d").date()
    except (TypeError, ValueError):
        return None


def market_window_open() -> bool:
    # NSE status is checked immediately afterwards and is the authoritative
    # open/closed gate. Avoid a separate holiday API call on every 5-minute run.
    now = now_ist()
    return now.weekday() < 5 and MARKET_START <= now.time() <= MARKET_END


# =============================================================================
# UPSTOX HTTP
# =============================================================================

def api_headers() -> dict[str, str]:
    """Compatibility adapter to the default provider's authorization headers."""
    return DEFAULT_DATA_PROVIDER.api_headers()


def api_get(
    url: str,
    params: Optional[dict[str, Any]] = None,
    retries: int = 3,
) -> dict[str, Any]:
    """Compatibility adapter; HTTP and retry handling live in UpstoxDataProvider."""
    return DEFAULT_DATA_PROVIDER.api_get(url, params=params, retries=retries)


# =============================================================================
# MARKET STATUS / HOLIDAYS
# =============================================================================



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
    """Fetch a quote using the configured Upstox provider."""
    return DEFAULT_DATA_PROVIDER.get_quote(instrument_key)



def extract_ltp(quote: dict[str, Any]) -> float:
    for key in ("last_price", "ltp", "lastPrice"):
        value = safe_float(quote.get(key), 0.0)
        if value > 0:
            return value
    raise ScannerError("LTP not present in quote.")


def quote_freshness_status(
    quote: Optional[dict[str, Any]],
    *,
    now: Optional[datetime] = None,
    max_age_seconds: int = FUTURES_QUOTE_MAX_AGE_SECONDS,
) -> dict[str, Any]:
    """Assess an explicitly timestamped quote; absence of timestamp is UNVERIFIED, not assumed stale."""
    current = now or now_ist()
    if current.tzinfo is None:
        current = current.replace(tzinfo=IST)
    current = current.astimezone(IST)
    if not isinstance(quote, dict):
        return {"status": "UNAVAILABLE", "field": "", "age_seconds": float("nan"), "timestamp": ""}

    timestamp_fields = (
        "last_trade_time", "last_trade_timestamp", "exchange_timestamp",
        "last_traded_time", "timestamp", "lastTradeTime",
    )
    selected_field = ""
    parsed: Optional[pd.Timestamp] = None
    for field in timestamp_fields:
        raw = quote.get(field)
        if raw is None or str(raw).strip() == "":
            continue
        selected_field = field
        try:
            numeric = safe_float(raw, float("nan"))
            if math.isfinite(numeric) and numeric > 1_000_000_000:
                if numeric >= 100_000_000_000_000_000:
                    unit = "ns"
                elif numeric >= 100_000_000_000_000:
                    unit = "us"
                elif numeric >= 100_000_000_000:
                    unit = "ms"
                else:
                    unit = "s"
                parsed = pd.to_datetime(numeric, unit=unit, utc=True, errors="coerce")
            else:
                parsed = pd.Timestamp(raw)
                if not pd.isna(parsed):
                    if parsed.tzinfo is None:
                        parsed = parsed.tz_localize(IST)
                    else:
                        parsed = parsed.tz_convert(IST)
            if parsed is not None and not pd.isna(parsed):
                parsed = parsed.tz_convert(IST) if parsed.tzinfo is not None else parsed.tz_localize(IST)
                break
        except (TypeError, ValueError, OverflowError):
            parsed = None
        parsed = None

    if parsed is None or pd.isna(parsed):
        return {"status": "UNVERIFIED", "field": selected_field, "age_seconds": float("nan"), "timestamp": ""}
    age = (pd.Timestamp(current) - parsed).total_seconds()
    if age < -60.0:
        status = "FUTURE_TIMESTAMP"
    elif age > max(30, int(max_age_seconds)):
        status = "STALE"
    else:
        status = "FRESH"
    return {
        "status": status,
        "field": selected_field,
        "age_seconds": float(age),
        "timestamp": parsed.isoformat(),
    }


# =============================================================================
# INSTRUMENT DISCOVERY
# =============================================================================

def get_current_nifty_future(state: Optional[dict[str, Any]] = None) -> FuturesContract:
    # The nearest NIFTY future normally remains unchanged throughout the session.
    # Persisting it avoids two instrument-search requests on every scan.
    today = now_ist().date()
    if isinstance(state, dict):
        cached = state.get("nifty_future")
        if isinstance(cached, dict):
            expiry = parse_date(str(cached.get("expiry", "")))
            key = str(cached.get("instrument_key", "")).strip()
            symbol = str(cached.get("trading_symbol", "")).strip()
            if key and symbol and expiry and expiry >= today and "NIFTY" in symbol.upper():
                contract = FuturesContract(key, symbol, expiry.isoformat())
                logger.info(
                    "FUTURES CONTRACT VALIDATION: source=STATE_CACHE symbol=%s expiry=%s expiry_valid=%s key=%s",
                    contract.trading_symbol, contract.expiry, contract.expiry >= today.isoformat(), contract.instrument_key,
                )
                return contract

    candidates: list[dict[str, Any]] = []

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
            and ("NIFTY" in underlying or "NIFTY" in symbol.upper())
        ):
            valid.append(row)

    if not valid:
        raise ScannerError("No active NIFTY futures found.")

    valid.sort(key=lambda x: parse_date(str(x["expiry"])) or date.max)
    selected = valid[0]

    logger.info(
        "FUTURES CONTRACT VALIDATION: source=INSTRUMENT_SEARCH symbol=%s expiry=%s expiry_valid=%s key=%s",
        selected["trading_symbol"], selected["expiry"],
        bool(parse_date(str(selected["expiry"])) and parse_date(str(selected["expiry"])) >= today),
        selected["instrument_key"],
    )

    contract = FuturesContract(
        instrument_key=str(selected["instrument_key"]),
        trading_symbol=str(selected["trading_symbol"]),
        expiry=str(selected["expiry"])[:10],
    )
    if isinstance(state, dict):
        state["nifty_future"] = asdict(contract)
    return contract


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
    """Fetch current-session candles using the configured Upstox provider."""
    return DEFAULT_DATA_PROVIDER.get_intraday_candles(
        instrument_key, interval_minutes, strict=strict
    )



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


def get_current_session_3m_candles(instrument_key: str) -> pd.DataFrame:
    """Prefer native 3m data; log the instrument explicitly and fall back to 1m aggregation."""
    instrument_label = "NIFTY_INDEX" if instrument_key == NIFTY_KEY else str(instrument_key)
    native = get_intraday_candles(instrument_key, 3, strict=False)
    if not native.empty:
        logger.info(
            "CURRENT-SESSION CANDLES: instrument=%s interval=3m count=%d",
            instrument_label, len(native),
        )
        return native

    one_min = get_intraday_candles(instrument_key, 1, strict=False)
    if not one_min.empty:
        rebuilt = _resample_one_minute_to_three(one_min)
        if not rebuilt.empty:
            logger.warning(
                "NATIVE 3M CANDLES UNAVAILABLE: instrument=%s; rebuilt interval=3m count=%d from 1m data.",
                instrument_label, len(rebuilt),
            )
            return rebuilt

    logger.warning(
        "CURRENT-SESSION CANDLES UNAVAILABLE: instrument=%s intervals=3m,1m; using quote/historical fallbacks.",
        instrument_label,
    )
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


def filter_completed_candles(
    df: pd.DataFrame,
    interval_minutes: int,
    now: Optional[datetime] = None,
) -> pd.DataFrame:
    """Keep only fully completed OHLC bars for the requested interval."""
    if df is None or df.empty:
        return pd.DataFrame()
    current = now or now_ist()
    work = df.copy()
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    work = work.dropna(subset=["timestamp"]).sort_values("timestamp")
    local_ts = work["timestamp"].dt.tz_convert(IST)
    completed = local_ts + pd.to_timedelta(int(interval_minutes), unit="m") <= current
    return work.loc[completed].reset_index(drop=True)


def get_regime_indicator_history(
    state: dict[str, Any],
    instrument_key: str,
    *,
    now: Optional[datetime] = None,
) -> pd.DataFrame:
    """Return cached completed index candles from prior sessions for ADX/RSI seeding.

    Historical candles are fetched once per trading date and cached in scanner
    state. Only dates before the current IST session are retained; current-session
    VWAP, volume confirmation and swing structure continue to use live session bars.
    Failed fetches are retried after a short cooldown rather than on every scan.
    """
    current = now or now_ist()
    if current.tzinfo is None:
        current = current.replace(tzinfo=IST)
    current = current.astimezone(IST)
    today_iso = current.date().isoformat()
    cache = state.get(REGIME_INDICATOR_CACHE_KEY) if isinstance(state, dict) else None

    def _frame_from_cache(cached: dict[str, Any]) -> pd.DataFrame:
        records = cached.get("candles", [])
        if not isinstance(records, list) or not records:
            return pd.DataFrame()
        frame = pd.DataFrame(records)
        required = {"timestamp", "open", "high", "low", "close", "volume"}
        if not required.issubset(frame.columns):
            return pd.DataFrame()
        frame["timestamp"] = pd.to_datetime(frame["timestamp"], utc=True, errors="coerce")
        for col in ("open", "high", "low", "close", "volume"):
            frame[col] = pd.to_numeric(frame[col], errors="coerce")
        frame = (frame.dropna(subset=["timestamp", "open", "high", "low", "close"])
                      .sort_values("timestamp")
                      .drop_duplicates("timestamp", keep="last"))
        if frame.empty:
            return pd.DataFrame()
        local_dates = frame["timestamp"].dt.tz_convert(IST).dt.date
        frame = frame.loc[local_dates < current.date()]
        return frame.tail(REGIME_INDICATOR_HISTORY_BARS).reset_index(drop=True)

    if (isinstance(cache, dict)
            and str(cache.get("session_date", "")) == today_iso
            and str(cache.get("instrument_key", "")) == instrument_key):
        cached_frame = _frame_from_cache(cache)
        if str(cache.get("status", "")) == "AVAILABLE" and not cached_frame.empty:
            logger.info(
                "REGIME INDICATOR HISTORY: source=STATE_CACHE status=AVAILABLE bars=%d instrument=%s latest=%s",
                len(cached_frame), instrument_key,
                cached_frame["timestamp"].iloc[-1].tz_convert(IST).isoformat(),
            )
            return cached_frame
        if str(cache.get("status", "")) != "AVAILABLE":
            attempted = pd.to_datetime(cache.get("attempted_at", ""), utc=True, errors="coerce")
            if not pd.isna(attempted):
                age = (pd.Timestamp(current).tz_convert("UTC") - attempted).total_seconds()
                if 0 <= age < REGIME_INDICATOR_CACHE_RETRY_SECONDS:
                    logger.warning(
                        "REGIME INDICATOR HISTORY: source=STATE_CACHE status=UNAVAILABLE retry_in_seconds=%d instrument=%s",
                        int(REGIME_INDICATOR_CACHE_RETRY_SECONDS - age), instrument_key,
                    )
                    return pd.DataFrame()

    attempted_at = current.isoformat()
    try:
        historical = get_historical_candles(instrument_key, 3)
        historical = filter_completed_candles(historical, 3, now=current)
        if not historical.empty:
            local_dates = historical["timestamp"].dt.tz_convert(IST).dt.date
            historical = historical.loc[local_dates < current.date()]
        historical = historical.tail(REGIME_INDICATOR_HISTORY_BARS).reset_index(drop=True)
        if historical.empty:
            raise ScannerError("Historical index endpoint returned no completed prior-session 3m candles.")

        records: list[dict[str, Any]] = []
        for row in historical.to_dict("records"):
            timestamp = pd.to_datetime(row.get("timestamp"), utc=True, errors="coerce")
            if pd.isna(timestamp):
                continue
            records.append({
                "timestamp": timestamp.isoformat(),
                "open": safe_float(row.get("open"), float("nan")),
                "high": safe_float(row.get("high"), float("nan")),
                "low": safe_float(row.get("low"), float("nan")),
                "close": safe_float(row.get("close"), float("nan")),
                "volume": max(0.0, safe_float(row.get("volume"), 0.0)),
            })
        historical = _frame_from_cache({"candles": records})
        if historical.empty:
            raise ScannerError("Historical index candles were invalid after normalization.")
        state[REGIME_INDICATOR_CACHE_KEY] = {
            "session_date": today_iso, "instrument_key": instrument_key,
            "interval_minutes": 3, "status": "AVAILABLE",
            "attempted_at": attempted_at, "candles": records,
        }
        logger.info(
            "REGIME INDICATOR HISTORY: source=API_FETCH status=AVAILABLE bars=%d instrument=%s earliest=%s latest=%s",
            len(historical), instrument_key,
            historical["timestamp"].iloc[0].tz_convert(IST).isoformat(),
            historical["timestamp"].iloc[-1].tz_convert(IST).isoformat(),
        )
        return historical
    except (ScannerError, requests.RequestException, ValueError, TypeError, KeyError) as exc:
        state[REGIME_INDICATOR_CACHE_KEY] = {
            "session_date": today_iso, "instrument_key": instrument_key,
            "interval_minutes": 3, "status": "UNAVAILABLE",
            "attempted_at": attempted_at, "candles": [], "error": str(exc)[:500],
        }
        logger.warning(
            "REGIME INDICATOR HISTORY: source=API_FETCH status=UNAVAILABLE instrument=%s reason=%s; current-session-only warm-up will be used safely.",
            instrument_key, exc,
        )
        return pd.DataFrame()


def get_cached_futures_oi_history(
    state: dict[str, Any],
    instrument_key: str,
    *,
    now: Optional[datetime] = None,
) -> pd.DataFrame:
    """Fetch and cache prior-session futures candles once per date and contract.

    Current-session futures candles remain live. This cache is used only for OI
    warm-up/context and never substitutes for current prices or current-session OI.
    """
    current = now or now_ist()
    if current.tzinfo is None:
        current = current.replace(tzinfo=IST)
    current = current.astimezone(IST)
    today_iso = current.date().isoformat()
    cache = state.get(FUTURES_HISTORY_CACHE_KEY) if isinstance(state, dict) else None

    def cached_frame(records: Any) -> pd.DataFrame:
        if not isinstance(records, list) or not records:
            return pd.DataFrame()
        frame = pd.DataFrame(records)
        required = {"timestamp", "open", "high", "low", "close", "volume"}
        if not required.issubset(frame.columns):
            return pd.DataFrame()
        frame["timestamp"] = pd.to_datetime(frame["timestamp"], utc=True, errors="coerce")
        for column in ("open", "high", "low", "close", "volume"):
            frame[column] = pd.to_numeric(frame[column], errors="coerce")
        if "oi" not in frame.columns:
            frame["oi"] = np.nan
        frame["oi"] = pd.to_numeric(frame["oi"], errors="coerce")
        frame = (frame.dropna(subset=["timestamp", "open", "high", "low", "close"])
                      .sort_values("timestamp")
                      .drop_duplicates("timestamp", keep="last"))
        if frame.empty:
            return pd.DataFrame()
        local_dates = frame["timestamp"].dt.tz_convert(IST).dt.date
        frame = frame.loc[local_dates < current.date()]
        return frame.tail(FUTURES_HISTORY_CACHE_BARS).reset_index(drop=True)

    if (isinstance(cache, dict)
            and str(cache.get("session_date", "")) == today_iso
            and str(cache.get("instrument_key", "")) == instrument_key):
        frame = cached_frame(cache.get("candles", []))
        if str(cache.get("status", "")) == "AVAILABLE" and not frame.empty:
            logger.info(
                "FUTURES HISTORICAL CACHE: source=STATE_CACHE status=AVAILABLE bars=%d instrument=%s latest=%s",
                len(frame), instrument_key, frame["timestamp"].iloc[-1].tz_convert(IST).isoformat(),
            )
            return frame
        if str(cache.get("status", "")) != "AVAILABLE":
            attempted = pd.to_datetime(cache.get("attempted_at", ""), utc=True, errors="coerce")
            if not pd.isna(attempted):
                age_seconds = (pd.Timestamp(current).tz_convert("UTC") - attempted).total_seconds()
                if 0 <= age_seconds < REGIME_INDICATOR_CACHE_RETRY_SECONDS:
                    logger.warning(
                        "FUTURES HISTORICAL CACHE: source=STATE_CACHE status=UNAVAILABLE retry_in_seconds=%d instrument=%s",
                        int(REGIME_INDICATOR_CACHE_RETRY_SECONDS - age_seconds), instrument_key,
                    )
                    return pd.DataFrame()

    attempted_at = current.isoformat()
    try:
        historical = get_historical_candles(instrument_key, 3)
        historical = filter_completed_candles(historical, 3, now=current)
        if not historical.empty:
            local_dates = historical["timestamp"].dt.tz_convert(IST).dt.date
            historical = historical.loc[local_dates < current.date()]
        historical = historical.tail(FUTURES_HISTORY_CACHE_BARS).reset_index(drop=True)
        if historical.empty:
            raise ScannerError("Historical futures endpoint returned no completed prior-session 3m candles.")

        records: list[dict[str, Any]] = []
        for row in historical.to_dict("records"):
            timestamp = pd.to_datetime(row.get("timestamp"), utc=True, errors="coerce")
            if pd.isna(timestamp):
                continue
            oi_value = safe_float(row.get("oi"), float("nan"))
            records.append({
                "timestamp": timestamp.isoformat(),
                "open": safe_float(row.get("open"), float("nan")),
                "high": safe_float(row.get("high"), float("nan")),
                "low": safe_float(row.get("low"), float("nan")),
                "close": safe_float(row.get("close"), float("nan")),
                "volume": max(0.0, safe_float(row.get("volume"), 0.0)),
                "oi": oi_value if math.isfinite(oi_value) else None,
            })
        frame = cached_frame(records)
        if frame.empty:
            raise ScannerError("Historical futures candles were invalid after normalization.")
        state[FUTURES_HISTORY_CACHE_KEY] = {
            "session_date": today_iso, "instrument_key": instrument_key,
            "interval_minutes": 3, "status": "AVAILABLE",
            "attempted_at": attempted_at, "candles": records,
        }
        logger.info(
            "FUTURES HISTORICAL CACHE: source=API_FETCH status=AVAILABLE bars=%d instrument=%s earliest=%s latest=%s",
            len(frame), instrument_key, frame["timestamp"].iloc[0].tz_convert(IST).isoformat(),
            frame["timestamp"].iloc[-1].tz_convert(IST).isoformat(),
        )
        return frame
    except (ScannerError, requests.RequestException, ValueError, TypeError, KeyError) as exc:
        state[FUTURES_HISTORY_CACHE_KEY] = {
            "session_date": today_iso, "instrument_key": instrument_key,
            "interval_minutes": 3, "status": "UNAVAILABLE",
            "attempted_at": attempted_at, "candles": [], "error": str(exc)[:500],
        }
        logger.warning(
            "FUTURES HISTORICAL CACHE: source=API_FETCH status=UNAVAILABLE instrument=%s reason=%s; live-session candles remain in use.",
            instrument_key, exc,
        )
        return pd.DataFrame()


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

def calculate_rsi(
    close: pd.Series,
    period: int = 14,
    session_dates: Optional[pd.Series] = None,
) -> pd.Series:
    """Wilder RSI with a full-period warm-up and no overnight-gap return spike.

    ``session_dates`` may be supplied for intraday candles. The first close-to-close
    delta of a new session is excluded, while Wilder's smoothed averages carry over.
    """
    values = pd.to_numeric(close, errors="coerce")
    n = max(int(period), 2)
    delta = values.diff()
    if session_dates is not None:
        dates = pd.Series(session_dates, index=values.index)
        new_session = dates.ne(dates.shift(1))
        delta = delta.mask(new_session)
    gain = delta.clip(lower=0.0)
    loss = -delta.clip(upper=0.0)
    avg_gain = gain.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean()
    avg_loss = loss.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean()
    rs = avg_gain / avg_loss.replace(0.0, np.nan)
    rsi = 100.0 - (100.0 / (1.0 + rs))
    # Explicitly define one-sided and flat markets instead of leaking NaN values.
    rsi = rsi.where(avg_loss > 0.0, 100.0)
    rsi = rsi.where(avg_gain > 0.0, 0.0).where(avg_loss > 0.0, rsi)
    both_flat = (avg_gain == 0.0) & (avg_loss == 0.0)
    return rsi.where(~both_flat, 50.0).clip(0.0, 100.0)


def calculate_adx(df: pd.DataFrame, period: int = ADX_PERIOD) -> pd.Series:
    """Wilder ADX requiring a full DI and ADX smoothing window.

    Historical completed candles should be prepended to the current session so
    the normal warm-up completes before the opening-session signal window. If a
    timestamp is present, price gaps between sessions are not counted as intraday
    directional movement; the first bar's own high-low range is retained.
    """
    required = {"high", "low", "close"}
    if df is None or df.empty or not required.issubset(df.columns):
        return pd.Series(dtype=float)
    work = df.copy()
    if "timestamp" in work.columns:
        work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
        work = work.dropna(subset=["timestamp"]).sort_values("timestamp")
        work = work.drop_duplicates("timestamp", keep="last")
    for column in ("high", "low", "close"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    work = work.dropna(subset=["high", "low", "close"])
    n = max(int(period), 2)
    if len(work) < 2 * n:
        return pd.Series(np.nan, index=work.index, dtype=float)

    high = work["high"]
    low = work["low"]
    close = work["close"]
    up = high.diff()
    down = -low.diff()
    previous_close = close.shift(1)
    if "timestamp" in work.columns:
        local_dates = work["timestamp"].dt.tz_convert(IST).dt.date
        new_session = local_dates.ne(local_dates.shift(1))
        up = up.mask(new_session)
        down = down.mask(new_session)
        previous_close = previous_close.mask(new_session)

    valid_dm = up.notna() & down.notna()
    plus_dm = pd.Series(np.where((up > down) & (up > 0), up, 0.0), index=work.index, dtype=float).where(valid_dm)
    minus_dm = pd.Series(np.where((down > up) & (down > 0), down, 0.0), index=work.index, dtype=float).where(valid_dm)
    true_range = pd.concat(
        [(high - low), (high - previous_close).abs(), (low - previous_close).abs()], axis=1
    ).max(axis=1)
    # Standard Wilder smoothing: one full period for directional indicators and
    # another full period for ADX itself. This avoids the premature, noisy ADX
    # values produced by half-period warm-ups.
    atr = true_range.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean()
    plus_smoothed = plus_dm.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean()
    minus_smoothed = minus_dm.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean()
    plus_di = 100.0 * plus_smoothed / atr.replace(0.0, np.nan)
    minus_di = 100.0 * minus_smoothed / atr.replace(0.0, np.nan)
    denominator = (plus_di + minus_di).replace(0.0, np.nan)
    dx = 100.0 * (plus_di - minus_di).abs() / denominator
    adx = dx.ewm(alpha=1.0 / n, adjust=False, min_periods=n).mean().clip(0.0, 100.0)
    return adx.reindex(df.index)


def calculate_vwap_bands(df: pd.DataFrame) -> tuple[float, float, float]:
    """Return current-session VWAP, upper 1-sigma band and lower 1-sigma band."""
    if df is None or df.empty:
        return float("nan"), float("nan"), float("nan")
    work = df.copy()
    for column in ("high", "low", "close", "volume"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    typical = (work["high"] + work["low"] + work["close"]) / 3.0
    volume = work["volume"].fillna(0.0).clip(lower=0.0)
    local_date = pd.to_datetime(work["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST).dt.date
    cum_v = volume.groupby(local_date).cumsum()
    cum_pv = (typical * volume).groupby(local_date).cumsum()
    cum_p2v = (typical.pow(2) * volume).groupby(local_date).cumsum()
    vwap_series = cum_pv / cum_v.replace(0.0, np.nan)
    variance = (cum_p2v / cum_v.replace(0.0, np.nan)) - vwap_series.pow(2)
    std_series = np.sqrt(variance.clip(lower=0.0))
    if vwap_series.notna().any():
        vwap_now = safe_float(vwap_series.dropna().iloc[-1], float("nan"))
        std_now = safe_float(std_series.dropna().iloc[-1], float("nan")) if std_series.notna().any() else float("nan")
    else:
        vwap_now, std_now = float("nan"), float("nan")
    return vwap_now, vwap_now + std_now, vwap_now - std_now


def _resample_ohlcv(df: pd.DataFrame, minutes: int) -> pd.DataFrame:
    if df is None or df.empty:
        return pd.DataFrame()
    work = df.copy()
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    work = work.dropna(subset=["timestamp"]).set_index("timestamp").sort_index()
    for c in ("open", "high", "low", "close", "volume"):
        if c in work:
            work[c] = pd.to_numeric(work[c], errors="coerce")
    result = work.resample(
        f"{int(minutes)}min", origin="start_day", offset="9h15min", label="left", closed="left"
    ).agg(open=("open", "first"), high=("high", "max"), low=("low", "min"),
          close=("close", "last"), volume=("volume", "sum"))
    result = result.dropna(subset=["open", "high", "low", "close"]).reset_index()
    return filter_completed_candles(result, minutes)


def detect_rsi_divergence(
    df: pd.DataFrame,
    window: int = 5,
    rsi_values: Optional[pd.Series] = None,
) -> str:
    """Detect confirmed divergence inside the supplied window, optionally using history-seeded RSI."""
    if df is None or df.empty or len(df) < 2 * window:
        return "NONE"
    work = df.copy().reset_index(drop=True)
    for column in ("close", "high", "low"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    if rsi_values is None:
        session_dates = (
            pd.to_datetime(work["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST).dt.date
            if "timestamp" in work.columns else None
        )
        work["rsi"] = calculate_rsi(work["close"], 14, session_dates=session_dates)
    else:
        seeded = pd.to_numeric(pd.Series(rsi_values).reset_index(drop=True), errors="coerce")
        if len(seeded) != len(work):
            return "NONE"
        work["rsi"] = seeded.to_numpy(dtype=float)
    previous = work.iloc[-2 * window:-window]
    recent = work.iloc[-window:]
    required_valid = max(2, int(window))
    if previous["rsi"].notna().sum() < required_valid or recent["rsi"].notna().sum() < required_valid:
        return "NONE"
    p_low_i = previous["low"].idxmin()
    r_low_i = recent["low"].idxmin()
    p_high_i = previous["high"].idxmax()
    r_high_i = recent["high"].idxmax()
    previous_low, recent_low = work.loc[p_low_i], work.loc[r_low_i]
    previous_high, recent_high = work.loc[p_high_i], work.loc[r_high_i]
    bullish = (
        safe_float(recent_low["low"]) < safe_float(previous_low["low"])
        and safe_float(recent_low["rsi"], float("nan")) >= safe_float(previous_low["rsi"], float("nan")) + 2.0
    )
    bearish = (
        safe_float(recent_high["high"]) > safe_float(previous_high["high"])
        and safe_float(recent_high["rsi"], float("nan")) <= safe_float(previous_high["rsi"], float("nan")) - 2.0
    )
    return "BULLISH" if bullish else "BEARISH" if bearish else "NONE"


def time_of_day_window(now: Optional[datetime] = None) -> str:
    current = now or now_ist()
    clock = current.astimezone(IST).time() if current.tzinfo else current.time()
    if clock >= NEW_ENTRY_CUTOFF:
        return "CUTOFF"
    if clock < OPENING_END:
        return "OPENING"
    if clock < MIDDAY_END:
        return "MIDDAY"
    return "AFTERNOON"



def structural_direction_override_decision(
    *,
    direction: str,
    structure_phase: str,
    entry_confirmed: bool,
    spot: float,
    vwap: float,
    last_completed_close: float,
    atr: float,
    vwap_slope: float,
    change_oi: float,
    divergence: str = "NONE",
    near_structural_level: bool = False,
) -> tuple[bool, str]:
    """Assess whether confirmed PA/OI structure should remain directional regardless of ADX.

    ADX is a trend-strength measurement, not a direction veto. This guard is only
    eligible when the structural engine has already confirmed a continuous phase,
    spot and the latest completed close remain on the correct side of VWAP (within
    a small noise buffer), VWAP slope and option Change-OI agree, and there is no
    confirmed opposing RSI divergence at a structural level. Entry risk, wall,
    persistence, premium, execution-score and reward/risk checks remain downstream.
    """
    side = str(direction or "").strip().upper()
    phase = str(structure_phase or "").strip().upper()
    div = str(divergence or "NONE").strip().upper()
    px = safe_float(spot, float("nan"))
    vw = safe_float(vwap, float("nan"))
    close = safe_float(last_completed_close, float("nan"))
    atr_value = max(0.0, safe_float(atr, 0.0))
    slope = safe_float(vwap_slope, float("nan"))
    flow = safe_float(change_oi, float("nan"))
    reasons: list[str] = []

    phase_aligned = side in {"BULLISH", "BEARISH"} and phase == f"CONTINUOUS_{side}" and bool(entry_confirmed)
    if not phase_aligned:
        reasons.append("continuous phase/entry confirmation not aligned")

    if not all(math.isfinite(v) for v in (px, vw, close, slope, flow)) or px <= 0 or vw <= 0:
        reasons.append("invalid price/VWAP/slope/Change-OI input")
        price_aligned = slope_aligned = flow_aligned = False
    else:
        # Let a latest completed close sit just inside the VWAP by a small,
        # volatility-scaled noise buffer; live spot must still confirm direction.
        vwap_noise_buffer = max(0.10 * atr_value, abs(px) * 0.00005, 1.0)
        if side == "BULLISH":
            price_aligned = px > vw and close >= vw - vwap_noise_buffer
            slope_aligned = slope > 0.0
            flow_aligned = flow >= STRUCTURE_CHANGE_OI_CONFIRM
        elif side == "BEARISH":
            price_aligned = px < vw and close <= vw + vwap_noise_buffer
            slope_aligned = slope < 0.0
            flow_aligned = flow <= -STRUCTURE_CHANGE_OI_CONFIRM
        else:
            price_aligned = slope_aligned = flow_aligned = False
        if not price_aligned:
            reasons.append(f"price/VWAP alignment failed (spot={px:.2f}, VWAP={vw:.2f}, close={close:.2f})")
        if not slope_aligned:
            reasons.append(f"VWAP slope conflicts with {side or 'NEUTRAL'} direction (slope={slope:+.4f})")
        if not flow_aligned:
            reasons.append(f"Change-OI does not confirm {side or 'NEUTRAL'} direction (flow={flow:+.3f})")

    opposing_divergence = bool(
        side in {"BULLISH", "BEARISH"}
        and div in {"BULLISH", "BEARISH"}
        and div != side
        and near_structural_level
    )
    if opposing_divergence:
        reasons.append(f"confirmed opposing {div} RSI divergence near structural level")

    eligible = bool(
        phase_aligned and price_aligned and slope_aligned and flow_aligned
        and not opposing_divergence
    )
    if eligible:
        return True, (
            f"aligned continuous {side} PA/OI structure: spot/last close aligned with VWAP buffer, "
            f"VWAP slope aligned, Change-OI={flow:+.3f}; ADX treated as strength only"
        )
    return False, "; ".join(reasons) if reasons else "structural alignment not established"


def classify_market_regime(
    price_session: pd.DataFrame,
    current_spot: float,
    current_vwap: float,
    proposed_direction: str,
    support: float,
    resistance: float,
    indicator_history: Optional[pd.DataFrame] = None,
    *,
    structure_phase: str = "",
    structure_change_oi: float = 0.0,
    structure_vwap_slope: float = float("nan"),
    structure_entry_confirmed: bool = False,
) -> dict[str, Any]:
    """Classify market regime using live-session structure and history-seeded ADX/RSI.

    Only current-session candles determine VWAP bands, swing structure, volume
    confirmation and local reversal bars. Prior-session completed index candles
    seed Wilder ADX/RSI, allowing those indicators to be valid near the open.
    """
    work = filter_completed_candles(price_session, 3) if price_session is not None and not price_session.empty else pd.DataFrame()
    result: dict[str, Any] = {
        "direction": "NEUTRAL", "intensity": "UNKNOWN", "adx": float("nan"),
        "rsi_3m": float("nan"), "rsi_15m": float("nan"), "upper_vwap_band": float("nan"),
        "lower_vwap_band": float("nan"), "volume_confirmed": False, "divergence": "NONE",
        "near_structural_level": False, "reversal_price_confirmed": False,
        "indicator_history_bars": int(len(indicator_history)) if isinstance(indicator_history, pd.DataFrame) else 0,
        "indicator_3m_bars": 0, "indicator_15m_bars": 0,
        "structural_direction_override": False,
        "structural_direction_override_applied": False,
        "structural_direction_override_reason": "Not evaluated: insufficient completed current-session candles.",
        "session_completed_bars": 0,
        "adx_role": "TREND_STRENGTH_ONLY",
        "reason": "Insufficient completed current-session candles.",
    }
    result["session_completed_bars"] = int(len(work))
    if work.empty or len(work) < OPENING_MIN_COMPLETED_BARS or not math.isfinite(current_vwap) or current_spot <= 0:
        available_history = result["indicator_history_bars"]
        result["indicator_3m_bars"] = available_history + len(work)
        result["reason"] = (
            f"Insufficient completed current-session candles ({len(work)}/{OPENING_MIN_COMPLETED_BARS}); "
            f"prior-session indicator seed bars available={available_history}."
        )
        return result

    work = (work.sort_values("timestamp").drop_duplicates("timestamp", keep="last").reset_index(drop=True))
    for column in ("high", "low", "close", "volume"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    work = work.dropna(subset=["timestamp", "high", "low", "close"]).reset_index(drop=True)
    result["session_completed_bars"] = int(len(work))
    if len(work) < OPENING_MIN_COMPLETED_BARS:
        result["indicator_3m_bars"] = result["indicator_history_bars"] + len(work)
        result["reason"] = (
            f"Insufficient valid completed current-session candles after OHLC validation "
            f"({len(work)}/{OPENING_MIN_COMPLETED_BARS}); "
            f"prior-session indicator seed bars available={result['indicator_history_bars']}."
        )
        return result
    today = pd.to_datetime(work["timestamp"], utc=True).dt.tz_convert(IST).dt.date.iloc[-1]

    history = indicator_history.copy() if isinstance(indicator_history, pd.DataFrame) else pd.DataFrame()
    if not history.empty:
        history["timestamp"] = pd.to_datetime(history["timestamp"], utc=True, errors="coerce")
        for column in ("high", "low", "close", "open", "volume"):
            if column not in history.columns:
                history[column] = 0.0 if column == "volume" else np.nan
            history[column] = pd.to_numeric(history[column], errors="coerce")
        history = history.dropna(subset=["timestamp", "high", "low", "close"])
        history_dates = history["timestamp"].dt.tz_convert(IST).dt.date
        history = history.loc[history_dates < today]
        history = history.sort_values("timestamp").drop_duplicates("timestamp", keep="last")
    indicator_work = pd.concat([history, work], ignore_index=True, sort=False)
    indicator_work["timestamp"] = pd.to_datetime(indicator_work["timestamp"], utc=True, errors="coerce")
    indicator_work = (indicator_work.dropna(subset=["timestamp", "high", "low", "close"])
                                      .sort_values("timestamp")
                                      .drop_duplicates("timestamp", keep="last")
                                      .reset_index(drop=True))
    indicator_dates = indicator_work["timestamp"].dt.tz_convert(IST).dt.date
    rsi3_all = calculate_rsi(indicator_work["close"], 14, session_dates=indicator_dates)
    adx_values = calculate_adx(indicator_work, ADX_PERIOD)
    adx = safe_float(adx_values.iloc[-1], float("nan")) if not adx_values.empty else float("nan")
    current_mask_3m = indicator_dates.eq(today)
    current_rsi3 = rsi3_all.loc[current_mask_3m].reset_index(drop=True)
    rsi_3m = safe_float(current_rsi3.iloc[-1], float("nan")) if not current_rsi3.empty else float("nan")

    # Calculate indicator 15m RSI on the complete seeded series, but keep RSI
    # divergence detection restricted to today's 15m candles to avoid comparing
    # unrelated prior-session swings with today's structural levels.
    fifteen_all = _resample_ohlcv(indicator_work, 15)
    fifteen_today = pd.DataFrame()
    rsi15_today = pd.Series(dtype=float)
    if not fifteen_all.empty:
        fifteen_dates = pd.to_datetime(fifteen_all["timestamp"], utc=True).dt.tz_convert(IST).dt.date
        rsi15_all = calculate_rsi(fifteen_all["close"], 14, session_dates=fifteen_dates)
        current_mask_15m = fifteen_dates.eq(today)
        fifteen_today = fifteen_all.loc[current_mask_15m].reset_index(drop=True)
        rsi15_today = rsi15_all.loc[current_mask_15m].reset_index(drop=True)
    rsi_15m = safe_float(rsi15_today.iloc[-1], float("nan")) if not rsi15_today.empty else float("nan")

    _, upper_band, lower_band = calculate_vwap_bands(work)
    recent = work.tail(3)
    previous = work.iloc[-6:-3] if len(work) >= 6 else work.iloc[:-3]
    if previous.empty:
        return result
    higher_high = float(recent["high"].max()) > float(previous["high"].max())
    higher_low = float(recent["low"].min()) > float(previous["low"].min())
    lower_high = float(recent["high"].max()) < float(previous["high"].max())
    lower_low = float(recent["low"].min()) < float(previous["low"].min())
    above_vwap = current_spot > current_vwap
    below_vwap = current_spot < current_vwap
    pa_direction = "BULLISH" if higher_high and higher_low else "BEARISH" if lower_high and lower_low else "NEUTRAL"
    proposed = str(proposed_direction or "NEUTRAL").upper()
    direction = proposed
    direction_gate_reason = "directional price-action confirmation passed"
    if not ((direction == "BULLISH" and above_vwap and pa_direction == "BULLISH") or
            (direction == "BEARISH" and below_vwap and pa_direction == "BEARISH")):
        direction = "NEUTRAL"
        direction_gate_reason = (
            f"proposed={proposed}, above_vwap={above_vwap}, below_vwap={below_vwap}, "
            f"recent_swing_structure={pa_direction}, HH={higher_high}, HL={higher_low}, "
            f"LH={lower_high}, LL={lower_low}; price/VWAP plus matching swing structure required"
        )

    current_volume = safe_float(work["volume"].iloc[-1], 0.0)
    reference_volume = work["volume"].iloc[-21:-1] if len(work) > 2 else work["volume"].iloc[:-1]
    median_volume = safe_float(reference_volume.median(), 0.0) if not reference_volume.empty else 0.0
    volume_confirmed = median_volume > 0 and current_volume >= median_volume * STRONG_VOLUME_MULTIPLIER
    divergence_3m = detect_rsi_divergence(work, window=5, rsi_values=current_rsi3)
    # Use only today's completed 15m price swings for divergence; prior-session
    # bars seed RSI but are never paired with today's price pivots across the gap.
    # Four current-session bars (two-vs-two) are sufficient for an early signal
    # because it is additionally gated by 3m divergence, OI structure, and a
    # confirmed reversal bar near support/resistance. With six bars, use 3-vs-3.
    if len(fifteen_today) >= 6:
        divergence_15m = detect_rsi_divergence(fifteen_today, window=3, rsi_values=rsi15_today)
    elif len(fifteen_today) >= 4:
        divergence_15m = detect_rsi_divergence(fifteen_today, window=2, rsi_values=rsi15_today)
    else:
        divergence_15m = "NONE"
    divergence = divergence_3m if divergence_3m == divergence_15m else "NONE"
    atr_series = calculate_atr(work, ATR_PERIOD)
    atr = safe_float(atr_series.iloc[-1], 0.0) if not atr_series.empty else 0.0
    level_tolerance = max(0.75 * atr, current_spot * 0.0015)
    near_support = math.isfinite(safe_float(support, float("nan"))) and abs(current_spot - support) <= level_tolerance
    near_resistance = math.isfinite(safe_float(resistance, float("nan"))) and abs(current_spot - resistance) <= level_tolerance
    near_level = (divergence == "BULLISH" and near_support) or (divergence == "BEARISH" and near_resistance)
    last_bar = work.iloc[-1]
    prior_bar = work.iloc[-2]
    bullish_reversal_bar = (
        safe_float(last_bar.get("close"), float("nan")) > safe_float(prior_bar.get("high"), float("inf"))
        and safe_float(last_bar.get("close"), float("nan")) > safe_float(prior_bar.get("close"), float("inf"))
    )
    bearish_reversal_bar = (
        safe_float(last_bar.get("close"), float("nan")) < safe_float(prior_bar.get("low"), float("-inf"))
        and safe_float(last_bar.get("close"), float("nan")) < safe_float(prior_bar.get("close"), float("-inf"))
    )
    reversal_price_confirmed = bool(
        near_level and (
            (divergence == "BULLISH" and bullish_reversal_bar)
            or (divergence == "BEARISH" and bearish_reversal_bar)
        )
    )

    # ADX is strength only. The confirmed PA/OI state machine is the direction
    # authority; the strict recent HH/HL (or LH/LL) check is supplementary, not a
    # second independent direction veto when the structure engine is already
    # continuous and confirmed. This alignment decision is shared and testable.
    phase_upper = str(structure_phase or "").upper()
    flow_value = safe_float(structure_change_oi, 0.0)
    last_completed_close = safe_float(work["close"].iloc[-1], float("nan")) if not work.empty else float("nan")
    opposing_confirmed_divergence = bool(
        divergence in {"BULLISH", "BEARISH"} and near_level and divergence != proposed
    )
    structural_direction_override, structural_override_reason = structural_direction_override_decision(
        direction=proposed,
        structure_phase=phase_upper,
        entry_confirmed=structure_entry_confirmed,
        spot=current_spot,
        vwap=current_vwap,
        last_completed_close=last_completed_close,
        atr=atr,
        vwap_slope=structure_vwap_slope,
        change_oi=flow_value,
        divergence=divergence,
        near_structural_level=near_level,
    )
    # Keep the direction consistent across the regime matrix and strike router.
    # This does not skip downstream persistence, wall, R/R, liquidity, premium,
    # COI scoring or execution-score vetoes.
    if structural_direction_override:
        direction = proposed
        direction_gate_reason = structural_override_reason

    if not math.isfinite(adx):
        # Robust opening fallback: prior-session indicator API outages must not
        # hide live market structure. The fallback is directional only when the
        # proposed direction, current VWAP side, recent swing structure, VWAP
        # slope and a minimum price displacement all agree.
        vwap_series_open = calculate_vwap(work)
        vwap_slope_open = (
            safe_float(vwap_series_open.iloc[-1], float("nan"))
            - safe_float(vwap_series_open.iloc[-min(4, len(vwap_series_open))], float("nan"))
            if len(vwap_series_open) >= 2 else float("nan")
        )
        atr_open = safe_float(calculate_atr(work, ATR_PERIOD).iloc[-1], 0.0)
        close_series = pd.to_numeric(work["close"], errors="coerce").dropna()
        momentum_window = close_series.tail(min(5, len(close_series)))
        net_move = float(momentum_window.iloc[-1] - momentum_window.iloc[0]) if len(momentum_window) >= 2 else 0.0
        required_move = max(0.15 * atr_open, current_spot * 0.00015, 1.0)
        opening_bull = (
            proposed == "BULLISH" and above_vwap and pa_direction == "BULLISH"
            and math.isfinite(vwap_slope_open) and vwap_slope_open > 0
            and net_move >= required_move
        )
        opening_bear = (
            proposed == "BEARISH" and below_vwap and pa_direction == "BEARISH"
            and math.isfinite(vwap_slope_open) and vwap_slope_open < 0
            and net_move <= -required_move
        )
        if opening_bull or opening_bear:
            direction = proposed
            intensity = "NORMAL"
            reason = (
                f"OPENING_TAPE_FALLBACK: ADX unavailable (history={len(history)}), but VWAP, "
                f"swing structure and {len(momentum_window)}-bar movement agree; "
                f"net_move={net_move:+.2f}, required={required_move:.2f}, vwap_slope={vwap_slope_open:+.3f}."
            )
        elif structural_direction_override:
            direction = proposed
            intensity = "NORMAL"
            reason = (
                f"CONFIRMED_STRUCTURAL_CONTINUATION_OVERRIDE: ADX unavailable; {structural_override_reason}."
            )
        else:
            intensity = "UNKNOWN"
            reason = (
                f"ADX unavailable after {len(indicator_work)} seeded completed 3m bars "
                f"(history={len(history)}, current_session={len(work)}); opening fallback did not pass "
                f"VWAP/swing/momentum alignment (proposed={proposed}, PA={pa_direction}, net_move={net_move:+.2f}); "
                f"continuous-structure override={structural_direction_override}."
            )
            direction = "NEUTRAL"
    elif adx < ADX_SIDEWAYS_THRESHOLD:
        if structural_direction_override:
            direction = proposed
            intensity = "NORMAL"
            reason = (
                f"LOW_ADX_STRUCTURAL_CONTINUATION_OVERRIDE: ADX {adx:.1f} below "
                f"{ADX_SIDEWAYS_THRESHOLD:.1f}; {structural_override_reason}. "
                "ADX does not override confirmed directional structure."
            )
        else:
            intensity = "SIDEWAYS"
            reason = f"ADX {adx:.1f} below {ADX_SIDEWAYS_THRESHOLD:.1f}; continuous-structure override conditions not met."
            if opposing_confirmed_divergence:
                reason += f" Opposing {divergence} RSI divergence is confirmed near a structural level."
            direction = "NEUTRAL"
    elif divergence != "NONE" and near_level:
        intensity = "EXHAUSTION"
        direction = divergence
        reason = (
            f"Confirmed 3m/15m RSI {divergence.lower()} divergence near structural level; "
            + ("local reversal-price confirmation passed." if reversal_price_confirmed else "waiting for price to clear the preceding 3m bar extreme.")
        )
    elif (adx > ADX_STRONG_THRESHOLD and volume_confirmed and
          ((direction == "BULLISH" and math.isfinite(upper_band) and current_spot >= upper_band) or
           (direction == "BEARISH" and math.isfinite(lower_band) and current_spot <= lower_band))):
        intensity = "STRONG"
        reason = f"ADX {adx:.1f} > {ADX_STRONG_THRESHOLD:.1f}, price at outer VWAP band and volume confirmed."
    else:
        intensity = "NORMAL"
        if structural_direction_override:
            direction = proposed
            reason = (
                f"CONFIRMED_STRUCTURAL_CONTINUATION: {structural_override_reason}; "
                f"ADX={adx:.1f} is used for intensity only."
            )
        elif direction in {"BULLISH", "BEARISH"}:
            reason = f"Directional structure with ADX {adx:.1f}; strong-breakout confirmation absent."
        else:
            reason = (
                f"Direction remains NEUTRAL despite proposed={proposed}; {direction_gate_reason}; "
                f"ADX={adx:.1f}, strong-breakout confirmation absent."
            )

    return {
        "direction": direction, "intensity": intensity, "adx": adx, "rsi_3m": rsi_3m,
        "rsi_15m": rsi_15m, "upper_vwap_band": upper_band, "lower_vwap_band": lower_band,
        "volume_confirmed": bool(volume_confirmed), "divergence": divergence,
        "near_structural_level": bool(near_level),
        "reversal_price_confirmed": bool(reversal_price_confirmed),
        "indicator_history_bars": int(len(history)), "indicator_3m_bars": int(len(indicator_work)),
        "indicator_15m_bars": int(len(fifteen_all)),
        "structural_direction_override": structural_direction_override,
        "structural_direction_override_applied": bool(structural_direction_override and direction == proposed),
        "structural_direction_override_reason": structural_override_reason,
        "session_completed_bars": int(len(work)),
        "adx_role": "TREND_STRENGTH_ONLY",
        "reason": reason,
    }

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

    scenario = classify_price_oi_scenario(price_dir, oi_dir)
    if scenario == "SHORT_BUILDUP":
        regime, bias = scenario, -1
    elif scenario == "LONG_BUILDUP":
        regime, bias = scenario, 1
    elif scenario == "SHORT_COVERING":
        regime, bias = scenario, 1
    elif scenario == "LONG_UNWINDING":
        regime, bias = scenario, -1
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


# =============================================================================
# OPTION CHAIN
# =============================================================================

def _nearest_active_option_expiry() -> str:
    """Return the nearest non-expired NIFTY option expiry available to Upstox."""
    payload = api_get(
        OPTION_CONTRACT_URL,
        {"instrument_key": NIFTY_KEY},
        retries=4,
    )
    contracts = payload.get("data", [])

    if not isinstance(contracts, list) or not contracts:
        raise ScannerError("No active NIFTY option contracts returned by Upstox.")

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
            f"No active NIFTY option expiry found on or after {today.isoformat()}."
        )

    selected = min(future_expiries)
    logger.info(
        "Selected nearest active NIFTY option expiry: %s",
        selected.isoformat(),
    )
    return selected.isoformat()


def get_option_chain(state: Optional[dict[str, Any]] = None) -> tuple[str, list[dict[str, Any]]]:
    """Fetch and validate the current NIFTY option chain using the provider."""
    return DEFAULT_DATA_PROVIDER.get_option_chain(state)



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
    """Infer the chain's normal strike interval without treating missing strikes as a new step."""
    unique = sorted(set(float(x) for x in strikes))
    diffs = [
        round(unique[i + 1] - unique[i], 4)
        for i in range(len(unique) - 1)
        if unique[i + 1] > unique[i]
    ]
    if not diffs:
        raise ScannerError("Unable to determine strike interval.")

    # A sparse test/API response may contain 50-point gaps alongside 200/250-point
    # gaps. The mode (ties resolve to the smaller interval) is a better estimate
    # of the contractual step than the median in that case.
    counts: dict[float, int] = {}
    for diff in diffs:
        counts[diff] = counts.get(diff, 0) + 1
    highest_frequency = max(counts.values())
    normal_steps = [gap for gap, count in counts.items() if count == highest_frequency]
    return float(min(normal_steps))


def option_chain_atm_window(
    chain: list[dict[str, Any]],
    spot: float,
    radius_levels: int = ATM_ANALYSIS_RADIUS_LEVELS,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Return only strikes between current ATM - N steps and ATM + N steps.

    The raw chain is still fetched once and can still be retained for OI history.
    This helper restricts local analysis; it does not create per-strike API calls.
    """
    rows = chain_rows(chain)
    strikes = sorted(rows)
    step = strike_step(strikes)
    atm = nearest_strike(float(spot), strikes)
    radius = max(0, int(radius_levels))
    lower_bound = float(atm - radius * step)
    upper_bound = float(atm + radius * step)
    atm_index = strikes.index(atm)
    # The index cap guarantees no more than 2*N+1 contracts even if an unexpected
    # API response mixes strike intervals; price bounds prevent a missing strike
    # from causing a distant level to be pulled into the active window.
    index_low = max(0, atm_index - radius)
    index_high = min(len(strikes), atm_index + radius + 1)
    selected = [
        strike for strike in strikes[index_low:index_high]
        if lower_bound - 0.01 <= float(strike) <= upper_bound + 0.01
    ]
    if atm not in selected:
        raise ScannerError(
            f"ATM window integrity check failed: ATM={atm:.2f} outside [{lower_bound:.2f}, {upper_bound:.2f}]."
        )
    window_chain = [rows[strike] for strike in selected]
    meta = {
        "atm_strike": float(atm),
        "strike_step": float(step),
        "radius_levels": radius,
        "lower_bound": lower_bound,
        "upper_bound": upper_bound,
        "window_strikes": [float(x) for x in selected],
        "window_count": len(selected),
        "full_chain_count": len(strikes),
    }
    return window_chain, meta


def restrict_price_action_swings(
    swings: dict[str, list[float]],
    lower_bound: float,
    upper_bound: float,
) -> dict[str, list[float]]:
    """Keep PA reference points inside the active ATM window; never fabricate a replacement."""
    low = min(float(lower_bound), float(upper_bound))
    high = max(float(lower_bound), float(upper_bound))
    return {
        "highs": sorted({float(x) for x in swings.get("highs", []) if math.isfinite(safe_float(x, float("nan"))) and low <= float(x) <= high}),
        "lows": sorted({float(x) for x in swings.get("lows", []) if math.isfinite(safe_float(x, float("nan"))) and low <= float(x) <= high}),
    }


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
        "close_price": safe_float(market.get("close_price")),
        "oi": safe_float(market.get("oi")),
        "prev_oi": safe_float(market.get("prev_oi")),
        "volume": safe_float(market.get("volume")),
        "bid": safe_float(market.get("bid_price")),
        "ask": safe_float(market.get("ask_price")),
        "bid_qty": safe_float(market.get("bid_qty")),
        "ask_qty": safe_float(market.get("ask_qty")),
        "delta": safe_float(greeks.get("delta"), float("nan")),
        "theta": safe_float(greeks.get("theta"), 0.0),
    }



def classify_option_flow(
    option_type: str,
    price_change_pct: float,
    oi_change: float,
    noise_pct: float = STRUCTURE_ACTIVITY_PRICE_NOISE_PCT,
) -> tuple[str, int]:
    """Classify option price/OI flow into underlying directional bias."""
    option_type = str(option_type).upper()
    if option_type not in {"CE", "PE"}:
        return "UNKNOWN", 0
    if abs(float(oi_change)) <= 0:
        return "NO_OI_CHANGE", 0
    if abs(float(price_change_pct)) < noise_pct:
        return (
            "OI_BUILDING_UNCERTAIN" if oi_change > 0 else "OI_UNWINDING_UNCERTAIN",
            0,
        )

    price_up = price_change_pct > 0
    oi_up = oi_change > 0

    if option_type == "CE":
        if price_up and oi_up:
            return "CALL_BUYING", 1
        if (not price_up) and oi_up:
            return "CALL_WRITING", -1
        if price_up and (not oi_up):
            return "CALL_SHORT_COVERING", 1
        return "CALL_LONG_UNWINDING", -1

    if price_up and oi_up:
        return "PUT_BUYING", -1
    if (not price_up) and oi_up:
        return "PUT_WRITING", 1
    if price_up and (not oi_up):
        return "PUT_SHORT_COVERING", -1
    return "PUT_LONG_UNWINDING", 1


def build_option_oi_snapshot(
    chain: list[dict[str, Any]],
    expiry: str,
    *,
    now: Optional[datetime] = None,
    spot: Optional[float] = None,
) -> dict[str, Any]:
    """Build a consistent legacy snapshot for support/resistance and migration."""
    current_time = now or now_ist()
    if current_time.tzinfo is None:
        current_time = current_time.replace(tzinfo=IST)
    else:
        current_time = current_time.astimezone(IST)
    snapshot: dict[str, Any] = {
        "date": current_time.date().isoformat(),
        "expiry": str(expiry)[:10],
        "timestamp": current_time.isoformat(),
        "spot": safe_float(spot, float("nan")) if spot is not None else None,
        "strikes": {},
    }
    for row in chain:
        if not isinstance(row, dict):
            continue
        strike = safe_float(row.get("strike_price"), float("nan"))
        if not math.isfinite(strike):
            continue
        ce = option_side_data(row, "CE")
        pe = option_side_data(row, "PE")
        snapshot["strikes"][str(float(strike))] = {
            "call_oi": safe_float(ce.get("oi")),
            "put_oi": safe_float(pe.get("oi")),
            "call_ltp": safe_float(ce.get("ltp")),
            "put_ltp": safe_float(pe.get("ltp")),
        }
    return snapshot


def update_option_oi_velocity_history(
    state: dict[str, Any],
    chain: list[dict[str, Any]],
    expiry: str,
    *,
    now: Optional[datetime] = None,
    spot: Optional[float] = None,
) -> dict[float, dict[str, Any]]:
    """Persist OI/LTP snapshots and calculate the time-of-day COI matrix inputs.

    09:15-09:45: compare cumulatively with the earliest usable same-session snapshot.
    09:45 onward: compare with the best-overlap snapshot aged 15-30 minutes.
    Missing history is explicitly unavailable; it never fabricates a directional score.
    """
    current_time = now or now_ist()
    if current_time.tzinfo is None:
        current_time = current_time.replace(tzinfo=IST)
    else:
        current_time = current_time.astimezone(IST)
    today = current_time.date().isoformat()
    expiry_key = str(expiry)[:10]
    now_stamp = pd.Timestamp(current_time)
    cold_start = current_time.time() < COI_COLD_START_END
    current_spot = safe_float(spot, float("nan")) if spot is not None else float("nan")

    rows = chain_rows(chain)
    current_by_key: dict[str, dict[str, Any]] = {}
    current_by_contract: dict[str, dict[str, Any]] = {}
    current_instrument_by_contract: dict[str, str] = {}
    for strike, row in rows.items():
        for side in ("CE", "PE"):
            data = option_side_data(row, side)
            oi = safe_float(data.get("oi"), float("nan"))
            if not math.isfinite(oi) or oi <= 0:
                continue
            ltp = safe_float(data.get("ltp"), float("nan"))
            record = {"strike": float(strike), "side": side, "oi": float(oi), "ltp": ltp}
            instrument_key = str(data.get("instrument_key") or "").strip()
            contract_key = f"{float(strike):.2f}|{side}"
            if instrument_key:
                current_by_key[instrument_key] = record
                current_instrument_by_contract[contract_key] = instrument_key
            current_by_contract[contract_key] = record

    def normalize_timestamp(raw: Any) -> Optional[pd.Timestamp]:
        try:
            stamp = pd.Timestamp(raw)
            if pd.isna(stamp):
                return None
            return stamp.tz_localize(IST) if stamp.tzinfo is None else stamp.tz_convert(IST)
        except (TypeError, ValueError, OverflowError):
            return None

    def finite_record(raw: Any, key: str, *, positive: bool = False) -> float:
        value = safe_float(raw.get(key), float("nan")) if isinstance(raw, dict) else float("nan")
        if not math.isfinite(value) or (positive and value <= 0):
            return float("nan")
        return value

    def normalize_history_item(item: Any) -> Optional[dict[str, Any]]:
        if not isinstance(item, dict):
            return None
        stamp = normalize_timestamp(item.get("timestamp"))
        if stamp is None:
            return None
        item_date = str(item.get("date") or stamp.date().isoformat())[:10]
        item_expiry = str(item.get("expiry") or "")[:10]
        if item_date != today or item_expiry != expiry_key or stamp.time() < time(9, 15):
            return None
        age = (now_stamp - stamp).total_seconds() / 60.0
        if age < 0 or age > OPTION_OI_HISTORY_KEEP_MINUTES:
            return None

        by_instrument: dict[str, dict[str, Any]] = {}
        raw_by_instrument = item.get("oi_by_instrument", {})
        if isinstance(raw_by_instrument, dict):
            for key, detail in raw_by_instrument.items():
                if not isinstance(detail, dict):
                    continue
                strike_value = finite_record(detail, "strike")
                side_value = str(detail.get("side", "")).upper()
                oi_value = finite_record(detail, "oi", positive=True)
                if math.isfinite(strike_value) and side_value in {"CE", "PE"} and math.isfinite(oi_value):
                    by_instrument[str(key).strip()] = {
                        "strike": strike_value, "side": side_value, "oi": oi_value,
                        "ltp": finite_record(detail, "ltp", positive=True),
                    }

        by_contract: dict[str, dict[str, Any]] = {}
        raw_by_contract = item.get("oi_by_contract", {})
        if isinstance(raw_by_contract, dict):
            for key, detail in raw_by_contract.items():
                if not isinstance(detail, dict):
                    continue
                strike_value = finite_record(detail, "strike")
                side_value = str(detail.get("side", "")).upper()
                oi_value = finite_record(detail, "oi", positive=True)
                if math.isfinite(strike_value) and side_value in {"CE", "PE"} and math.isfinite(oi_value):
                    by_contract[f"{strike_value:.2f}|{side_value}"] = {
                        "strike": strike_value, "side": side_value, "oi": oi_value,
                        "ltp": finite_record(detail, "ltp", positive=True),
                    }

        # Backfill logical keys from historical instrument-keyed state.
        for detail in by_instrument.values():
            by_contract.setdefault(f"{detail['strike']:.2f}|{detail['side']}", dict(detail))

        # Migrate the older strikes[strike].call_oi/put_oi format, preserving LTP when present.
        legacy_strikes = item.get("strikes", {})
        if isinstance(legacy_strikes, dict):
            for raw_strike, detail in legacy_strikes.items():
                if not isinstance(detail, dict):
                    continue
                strike_value = safe_float(raw_strike, float("nan"))
                if not math.isfinite(strike_value):
                    continue
                for side, oi_field, ltp_field in (
                    ("CE", "call_oi", "call_ltp"), ("PE", "put_oi", "put_ltp")
                ):
                    oi_value = finite_record(detail, oi_field, positive=True)
                    if math.isfinite(oi_value):
                        key = f"{strike_value:.2f}|{side}"
                        legacy_record = {
                            "strike": strike_value, "side": side, "oi": oi_value,
                            "ltp": finite_record(detail, ltp_field, positive=True),
                        }
                        existing = by_contract.get(key)
                        if not isinstance(existing, dict) or not math.isfinite(finite_record(existing, "oi", positive=True)):
                            by_contract[key] = legacy_record
                        elif not math.isfinite(finite_record(existing, "ltp", positive=True)) and math.isfinite(legacy_record["ltp"]):
                            existing["ltp"] = legacy_record["ltp"]

        if not by_instrument and not by_contract:
            return None
        stored_spot = finite_record(item, "spot", positive=True)
        return {
            "date": today, "expiry": expiry_key, "timestamp": stamp.isoformat(),
            "spot": stored_spot if math.isfinite(stored_spot) else None,
            "oi_by_instrument": by_instrument, "oi_by_contract": by_contract,
        }

    raw_history = state.get("option_oi_history")
    if not isinstance(raw_history, list):
        raw_history = []
    valid_by_timestamp: dict[str, dict[str, Any]] = {}
    for item in raw_history:
        normalized = normalize_history_item(item)
        if normalized:
            valid_by_timestamp[normalized["timestamp"]] = normalized

    legacy_snapshot = normalize_history_item(state.get("option_oi_snapshot"))
    if legacy_snapshot:
        valid_by_timestamp.setdefault(legacy_snapshot["timestamp"], legacy_snapshot)
    valid_history = sorted(
        valid_by_timestamp.values(),
        key=lambda item: normalize_timestamp(item["timestamp"]) or pd.Timestamp.min.tz_localize(IST),
    )

    # Contract overlap uses logical strike+side keys so an API instrument-key change
    # cannot make a valid historical baseline appear empty.
    baseline_candidates: list[tuple[int, float, dict[str, Any]]] = []
    age_window_count = 0
    for item in valid_history:
        stamp = normalize_timestamp(item.get("timestamp"))
        if stamp is None:
            continue
        age = (now_stamp - stamp).total_seconds() / 60.0
        if age <= 0.25:
            continue
        if cold_start:
            if age > OPTION_OI_HISTORY_KEEP_MINUTES or stamp.time() < time(9, 15):
                continue
        else:
            if not OPTION_OI_MIN_AGE_MINUTES <= age <= OPTION_OI_MAX_AGE_MINUTES:
                continue
            age_window_count += 1
        baseline_by_key = item.get("oi_by_instrument", {})
        baseline_by_contract = item.get("oi_by_contract", {})
        overlap = 0
        for contract_key, current in current_by_contract.items():
            old = baseline_by_contract.get(contract_key) if isinstance(baseline_by_contract, dict) else None
            if not isinstance(old, dict):
                instr = current_instrument_by_contract.get(contract_key, "")
                old = baseline_by_key.get(instr) if isinstance(baseline_by_key, dict) else None
            if isinstance(old, dict) and math.isfinite(finite_record(old, "oi", positive=True)):
                overlap += 1
        if overlap:
            baseline_candidates.append((overlap, age, item))

    baseline: dict[str, Any] = {}
    baseline_age = float("nan")
    baseline_coverage = 0
    if baseline_candidates:
        if cold_start:
            # Cumulative opening comparison: choose the earliest observed snapshot
            # with usable overlap, not the nearest/most convenient snapshot.
            baseline_coverage, baseline_age, baseline = max(
                baseline_candidates, key=lambda candidate: (candidate[1], candidate[0])
            )
            baseline_mode = "COLD_START_CUMULATIVE"
        else:
            baseline_coverage, baseline_age, baseline = max(
                baseline_candidates, key=lambda candidate: (candidate[0], -abs(candidate[1] - 20.0))
            )
            baseline_mode = "ROLLING_15_30"
    else:
        baseline_mode = "COLD_START_WAIT" if cold_start else "ROLLING_WAIT"

    baseline_by_instrument = baseline.get("oi_by_instrument", {}) if baseline else {}
    baseline_by_contract = baseline.get("oi_by_contract", {}) if baseline else {}
    baseline_spot = finite_record(baseline, "spot", positive=True) if baseline else float("nan")
    underlying_change_pct = (
        (current_spot - baseline_spot) / baseline_spot
        if math.isfinite(current_spot) and current_spot > 0 and math.isfinite(baseline_spot) and baseline_spot > 0
        else float("nan")
    )

    def old_record(instrument_key: str, contract_key: str) -> dict[str, Any]:
        old = baseline_by_instrument.get(instrument_key, {}) if isinstance(baseline_by_instrument, dict) else {}
        contract = baseline_by_contract.get(contract_key, {}) if isinstance(baseline_by_contract, dict) else {}
        if not isinstance(old, dict):
            old = {}
        if not isinstance(contract, dict):
            contract = {}
        old_oi = finite_record(old, "oi", positive=True)
        contract_oi = finite_record(contract, "oi", positive=True)
        if not math.isfinite(old_oi) and math.isfinite(contract_oi):
            return contract
        if not math.isfinite(finite_record(old, "ltp", positive=True)) and math.isfinite(finite_record(contract, "ltp", positive=True)):
            merged = dict(old)
            merged["ltp"] = contract["ltp"]
            return merged
        return old

    by_strike: dict[float, dict[str, Any]] = {}
    for strike, row in rows.items():
        side_values: dict[str, dict[str, Any]] = {}
        for side, field_prefix in (("CE", "call"), ("PE", "put")):
            current = option_side_data(row, side)
            instrument_key = str(current.get("instrument_key") or "").strip()
            contract_key = f"{float(strike):.2f}|{side}"
            old = old_record(instrument_key, contract_key) if baseline else {}
            old_oi = finite_record(old, "oi", positive=True)
            new_oi = safe_float(current.get("oi"), float("nan"))
            old_ltp = finite_record(old, "ltp", positive=True)
            new_ltp = safe_float(current.get("ltp"), float("nan"))
            oi_available = math.isfinite(old_oi) and old_oi > 0 and math.isfinite(new_oi) and new_oi > 0
            ltp_available = math.isfinite(old_ltp) and old_ltp > 0 and math.isfinite(new_ltp) and new_ltp > 0
            oi_change = new_oi - old_oi if oi_available else float("nan")
            ltp_change_pct = (new_ltp - old_ltp) / old_ltp if ltp_available else float("nan")
            side_values[field_prefix] = {
                "available": bool(oi_available),
                "oi_change": oi_change,
                "oi_change_pct": oi_change / old_oi if oi_available else float("nan"),
                "ltp_change_pct": ltp_change_pct,
                "old_oi": old_oi,
                "current_oi": new_oi,
                "old_ltp": old_ltp,
                "current_ltp": new_ltp,
            }
        call = side_values["call"]
        put = side_values["put"]
        by_strike[float(strike)] = {
            "available": bool(call["available"] or put["available"]),
            "call_available": call["available"], "put_available": put["available"],
            "call_oi_change": call["oi_change"], "put_oi_change": put["oi_change"],
            "call_oi_change_pct": call["oi_change_pct"], "put_oi_change_pct": put["oi_change_pct"],
            "call_ltp_change_pct": call["ltp_change_pct"], "put_ltp_change_pct": put["ltp_change_pct"],
            "underlying_change_pct": underlying_change_pct,
            "baseline_minutes": baseline_age,
            "baseline_mode": baseline_mode,
            "baseline_timestamp": baseline.get("timestamp") if baseline else None,
            "pin": bool(
                math.isfinite(call["oi_change_pct"]) and math.isfinite(put["oi_change_pct"])
                and call["oi_change_pct"] >= COI_STRONG_CHANGE_PCT
                and put["oi_change_pct"] >= COI_STRONG_CHANGE_PCT
            ),
        }

    # Keep the full chain in the history ring so the baseline survives ATM shifts,
    # but scope all live profit-booking/guard decisions to the current ATM +/-4 window.
    try:
        if math.isfinite(current_spot) and current_spot > 0:
            _, active_window_meta = option_chain_atm_window(chain, current_spot)
            active_window_strikes = {float(x) for x in active_window_meta.get("window_strikes", [])}
        else:
            active_window_strikes = set()
    except ScannerError:
        active_window_strikes = set()
    decision_velocity_by_strike = {
        float(k): v for k, v in by_strike.items()
        if float(k) in active_window_strikes and isinstance(v, dict)
    }
    logger.info(
        "COI HISTORY/DECISION SCOPE: full_chain_snapshots_retained=%d contracts; current_window_velocity=%d/%d strikes",
        len(current_by_contract), len(decision_velocity_by_strike), len(active_window_strikes),
    )
    profit_booking_event: Optional[dict[str, Any]] = None
    call_long_unwind = any(
        math.isfinite(v.get("call_oi_change_pct", float("nan")))
        and v["call_oi_change_pct"] <= -COI_STRONG_CHANGE_PCT
        and math.isfinite(v.get("call_ltp_change_pct", float("nan")))
        and v["call_ltp_change_pct"] <= -STRUCTURE_ACTIVITY_PRICE_NOISE_PCT
        for v in decision_velocity_by_strike.values()
    )
    put_long_unwind = any(
        math.isfinite(v.get("put_oi_change_pct", float("nan")))
        and v["put_oi_change_pct"] <= -COI_STRONG_CHANGE_PCT
        and math.isfinite(v.get("put_ltp_change_pct", float("nan")))
        and v["put_ltp_change_pct"] <= -STRUCTURE_ACTIVITY_PRICE_NOISE_PCT
        for v in decision_velocity_by_strike.values()
    )
    if math.isfinite(underlying_change_pct):
        if underlying_change_pct <= -COI_UNDERLYING_MOVE_PCT and call_long_unwind:
            profit_booking_event = {
                "blocked_direction": "BULLISH", "reason": "CALL_LONG_UNWINDING_PROFIT_BOOKING",
                "date": today, "expiry": expiry_key, "timestamp": current_time.isoformat(),
                "underlying_change_pct": underlying_change_pct,
            }
        elif underlying_change_pct >= COI_UNDERLYING_MOVE_PCT and put_long_unwind:
            profit_booking_event = {
                "blocked_direction": "BEARISH", "reason": "PUT_LONG_UNWINDING_PROFIT_BOOKING",
                "date": today, "expiry": expiry_key, "timestamp": current_time.isoformat(),
                "underlying_change_pct": underlying_change_pct,
            }

    rows_for_writing = [(float(k), v) for k, v in decision_velocity_by_strike.items()]
    strike_step_value = max(strike_step(sorted(rows)), 1.0) if rows else 50.0
    def fresh_structural_writing(direction: str) -> bool:
        if not math.isfinite(current_spot) or not by_strike:
            return False
        for strike, v in rows_for_writing:
            if abs(strike - current_spot) > 4 * strike_step_value:
                continue
            if direction == "BULLISH":
                change = safe_float(v.get("put_oi_change_pct"), float("nan"))
                premium_change = safe_float(v.get("put_ltp_change_pct"), float("nan"))
                located = strike <= current_spot + strike_step_value
            else:
                change = safe_float(v.get("call_oi_change_pct"), float("nan"))
                premium_change = safe_float(v.get("call_ltp_change_pct"), float("nan"))
                located = strike >= current_spot - strike_step_value
            if located and math.isfinite(change) and change >= COI_STRONG_CHANGE_PCT and math.isfinite(premium_change) and premium_change <= STRUCTURE_ACTIVITY_PRICE_NOISE_PCT:
                return True
        return False

    guard = state.get("coi_market_guard")
    if not isinstance(guard, dict) or guard.get("date") != today or str(guard.get("expiry", ""))[:10] != expiry_key:
        guard = None
        state.pop("coi_market_guard", None)
    if isinstance(guard, dict):
        guarded_direction = str(guard.get("blocked_direction", "")).upper()
        if guarded_direction in {"BULLISH", "BEARISH"} and fresh_structural_writing(guarded_direction):
            logger.info("COI PROFIT-BOOKING GUARD CLEARED: fresh %s structural writing confirmed.", guarded_direction)
            state.pop("coi_market_guard", None)
            guard = None
    if profit_booking_event:
        blocked = str(profit_booking_event["blocked_direction"])
        if not fresh_structural_writing(blocked):
            state["coi_market_guard"] = profit_booking_event
            logger.warning(
                "COI PROFIT-BOOKING GUARD: blocked_direction=%s reason=%s underlying_change=%+.3f%%; waiting for fresh structural writing.",
                blocked, profit_booking_event["reason"], underlying_change_pct * 100.0,
            )

    current_snapshot = {
        "date": today, "expiry": expiry_key, "timestamp": current_time.isoformat(),
        "spot": current_spot if math.isfinite(current_spot) else None,
        "oi_by_instrument": current_by_key, "oi_by_contract": current_by_contract,
    }
    if current_snapshot["timestamp"] not in valid_by_timestamp:
        valid_history.append(current_snapshot)
    history_limit = max(OPTION_OI_HISTORY_KEEP_MINUTES + 10, 40)
    state["option_oi_history"] = valid_history[-history_limit:]

    available_strikes = sum(1 for v in by_strike.values() if v.get("available"))
    baseline_timestamp = baseline.get("timestamp") if baseline else None
    reason = (
        "OK" if math.isfinite(baseline_age) and available_strikes else
        "COLD_START_BASELINE_NOT_YET_AVAILABLE" if cold_start else
        "BASELINE_NOT_YET_15_MIN_OLD" if age_window_count == 0 else
        "NO_CONTRACT_OVERLAP_WITH_BASELINE" if not baseline_candidates else
        "OI_MISSING_ON_ONE_SIDE"
    )
    latest_age = float("nan")
    if valid_history:
        latest_stamp = normalize_timestamp(valid_history[-1].get("timestamp"))
        if latest_stamp is not None:
            latest_age = max((now_stamp - latest_stamp).total_seconds() / 60.0, 0.0)
    logger.info(
        "OPTION COI MATRIX DATA: protocol=%s status=%s baseline_mode=%s baseline_age_min=%s "
        "baseline_timestamp=%s eligible_snapshots=%d history_snapshots=%d current_contracts=%d "
        "baseline_overlap=%d strikes_with_coi=%d/%d latest_snapshot_age_min=%s reason=%s state_file=%s",
        "COLD_START_09:15_09:45" if cold_start else "ROLLING_15_30_AFTER_09:45",
        "AVAILABLE" if math.isfinite(baseline_age) and available_strikes else "WARMING_UP",
        baseline_mode, f"{baseline_age:.1f}" if math.isfinite(baseline_age) else "NA",
        baseline_timestamp or "NA", age_window_count, len(state["option_oi_history"]), len(current_by_contract),
        baseline_coverage, available_strikes, len(by_strike),
        f"{latest_age:.1f}" if math.isfinite(latest_age) else "NA", reason, STATE_FILE,
    )
    return by_strike


def score_coi_matrix_for_strike(
    direction: str,
    strike: float,
    atm: float,
    step: float,
    velocity_map: dict[float, dict[str, Any]],
    *,
    now: Optional[datetime] = None,
) -> dict[str, Any]:
    """Score Push, Floor, Roll and Wall from measured OI/LTP changes.

    COI percentages are fractions (0.01 == 1%). Pin is a hard disqualifier;
    all other COI points/penalties are weighted down during the 09:15-09:45 cold start.
    """
    direction = str(direction).upper()
    current_time = now or now_ist()
    if current_time.tzinfo is None:
        current_time = current_time.replace(tzinfo=IST)
    else:
        current_time = current_time.astimezone(IST)
    cold_start = current_time.time() < COI_COLD_START_END
    coi_weight = max(0.0, min(COI_COLD_START_WEIGHT, 1.0)) if cold_start else 1.0
    threshold = max(COI_STRONG_CHANGE_PCT, 1e-6)
    noise = STRUCTURE_ACTIVITY_PRICE_NOISE_PCT

    def row_for(value: float) -> dict[str, Any]:
        item = velocity_map.get(float(value), {}) if isinstance(velocity_map, dict) else {}
        return item if isinstance(item, dict) and item.get("available") else {}

    row = row_for(strike)
    if not row:
        return {"available": False, "disqualified": False, "push": 0.0, "floor": 0.0,
                "roll": 0.0, "wall_penalty": 0.0, "score": 0.0, "weight": coi_weight,
                "label": "COI_UNAVAILABLE", "baseline_mode": "UNAVAILABLE", "reason": "No same-session OI baseline"}

    call_pct = safe_float(row.get("call_oi_change_pct"), float("nan"))
    put_pct = safe_float(row.get("put_oi_change_pct"), float("nan"))
    call_ltp_pct = safe_float(row.get("call_ltp_change_pct"), float("nan"))
    put_ltp_pct = safe_float(row.get("put_ltp_change_pct"), float("nan"))
    baseline_mode = str(row.get("baseline_mode", "UNKNOWN"))
    pin = bool(
        math.isfinite(call_pct) and math.isfinite(put_pct)
        and call_pct >= threshold and put_pct >= threshold
    )
    if pin:
        return {"available": True, "disqualified": True, "push": 0.0, "floor": 0.0,
                "roll": 0.0, "wall_penalty": 0.0, "score": float("-inf"), "weight": coi_weight,
                "label": "PIN_DISQUALIFICATION", "baseline_mode": baseline_mode,
                "reason": "Large positive Call and Put COI at the same strike"}

    if direction == "BULLISH":
        push_strength = min(max(-call_pct, 0.0) / threshold, 1.0) if math.isfinite(call_pct) and math.isfinite(call_ltp_pct) and call_ltp_pct >= noise else 0.0
        floor_strength = min(max(put_pct, 0.0) / threshold, 1.0) if math.isfinite(put_pct) and math.isfinite(put_ltp_pct) and put_ltp_pct <= noise else 0.0
        opposing_pct = call_pct
        atm_opposing_pct = safe_float(row_for(atm).get("call_oi_change_pct"), float("nan"))
        atm_opposing_ltp = safe_float(row_for(atm).get("call_ltp_change_pct"), float("nan"))
        far_wall_candidates = [
            s for s, v in velocity_map.items()
            if isinstance(s, (int, float)) and float(s) >= atm + step - 0.01
            and math.isfinite(safe_float(v.get("call_oi_change_pct"), float("nan")))
            and safe_float(v.get("call_oi_change_pct"), float("nan")) >= threshold
        ]
        roll_active = (
            math.isfinite(atm_opposing_pct) and atm_opposing_pct <= -threshold
            and math.isfinite(atm_opposing_ltp) and atm_opposing_ltp >= noise
            and any(float(strike) < float(wall) - 0.01 for wall in far_wall_candidates)
        )
    else:
        push_strength = min(max(-put_pct, 0.0) / threshold, 1.0) if math.isfinite(put_pct) and math.isfinite(put_ltp_pct) and put_ltp_pct >= noise else 0.0
        floor_strength = min(max(call_pct, 0.0) / threshold, 1.0) if math.isfinite(call_pct) and math.isfinite(call_ltp_pct) and call_ltp_pct <= noise else 0.0
        opposing_pct = put_pct
        atm_opposing_pct = safe_float(row_for(atm).get("put_oi_change_pct"), float("nan"))
        atm_opposing_ltp = safe_float(row_for(atm).get("put_ltp_change_pct"), float("nan"))
        far_wall_candidates = [
            s for s, v in velocity_map.items()
            if isinstance(s, (int, float)) and float(s) <= atm - step + 0.01
            and math.isfinite(safe_float(v.get("put_oi_change_pct"), float("nan")))
            and safe_float(v.get("put_oi_change_pct"), float("nan")) >= threshold
        ]
        roll_active = (
            math.isfinite(atm_opposing_pct) and atm_opposing_pct <= -threshold
            and math.isfinite(atm_opposing_ltp) and atm_opposing_ltp >= noise
            and any(float(strike) > float(wall) + 0.01 for wall in far_wall_candidates)
        )

    roll_score = COI_ROLL_MAX_POINTS if roll_active else 0.0
    wall_penalty = 0.0
    if math.isfinite(opposing_pct) and opposing_pct >= threshold:
        # A confirmed opposing OI wall is the full configured penalty, not a
        # fractional adjustment that could leave a wall strike executable.
        wall_penalty = COI_WALL_MAX_PENALTY
    push_points = COI_PUSH_MAX_POINTS * push_strength
    floor_points = COI_FLOOR_MAX_POINTS * floor_strength
    raw_score = push_points + floor_points + roll_score - wall_penalty
    weighted_score = raw_score * coi_weight
    labels = []
    if push_points > 0:
        labels.append("PUSH")
    if floor_points > 0:
        labels.append("FLOOR")
    if roll_score > 0:
        labels.append("ROLL")
    if wall_penalty > 0:
        labels.append("WALL_PENALTY")
    label = "+".join(labels) if labels else "NO_CLEAR_COI_EDGE"
    return {
        "available": True, "disqualified": False,
        "push": push_points, "floor": floor_points, "roll": roll_score,
        "wall_penalty": wall_penalty, "score": weighted_score,
        "raw_score": raw_score, "weight": coi_weight,
        "label": label, "baseline_mode": baseline_mode,
        "reason": ";".join(labels) if labels else "No qualifying Push/Floor/Roll/Wall condition",
    }

def permitted_strikes_for_regime(
    atm: float,
    step: float,
    direction: str,
    intensity: str,
    *,
    is_expiry_day: bool = False,
    now: Optional[datetime] = None,
) -> list[float]:
    """Return the single authoritative strike-routing array for all call sites."""
    direction = str(direction).upper()
    intensity = str(intensity).upper()
    if direction not in {"BULLISH", "BEARISH"} or step <= 0 or intensity in {"SIDEWAYS", "UNKNOWN"}:
        return []
    # The 15:15 hard cutoff overrides every regime, including expiry-day routing.
    window = time_of_day_window(now)
    if window == "CUTOFF":
        return []
    if is_expiry_day:
        # On expiry, evaluate a second ITM strike as well. Deep(er) ITM options
        # may offer a better delta/continuation profile when the move is strong.
        # The score/liquidity/COI gates still choose the contract; this is not a
        # guarantee that a specific strike is the future maximum-return choice.
        return [atm - 2 * step, atm - step, atm] if direction == "BULLISH" else [atm, atm + step, atm + 2 * step]
    if intensity == "EXHAUSTION":
        return [atm - 2 * step, atm - 3 * step] if direction == "BULLISH" else [atm + 2 * step, atm + 3 * step]
    # OTM candidates are only allowed after 13:30 and only for a confirmed STRONG regime.
    if intensity == "STRONG" and window == "AFTERNOON":
        return [atm, atm + step, atm + 2 * step] if direction == "BULLISH" else [atm - 2 * step, atm - step, atm]
    # Opening and normal/midday conditions keep the candidate set ATM/ITM only.
    return [atm - step, atm] if direction == "BULLISH" else [atm, atm + step]


def is_confirmed_local_break(event: Optional[dict[str, Any]]) -> bool:
    """True only for a price-confirmed directional breakout/breakdown event."""
    if not isinstance(event, dict) or not bool(event.get("confirmed")):
        return False
    return (
        str(event.get("kind", "")).upper() in {"BREAKOUT", "BREAKDOWN"}
        and str(event.get("direction", "")).upper() in {"BULLISH", "BEARISH"}
        and math.isfinite(safe_float(event.get("level"), float("nan")))
    )



def is_confirmed_local_rejection(event: Optional[dict[str, Any]]) -> bool:
    """True for a completed-bar support bounce or resistance rejection with a valid level."""
    if not isinstance(event, dict) or not bool(event.get("confirmed")):
        return False
    return (
        str(event.get("kind", "")).upper() in {"SUPPORT_BOUNCE", "RESISTANCE_REJECTION"}
        and str(event.get("direction", "")).upper() in {"BULLISH", "BEARISH"}
        and math.isfinite(safe_float(event.get("level"), float("nan")))
    )


def is_confirmed_local_directional_event(event: Optional[dict[str, Any]]) -> bool:
    """True for a fully confirmed local break or wall rejection/bounce event."""
    return is_confirmed_local_break(event) or is_confirmed_local_rejection(event)


def cold_start_entry_gate_passed(
    *,
    current_time: time,
    volume_confirmed: bool,
    directional_break: bool,
    opening_tape_aligned: bool,
    local_event_entry: bool,
    confirmed_local_event_override: bool,
) -> bool:
    """Apply the opening-session gate without discarding confirmed structure events.

    A confirmed completed-bar OI breakout/breakdown or wall bounce/rejection is an
    independent opening trigger. It still must pass downstream wall clearance,
    structural T1/SL, reward-to-risk, persistence where applicable, and option-quality
    checks; this helper only avoids rejecting it for unrelated cold-start proxies.
    """
    if current_time >= COI_COLD_START_END:
        return True
    confirmed_event_trigger = bool(local_event_entry and confirmed_local_event_override)
    return bool(
        volume_confirmed
        or directional_break
        or opening_tape_aligned
        or confirmed_event_trigger
    )


def structural_reward_risk_ratio(
    direction: str, spot: float, target_1: float, stop: float
) -> tuple[float, float, float]:
    """Return (ratio, reward, risk) using NIFTY structural T1 and stop levels."""
    side = str(direction or "").upper()
    price = safe_float(spot, float("nan"))
    target = safe_float(target_1, float("nan"))
    stop_value = safe_float(stop, float("nan"))
    if not all(math.isfinite(v) for v in (price, target, stop_value)):
        return 0.0, 0.0, 0.0
    if side == "BEARISH":
        reward, risk = price - target, stop_value - price
    elif side == "BULLISH":
        reward, risk = target - price, price - stop_value
    else:
        return 0.0, 0.0, 0.0
    if reward <= 0 or risk <= 0:
        return 0.0, max(reward, 0.0), max(risk, 0.0)
    return reward / risk, reward, risk


def opposing_oi_wall_veto(
    direction: str,
    spot: float,
    support: float,
    resistance: float,
    strike_step_value: float,
    *,
    confirmed_local_break: bool = False,
    confirmed_local_rejection: bool = False,
    clearance_steps: Optional[float] = None,
) -> str:
    """Block entries near an opposing OI wall, except validated breaks/rejections."""
    direction = str(direction or "").upper()
    step = max(safe_float(strike_step_value, 50.0), 1.0)
    clearance = max(0.5, safe_float(clearance_steps, MIN_OPPOSING_WALL_CLEARANCE_STEPS)) * step
    if confirmed_local_break or confirmed_local_rejection:
        return ""
    if direction == "BULLISH" and math.isfinite(safe_float(resistance, float("nan"))):
        wall = safe_float(resistance, float("nan"))
        gap = wall - safe_float(spot)
        if gap >= -0.20 * step and gap < clearance:
            return f"NEAR_RESISTANCE_VETO wall={wall:.2f} spot={spot:.2f} runway={max(gap,0.0):.2f} required={clearance:.2f}"
    if direction == "BEARISH" and math.isfinite(safe_float(support, float("nan"))):
        wall = safe_float(support, float("nan"))
        gap = safe_float(spot) - wall
        if gap >= -0.20 * step and gap < clearance:
            return f"NEAR_SUPPORT_VETO wall={wall:.2f} spot={spot:.2f} runway={max(gap,0.0):.2f} required={clearance:.2f}"
    return ""


def collect_option_premium_vwaps(
    chain: list[dict[str, Any]],
    spot: float,
    direction: str,
    intensity: str,
    *,
    is_expiry_day: bool,
    now: Optional[datetime] = None,
) -> dict[str, dict[str, float]]:
    """Fetch completed 1-minute option candles and calculate each contract's own VWAP."""
    decision_chain, window_meta = option_chain_atm_window(chain, spot)
    rows = chain_rows(decision_chain)
    strikes = sorted(rows)
    step = safe_float(window_meta.get("strike_step"), strike_step(strikes))
    atm = safe_float(window_meta.get("atm_strike"), nearest_strike(spot, strikes))
    option_type = "CE" if direction == "BULLISH" else "PE"
    targets = permitted_strikes_for_regime(
        atm, step, direction, intensity, is_expiry_day=is_expiry_day, now=now
    )
    result: dict[str, dict[str, float]] = {}
    for target in targets:
        matched = min(strikes, key=lambda value: abs(value - target))
        if abs(matched - target) > 0.01:
            continue
        data = option_side_data(rows[matched], option_type)
        key = str(data.get("instrument_key") or "").strip()
        if not key:
            continue
        try:
            candles = get_intraday_candles(key, 1, strict=False)
            completed = filter_completed_candles(candles, 1) if not candles.empty else pd.DataFrame()
            if completed.empty or safe_float(completed["volume"].sum(), 0.0) <= 0:
                logger.info("OPTION PREMIUM VWAP UNAVAILABLE: %s %.0f; candidate will be rejected.", option_type, matched)
                continue
            vwap_series = calculate_vwap(completed)
            premium_vwap = safe_float(vwap_series.iloc[-1], float("nan")) if not vwap_series.empty else float("nan")
            if math.isfinite(premium_vwap) and premium_vwap > 0:
                result[key] = {"premium_vwap": premium_vwap}
                logger.info(
                    "OPTION PREMIUM VWAP: %s %.0f LTP=%.2f VWAP=%.2f above=%s",
                    option_type, matched, safe_float(data.get("ltp")), premium_vwap,
                    safe_float(data.get("ltp")) > premium_vwap,
                )
        except (ScannerError, KeyError, ValueError, TypeError) as exc:
            logger.info("OPTION PREMIUM VWAP UNAVAILABLE: %s %.0f: %s", option_type, matched, exc)
    return result


def _intraday_option_changes(
    chain: list[dict[str, Any]],
    previous_snapshot: Optional[dict[str, Any]],
    change_oi_by_strike: Optional[dict[float, dict[str, float]]],
    expiry: str,
) -> tuple[dict[float, dict[str, Any]], str]:
    """Calculate scan-to-scan OI changes; use API day-change only on the first scan of a session."""
    rows = chain_rows(chain)
    today = now_ist().date().isoformat()
    same_day = bool(
        isinstance(previous_snapshot, dict)
        and str(previous_snapshot.get("date", "")) == today
        and str(previous_snapshot.get("expiry", "")) == str(expiry)
        and isinstance(previous_snapshot.get("strikes"), dict)
    )
    prior = previous_snapshot.get("strikes", {}) if same_day else {}
    mode = "INTRADAY_SNAPSHOT" if same_day and prior else "DAY_CHANGE_API_WARMUP"
    out: dict[float, dict[str, Any]] = {}

    for strike, row in rows.items():
        ce = option_side_data(row, "CE")
        pe = option_side_data(row, "PE")
        api = (change_oi_by_strike or {}).get(float(strike), {})
        old = prior.get(str(float(strike)), {}) if same_day else {}

        if same_day and old:
            call_oi_change = safe_float(ce.get("oi")) - safe_float(old.get("call_oi"))
            put_oi_change = safe_float(pe.get("oi")) - safe_float(old.get("put_oi"))
            old_call_ltp = safe_float(old.get("call_ltp"))
            old_put_ltp = safe_float(old.get("put_ltp"))
            call_price_change = (
                (safe_float(ce.get("ltp")) - old_call_ltp) / old_call_ltp
                if old_call_ltp > 0 else 0.0
            )
            put_price_change = (
                (safe_float(pe.get("ltp")) - old_put_ltp) / old_put_ltp
                if old_put_ltp > 0 else 0.0
            )
        else:
            call_oi_change = safe_float(
                api.get("call_oi_change", api.get("call_change")),
                safe_float(ce.get("oi")) - safe_float(ce.get("prev_oi")),
            )
            put_oi_change = safe_float(
                api.get("put_oi_change", api.get("put_change")),
                safe_float(pe.get("oi")) - safe_float(pe.get("prev_oi")),
            )
            ce_close = safe_float(ce.get("close_price"))
            pe_close = safe_float(pe.get("close_price"))
            call_price_change = (
                (safe_float(ce.get("ltp")) - ce_close) / ce_close
                if ce_close > 0 else 0.0
            )
            put_price_change = (
                (safe_float(pe.get("ltp")) - pe_close) / pe_close
                if pe_close > 0 else 0.0
            )

        call_activity, call_bias = classify_option_flow("CE", call_price_change, call_oi_change)
        put_activity, put_bias = classify_option_flow("PE", put_price_change, put_oi_change)
        out[float(strike)] = {
            "call_oi_change": float(call_oi_change),
            "put_oi_change": float(put_oi_change),
            "call_price_change_pct": float(call_price_change),
            "put_price_change_pct": float(put_price_change),
            "call_bias": int(call_bias),
            "put_bias": int(put_bias),
            "call_activity": call_activity,
            "put_activity": put_activity,
        }
    return out, mode



def chain_oi_support_resistance(
    chain: list[dict[str, Any]],
    spot: float,
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
    previous_option_snapshot: Optional[dict[str, Any]] = None,
    expiry: str = "",
) -> dict[str, Any]:
    """Build authoritative support/resistance from current option OI.

    OI concentration is the structural source. Change-OI/option price behavior
    is used only to describe the wall and to break ties; it never replaces OI
    with a price-derived level.
    """
    full_chain_count = len(chain_rows(chain))
    decision_chain, window_meta = option_chain_atm_window(chain, spot)
    rows = chain_rows(decision_chain)
    strikes = sorted(rows)
    step = safe_float(window_meta.get("strike_step"), strike_step(strikes))
    atm = safe_float(window_meta.get("atm_strike"), nearest_strike(spot, strikes))
    flow_map, flow_mode = _intraday_option_changes(
        decision_chain, previous_option_snapshot, change_oi_by_strike, expiry
    )
    logger.info(
        "ATM OI WINDOW: spot=%.2f ATM=%.0f step=%.0f radius=+-%d levels range=%.0f-%.0f "
        "analysed=%d full_chain=%d strikes=%s",
        float(spot), atm, step, ATM_ANALYSIS_RADIUS_LEVELS,
        safe_float(window_meta.get("lower_bound")), safe_float(window_meta.get("upper_bound")),
        int(window_meta.get("window_count", len(rows))), full_chain_count,
        ",".join(f"{x:.0f}" for x in window_meta.get("window_strikes", [])),
    )

    previous_spot = safe_float((previous_option_snapshot or {}).get("spot"), float("nan"))
    underlying_move = float(spot - previous_spot) if math.isfinite(previous_spot) else 0.0
    entries: list[dict[str, Any]] = []
    oi_structure_by_strike: dict[str, dict[str, Any]] = {}
    # A dominance ratio alone made almost every far-OTM strike look "reliable".
    # Require meaningful absolute OI too, using the same chain-relative floor
    # used by the support/resistance selector (30% of maximum or median OI).
    call_oi_by_strike = {
        float(k): max(safe_float(option_side_data(row, "CE").get("oi")), 0.0)
        for k, row in rows.items()
    }
    put_oi_by_strike = {
        float(k): max(safe_float(option_side_data(row, "PE").get("oi")), 0.0)
        for k, row in rows.items()
    }
    max_call_oi = max(call_oi_by_strike.values(), default=0.0)
    max_put_oi = max(put_oi_by_strike.values(), default=0.0)
    min_reliable_call_oi = max(0.30 * max_call_oi, float(np.median(list(call_oi_by_strike.values()))) if call_oi_by_strike else 0.0)
    min_reliable_put_oi = max(0.30 * max_put_oi, float(np.median(list(put_oi_by_strike.values()))) if put_oi_by_strike else 0.0)
    for strike in rows:
        flow = flow_map.get(float(strike), {})
        dist_steps = abs(float(strike) - atm) / max(step, 1.0)
        call_oi = call_oi_by_strike[float(strike)]
        put_oi = put_oi_by_strike[float(strike)]
        call_oi_change = safe_float(flow.get("call_oi_change"))
        put_oi_change = safe_float(flow.get("put_oi_change"))
        oi_state = classify_strike_oi_state(
            float(strike), float(spot), call_oi, put_oi,
            call_oi_change, put_oi_change, underlying_move, step,
            min_call_oi=min_reliable_call_oi,
            min_put_oi=min_reliable_put_oi,
        )
        entries.append({
            "strike": float(strike),
            "call_oi": call_oi,
            "put_oi": put_oi,
            "call_oi_change": call_oi_change,
            "put_oi_change": put_oi_change,
            "call_bias": int(flow.get("call_bias", 0)),
            "put_bias": int(flow.get("put_bias", 0)),
            "call_activity": str(flow.get("call_activity", "NO_OI_CHANGE")),
            "put_activity": str(flow.get("put_activity", "NO_OI_CHANGE")),
            "dominant_role": oi_state["dominant_role"],
            "dominance_ratio": oi_state["dominance_ratio"],
            "oi_state": oi_state["state"],
            "reliability": oi_state["reliability"],
            "scenario": oi_state["scenario"],
            "dist_steps": float(dist_steps),
        })
        oi_structure_by_strike[f"{float(strike):.0f}"] = oi_state

    # Compact, current chain classification is logged each scan for auditability.
    role_counts: dict[str, int] = {}
    for item in oi_structure_by_strike.values():
        label = str(item.get("state", "UNKNOWN"))
        role_counts[label] = role_counts.get(label, 0) + 1
    logger.info("OI STRIKE CLASSIFICATION: %s", ", ".join(f"{k}={v}" for k, v in sorted(role_counts.items())))
    nearby_diagnostics = sorted(entries, key=lambda item: float(item["strike"]))
    if nearby_diagnostics:
        logger.info(
            "OI DOMINANCE MAP (near spot): %s",
            " | ".join(
                f"{float(item['strike']):.0f}:{item['oi_state']} role={item['dominant_role']} "
                f"C/P={float(item['call_oi']):.0f}/{float(item['put_oi']):.0f} "
                f"dC/dP={float(item['call_oi_change']):+.0f}/{float(item['put_oi_change']):+.0f} "
                f"strike_watch={item['scenario']}"
                for item in nearby_diagnostics
            ),
        )

    if not entries:
        raise ScannerError("No option-chain strikes available for structural analysis.")

    def pick_wall(side: str) -> Optional[dict[str, Any]]:
        pool = [
            x for x in entries
            if (
                float(x["strike"]) < spot and float(x["put_oi"]) > float(x["call_oi"])
                if side == "support" else
                float(x["strike"]) > spot and float(x["call_oi"]) > float(x["put_oi"])
            )
        ]
        if not pool:
            return None
        oi_key = "put_oi" if side == "support" else "call_oi"
        change_key = "put_oi_change" if side == "support" else "call_oi_change"
        max_oi = max(float(x[oi_key]) for x in pool)
        median_oi = float(np.median([float(x[oi_key]) for x in pool]))
        meaningful = [x for x in pool if float(x[oi_key]) >= max(0.30 * max_oi, median_oi)]
        source_pool = meaningful or sorted(pool, key=lambda x: (-float(x[oi_key]), float(x["dist_steps"])))[:6]
        # For the authoritative active structural level, nearest meaningful OI
        # wall is used; OI size breaks ties. This makes T1 an actionable wall.
        source_pool.sort(key=lambda x: (float(x["dist_steps"]), -float(x[oi_key]), -abs(float(x[change_key]))))
        return source_pool[0]

    support_row = pick_wall("support")
    resistance_row = pick_wall("resistance")

    def rank_other(side: str, primary: Optional[dict[str, Any]]) -> list[dict[str, Any]]:
        pool = [
            x for x in entries
            if (
                float(x["strike"]) < spot and float(x["put_oi"]) > float(x["call_oi"])
                if side == "support" else
                float(x["strike"]) > spot and float(x["call_oi"]) > float(x["put_oi"])
            )
            and (primary is None or abs(float(x["strike"]) - float(primary["strike"])) > 0.01)
        ]
        oi_key = "put_oi" if side == "support" else "call_oi"
        max_oi = max((float(x[oi_key]) for x in pool), default=1.0)
        median_oi = float(np.median([float(x[oi_key]) for x in pool])) if pool else 0.0
        meaningful = [x for x in pool if float(x[oi_key]) >= max(0.30 * max_oi, median_oi)]
        pool = meaningful or pool
        return sorted(pool, key=lambda x: (float(x["dist_steps"]), -float(x[oi_key]), float(x["strike"])))

    support_level = float(support_row["strike"]) if support_row else float("nan")
    resistance_level = float(resistance_row["strike"]) if resistance_row else float("nan")
    support_others = rank_other("support", support_row)
    resistance_others = rank_other("resistance", resistance_row)
    support_2 = float(support_others[0]["strike"]) if support_others else support_level
    resistance_2 = float(resistance_others[0]["strike"]) if resistance_others else resistance_level

    support_source = "OPTION_OI_OI_DOMINANCE" if support_row else "NONE_NO_PUT_OI_DOMINANCE_BELOW_SPOT"
    resistance_source = "OPTION_OI_OI_DOMINANCE" if resistance_row else "NONE_NO_CALL_OI_DOMINANCE_ABOVE_SPOT"

    # A level that no longer wins the current same-strike OI comparison is not
    # advertised as a current support/resistance wall. Previous levels are retained
    # separately for completed-bar break detection, never substituted as live OI.

    total_put_oi = sum(float(x["put_oi"]) for x in entries)
    total_call_oi = sum(float(x["call_oi"]) for x in entries)
    pcr = total_put_oi / total_call_oi if total_call_oi > 0 else float("nan")
    pcr_bias = 1 if math.isfinite(pcr) and pcr >= PCR_BULL_THRESHOLD else -1 if math.isfinite(pcr) and pcr <= PCR_BEAR_THRESHOLD else 0

    # All entries are restricted to the same current ATM window, so this pressure
    # measure is local to the nine-strike decision universe rather than the full chain.
    nearby = entries
    bull_pressure = sum(
        max(float(x["put_oi_change"]), 0.0) + max(-float(x["call_oi_change"]), 0.0) for x in nearby
    )
    bear_pressure = sum(
        max(float(x["call_oi_change"]), 0.0) + max(-float(x["put_oi_change"]), 0.0) for x in nearby
    )
    pressure_den = bull_pressure + bear_pressure
    pressure_score = (bull_pressure - bear_pressure) / pressure_den if pressure_den > 0 else 0.0
    oi_bias = 1 if pressure_score >= 0.08 else -1 if pressure_score <= -0.08 else 0

    support_change_strength = 0.0
    if support_row and total_put_oi > 0:
        support_change_strength = min(abs(float(support_row["put_oi_change"])) / total_put_oi, 1.0)
    resistance_change_strength = 0.0
    if resistance_row and total_call_oi > 0:
        resistance_change_strength = min(abs(float(resistance_row["call_oi_change"])) / total_call_oi, 1.0)

    support_flow_bias = int(support_row["put_bias"]) if support_row else 0
    resistance_flow_bias = int(resistance_row["call_bias"]) if resistance_row else 0
    support_activity = str(support_row["put_activity"]) if support_row else "NO_OI_DATA"
    resistance_activity = str(resistance_row["call_activity"]) if resistance_row else "NO_OI_DATA"

    logger.info(
        "CHAIN STRUCTURE: support=%s/%s resistance=%s/%s source=%s/%s flow_mode=%s pressure=%+.3f bias=%+d PCR=%s",
        f"{support_level:.0f}" if math.isfinite(support_level) else "NA",
        f"{support_2:.0f}" if math.isfinite(support_2) else "NA",
        f"{resistance_level:.0f}" if math.isfinite(resistance_level) else "NA",
        f"{resistance_2:.0f}" if math.isfinite(resistance_2) else "NA",
        support_source, resistance_source, flow_mode, pressure_score, oi_bias,
        f"{pcr:.3f}" if math.isfinite(pcr) else "NA",
    )

    return {
        "support_1": float(support_level), "support_2": float(support_2),
        "resistance_1": float(resistance_level), "resistance_2": float(resistance_2),
        "support_source": support_source, "resistance_source": resistance_source,
        "support_strength": float((support_row or {}).get("put_oi", 0.0)),
        "resistance_strength": float((resistance_row or {}).get("call_oi", 0.0)),
        "support_change_strength": float(support_change_strength),
        "resistance_change_strength": float(resistance_change_strength),
        "major_support": float(support_level), "major_resistance": float(resistance_level),
        "support_flow_bias": support_flow_bias, "resistance_flow_bias": resistance_flow_bias,
        "support_activity": support_activity, "resistance_activity": resistance_activity,
        "put_writing_at_support": support_activity == "PUT_WRITING",
        "put_unwinding_at_support": support_activity in {"PUT_LONG_UNWINDING", "PUT_SHORT_COVERING"},
        "call_writing_at_resistance": resistance_activity == "CALL_WRITING",
        "call_unwinding_at_resistance": resistance_activity in {"CALL_LONG_UNWINDING", "CALL_SHORT_COVERING"},
        "pressure_score": float(pressure_score), "normalized_diff": float(pressure_score),
        "oi_bias": int(oi_bias), "change_bias": int(oi_bias),
        "predictive_bias": int(oi_bias), "predictive_strength": float(abs(pressure_score)),
        "level_bias": 0, "pcr": float(pcr) if math.isfinite(pcr) else float("nan"),
        "pcr_bias": int(pcr_bias), "flow_mode": flow_mode,
        "change_flow_score": float(pressure_score), "change_flow_bias": int(oi_bias),
        "option_flow_by_strike": flow_map,
        "oi_structure_by_strike": oi_structure_by_strike,
        "window_atm_strike": float(atm),
        "window_strike_step": float(step),
        "window_lower_bound": float(window_meta["lower_bound"]),
        "window_upper_bound": float(window_meta["upper_bound"]),
        "window_strikes": list(window_meta["window_strikes"]),
        "window_count": int(window_meta["window_count"]),
        "full_chain_count": int(full_chain_count),
        "underlying_move_since_oi_snapshot": float(underlying_move),
    }


def fetch_change_oi_by_strike(
    expiry: str,
) -> dict[float, dict[str, float]]:
    """Fetch per-strike Change-in-OI in one API call for local-window filtering."""
    today = now_ist().date().isoformat()
    by_strike: dict[float, dict[str, float]] = {}

    try:
        payload = api_get(
            CHANGE_OI_URL,
            {
                "instrument_key": NIFTY_KEY,
                "expiry": expiry,
                "date": today,
                "interval": 1,
            },
            retries=2,
        )
    except ScannerError as exc:
        logger.info("Change-OI endpoint unavailable: %s", exc)
        return by_strike

    data = payload.get("data", {})
    if not isinstance(data, dict):
        return by_strike

    detail_rows = data.get("call_put_oi_data_list", [])
    if isinstance(detail_rows, list):
        for item in detail_rows:
            if not isinstance(item, dict):
                continue
            strike = safe_float(item.get("strike_price"), float("nan"))
            if not math.isfinite(strike):
                continue
            call_change_value = safe_float(item.get("call_change_oi"))
            put_change_value = safe_float(item.get("put_change_oi"))
            by_strike[float(strike)] = {
                "call_oi_change": call_change_value,
                "put_oi_change": put_change_value,
                # Legacy aliases retained defensively for existing helper contracts.
                "call_change": call_change_value,
                "put_change": put_change_value,
            }

    logger.info(
        "CHANGE-OI API DATA: expiry=%s per_strike=%d; aggregate totals are not used for decisions.",
        expiry, len(by_strike),
    )
    return by_strike

def local_change_oi_confirmation(
    chain: list[dict[str, Any]],
    spot: float,
    change_oi_by_strike: Optional[dict[float, dict[str, float]]],
    *,
    now: Optional[datetime] = None,
) -> tuple[float, dict[float, dict[str, Any]], dict[str, Any]]:
    """Return the directional Change-OI score and per-strike map for ATM +/-4 only.

    The full-chain API response remains a single fetch. When per-strike API rows
    are incomplete, the helper falls back only to OI-prev_OI from strikes in the
    same local window; it never falls back to the full-chain aggregate.
    """
    decision_chain, meta = option_chain_atm_window(chain, spot)
    rows = chain_rows(decision_chain)
    api_map: dict[float, dict[str, Any]] = {}
    for raw_strike, detail in (change_oi_by_strike or {}).items():
        strike = safe_float(raw_strike, float("nan"))
        if math.isfinite(strike) and strike in rows and isinstance(detail, dict):
            api_map[float(strike)] = dict(detail)

    window_count = len(rows)
    min_coverage = max(1, int(math.ceil(window_count * COI_WINDOW_MIN_COVERAGE_FRACTION)))
    api_rows: dict[float, dict[str, Any]] = {}
    for strike in rows:
        detail = api_map.get(float(strike))
        if not isinstance(detail, dict):
            continue
        call_value = safe_float(detail.get("call_oi_change", detail.get("call_change")), float("nan"))
        put_value = safe_float(detail.get("put_oi_change", detail.get("put_change")), float("nan"))
        if math.isfinite(call_value) and math.isfinite(put_value):
            enriched = dict(detail)
            enriched.update({
                "call_oi_change": call_value, "put_oi_change": put_value,
                "call_change": call_value, "put_change": put_value,
            })
            api_rows[float(strike)] = enriched

    local_map: dict[float, dict[str, Any]] = {}
    if len(api_rows) >= min_coverage:
        local_map = api_rows
        source = "ATM_WINDOW_PER_STRIKE_API"
        covered = len(api_rows)
    else:
        # If the API's per-strike data is incomplete, use previous-OI fields from
        # the already-fetched option chain, but only if enough local levels have them.
        fallback: dict[float, dict[str, Any]] = {}
        for strike, row in rows.items():
            ce = option_side_data(row, "CE")
            pe = option_side_data(row, "PE")
            ce_oi, ce_prev = safe_float(ce.get("oi"), float("nan")), safe_float(ce.get("prev_oi"), float("nan"))
            pe_oi, pe_prev = safe_float(pe.get("oi"), float("nan")), safe_float(pe.get("prev_oi"), float("nan"))
            if not all(math.isfinite(v) and v > 0 for v in (ce_oi, ce_prev, pe_oi, pe_prev)):
                continue
            c_change, p_change = ce_oi - ce_prev, pe_oi - pe_prev
            c_close, p_close = safe_float(ce.get("close_price"), float("nan")), safe_float(pe.get("close_price"), float("nan"))
            c_ltp, p_ltp = safe_float(ce.get("ltp"), float("nan")), safe_float(pe.get("ltp"), float("nan"))
            c_pct = (c_ltp - c_close) / c_close if math.isfinite(c_close) and c_close > 0 and math.isfinite(c_ltp) else 0.0
            p_pct = (p_ltp - p_close) / p_close if math.isfinite(p_close) and p_close > 0 and math.isfinite(p_ltp) else 0.0
            c_activity, c_bias = classify_option_flow("CE", c_pct, c_change)
            p_activity, p_bias = classify_option_flow("PE", p_pct, p_change)
            fallback[float(strike)] = {
                "call_oi_change": c_change, "put_oi_change": p_change,
                "call_change": c_change, "put_change": p_change,
                "call_bias": c_bias, "put_bias": p_bias,
                "call_activity": c_activity, "put_activity": p_activity,
                "call_price_change_pct": c_pct, "put_price_change_pct": p_pct,
                "source": "OPTION_CHAIN_PREV_OI_FALLBACK",
            }
        if len(fallback) >= min_coverage:
            local_map = fallback
            source = "ATM_WINDOW_OPTION_CHAIN_PREV_OI"
            covered = len(fallback)
        else:
            # Keep any valid window API details for strike-level diagnostics, but
            # do not manufacture an aggregate directional score from weak coverage.
            local_map = api_rows
            source = "WINDOW_COI_INSUFFICIENT_COVERAGE"
            covered = len(api_rows)

    call_total = sum(safe_float(detail.get("call_oi_change", detail.get("call_change")), 0.0) for detail in local_map.values())
    put_total = sum(safe_float(detail.get("put_oi_change", detail.get("put_change")), 0.0) for detail in local_map.values())
    denominator = abs(call_total) + abs(put_total)
    raw_score = (put_total - call_total) / denominator if denominator > 0 and covered >= min_coverage else 0.0
    current_time = now or now_ist()
    current_time = current_time.replace(tzinfo=IST) if current_time.tzinfo is None else current_time.astimezone(IST)
    cold_start = current_time.time() < COI_COLD_START_END
    weight = COI_COLD_START_WEIGHT if cold_start else 1.0
    weighted_score = raw_score * weight
    bias = 1 if weighted_score >= 0.10 else -1 if weighted_score <= -0.10 else 0
    meta_out = {
        **meta,
        "source": source,
        "coverage": int(covered),
        "required_coverage": int(min_coverage),
        "call_change_sum": float(call_total),
        "put_change_sum": float(put_total),
        "raw_score": float(raw_score),
        "weight": float(weight),
        "weighted_score": float(weighted_score),
        "bias": int(bias),
        "protocol": "COLD_START_CUMULATIVE_OR_API_WARMUP" if cold_start else "LOCAL_DAY_CHANGE_FALLBACK",
    }
    logger.info(
        "ATM CHANGE-OI DECISION SCOPE: spot=%.2f ATM=%.0f window=%d/%d coverage=%d/%d source=%s "
        "call_change=%+.0f put_change=%+.0f raw_score=%+.3f weight=%.2f effective_score=%+.3f bias=%+d",
        spot, safe_float(meta.get("atm_strike")), len(rows), full_chain_count_for_log(chain),
        covered, window_count, source, call_total, put_total, raw_score, weight, weighted_score, bias,
    )
    return float(weighted_score), local_map, meta_out


def full_chain_count_for_log(chain: list[dict[str, Any]]) -> int:
    """Safe full-chain count for diagnostic logging."""
    try:
        return len(chain_rows(chain))
    except ScannerError:
        return 0


def aggregate_atm_window_coi_velocity(
    chain: list[dict[str, Any]],
    spot: float,
    velocity_by_strike: Optional[dict[float, dict[str, Any]]],
    *,
    now: Optional[datetime] = None,
) -> dict[str, Any]:
    """Aggregate cumulative-opening/rolling COI velocity inside current ATM +/-4 only."""
    decision_chain, meta = option_chain_atm_window(chain, spot)
    rows = chain_rows(decision_chain)
    current_time = now or now_ist()
    current_time = current_time.replace(tzinfo=IST) if current_time.tzinfo is None else current_time.astimezone(IST)
    cold_start = current_time.time() < COI_COLD_START_END
    expected_mode = "COLD_START_CUMULATIVE" if cold_start else "ROLLING_15_30"
    minimum = max(1, int(math.ceil(len(rows) * COI_WINDOW_MIN_COVERAGE_FRACTION)))
    covered_rows: list[dict[str, Any]] = []
    for strike in rows:
        detail = (velocity_by_strike or {}).get(float(strike), {})
        if not isinstance(detail, dict) or not bool(detail.get("available")):
            continue
        mode = str(detail.get("baseline_mode", "")).upper()
        if mode != expected_mode:
            continue
        call_change = safe_float(detail.get("call_oi_change"), float("nan"))
        put_change = safe_float(detail.get("put_oi_change"), float("nan"))
        if bool(detail.get("call_available", math.isfinite(call_change))) and bool(detail.get("put_available", math.isfinite(put_change))) and math.isfinite(call_change) and math.isfinite(put_change):
            covered_rows.append(detail)
    call_total = sum(safe_float(item.get("call_oi_change"), 0.0) for item in covered_rows)
    put_total = sum(safe_float(item.get("put_oi_change"), 0.0) for item in covered_rows)
    den = abs(call_total) + abs(put_total)
    available = len(covered_rows) >= minimum and den > 0
    raw_score = (put_total - call_total) / den if available else 0.0
    weight = COI_COLD_START_WEIGHT if cold_start else 1.0
    weighted_score = raw_score * weight
    baseline_ages = [safe_float(item.get("baseline_minutes"), float("nan")) for item in covered_rows]
    baseline_ages = [age for age in baseline_ages if math.isfinite(age)]
    return {
        "available": bool(available), "baseline_mode": expected_mode if available else "UNAVAILABLE",
        "coverage": len(covered_rows), "required_coverage": minimum, "window_count": len(rows),
        "window_strikes": list(meta.get("window_strikes", [])),
        "call_change_sum": float(call_total), "put_change_sum": float(put_total),
        "raw_score": float(raw_score), "weight": float(weight), "score": float(weighted_score),
        "baseline_age_minutes": float(np.median(baseline_ages)) if baseline_ages else float("nan"),
    }



# =============================================================================
# VWAP / PRICE ACTION
# =============================================================================

def vwap_snapshot(
    price_session: pd.DataFrame,
) -> tuple[float, float, int]:
    """Calculate session VWAP from the NIFTY index price feed.

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



def price_action_regime_snapshot(
    price_session: pd.DataFrame,
    vwap: float,
    atr3: float,
) -> dict[str, Any]:
    """Describe NIFTY price regime using multi-window persistence.

    Recent 3 bars are deliberately contextual. Primary directional persistence is
    measured from the session, a 12-bar window and the ratio/efficiency of recent
    directional movement. This prevents a short bounce from erasing an established
    trend while still detecting genuinely strong reversals.
    """
    result: dict[str, Any] = {
        "state": "UNKNOWN", "bias": 0, "strength": 0.0,
        "session_move_atr": 0.0, "recent7_move_atr": 0.0,
        "recent3_move_atr": 0.0, "recent12_move_atr": 0.0,
        "directional_down_ratio": 0.0, "directional_up_ratio": 0.0,
        "trend_efficiency": 0.0,
        "range12_atr": 0.0, "alternation": 0.0,
        "structure": "MIXED", "vwap_distance_atr": float("inf"),
        "latest_move_atr": 0.0, "bullish_structure": False,
        "bearish_structure": False, "sideways": False,
    }
    if price_session is None or price_session.empty:
        return result

    work = filter_completed_candles(price_session.copy().sort_values("timestamp"), 3)
    if len(work) < 8:
        return result
    for c in ("open", "high", "low", "close"):
        work[c] = pd.to_numeric(work[c], errors="coerce")
    work = work.dropna(subset=["open", "high", "low", "close"]).reset_index(drop=True)
    if len(work) < 8:
        return result

    atr = max(float(atr3), 1.0)
    closes = work["close"].to_numpy(dtype=float)
    diffs = np.diff(closes)
    session_move = float(closes[-1] - closes[0])

    recent7_count = min(8, len(closes))
    recent3_count = min(4, len(closes))
    recent12_count = min(13, len(closes))
    recent7_move = float(closes[-1] - closes[-recent7_count])
    recent3_move = float(closes[-1] - closes[-recent3_count])
    recent12_move = float(closes[-1] - closes[-recent12_count])
    latest_move = float(diffs[-1]) if len(diffs) else 0.0

    w12 = work.tail(min(12, len(work)))
    split = max(2, len(w12) // 2)
    early = w12.iloc[:split]
    late = w12.iloc[-split:]
    higher_structure = bool(
        float(late["high"].mean()) > float(early["high"].mean())
        and float(late["low"].mean()) > float(early["low"].mean())
    )
    lower_structure = bool(
        float(late["high"].mean()) < float(early["high"].mean())
        and float(late["low"].mean()) < float(early["low"].mean())
    )
    structure = "HH_HL" if higher_structure else "LH_LL" if lower_structure else "MIXED"

    movement_window = diffs[-min(12, len(diffs)):]
    down_count = int(np.sum(movement_window < 0)) if len(movement_window) else 0
    up_count = int(np.sum(movement_window > 0)) if len(movement_window) else 0
    valid_count = max(down_count + up_count, 1)
    down_ratio = down_count / valid_count
    up_ratio = up_count / valid_count
    abs_path = float(np.sum(np.abs(movement_window))) if len(movement_window) else 0.0
    efficiency = abs(recent12_move) / abs_path if abs_path > 0 else 0.0

    last12 = work.tail(min(12, len(work)))
    range12 = float(last12["high"].max() - last12["low"].min())
    sign_diffs = np.sign(movement_window) if len(movement_window) else np.array([])
    valid_signs = sign_diffs[sign_diffs != 0]
    alternation = (
        float(np.sum(valid_signs[1:] != valid_signs[:-1]) / max(len(valid_signs) - 1, 1))
        if len(valid_signs) >= 2 else 0.0
    )

    price = float(closes[-1])
    vwap_distance = abs(price - vwap) / atr if math.isfinite(vwap) else float("inf")
    below_vwap = price < vwap
    above_vwap = price > vwap

    session_atr = session_move / atr
    recent7_atr = recent7_move / atr
    recent3_atr = recent3_move / atr
    recent12_atr = recent12_move / atr
    latest_atr = latest_move / atr

    # Strong current price structure requires the trend to agree with VWAP, but
    # continuous persistence may also be established by the longer movement window.
    bullish_structure = bool(
        above_vwap
        and (
            higher_structure
            or recent12_atr >= 0.20
        )
        and up_ratio >= 0.45
    )
    bearish_structure = bool(
        below_vwap
        and (
            lower_structure
            or recent12_atr <= -0.20
        )
        and down_ratio >= 0.45
    )

    sideways = bool(
        range12 / atr <= REGIME_SIDEWAYS_RANGE_ATR
        and abs(recent12_atr) <= REGIME_SIDEWAYS_NET_ATR
        and vwap_distance <= REGIME_SIDEWAYS_VWAP_DISTANCE_ATR
        and alternation >= REGIME_SIDEWAYS_ALTERNATION
    )

    if bullish_structure and not sideways:
        state = "BULLISH"
        bias = 1
        strength = min(1.0, 0.40 * min(abs(recent12_atr) / 1.0, 1.0) + 0.25 * up_ratio + 0.20 * efficiency + 0.15 * min(vwap_distance, 1.0))
    elif bearish_structure and not sideways:
        state = "BEARISH"
        bias = -1
        strength = min(1.0, 0.40 * min(abs(recent12_atr) / 1.0, 1.0) + 0.25 * down_ratio + 0.20 * efficiency + 0.15 * min(vwap_distance, 1.0))
    elif sideways:
        state = "SIDEWAYS"
        bias = 0
        strength = max(0.0, min(1.0, 0.55 + 0.15 * alternation))
    elif session_atr > 0.15 and recent12_atr < -0.15:
        state = "BULLISH_WEAKENING"
        bias = -1
        strength = min(1.0, abs(recent12_atr) / 1.5)
    elif session_atr < -0.15 and recent12_atr > 0.15:
        state = "BEARISH_WEAKENING"
        bias = 1
        strength = min(1.0, abs(recent12_atr) / 1.5)
    elif recent12_atr > 0.15:
        state = "BULLISH"
        bias = 1
        strength = min(1.0, abs(recent12_atr) / 1.5)
    elif recent12_atr < -0.15:
        state = "BEARISH"
        bias = -1
        strength = min(1.0, abs(recent12_atr) / 1.5)
    else:
        state = "SIDEWAYS"
        bias = 0
        strength = 0.35

    result.update({
        "state": state, "bias": int(bias), "strength": float(strength),
        "session_move_atr": float(session_atr),
        "recent7_move_atr": float(recent7_atr),
        "recent3_move_atr": float(recent3_atr),
        "recent12_move_atr": float(recent12_atr),
        "directional_down_ratio": float(down_ratio),
        "directional_up_ratio": float(up_ratio),
        "trend_efficiency": float(efficiency),
        "range12_atr": float(range12 / atr), "alternation": float(alternation),
        "structure": structure, "vwap_distance_atr": float(vwap_distance),
        "latest_move_atr": float(latest_atr),
        "bullish_structure": bullish_structure, "bearish_structure": bearish_structure,
        "sideways": sideways,
    })
    return result



# =============================================================================
# MARKET STRUCTURE ENGINE
# =============================================================================

def resolve_change_oi_flow(
    intraday_score: float,
    day_score: float,
    flow_mode: str,
) -> tuple[float, int, str, bool]:
    """Resolve the Change-OI signal without allowing neutral/contradictory snapshots to mislead direction.

    Priority:
      1. Warm/strong scan-to-scan intraday flow is primary.
      2. If the intraday snapshot is neutral/insufficient, the current-session
         Upstox aggregate Change-OI is the fallback.
      3. A strong contradiction is reported as a conflict and supplies no
         directional Change-OI confirmation; price/VWAP may still retain a
         directional WATCH state, but the conflicting flow cannot authorize entry.
    """
    intra = float(intraday_score) if math.isfinite(float(intraday_score)) else 0.0
    day = float(day_score) if math.isfinite(float(day_score)) else 0.0
    intra_abs = abs(intra)
    day_abs = abs(day)
    intra_directional = intra_abs >= STRUCTURE_CHANGE_OI_CONFIRM
    day_directional = day_abs >= STRUCTURE_CHANGE_OI_STRONG

    mode = str(flow_mode).upper()
    primary_window_modes = {"INTRADAY_SNAPSHOT", "COLD_START_CUMULATIVE", "ROLLING_15_30"}
    if mode in primary_window_modes and intra_directional:
        # Do not let one small scan-to-scan snapshot reverse a clearly directional
        # session-level Change-OI signal. If both sources are directional and
        # disagree, preserve the conflict and block a new entry until they align.
        if day_directional and (intra * day) < 0:
            return 0.0, 0, "INTRADAY_DAY_CONFLICT", True
        bias = 1 if intra >= STRUCTURE_CHANGE_OI_CONFIRM else -1
        return intra, bias, "INTRADAY_PRIMARY" if mode == "INTRADAY_SNAPSHOT" else mode + "_PRIMARY", False

    # A valid cumulative-opening or rolling-window measure that is neutral is
    # not overridden by a stronger day-total score. That would reintroduce a
    # day/full-chain signal precisely when the current local window is neutral.
    if mode in {"COLD_START_CUMULATIVE", "ROLLING_15_30"}:
        return 0.0, 0, mode + "_NEUTRAL", False

    # Neutral/empty intraday snapshot: fall back to the local current-session
    # Change-OI endpoint rather than turning a clearly bearish/bullish session into
    # SIDEWAYS merely because the latest scan's local changes cancelled out.
    if day_directional:
        bias = 1 if day >= STRUCTURE_CHANGE_OI_STRONG else -1
        source = "DAY_CHANGE_API_FALLBACK_NEUTRAL_INTRADAY" if str(flow_mode).upper() == "INTRADAY_SNAPSHOT" else "DAY_CHANGE_API"
        return day, bias, source, False

    if intra_abs > 0.0:
        bias = 1 if intra >= STRUCTURE_CHANGE_OI_CONFIRM else -1 if intra <= -STRUCTURE_CHANGE_OI_CONFIRM else 0
        return intra, bias, "INTRADAY_WEAK", False

    return 0.0, 0, "NO_DIRECTIONAL_CHANGE_OI", False


def build_market_structure(
    spot: float,
    futures_3m: pd.DataFrame,
    futures_session: pd.DataFrame,
    chain_levels: dict[str, Any],
    change_oi_score: float,
    futures_live_quote: Optional[dict[str, Any]] = None,
    previous_direction: Optional[str] = None,
    previous_phase: Optional[str] = None,
    price_session: Optional[pd.DataFrame] = None,
) -> StructureResult:
    """Authoritative NIFTY market-structure state machine.

    Direction is decided by exactly three primary conditions:
      1. NIFTY price vs VWAP;
      2. sustained NIFTY price action (session + recent structure);
      3. directional Change-OI confirmation.

    OI support/resistance defines structural levels. A break strengthens the
    setup but is not required for an already-continuous trend. Futures price/OI
    and PCR remain descriptive context only.
    """
    primary_session = price_session if price_session is not None and not price_session.empty else futures_session
    futures_info = futures_oi_structure(futures_3m, futures_live_quote)
    futures_regime = str(futures_info.get("regime", "UNAVAILABLE"))
    market_scenario = (
        futures_regime
        if futures_regime in {"LONG_BUILDUP", "SHORT_BUILDUP", "SHORT_COVERING", "LONG_UNWINDING"}
        else "NEUTRAL_UNCONFIRMED"
    )
    logger.info(
        "MARKET SCENARIO (futures price + futures OI): %s | futures_context=%s "
        "price_delta=%+.2f OI_delta=%+.0f; strike OI labels are structural wall/break watches.",
        market_scenario,
        futures_regime,
        safe_float(futures_info.get("price_delta"), float("nan")),
        safe_float(futures_info.get("oi_delta"), float("nan")),
    )
    futures_bias = int(futures_info.get("bias", 0))
    futures_strength = safe_float(futures_info.get("oi_strength"), 0.0)
    completed = filter_completed_candles(primary_session.copy().sort_values("timestamp"), 3)
    for c in ("open", "high", "low", "close"):
        if c in completed.columns:
            completed[c] = pd.to_numeric(completed[c], errors="coerce")
    completed = completed.dropna(subset=["open", "high", "low", "close"]).reset_index(drop=True)

    vwap, vwap_slope, _ = vwap_snapshot(primary_session)
    volatility_unit = max(safe_float(calculate_atr(completed, period=ATR_PERIOD).iloc[-1], 50.0) if len(completed) else 50.0, 1.0)
    work = completed
    current_close = float(work["close"].iloc[-1]) if not work.empty else float(spot)
    latest_move = float(work["close"].iloc[-1] - work["close"].iloc[-2]) if len(work) >= 2 else 0.0

    support_1 = safe_float(chain_levels.get("support_1"), float("nan"))
    support_2 = safe_float(chain_levels.get("support_2"), float("nan"))
    resistance_1 = safe_float(chain_levels.get("resistance_1"), float("nan"))
    resistance_2 = safe_float(chain_levels.get("resistance_2"), float("nan"))

    break_buffer = STRUCTURE_BREAK_BUFFER_ATR * volatility_unit
    if not math.isfinite(break_buffer) or break_buffer <= 0:
        break_buffer = 1.0

    previous_support = safe_float(chain_levels.get("previous_support_1"), float("nan"))
    previous_resistance = safe_float(chain_levels.get("previous_resistance_1"), float("nan"))
    prior = str(previous_direction or "").upper()
    prior_phase = str(previous_phase or "").upper()
    bullish_prior = prior == "BULLISH" or prior_phase in {"BULLISH", "CONTINUOUS_BULLISH", "BULLISH_BREAKOUT"}
    bearish_prior = prior == "BEARISH" or prior_phase in {"BEARISH", "CONTINUOUS_BEARISH", "BEARISH_BREAKDOWN"}

    # Validate OI levels against the live underlying price. A previously broken
    # resistance/support is a breakout reference, NOT the current resistance/
    # support. The old implementation overwrote a fresh resistance with the
    # prior resistance and could report resistance below spot (e.g. 22400 while
    # NIFTY was trading near 22417 on 09-Oct).
    price_reference = max(
        x for x in (safe_float(spot, float("nan")), current_close)
        if math.isfinite(x)
    )
    original_supports = [support_1, support_2]
    original_resistances = [resistance_1, resistance_2]
    live_supports = sorted(
        {float(x) for x in original_supports if math.isfinite(safe_float(x, float("nan"))) and float(x) < price_reference},
        reverse=True,
    )
    live_resistances = sorted(
        {float(x) for x in original_resistances if math.isfinite(safe_float(x, float("nan"))) and float(x) > price_reference},
    )
    prior_support_valid = math.isfinite(previous_support) and previous_support < price_reference
    prior_resistance_valid = math.isfinite(previous_resistance) and previous_resistance > price_reference

    if live_supports:
        support_1 = live_supports[0]
        support_2 = live_supports[1] if len(live_supports) > 1 else float("nan")
        if len(live_supports) == 1 and prior_support_valid and previous_support < support_1:
            support_2 = previous_support
    elif prior_support_valid and abs(previous_support - price_reference) <= 300.0:
        support_1, support_2 = previous_support, float("nan")
        chain_levels["support_source"] = "PERSISTED_OPTION_OI"
    else:
        support_1 = support_2 = float("nan")

    if live_resistances:
        resistance_1 = live_resistances[0]
        resistance_2 = live_resistances[1] if len(live_resistances) > 1 else float("nan")
        if len(live_resistances) == 1 and prior_resistance_valid and previous_resistance > resistance_1:
            resistance_2 = previous_resistance
    elif prior_resistance_valid and abs(previous_resistance - price_reference) <= 300.0:
        resistance_1, resistance_2 = previous_resistance, float("nan")
        chain_levels["resistance_source"] = "PERSISTED_OPTION_OI"
    else:
        resistance_1 = resistance_2 = float("nan")

    if math.isfinite(support_1) and math.isfinite(resistance_1) and support_1 >= resistance_1:
        logger.warning(
            "INVALID OI LEVEL ORDER: support=%.2f resistance=%.2f price=%.2f; directional entries will be blocked.",
            support_1, resistance_1, price_reference,
        )
        support_1 = support_2 = resistance_1 = resistance_2 = float("nan")

    below_vwap = math.isfinite(vwap) and current_close < vwap - STRUCTURE_VWAP_RECLAIM_BUFFER_ATR * volatility_unit
    above_vwap = math.isfinite(vwap) and current_close > vwap + STRUCTURE_VWAP_RECLAIM_BUFFER_ATR * volatility_unit

    flow_mode = str(chain_levels.get("flow_mode", "DAY_CHANGE_API_WARMUP")).upper()
    raw_intraday_flow = safe_float(chain_levels.get("change_flow_score"), safe_float(change_oi_score))
    effective_flow, effective_bias, effective_source, flow_conflict = resolve_change_oi_flow(
        intraday_score=raw_intraday_flow,
        day_score=change_oi_score,
        flow_mode=flow_mode,
    )
    # Directional option entries require material, not merely marginal, Change-OI.
    # The lower CONFIRM threshold still detects/report conflicts; the STRONG
    # threshold is the authorization threshold for actual entries.
    bearish_flow_ok = effective_flow <= -STRUCTURE_CHANGE_OI_STRONG and not flow_conflict
    bullish_flow_ok = effective_flow >= STRUCTURE_CHANGE_OI_STRONG and not flow_conflict

    futures_conflict_bearish = bool(
        futures_bias > 0 and futures_strength >= STRUCTURE_FUTURES_CONFLICT_STRENGTH
    )
    futures_conflict_bullish = bool(
        futures_bias < 0 and futures_strength >= STRUCTURE_FUTURES_CONFLICT_STRENGTH
    )

    price_info = price_action_regime_snapshot(primary_session, vwap, volatility_unit)
    session_move = safe_float(price_info.get("session_move_atr"), 0.0)
    recent12_move = safe_float(price_info.get("recent12_move_atr"), 0.0)
    recent3_move = safe_float(price_info.get("recent3_move_atr"), 0.0)
    down_ratio = safe_float(price_info.get("directional_down_ratio"), 0.0)
    up_ratio = safe_float(price_info.get("directional_up_ratio"), 0.0)
    efficiency = safe_float(price_info.get("trend_efficiency"), 0.0)
    price_structure = str(price_info.get("structure", "MIXED")).upper()

    bearish_movement = bool(
        session_move <= -0.15
        or recent12_move <= -0.20
        or (price_structure == "LH_LL" and down_ratio >= 0.45)
    )
    bullish_movement = bool(
        session_move >= 0.15
        or recent12_move >= 0.20
        or (price_structure == "HH_HL" and up_ratio >= 0.45)
    )

    bearish_environment = below_vwap and bearish_movement
    bullish_environment = above_vwap and bullish_movement
    bearish_base = below_vwap and bearish_flow_ok
    bullish_base = above_vwap and bullish_flow_ok

    strong_bullish_reversal = bool(
        above_vwap and bullish_flow_ok
        and (bool(price_info.get("bullish_structure")) or recent12_move >= 0.35)
        and (efficiency >= 0.20 or recent3_move >= 0.35)
    )
    strong_bearish_reversal = bool(
        below_vwap and bearish_flow_ok
        and (bool(price_info.get("bearish_structure")) or recent12_move <= -0.35)
        and (efficiency >= 0.20 or recent3_move <= -0.35)
    )

    carried_bearish = bearish_prior and bearish_base and not strong_bullish_reversal
    carried_bullish = bullish_prior and bullish_base and not strong_bearish_reversal

    support_is_authoritative = str(chain_levels.get("support_source", "")).upper() in {"OPTION_OI", "OPTION_OI_OI_DOMINANCE", "PERSISTED_OPTION_OI"}
    resistance_is_authoritative = str(chain_levels.get("resistance_source", "")).upper() in {"OPTION_OI", "OPTION_OI_OI_DOMINANCE", "PERSISTED_OPTION_OI"}

    # Preserve a crossed prior OI wall only as a breakout/breakdown reference.
    # It must never replace the current support/resistance used for targets.
    breakdown_reference = (
        previous_support
        if bearish_prior and math.isfinite(previous_support) and previous_support > price_reference
        else support_1
    )
    breakout_reference = (
        previous_resistance
        if bullish_prior and math.isfinite(previous_resistance) and previous_resistance < price_reference
        else resistance_1
    )
    below_support_bars = int(np.sum(work["close"].tail(max(STRUCTURE_HOLD_BARS, 2)).to_numpy(dtype=float) < breakdown_reference - break_buffer)) if math.isfinite(breakdown_reference) and not work.empty else 0
    above_resistance_bars = int(np.sum(work["close"].tail(max(STRUCTURE_HOLD_BARS, 2)).to_numpy(dtype=float) > breakout_reference + break_buffer)) if math.isfinite(breakout_reference) and not work.empty else 0

    fresh_bearish_break = bool(support_is_authoritative and math.isfinite(breakdown_reference) and below_vwap and current_close < breakdown_reference - break_buffer and below_support_bars >= max(1, STRUCTURE_HOLD_BARS) and bearish_flow_ok)
    fresh_bullish_break = bool(resistance_is_authoritative and math.isfinite(breakout_reference) and above_vwap and current_close > breakout_reference + break_buffer and above_resistance_bars >= max(1, STRUCTURE_HOLD_BARS) and bullish_flow_ok)

    bearish_level_ok = bool(support_is_authoritative and math.isfinite(support_1) and support_1 < price_reference)
    bullish_level_ok = bool(resistance_is_authoritative and math.isfinite(resistance_1) and resistance_1 > price_reference)

    continuous_bearish = bool(
        bearish_base and bearish_level_ok and not futures_conflict_bearish
        and (bearish_movement or carried_bearish or fresh_bearish_break)
        and not strong_bullish_reversal
    )
    continuous_bullish = bool(
        bullish_base and bullish_level_ok and not futures_conflict_bullish
        and (bullish_movement or carried_bullish or fresh_bullish_break)
        and not strong_bearish_reversal
    )

    if continuous_bearish and continuous_bullish:
        if effective_flow < 0:
            continuous_bullish = False
        elif effective_flow > 0:
            continuous_bearish = False
        else:
            continuous_bearish = continuous_bullish = False

    if continuous_bearish:
        direction, market_phase = "BEARISH", "CONTINUOUS_BEARISH"
        entry_confirmed, confirmation_state = True, "STRUCTURAL_CONTINUATION"
        interpretation = "CONTINUOUS BEARISH — BELOW VWAP + SUSTAINED DOWNWARD PRICE ACTION + BEARISH CHANGE-OI"
        scenario_trigger = f"NIFTY remains below VWAP with sustained bearish price action and bearish Change-OI; OI support={support_1:.2f} is the T1/breakdown reference when available."
        scenario_invalidation = "Invalidate bearish structure after sustained VWAP reclaim with opposing Change-OI and decisive bullish price structure; a small 3m bounce alone does not invalidate the trend."
    elif continuous_bullish:
        direction, market_phase = "BULLISH", "CONTINUOUS_BULLISH"
        entry_confirmed, confirmation_state = True, "STRUCTURAL_CONTINUATION"
        interpretation = "CONTINUOUS BULLISH — ABOVE VWAP + SUSTAINED UPWARD PRICE ACTION + BULLISH CHANGE-OI"
        scenario_trigger = f"NIFTY remains above VWAP with sustained bullish price action and bullish Change-OI; OI resistance={resistance_1:.2f} is the T1/breakout reference when available."
        scenario_invalidation = "Invalidate bullish structure after sustained VWAP loss with opposing Change-OI and decisive bearish price structure; a small 3m dip alone does not invalidate the trend."
    elif below_vwap and flow_conflict:
        direction, market_phase = "BEARISH", "BEARISH"
        entry_confirmed, confirmation_state = False, "FLOW_CONFLICT"
        interpretation = "BEARISH WATCH — BELOW VWAP BUT CHANGE-OI CONFLICTING"
        scenario_trigger = f"Wait for non-conflicting bearish Change-OI and sustained bearish price action; support={support_1:.2f}."
        scenario_invalidation = "Bearish watch weakens on sustained VWAP reclaim and bullish price structure."
    elif above_vwap and flow_conflict:
        direction, market_phase = "BULLISH", "BULLISH"
        entry_confirmed, confirmation_state = False, "FLOW_CONFLICT"
        interpretation = "BULLISH WATCH — ABOVE VWAP BUT CHANGE-OI CONFLICTING"
        scenario_trigger = f"Wait for non-conflicting bullish Change-OI and sustained bullish price action; resistance={resistance_1:.2f}."
        scenario_invalidation = "Bullish watch weakens on sustained VWAP loss and bearish price structure."
    elif below_vwap and bearish_flow_ok and futures_conflict_bearish:
        direction, market_phase = "BEARISH", "BEARISH"
        entry_confirmed, confirmation_state = False, "FUTURES_CONFLICT"
        interpretation = "BEARISH WATCH — PRICE/VWAP + CHANGE-OI BEARISH, BUT FUTURES OI IS BULLISH"
        scenario_trigger = f"Wait for futures price/OI to stop contradicting the bearish structure; support={support_1:.2f}."
        scenario_invalidation = "Do not open a bearish option while strong futures positioning remains bullish."
    elif above_vwap and bullish_flow_ok and futures_conflict_bullish:
        direction, market_phase = "BULLISH", "BULLISH"
        entry_confirmed, confirmation_state = False, "FUTURES_CONFLICT"
        interpretation = "BULLISH WATCH — PRICE/VWAP + CHANGE-OI BULLISH, BUT FUTURES OI IS BEARISH"
        scenario_trigger = f"Wait for futures price/OI to stop contradicting the bullish structure; resistance={resistance_1:.2f}."
        scenario_invalidation = "Do not open a bullish option while strong futures positioning remains bearish."
    elif below_vwap and bearish_flow_ok:
        direction, market_phase = "BEARISH", "BEARISH"
        entry_confirmed, confirmation_state = False, "STRUCTURAL_WATCH"
        interpretation = "BEARISH WATCH — BELOW VWAP + BEARISH CHANGE-OI, PRICE PERSISTENCE OR OI LEVEL NOT CONFIRMED"
        scenario_trigger = f"Wait for sustained bearish price action and valid OI support; support={support_1:.2f}."
        scenario_invalidation = "Bearish watch weakens on sustained VWAP reclaim with opposing price structure and Change-OI."
    elif above_vwap and bullish_flow_ok:
        direction, market_phase = "BULLISH", "BULLISH"
        entry_confirmed, confirmation_state = False, "STRUCTURAL_WATCH"
        interpretation = "BULLISH WATCH — ABOVE VWAP + BULLISH CHANGE-OI, PRICE PERSISTENCE OR OI LEVEL NOT CONFIRMED"
        scenario_trigger = f"Wait for sustained bullish price action and valid OI resistance; resistance={resistance_1:.2f}."
        scenario_invalidation = "Bullish watch weakens on sustained VWAP loss with opposing price structure and Change-OI."
    elif bearish_environment:
        direction, market_phase = "BEARISH", "BEARISH"
        entry_confirmed, confirmation_state = False, "FLOW_WAIT"
        interpretation = "BEARISH WATCH — PRICE/VWAP STRUCTURE DOWN, CHANGE-OI NOT CONFIRMING"
        scenario_trigger = f"Wait for bearish Change-OI confirmation; support={support_1:.2f}."
        scenario_invalidation = "Bearish watch weakens on sustained VWAP reclaim and bullish price structure."
    elif bullish_environment:
        direction, market_phase = "BULLISH", "BULLISH"
        entry_confirmed, confirmation_state = False, "FLOW_WAIT"
        interpretation = "BULLISH WATCH — PRICE/VWAP STRUCTURE UP, CHANGE-OI NOT CONFIRMING"
        scenario_trigger = f"Wait for bullish Change-OI confirmation; resistance={resistance_1:.2f}."
        scenario_invalidation = "Bullish watch weakens on sustained VWAP loss and bearish price structure."
    else:
        direction, market_phase = "NEUTRAL", "SIDEWAYS"
        entry_confirmed, confirmation_state = False, "NO_TRADE"
        interpretation = "SIDEWAYS / MIXED — NO STRUCTURAL DIRECTION CONFIRMED"
        scenario_trigger = f"Wait for VWAP-side alignment + sustained price action + confirming Change-OI; support={support_1:.2f} resistance={resistance_1:.2f}."
        scenario_invalidation = "No directional entry while VWAP, price action and Change-OI remain mixed."

    pcr = safe_float(chain_levels.get("pcr"), float("nan"))
    pcr_bias = 1 if math.isfinite(pcr) and pcr >= 1.10 else -1 if math.isfinite(pcr) and pcr <= 0.90 else 0
    structure_score = 8.0 if continuous_bullish else -8.0 if continuous_bearish else 2.0 if direction == "BULLISH" else -2.0 if direction == "BEARISH" else 0.0
    confidence = 95.0 if (continuous_bullish or continuous_bearish) else 72.0 if direction in {"BULLISH", "BEARISH"} else 40.0

    reasons = [
        f"PRIMARY: NIFTY={current_close:.2f} vs VWAP={vwap:.2f}; below_vwap={below_vwap}; above_vwap={above_vwap}.",
        f"PRICE ACTION: structure={price_structure}; session={session_move:+.2f}vol; recent12={recent12_move:+.2f}vol; recent3={recent3_move:+.2f}vol; down_ratio={down_ratio:.2f}; up_ratio={up_ratio:.2f}; efficiency={efficiency:.2f}.",
        f"CHANGE-OI: effective={effective_flow:+.3f}; bias={effective_bias:+d}; source={effective_source}; conflict={flow_conflict}.",
        f"OI STRUCTURE: support={support_1:.2f}/{support_2:.2f}; resistance={resistance_1:.2f}/{resistance_2:.2f}; breakdown_ref={breakdown_reference:.2f}; breakout_ref={breakout_reference:.2f}; breakdown={fresh_bearish_break}; breakout={fresh_bullish_break}.",
        f"FUTURES CONTEXT: regime={futures_regime}; bias={futures_bias:+d}; strength={futures_strength:.3f}; conflict_bearish={futures_conflict_bearish}; conflict_bullish={futures_conflict_bullish}.",
        f"ENTRY GATES: bearish_level_ok={bearish_level_ok}; bullish_level_ok={bullish_level_ok}; minimum_entry_change_oi={STRUCTURE_CHANGE_OI_STRONG:.3f}.",
        f"PCR CONTEXT: value={pcr:.3f}; bias={pcr_bias:+d}." if math.isfinite(pcr) else "PCR CONTEXT: unavailable from current chain.",
    ]

    logger.info(
        "STRUCTURE ENGINE: phase=%s direction=%s price=%.2f VWAP=%.2f support=%s resistance=%s ChangeOI=%+.3f "
        "breakout=%s breakdown=%s Entry=%s",
        market_phase, direction, current_close, vwap,
        f"{support_1:.2f}" if math.isfinite(support_1) else "NA",
        f"{resistance_1:.2f}" if math.isfinite(resistance_1) else "NA",
        effective_flow, fresh_bullish_break, fresh_bearish_break, entry_confirmed,
    )

    components = {
        "structure_change_oi": float(effective_flow),
        "structure_change_oi_intraday_raw": float(raw_intraday_flow),
        "structure_change_oi_day_raw": float(change_oi_score),
        "structure_change_oi_conflict": 1.0 if flow_conflict else 0.0,
        "structure_change_oi_source": effective_source,
        "structure_futures_conflict_bullish": 1.0 if futures_conflict_bullish else 0.0,
        "structure_futures_conflict_bearish": 1.0 if futures_conflict_bearish else 0.0,
        "structure_vwap": 1.0 if above_vwap else -1.0 if below_vwap else 0.0,
        "structure_price_break": 1.0 if fresh_bullish_break else -1.0 if fresh_bearish_break else 0.0,
        "structure_score": float(structure_score),
        "intraday_trend": float(latest_move / volatility_unit),
        "vwap_level": 1.0 if above_vwap else -1.0 if below_vwap else 0.0,
        "recent3_movement_atr": float(recent3_move),
        "price_session_atr": float(session_move),
        "price_recent12_atr": float(recent12_move),
        "price_directional_down_ratio": float(down_ratio),
        "price_directional_up_ratio": float(up_ratio),
        "price_trend_efficiency": float(efficiency),
        "price_structure": 1.0 if price_structure == "HH_HL" else -1.0 if price_structure == "LH_LL" else 0.0,
        "vwap_distance_atr": float(abs(current_close - vwap) / volatility_unit) if math.isfinite(vwap) else float("inf"),
        "volatility_unit": float(volatility_unit),
        "active_structure_level": float(support_1 if direction == "BEARISH" else resistance_1 if direction == "BULLISH" else float("nan")),
    }

    return StructureResult(
        direction=direction, score=float(structure_score), confidence=float(confidence), interpretation=interpretation,
        components=components, vwap=float(vwap), vwap_slope=float(vwap_slope),
        futures_regime=futures_regime, futures_bias=futures_bias, futures_oi_strength=futures_strength,
        futures_oi_persistence=float(futures_info.get("oi_persistence", 0.0)),
        futures_live_oi_change=float(futures_info.get("live_oi_change", float("nan"))),
        intraday_bias=1 if latest_move > 0 else -1 if latest_move < 0 else 0,
        intraday_strength=float(min(abs(latest_move) / volatility_unit, 1.0)),
        intraday_score=float(latest_move / volatility_unit),
        chain_predictive_bias=int(chain_levels.get("predictive_bias", effective_bias)),
        chain_predictive_strength=float(chain_levels.get("predictive_strength", abs(effective_flow))),
        chain_level_bias=int(chain_levels.get("level_bias", 0)),
        support_strength=float(chain_levels.get("support_strength", 0.0)),
        resistance_strength=float(chain_levels.get("resistance_strength", 0.0)),
        support_change_strength=float(chain_levels.get("support_change_strength", 0.0)),
        resistance_change_strength=float(chain_levels.get("resistance_change_strength", 0.0)),
        support_1=float(support_1), support_2=float(support_2),
        resistance_1=float(resistance_1), resistance_2=float(resistance_2),
        market_phase=market_phase, entry_confirmed=bool(entry_confirmed), reversal_confirmations=0,
        confirmation_state=confirmation_state, pcr=pcr if math.isfinite(pcr) else float("nan"),
        pcr_bias=int(pcr_bias), false_breakout=False, trap_level=0.0,
        entry_trigger=scenario_trigger, invalidation_rule=scenario_invalidation, reasons=reasons,
    )
# OPTION SELECTION
# =============================================================================



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
        theta=theta,
        spread_pct=spread_pct,
        theta_burden_pct_day=theta_burden,
        premium_vwap=safe_float(data.get("premium_vwap"), float("nan")),
    )





def normalized_execution_score(
    flow_score: float,
    vwap_score: float,
    coi_score: float,
    delta_weight: float,
    *,
    coi_available: bool = True,
) -> float:
    """Return a transparent 0..1 weighted score; exclude unavailable/neutral COI.

    Flow (30%), option-premium VWAP (30%), COI (20%) and delta/moneyness (20%)
    are normalized before aggregation. A positive COI Push/Floor/Roll result uses
    its normalized share of the maximum configured COI points. Missing or neutral
    COI contributes zero points; the other weights are NOT renormalized upward.
    This prevents missing COI from being treated as evidence while also preventing
    a weak positive COI value from lowering the score merely because it became an
    available component. Cold-start COI has already been reduced by the COI matrix.

    MIN_EXECUTION_SCORE is an explicit rule-based quality threshold, not a
    statistically fitted win probability. Proper empirical calibration requires
    historical replay with outcome labels.
    """
    flow_component = min(1.0, max(0.0, safe_float(flow_score, 0.0)))
    vwap_component = min(1.0, max(0.0, safe_float(vwap_score, 0.0)))
    delta_component = min(1.0, max(0.0, safe_float(delta_weight, 0.0)))
    max_coi_points = max(
        COI_PUSH_MAX_POINTS + COI_FLOOR_MAX_POINTS + COI_ROLL_MAX_POINTS, 1e-9
    )
    coi_component = min(1.0, max(0.0, safe_float(coi_score, 0.0) / max_coi_points))

    score = (
        0.30 * flow_component
        + 0.30 * vwap_component
        + 0.20 * delta_component
        + (0.20 * coi_component if coi_available else 0.0)
    )
    return float(min(1.0, max(0.0, score)))


def select_directional_option(
    chain: list[dict[str, Any]],
    direction: str,
    spot: float,
    *,
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
    market_intensity: str = "NORMAL",
    is_expiry_day: bool = False,
    now: Optional[datetime] = None,
    option_metrics_by_instrument: Optional[dict[str, dict[str, float]]] = None,
    oi_velocity_by_strike: Optional[dict[float, dict[str, Any]]] = None,
) -> OptionCandidate:
    """Select a strike using regime routing + strict option VWAP/COI/delta gates."""
    direction = str(direction).upper()
    intensity = str(market_intensity).upper()
    current_time = now or now_ist()
    if current_time.tzinfo is None:
        current_time = current_time.replace(tzinfo=IST)
    else:
        current_time = current_time.astimezone(IST)
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("Option selection requires BULLISH or BEARISH.")
    if intensity in {"SIDEWAYS", "UNKNOWN"}:
        raise ScannerError(f"Directional option buying blocked for intensity={intensity}.")

    decision_chain, window_meta = option_chain_atm_window(chain, spot)
    rows = chain_rows(decision_chain)
    strikes = sorted(rows)
    step = safe_float(window_meta.get("strike_step"), strike_step(strikes))
    atm = safe_float(window_meta.get("atm_strike"), nearest_strike(spot, strikes))
    atm_distance_steps = abs(atm - spot) / max(step, 1.0)
    if atm_distance_steps > 1.25:
        raise ScannerError(
            f"ATM strike sanity check failed: index spot={spot:.2f}, nearest strike={atm:.0f}, "
            f"step={step:.0f} ({atm_distance_steps:.2f} steps away)."
        )

    permitted_list = [round(float(x), 2) for x in permitted_strikes_for_regime(
        atm, step, direction, intensity, is_expiry_day=is_expiry_day, now=now
    )]
    lower_bound = safe_float(window_meta.get("lower_bound"), atm - ATM_ANALYSIS_RADIUS_LEVELS * step)
    upper_bound = safe_float(window_meta.get("upper_bound"), atm + ATM_ANALYSIS_RADIUS_LEVELS * step)
    permitted_list = [x for x in permitted_list if lower_bound - 0.01 <= x <= upper_bound + 0.01]
    if not permitted_list:
        raise ScannerError(
            f"No permitted strikes inside ATM±{ATM_ANALYSIS_RADIUS_LEVELS} window "
            f"[{lower_bound:.0f},{upper_bound:.0f}] for {direction}/{intensity} at this time of day."
        )
    option_type = "CE" if direction == "BULLISH" else "PE"
    metrics = option_metrics_by_instrument if isinstance(option_metrics_by_instrument, dict) else {}
    velocity_map = oi_velocity_by_strike if isinstance(oi_velocity_by_strike, dict) else {}
    flow_map = change_oi_by_strike if isinstance(change_oi_by_strike, dict) else {}
    tod = time_of_day_window(now)
    max_spread = min(MAX_SPREAD_PCT, OPENING_MAX_SPREAD_PCT) if tod == "OPENING" else MAX_SPREAD_PCT

    eligible: list[tuple[float, OptionCandidate, bool]] = []
    rejection_log: list[str] = []
    velocity_coverage_count = 0
    for target in permitted_list:
        row_key = min(strikes, key=lambda value: abs(value - target))
        if abs(row_key - target) > 0.01:
            rejection_log.append(f"{option_type} {target:.0f}: strike absent from chain")
            continue
        data = option_side_data(rows[row_key], option_type)
        instrument_key = str(data.get("instrument_key") or "").strip()
        if not instrument_key:
            rejection_log.append(f"{option_type} {row_key:.0f}: no instrument key")
            continue
        ltp = safe_float(data.get("ltp"), 0.0)
        if ltp <= 0:
            rejection_log.append(f"{option_type} {row_key:.0f}: invalid LTP")
            continue
        if safe_float(data.get("oi"), 0.0) < MIN_OI or safe_float(data.get("volume"), 0.0) < MIN_VOLUME:
            rejection_log.append(f"{option_type} {row_key:.0f}: insufficient OI/volume")
            continue

        micro = metrics.get(instrument_key, {}) if isinstance(metrics, dict) else {}
        premium_vwap = safe_float(micro.get("premium_vwap"), float("nan")) if isinstance(micro, dict) else float("nan")
        if not math.isfinite(premium_vwap) or premium_vwap <= 0:
            rejection_log.append(f"{option_type} {row_key:.0f}: own premium VWAP unavailable")
            continue
        if ltp <= premium_vwap:
            rejection_log.append(f"{option_type} {row_key:.0f}: LTP {ltp:.2f} <= premium VWAP {premium_vwap:.2f}")
            continue

        delta = safe_float(data.get("delta"), float("nan"))
        if not math.isfinite(delta) or abs(delta) > 1.0 or abs(delta) <= 0.0:
            rejection_log.append(f"{option_type} {row_key:.0f}: valid live delta unavailable")
            continue
        delta_abs = abs(delta)
        if intensity == "EXHAUSTION":
            delta_floor = 0.75
        elif is_expiry_day or intensity != "STRONG":
            delta_floor = 0.50
        else:
            delta_floor = 0.0
        if delta_abs < delta_floor:
            rejection_log.append(f"{option_type} {row_key:.0f}: delta {delta_abs:.3f} below floor {delta_floor:.2f}")
            continue

        bid = safe_float(data.get("bid"), 0.0)
        ask = safe_float(data.get("ask"), 0.0)
        if bid <= 0 or ask <= 0 or ask < bid:
            rejection_log.append(f"{option_type} {row_key:.0f}: invalid bid/ask")
            continue
        mid = (bid + ask) / 2.0
        spread_pct = (ask - bid) / mid if mid > 0 else 1.0
        if spread_pct > max_spread:
            rejection_log.append(f"{option_type} {row_key:.0f}: spread {spread_pct:.2%} > {max_spread:.2%}")
            continue

        # OI is scored through the four-part COI matrix. During 09:15-09:45 it
        # uses cumulative opening COI with a reduced weight; after 09:45 it only
        # accepts measured 15-30 minute snapshots. Missing history scores zero.
        velocity = velocity_map.get(float(row_key), {}) if isinstance(velocity_map, dict) else {}
        coi_matrix = score_coi_matrix_for_strike(
            direction, float(row_key), float(atm), float(step), velocity_map, now=current_time
        )
        if bool(coi_matrix.get("disqualified")):
            rejection_log.append(
                f"{option_type} {row_key:.0f}: COI PIN disqualification; both Call and Put OI surged at the same strike."
            )
            logger.warning(
                "COI PIN DISQUALIFICATION: direction=%s candidate=%s %.0f call_COI=%s put_COI=%s.",
                direction, option_type, row_key,
                f"{safe_float(velocity.get('call_oi_change_pct'), float('nan')) * 100.0:+.2f}%",
                f"{safe_float(velocity.get('put_oi_change_pct'), float('nan')) * 100.0:+.2f}%",
            )
            continue

        wall_penalty_raw = safe_float(coi_matrix.get("wall_penalty"), 0.0)
        wall_veto = execution_veto_reason(
            None, coi_label=str(coi_matrix.get("label", "")), wall_penalty=wall_penalty_raw,
            disqualified=False,
        )
        if wall_veto:
            rejection_log.append(
                f"{option_type} {row_key:.0f}: {wall_veto}; opposing OI absorption is a hard execution veto."
            )
            logger.warning(
                "COI WALL PENALTY VETO: direction=%s candidate=%s %.0f state=%s call_COI=%s put_COI=%s penalty=%.3f.",
                direction, option_type, row_key, str(coi_matrix.get("label", "WALL_PENALTY")),
                f"{safe_float(velocity.get('call_oi_change_pct'), float('nan')) * 100.0:+.2f}%",
                f"{safe_float(velocity.get('put_oi_change_pct'), float('nan')) * 100.0:+.2f}%",
                wall_penalty_raw,
            )
            continue

        call_pct = safe_float(velocity.get("call_oi_change_pct"), float("nan")) if isinstance(velocity, dict) else float("nan")
        put_pct = safe_float(velocity.get("put_oi_change_pct"), float("nan")) if isinstance(velocity, dict) else float("nan")
        baseline_minutes = safe_float(velocity.get("baseline_minutes"), float("nan")) if isinstance(velocity, dict) else float("nan")
        baseline_mode = str(velocity.get("baseline_mode", "UNAVAILABLE")) if isinstance(velocity, dict) else "UNAVAILABLE"
        velocity_valid = bool(coi_matrix.get("available")) and (
            math.isfinite(call_pct) or math.isfinite(put_pct)
        )
        if velocity_valid:
            if baseline_mode == "COLD_START_CUMULATIVE":
                velocity_valid = 0.25 < baseline_minutes <= OPTION_OI_HISTORY_KEEP_MINUTES
            elif baseline_mode == "ROLLING_15_30":
                velocity_valid = OPTION_OI_MIN_AGE_MINUTES <= baseline_minutes <= OPTION_OI_MAX_AGE_MINUTES
            else:
                velocity_valid = False
        if not velocity_valid:
            call_pct = put_pct = baseline_minutes = float("nan")
            coi_score = 0.0
            coi_push = coi_floor = coi_roll = coi_wall = 0.0
            coi_label = "COI_UNAVAILABLE"
            coi_weight = COI_COLD_START_WEIGHT if current_time.time() < COI_COLD_START_END else 1.0
        else:
            coi_score = safe_float(coi_matrix.get("score"), 0.0)
            coi_weight = safe_float(coi_matrix.get("weight"), 1.0)
            coi_push = safe_float(coi_matrix.get("push"), 0.0) * coi_weight
            coi_floor = safe_float(coi_matrix.get("floor"), 0.0) * coi_weight
            coi_roll = safe_float(coi_matrix.get("roll"), 0.0) * coi_weight
            coi_wall = safe_float(coi_matrix.get("wall_penalty"), 0.0) * coi_weight
            coi_label = str(coi_matrix.get("label", "NO_CLEAR_COI_EDGE"))
            velocity_coverage_count += 1

        strike_flow = flow_map.get(float(row_key), {})
        call_bias = int(safe_float(strike_flow.get("call_bias"), 0))
        put_bias = int(safe_float(strike_flow.get("put_bias"), 0))
        desired_bias = 1 if direction == "BULLISH" else -1
        selected_bias = call_bias if option_type == "CE" else put_bias
        other_bias = put_bias if option_type == "CE" else call_bias
        normalized_flow_bias = 1 if selected_bias == desired_bias else -1 if selected_bias == -desired_bias else 0
        if normalized_flow_bias == 1:
            flow_score = 1.0
        elif selected_bias == 0 and other_bias == desired_bias:
            flow_score = 0.80
        elif selected_bias == -desired_bias and other_bias == desired_bias:
            flow_score = 0.50
        elif selected_bias == 0 and other_bias == 0:
            flow_score = 0.50
        else:
            # Conflicting flow lowers this component but does not erase the other valid score components.
            flow_score = 0.10

        if option_type == "CE":
            moneyness = "ITM" if row_key < atm - 0.01 else "ATM" if abs(row_key - atm) <= 0.01 else "OTM"
        else:
            moneyness = "ITM" if row_key > atm + 0.01 else "ATM" if abs(row_key - atm) <= 0.01 else "OTM"
        moneyness_multiplier = {"ITM": 1.0, "ATM": 0.85, "OTM": 0.65}[moneyness]
        delta_weight = moneyness_multiplier * min(delta_abs / 0.75, 1.0)
        premium_lift_pct = max((ltp - premium_vwap) / premium_vwap, 0.0)
        vwap_score = 0.50 + 0.50 * min(premium_lift_pct / 0.02, 1.0)
        # COI contributes a score bonus only when a positive Push/Floor/Roll edge is measured.
        # Neutral or unavailable COI is excluded from the score denominator, not treated as evidence.
        coi_contributes = bool(velocity_valid and math.isfinite(coi_score) and coi_score > 0.0)
        total = normalized_execution_score(
            flow_score, vwap_score, coi_score, delta_weight, coi_available=coi_contributes
        )
        coi_normalized = min(1.0, max(0.0, coi_score / max(
            COI_PUSH_MAX_POINTS + COI_FLOOR_MAX_POINTS + COI_ROLL_MAX_POINTS, 1e-9
        )))

        meta = {"strike": row_key, "type": option_type,
                "expiry": str(rows[row_key].get("expiry", ""))[:10]}
        data["premium_vwap"] = premium_vwap
        candidate = build_option_candidate(meta, data)
        candidate = replace(
            candidate,
            flow_score=flow_score,
            vwap_score=vwap_score,
            oi_momentum_score=coi_score,
            delta_weight=delta_weight,
            call_oi_change_pct_15m=call_pct * 100.0,
            put_oi_change_pct_15m=put_pct * 100.0,
            oi_velocity_baseline_minutes=baseline_minutes,
            market_intensity=intensity,
            coi_push_score=coi_push,
            coi_floor_score=coi_floor,
            coi_roll_score=coi_roll,
            coi_wall_penalty=coi_wall,
            coi_matrix_label=coi_label,
            coi_baseline_mode=baseline_mode if velocity_valid else "UNAVAILABLE",
            total_score=float(total),
        )
        eligible.append((total, candidate, moneyness == "OTM"))
        logger.info(
            "STRIKE RANK: %s %.0f regime=%s moneyness=%s total_norm_0_1=%.3f flow=%.3f vwap=%.3f "
            "COIraw=%+.3f COInorm=%.3f matrix=%s push=%.3f floor=%.3f roll=%.3f wall_penalty=%.3f "
            "coi_data=%s COI_mode=%s delta_weight=%.3f delta=%.3f premium_ltp=%.2f premium_vwap=%.2f "
            "call_COI=%s put_COI=%s baseline_min=%s flow_bias=%+d spread=%.2f%%",
            option_type, row_key, intensity, moneyness, total, flow_score, vwap_score,
            coi_score, coi_normalized, coi_label, coi_push, coi_floor, coi_roll, coi_wall,
            "AVAILABLE" if velocity_valid else "UNAVAILABLE_ZERO_WEIGHT",
            baseline_mode if velocity_valid else "UNAVAILABLE",
            delta_weight, delta, ltp, premium_vwap,
            f"{call_pct * 100.0:+.2f}%" if velocity_valid and math.isfinite(call_pct) else "NA",
            f"{put_pct * 100.0:+.2f}%" if velocity_valid and math.isfinite(put_pct) else "NA",
            f"{baseline_minutes:.1f}" if velocity_valid else "NA",
            normalized_flow_bias, spread_pct * 100.0,
        )

    logger.info(
        "COI MATRIX RANKING: valid_candidate_baselines=%d/%d protocol=%s cold_start_weight=%.2f "
        "missing_or_neutral_COI_adds_zero_points_without_reweighting; total_score_scale=0..1; pin=HARD_DISQUALIFIER; wall=HARD_EXECUTION_VETO; min_score=%.3f.",
        velocity_coverage_count, len(permitted_list),
        "COLD_START_CUMULATIVE" if current_time.time() < COI_COLD_START_END else "ROLLING_15_30",
        COI_COLD_START_WEIGHT, MIN_EXECUTION_SCORE,
    )
    if not eligible:
        detail = "; ".join(rejection_log[-10:]) or "no valid candidates"
        raise ScannerError(f"No eligible {direction}/{intensity} option. {detail}")

    eligible.sort(key=lambda item: (-item[0], item[1].strike))
    winning_score, selected, winner_is_otm = eligible[0]
    if winner_is_otm and winning_score > 0:
        safer = [
            item for item in eligible
            if not item[2]
            and item[0] >= winning_score * 0.95
            and item[0] >= MIN_EXECUTION_SCORE
        ]
        if safer:
            safer.sort(key=lambda item: (-item[0], item[1].strike))
            safer_score, safer_candidate, _ = safer[0]
            logger.info(
                "THETA SAFETY OVERRIDE: OTM winner %.0f score=%.3f replaced by safer %s %.0f score=%.3f (within 5%%).",
                selected.strike, winning_score, safer_candidate.option_type, safer_candidate.strike, safer_score,
            )
            selected = safer_candidate
            winning_score = safer_score

    final_veto = execution_veto_reason(
        winning_score, coi_label=selected.coi_matrix_label,
        wall_penalty=selected.coi_wall_penalty,
        disqualified=("PIN_DISQUALIFICATION" in str(selected.coi_matrix_label).upper()),
    )
    if final_veto:
        logger.warning("NO TRADE: selected strike vetoed before return: %s %.0f reason=%s score=%.3f",
                       selected.option_type, selected.strike, final_veto, winning_score)
        raise ScannerError(final_veto)

    permitted = {round(x, 2) for x in permitted_list}
    if round(selected.strike, 2) not in permitted:
        raise ScannerError(
            f"STRICT STRIKE VALIDATION FAILED: direction={direction} intensity={intensity} "
            f"ATM={atm:.2f} step={step:.2f} selected={selected.strike:.2f} permitted={sorted(permitted)}"
        )
    expected_type = "CE" if direction == "BULLISH" else "PE"
    if selected.option_type != expected_type:
        raise ScannerError(f"STRICT STRIKE VALIDATION FAILED: {direction} requires {expected_type}.")
    selected_call_coi = (
        f"{selected.call_oi_change_pct_15m:+.2f}%"
        if math.isfinite(selected.call_oi_change_pct_15m) else "NA"
    )
    selected_put_coi = (
        f"{selected.put_oi_change_pct_15m:+.2f}%"
        if math.isfinite(selected.put_oi_change_pct_15m) else "NA"
    )
    selected_baseline = (
        f"{selected.oi_velocity_baseline_minutes:.1f}m"
        if math.isfinite(selected.oi_velocity_baseline_minutes) else "NA"
    )
    logger.info(
        "OPTION SELECT: direction=%s intensity=%s tod=%s expiry_day=%s ATM=%.0f permitted=%s "
        "selected=%s %.0f total=%.3f LTP=%.2f option_VWAP=%.2f delta=%.3f flow=%.3f VWAPscore=%.3f "
        "COIscore=%+.3f COI_matrix=%s push=%.3f floor=%.3f roll=%.3f wall_penalty=%.3f "
        "delta_weight=%.3f call_COI=%s put_COI=%s baseline=%s mode=%s",
        direction, intensity, tod, is_expiry_day, atm, sorted(permitted), selected.option_type,
        selected.strike, winning_score, selected.ltp, selected.premium_vwap, selected.delta,
        selected.flow_score, selected.vwap_score, selected.oi_momentum_score,
        selected.coi_matrix_label, selected.coi_push_score, selected.coi_floor_score,
        selected.coi_roll_score, selected.coi_wall_penalty, selected.delta_weight,
        selected_call_coi, selected_put_coi, selected_baseline, selected.coi_baseline_mode,
    )
    return selected


def validate_continuous_option_entry(
    option: OptionCandidate,
    chain: list[dict[str, Any]],
    direction: str,
    market_phase: str,
    spot: float,
    *,
    market_intensity: str = "NORMAL",
    is_expiry_day: bool = False,
    now: Optional[datetime] = None,
) -> None:
    """Final pre-signal invariant for contract type, regime routing and hard risk filters."""
    phase = str(market_phase or "").upper()
    if phase not in {"CONTINUOUS_BULLISH", "CONTINUOUS_BEARISH"} and not phase.startswith("EXHAUSTION_"):
        raise ScannerError(f"PRE-EMAIL MARKET-PHASE VETO: phase={phase} is not an approved entry phase.")
    final_veto = execution_veto_reason(
        option.total_score, coi_label=option.coi_matrix_label,
        wall_penalty=option.coi_wall_penalty,
        disqualified=("PIN_DISQUALIFICATION" in str(option.coi_matrix_label).upper()),
    )
    if final_veto:
        raise ScannerError(f"PRE-EMAIL EXECUTION VETO: {final_veto}.")
    decision_chain, window_meta = option_chain_atm_window(chain, spot)
    rows = chain_rows(decision_chain)
    strikes = sorted(rows)
    step = safe_float(window_meta.get("strike_step"), strike_step(strikes))
    atm = safe_float(window_meta.get("atm_strike"), nearest_strike(spot, strikes))
    permitted = {
        round(float(x), 2) for x in permitted_strikes_for_regime(
            atm, step, direction, market_intensity, is_expiry_day=is_expiry_day, now=now
        )
    }
    selected_strike = round(float(option.strike), 2)
    if selected_strike not in permitted:
        raise ScannerError(
            f"PRE-EMAIL STRIKE VALIDATION FAILED: {direction}/{market_intensity} "
            f"requires {sorted(permitted)} but selected {selected_strike:.2f}."
        )
    expected_type = "CE" if direction == "BULLISH" else "PE"
    if option.option_type != expected_type:
        raise ScannerError(f"PRE-EMAIL OPTION TYPE VALIDATION FAILED: {direction} requires {expected_type}.")
    exact_row = rows.get(selected_strike)
    if exact_row is None:
        raise ScannerError(f"PRE-EMAIL CHAIN VALIDATION FAILED: strike {selected_strike:.2f} absent from live chain.")
    side = option_side_data(exact_row, expected_type)
    live_key = str(side.get("instrument_key") or "")
    if not live_key or live_key != option.instrument_key:
        raise ScannerError("PRE-EMAIL INSTRUMENT VALIDATION FAILED: selected key does not match live chain.")
    live_ltp = safe_float(side.get("ltp"), 0.0)
    if live_ltp <= 0 or not math.isfinite(option.premium_vwap) or live_ltp <= option.premium_vwap:
        raise ScannerError("PRE-EMAIL PREMIUM VWAP VALIDATION FAILED: live LTP must be above valid option VWAP.")
    delta_floor = 0.75 if market_intensity == "EXHAUSTION" else 0.50 if (is_expiry_day or market_intensity != "STRONG") else 0.0
    if abs(option.delta) < delta_floor:
        raise ScannerError(f"PRE-EMAIL DELTA VALIDATION FAILED: |delta|={abs(option.delta):.3f} < {delta_floor:.2f}.")
    logger.info(
        "STRICT STRIKE VALIDATION PASSED: direction=%s phase=%s intensity=%s ATM=%.0f step=%.0f "
        "selected=%s %.0f permitted=%s premium_LTP=%.2f premium_VWAP=%.2f delta=%.3f",
        direction, phase, market_intensity, atm, step, expected_type, selected_strike,
        sorted(permitted), live_ltp, option.premium_vwap, option.delta,
    )


# =============================================================================
# AUTHORITATIVE PA/OI TRADE LEVEL ENGINE
# =============================================================================


def _completed_price_action_frame(
    price_session: Optional[pd.DataFrame],
) -> pd.DataFrame:
    if price_session is None or price_session.empty:
        return pd.DataFrame()
    work = filter_completed_candles(price_session.copy(), 3)
    if work.empty:
        return work
    work = work.sort_values("timestamp").copy()
    for column in ("open", "high", "low", "close"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    return work.dropna(subset=["high", "low", "close"])


def _price_action_swings(
    price_session: Optional[pd.DataFrame],
    *,
    lookback: int = PA_OI_SWING_LOOKBACK,
) -> dict[str, list[float]]:
    """Return recent completed 3m swing levels without ATR-derived targets."""
    work = _completed_price_action_frame(price_session)
    if work.empty:
        return {"highs": [], "lows": []}
    work = work.tail(max(int(lookback), 5)).reset_index(drop=True)

    swing_highs: list[float] = []
    swing_lows: list[float] = []
    for i in range(1, len(work) - 1):
        high_i = safe_float(work.loc[i, "high"], float("nan"))
        low_i = safe_float(work.loc[i, "low"], float("nan"))
        prev_high = safe_float(work.loc[i - 1, "high"], float("nan"))
        next_high = safe_float(work.loc[i + 1, "high"], float("nan"))
        prev_low = safe_float(work.loc[i - 1, "low"], float("nan"))
        next_low = safe_float(work.loc[i + 1, "low"], float("nan"))
        if math.isfinite(high_i) and high_i >= prev_high and high_i >= next_high:
            swing_highs.append(high_i)
        if math.isfinite(low_i) and low_i <= prev_low and low_i <= next_low:
            swing_lows.append(low_i)

    # Include the latest completed extreme as price-action context even when it
    # is not a textbook pivot. This prevents a flat series from returning no PA level.
    if not swing_highs:
        latest_high = safe_float(work["high"].max(), float("nan"))
        if math.isfinite(latest_high):
            swing_highs.append(latest_high)
    if not swing_lows:
        latest_low = safe_float(work["low"].min(), float("nan"))
        if math.isfinite(latest_low):
            swing_lows.append(latest_low)

    return {
        "highs": sorted({round(x, 2) for x in swing_highs if math.isfinite(x)}),
        "lows": sorted({round(x, 2) for x in swing_lows if math.isfinite(x)}),
    }


def _rank_current_oi_walls(
    chain: list[dict[str, Any]],
    spot: float,
    *,
    side: str,
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
) -> list[dict[str, Any]]:
    """Return current OI walls with OI as the primary ranking variable.

    This is deliberately not a weighted multi-factor market vote. OI
    concentration determines the wall; distance and Change-OI are tie-breakers.
    """
    try:
        decision_chain, window_meta = option_chain_atm_window(chain, spot)
    except ScannerError:
        return []
    rows = chain_rows(decision_chain)
    strikes = sorted(rows)
    if not strikes:
        return []
    step = max(safe_float(window_meta.get("strike_step"), strike_step(strikes)), 1.0)
    candidates: list[dict[str, Any]] = []

    for strike, row in rows.items():
        distance_steps = abs(float(strike) - float(spot)) / step
        # Keep the closest OI wall even when spot is less than one strike step away;
        # omitting it can skip the real T1/obstacle and overstate reward-to-risk.
        ce_oi = max(safe_float(option_side_data(row, "CE").get("oi")), 0.0)
        pe_oi = max(safe_float(option_side_data(row, "PE").get("oi")), 0.0)
        if side == "support":
            if float(strike) >= float(spot) or pe_oi <= ce_oi:
                continue
            option_type = "PE"
            oi = pe_oi
            flow = (change_oi_by_strike or {}).get(float(strike), {})
            flow_change = safe_float(flow.get("put_oi_change"), 0.0)
            flow_bias = int(flow.get("put_bias", 0)) or (1 if flow_change > 0 else -1 if flow_change < 0 else 0)
        else:
            if float(strike) <= float(spot) or ce_oi <= pe_oi:
                continue
            option_type = "CE"
            oi = ce_oi
            flow = (change_oi_by_strike or {}).get(float(strike), {})
            flow_change = safe_float(flow.get("call_oi_change"), 0.0)
            flow_bias = int(flow.get("call_bias", 0)) or (1 if flow_change > 0 else -1 if flow_change < 0 else 0)
        if oi <= 0:
            continue
        candidates.append({
            "strike": float(strike),
            "oi": float(oi),
            "call_oi": float(ce_oi),
            "put_oi": float(pe_oi),
            "dominant_role": "SUPPORT" if pe_oi > ce_oi else "RESISTANCE",
            "flow_bias": int(flow_bias),
            "flow_change": float(flow_change),
            "option_type": option_type,
            "distance_steps": float(distance_steps),
        })

    if not candidates:
        return []
    max_oi = max(x["oi"] for x in candidates)
    median_oi = float(np.median([x["oi"] for x in candidates]))
    for item in candidates:
        item["oi_ratio"] = float(item["oi"] / max(max_oi, 1.0))
        item["meaningful"] = bool(
            item["oi_ratio"] >= PA_OI_SECONDARY_OI_RATIO
            or item["oi"] >= median_oi
        )
        item["strength"] = item["oi_ratio"]

    return sorted(
        candidates,
        key=lambda x: (-float(x["oi"]), float(x["distance_steps"]), -abs(float(x["flow_change"])), float(x["strike"])),
    )


def _initial_structural_stop(
    spot: float,
    direction: str,
    price_action: dict[str, list[float]],
    opposing_walls: list[dict[str, Any]],
    strike_step_value: float,
) -> tuple[float, str]:
    """Set the pre-T1 SL beyond the PA/OI invalidation structures."""
    buffer = max(0.10, strike_step_value * PA_OI_STOP_BUFFER_STEPS)
    if direction == "BEARISH":
        pa = min([x for x in price_action.get("highs", []) if x > spot], default=float("nan"))
        oi = min([float(x["strike"]) for x in opposing_walls if float(x["strike"]) > spot], default=float("nan"))
        if math.isfinite(pa) and math.isfinite(oi):
            return min(pa, oi) + buffer, "PRICE_ACTION_AND_OI_RESISTANCE"
        if math.isfinite(pa):
            return pa + buffer, "PRICE_ACTION_SWING_HIGH"
        if math.isfinite(oi):
            return oi + buffer, "OI_RESISTANCE"
        raise ScannerError("No bearish PA/OI invalidation level available.")

    pa = max([x for x in price_action.get("lows", []) if x < spot], default=float("nan"))
    oi = max([float(x["strike"]) for x in opposing_walls if float(x["strike"]) < spot], default=float("nan"))
    if math.isfinite(pa) and math.isfinite(oi):
        return max(pa, oi) - buffer, "PRICE_ACTION_AND_OI_SUPPORT"
    if math.isfinite(pa):
        return pa - buffer, "PRICE_ACTION_SWING_LOW"
    if math.isfinite(oi):
        return oi - buffer, "OI_SUPPORT"
    raise ScannerError("No bullish PA/OI invalidation level available.")


def determine_structural_trade_levels(
    chain: list[dict[str, Any]],
    spot: float,
    structure: StructureResult,
    price_session: Optional[pd.DataFrame],
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
) -> tuple[float, float, float, dict[str, Any]]:
    """Determine authoritative NIFTY T1/T2/SL strictly from price action + OI."""
    direction = str(structure.direction).upper()
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("Structural trade levels require BULLISH or BEARISH direction.")

    decision_chain, window_meta = option_chain_atm_window(chain, spot)
    rows = chain_rows(decision_chain)
    step = max(safe_float(window_meta.get("strike_step"), strike_step(sorted(rows))), 1.0)
    window_low = safe_float(window_meta.get("lower_bound"), float("nan"))
    window_high = safe_float(window_meta.get("upper_bound"), float("nan"))
    swings = restrict_price_action_swings(
        _price_action_swings(price_session), window_low, window_high
    )

    support_walls = _rank_current_oi_walls(
        decision_chain, spot, side="support", change_oi_by_strike=change_oi_by_strike,
    )
    resistance_walls = _rank_current_oi_walls(
        decision_chain, spot, side="resistance", change_oi_by_strike=change_oi_by_strike,
    )

    if direction == "BEARISH":
        # Every current strike where Put OI dominates Call OI is a potential
        # downside obstacle. T1 must be the nearest such wall below spot, not
        # whichever wall had the highest OI or a stale structure-level preference.
        target_walls = support_walls
        ahead = [x for x in target_walls if float(x["strike"]) < spot]
        if not ahead:
            raise ScannerError("No current OI support below spot for bearish T1.")
        t1 = float(min(
            ahead,
            key=lambda x: (float(spot) - float(x["strike"]), -float(x["strength"])),
        )["strike"])

        # T2 is the next distinct lower OI wall; PA is a fallback only when no
        # second OI wall exists.
        deeper = [x for x in support_walls if float(x["strike"]) < t1]
        pa_lows = sorted([x for x in swings.get("lows", []) if x < t1 - 0.01], reverse=True)
        oi_t2 = sorted([float(x["strike"]) for x in deeper], reverse=True)
        if oi_t2:
            t2 = oi_t2[0]
        elif pa_lows:
            t2 = pa_lows[0]
        else:
            raise ScannerError("No second price-action/OI downside objective exists for bearish trade.")
        current_resistance_matches = [x for x in resistance_walls if abs(float(x["strike"]) - safe_float(structure.resistance_1, float("nan"))) <= 0.01]
        stop_walls = current_resistance_matches[:1] if safe_float(structure.resistance_1, float("nan")) > spot and current_resistance_matches else resistance_walls
        stop_u, stop_source = _initial_structural_stop(
            spot, direction, swings, stop_walls, step,
        )
        if not all(math.isfinite(x) and window_low - 0.01 <= x <= window_high + 0.01 for x in (t1, t2, stop_u)):
            raise ScannerError(
                f"Bearish PA/OI levels outside current ATM window [{window_low:.2f},{window_high:.2f}]; "
                "entry rejected rather than using a distant/stale reference."
            )
        if not (t2 < t1 < spot < stop_u):
            raise ScannerError(
                f"Invalid bearish structural ordering: T2={t2:.2f}, T1={t1:.2f}, spot={spot:.2f}, SL={stop_u:.2f}."
            )
        t1_wall = next((x for x in target_walls if abs(float(x["strike"]) - t1) <= 0.01), {})
        t2_wall = next((x for x in deeper if abs(float(x["strike"]) - t2) <= 0.01), {})
        meta = {
            "t1_source": "OPTION_OI_SUPPORT",
            "t2_source": "OPTION_OI_SUPPORT" if t2_wall else "PRICE_ACTION_SWING_LOW",
            "sl_source": stop_source,
            "t1_oi": safe_float(t1_wall.get("oi"), 0.0),
            "t2_oi": safe_float(t2_wall.get("oi"), 0.0),
            "price_action_swing": swings,
            "t1_oi_wall_count": len(target_walls),
            "window_atm": float(window_meta["atm_strike"]),
            "window_lower_bound": float(window_low),
            "window_upper_bound": float(window_high),
        }
        return float(t1), float(t2), float(stop_u), meta

    # Symmetric rule: T1 is the nearest current Call-OI-dominant wall above spot.
    target_walls = resistance_walls
    ahead = [x for x in target_walls if float(x["strike"]) > spot]
    if not ahead:
        raise ScannerError("No current OI resistance above spot for bullish T1.")
    t1 = float(min(
        ahead,
        key=lambda x: (float(x["strike"]) - float(spot), -float(x["strength"])),
    )["strike"])

    # T2 is the next distinct higher OI wall; PA is a fallback only when no
    # second OI wall exists.
    higher = [x for x in resistance_walls if float(x["strike"]) > t1]
    pa_highs = sorted([x for x in swings.get("highs", []) if x > t1 + 0.01])
    oi_t2 = sorted([float(x["strike"]) for x in higher])
    t2 = oi_t2[0] if oi_t2 else (pa_highs[0] if pa_highs else float("nan"))
    if not math.isfinite(t2):
        raise ScannerError("No second price-action/OI upside objective exists for bullish trade.")
    current_support_matches = [x for x in support_walls if abs(float(x["strike"]) - safe_float(structure.support_1, float("nan"))) <= 0.01]
    stop_walls = current_support_matches[:1] if safe_float(structure.support_1, float("nan")) < spot and current_support_matches else support_walls
    stop_u, stop_source = _initial_structural_stop(
        spot, direction, swings, stop_walls, step,
    )
    if not all(math.isfinite(x) and window_low - 0.01 <= x <= window_high + 0.01 for x in (t1, t2, stop_u)):
        raise ScannerError(
            f"Bullish PA/OI levels outside current ATM window [{window_low:.2f},{window_high:.2f}]; "
            "entry rejected rather than using a distant/stale reference."
        )
    if not (stop_u < spot < t1 < t2):
        raise ScannerError(
            f"Invalid bullish structural ordering: SL={stop_u:.2f}, spot={spot:.2f}, T1={t1:.2f}, T2={t2:.2f}."
        )
    t1_wall = next((x for x in target_walls if abs(float(x["strike"]) - t1) <= 0.01), {})
    t2_wall = next((x for x in higher if abs(float(x["strike"]) - t2) <= 0.01), {})
    meta = {
        "t1_source": "OPTION_OI_RESISTANCE",
        "t2_source": "OPTION_OI_RESISTANCE" if t2_wall else "PRICE_ACTION_SWING_HIGH",
        "sl_source": stop_source,
        "t1_oi": safe_float(t1_wall.get("oi"), 0.0),
        "t2_oi": safe_float(t2_wall.get("oi"), 0.0),
        "price_action_swing": swings,
        "t1_oi_wall_count": len(target_walls),
        "window_atm": float(window_meta["atm_strike"]),
        "window_lower_bound": float(window_low),
        "window_upper_bound": float(window_high),
    }
    return float(t1), float(t2), float(stop_u), meta


def dynamic_oi_stop_after_t1(
    chain: list[dict[str, Any]],
    spot: float,
    direction: str,
    price_session: Optional[pd.DataFrame],
    entry_underlying: Optional[float] = None,
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
) -> tuple[float, str]:
    """Use the CURRENT opposing OI wall as the post-T1 structural stop."""
    direction = str(direction).upper()
    decision_chain, window_meta = option_chain_atm_window(chain, spot)
    window_low = safe_float(window_meta.get("lower_bound"), float("nan"))
    window_high = safe_float(window_meta.get("upper_bound"), float("nan"))
    swings = restrict_price_action_swings(
        _price_action_swings(price_session), window_low, window_high
    )

    walls = _rank_current_oi_walls(
        decision_chain, spot,
        side="resistance" if direction == "BEARISH" else "support",
        change_oi_by_strike=change_oi_by_strike,
    )
    meaningful = [x for x in walls if bool(x["meaningful"])] or walls

    def validated_stop(value: float, source: str) -> tuple[float, str]:
        if not math.isfinite(value) or not (window_low - 0.01 <= value <= window_high + 0.01):
            raise ScannerError(
                f"Dynamic {direction} stop unavailable inside current ATM window "
                f"[{window_low:.2f},{window_high:.2f}]."
            )
        if direction == "BEARISH" and value <= spot:
            raise ScannerError(f"Dynamic bearish stop {value:.2f} must be above spot {spot:.2f}.")
        if direction == "BULLISH" and value >= spot:
            raise ScannerError(f"Dynamic bullish stop {value:.2f} must be below spot {spot:.2f}.")
        return float(value), source

    if direction == "BEARISH":
        entry_u = safe_float(entry_underlying, float("nan"))
        favorable = [
            x for x in meaningful
            if float(x["strike"]) > spot
            and (not math.isfinite(entry_u) or float(x["strike"]) < entry_u)
        ]
        oi_pool = favorable or [x for x in meaningful if float(x["strike"]) > spot]
        oi_pool = sorted(
            oi_pool,
            key=lambda x: (float(x["strike"]) - float(spot), -float(x["strength"]), -abs(float(x.get("flow_change", 0.0)))),
        )
        oi_stop = float(oi_pool[0]["strike"]) if oi_pool else float("nan")
        pa_stop = min([x for x in swings.get("highs", []) if x > spot], default=float("nan"))
        if math.isfinite(oi_stop):
            return validated_stop(oi_stop, "CURRENT_OI_RESISTANCE")
        if math.isfinite(pa_stop):
            return validated_stop(pa_stop, "CURRENT_PRICE_ACTION_SWING_HIGH")
    else:
        entry_u = safe_float(entry_underlying, float("nan"))
        favorable = [
            x for x in meaningful
            if float(x["strike"]) < spot
            and (not math.isfinite(entry_u) or float(x["strike"]) > entry_u)
        ]
        oi_pool = favorable or [x for x in meaningful if float(x["strike"]) < spot]
        oi_pool = sorted(
            oi_pool,
            key=lambda x: (float(spot) - float(x["strike"]), -float(x["strength"]), -abs(float(x.get("flow_change", 0.0)))),
        )
        oi_stop = float(oi_pool[0]["strike"]) if oi_pool else float("nan")
        pa_stop = max([x for x in swings.get("lows", []) if x < spot], default=float("nan"))
        if math.isfinite(oi_stop):
            return validated_stop(oi_stop, "CURRENT_OI_SUPPORT")
        if math.isfinite(pa_stop):
            return validated_stop(pa_stop, "CURRENT_PRICE_ACTION_SWING_LOW")
    raise ScannerError("Unable to derive a dynamic post-T1 OI/price-action stop.")



def migrate_active_trade_to_v25(
    trade: dict[str, Any],
    *,
    chain: list[dict[str, Any]],
    spot: float,
    structure: StructureResult,
    price_session: Optional[pd.DataFrame],
    change_oi_by_strike: Optional[dict[float, dict[str, float]]],
) -> bool:
    """One-time migration of legacy trades to authoritative NIFTY PA/OI levels.

    Legacy V19/V21/V22/V25 trades may contain option-premium targets or a historical
    ``t1_hit`` flag generated by the old premium-target engine. V26 therefore
    re-derives T1/T2/SL from current NIFTY price action + current option OI and
    then recomputes whether the new structural T1 has actually been reached.
    """
    engine = str(trade.get("target_engine_version", "")).strip()
    if engine == OPTION_TARGET_ENGINE_VERSION:
        return False

    direction = str(trade.get("direction", structure.direction)).upper()
    if direction not in {"BULLISH", "BEARISH"}:
        logger.warning("V26 TRADE MIGRATION FAILED: invalid trade direction=%s", direction)
        return False

    if direction != structure.direction:
        direction_structure = type("TradeStructure", (), {
            "direction": direction,
            "support_1": structure.support_1,
            "support_2": structure.support_2,
            "resistance_1": structure.resistance_1,
            "resistance_2": structure.resistance_2,
            "vwap": structure.vwap,
        })()
    else:
        direction_structure = structure

    try:
        t1, t2, sl, meta = determine_structural_trade_levels(
            chain,
            float(spot),
            direction_structure,
            price_session,
            change_oi_by_strike=change_oi_by_strike,
        )
    except Exception as exc:
        logger.warning(
            "V26 TRADE MIGRATION FAILED: preserving existing trade levels | %s",
            exc,
        )
        return False

    old = (
        trade.get("target_1"),
        trade.get("target_2"),
        trade.get("stop_loss"),
        trade.get("underlying_target_1"),
        trade.get("underlying_target_2"),
        trade.get("underlying_stop"),
        trade.get("t1_hit"),
    )

    trade["target_1"] = round(float(t1), 2)
    trade["target_2"] = round(float(t2), 2)
    trade["stop_loss"] = round(float(sl), 2)
    trade["underlying_target_1"] = round(float(t1), 2)
    trade["underlying_target_2"] = round(float(t2), 2)
    trade["underlying_stop"] = round(float(sl), 2)

    structural_t1_hit = (
        float(spot) <= float(t1)
        if direction == "BEARISH"
        else float(spot) >= float(t1)
    )
    trade["t1_hit"] = bool(structural_t1_hit)
    trade["t1_notified"] = False
    trade["target_engine_version"] = OPTION_TARGET_ENGINE_VERSION
    trade.pop("post_t1_dynamic_stop", None)
    trade.pop("post_t1_dynamic_stop_source", None)
    trade.pop("post_t1_dynamic_stop_updated_at", None)
    trade["t1_hit_at"] = now_ist().isoformat() if structural_t1_hit else ""

    logger.info(
        "V28 TRADE MIGRATION: %s | old T1=%s T2=%s SL=%s old_uT1=%s old_uT2=%s old_uSL=%s old_t1_hit=%s -> "
        "PA/OI T1=%.2f T2=%.2f SL=%.2f t1_hit=%s | spot=%.2f | sources=%s/%s/%s",
        trade.get("trading_symbol", ""),
        old[0], old[1], old[2], old[3], old[4], old[5], old[6],
        t1, t2, sl, structural_t1_hit, spot,
        meta.get("t1_source", ""), meta.get("t2_source", ""), meta.get("sl_source", ""),
    )
    return True


# =============================================================================
# STATE
# =============================================================================

def load_state() -> dict[str, Any]:
    state_path = STATE_FILE
    legacy_cwd_path = Path.cwd() / "state" / "market_state.json"
    if (
        not state_path.exists()
        and not _state_file_override
        and legacy_cwd_path.exists()
        and legacy_cwd_path.resolve() != state_path.resolve()
    ):
        state_path = legacy_cwd_path
        logger.warning(
            "STATE MIGRATION: new script-anchored state file is absent; loading prior working-directory state from %s.",
            state_path.resolve(),
        )

    if not state_path.exists():
        logger.info("STATE LOAD: no previous state found at %s; OI velocity will warm up from fresh snapshots.", STATE_FILE)
        return {}

    try:
        with state_path.open("r", encoding="utf-8") as fh:
            data = json.load(fh)
        if not isinstance(data, dict):
            logger.warning("State file did not contain a JSON object: %s", state_path.resolve())
            return {}
        if isinstance(data.get("market_snapshot"), dict) and data["market_snapshot"]:
            data["market_snapshot"] = MarketSnapshot.from_mapping(data["market_snapshot"]).to_mapping()
        if isinstance(data.get("active_trade"), dict) and data["active_trade"]:
            data["active_trade"] = ActiveTradeState.from_mapping(data["active_trade"]).to_mapping()
        logger.info(
            "STATE LOADED: source=%s option_oi_history_snapshots=%d legacy_oi_snapshot=%s active_trade=%s",
            state_path.resolve(),
            len(data.get("option_oi_history", [])) if isinstance(data.get("option_oi_history"), list) else 0,
            isinstance(data.get("option_oi_snapshot"), dict),
            bool(isinstance(data.get("active_trade"), dict) and str(data["active_trade"].get("status", "")).upper() == "ACTIVE"),
        )
        if state_path.resolve() != STATE_FILE.resolve():
            # Migrate once to the new stable path while retaining every state key.
            original_path = STATE_FILE
            try:
                save_state(data)
                logger.info("STATE MIGRATION COMPLETE: %s -> %s", state_path.resolve(), original_path.resolve())
            except Exception as exc:
                logger.warning("STATE MIGRATION COPY FAILED; loaded legacy state in memory: %s", exc)
        return data
    except (OSError, json.JSONDecodeError, TypeError, ValueError) as exc:
        logger.error("State load failed from %s: %s", state_path.resolve(), exc)
        return {}


def save_state(state: dict[str, Any]) -> None:
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    tmp = STATE_FILE.with_suffix(".tmp")

    with tmp.open("w", encoding="utf-8") as fh:
        json.dump(state, fh, indent=2, ensure_ascii=False)

    tmp.replace(STATE_FILE)


def reset_intraday_memory_if_needed(state: dict[str, Any], today_iso: str) -> tuple[bool, str]:
    """Reset directional memory on session/version changes without discarding compatible same-day OI history."""
    snapshot = state.get("market_snapshot")
    snapshot_ts = str(snapshot.get("timestamp", ""))[:10] if isinstance(snapshot, dict) else ""
    stored_version = str(state.get("scanner_version", ""))
    new_session = bool(snapshot_ts and snapshot_ts != today_iso)
    version_changed = bool(stored_version and stored_version != SCANNER_VERSION)
    if not (new_session or version_changed):
        state["scanner_version"] = SCANNER_VERSION
        return False, ""

    state["market_history"] = []
    state["market_snapshot"] = {}
    state["persistent_direction"] = None
    state["continuation_phase"] = ""
    state["continuation_count"] = 0
    state["continuation_last_bar"] = ""
    state["scanner_version"] = SCANNER_VERSION
    state.pop("last_signal", None)
    state.pop("last_signal_hash", None)
    state.pop("last_signal_timestamp", None)

    # OI velocity is intraday and expiry-specific. Preserve it on a code-version
    # upgrade during the SAME trading date; the history normalizer validates each
    # timestamp/date/expiry and contract overlap before allowing it into a baseline.
    # A new trading date must start with a clean OI ring and legacy snapshot.
    if new_session:
        state.pop("option_oi_snapshot", None)
        state.pop("option_oi_history", None)
        reason = "NEW_TRADING_SESSION"
    else:
        reason = "SCANNER_VERSION_CHANGE_PRESERVED_OI_HISTORY"
    return True, reason


def active_trade_from_state(
    state: dict[str, Any],
) -> Optional[dict[str, Any]]:
    raw_trade = state.get("active_trade")
    if not isinstance(raw_trade, dict):
        return None
    model = ActiveTradeState.from_mapping(raw_trade)
    trade = model.to_mapping()
    if model.status.upper() != "ACTIVE":
        return None
    required = {"instrument_key", "trading_symbol", "direction", "entry", "target_1", "target_2", "stop_loss"}
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
    """Display NIFTY structural levels; option exits use the live option LTP."""
    return (
        f"1. Market State: [{signal.market_state}]\n"
        f"2. Bias: [{signal.bias}]\n"
        f"3. Entry Trigger: [{signal.entry_trigger}]\n"
        f"4. Targets:\n"
        f"   - T1: NIFTY {signal.underlying_target_1:.2f}\n"
        f"   - T2: NIFTY {signal.underlying_target_2:.2f}\n"
        f"5. Stop Loss: NIFTY {signal.underlying_stop:.2f}\n"
        f"   Option exits at the live option LTP when the NIFTY structural level is reached.\n"
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
<h2>NIFTY Predictive {html.escape(signal.direction)} Signal</h2>
<table border="1" cellpadding="6" cellspacing="0">
<tr><td><b>Time</b></td><td>{html.escape(signal.timestamp)}</td></tr>
<tr><td><b>Market State</b></td><td>{html.escape(signal.market_state)}</td></tr>
<tr><td><b>Regime</b></td><td>{html.escape(signal.regime)}</td></tr>
<tr><td><b>Entry Trigger</b></td><td>{html.escape(signal.entry_trigger)}</td></tr>
<tr><td><b>Invalidation</b></td><td>{html.escape(signal.invalidation_rule)}</td></tr>
<tr><td><b>Confidence</b></td><td>{signal.confidence:.1f}%</td></tr>
<tr><td><b>Spot</b></td><td>{signal.spot:.2f}</td></tr>
<tr><td><b>Futures Price/OI Scenario</b></td><td>{html.escape(signal.futures_state)}</td></tr>
<tr><td><b>Option</b></td><td>{html.escape(signal.trading_symbol)}</td></tr>
<tr><td><b>Strike</b></td><td>{signal.strike:.0f} {signal.option_type}</td></tr>
<tr><td><b>Entry</b></td><td>₹{signal.entry:.2f}</td></tr>
<tr><td><b>NIFTY Target 1</b></td><td>{signal.underlying_target_1:.2f}</td></tr>
<tr><td><b>NIFTY Target 2</b></td><td>{signal.underlying_target_2:.2f}</td></tr>
<tr><td><b>NIFTY Structural SL</b></td><td>{signal.underlying_stop:.2f}</td></tr>
<tr><td><b>Option Exit at T1</b></td><td>Live option LTP when NIFTY T1 is reached</td></tr>
<tr><td><b>Option Exit at T2</b></td><td>Live option LTP when NIFTY T2 is reached</td></tr>
<tr><td><b>Structural Exit</b></td><td>Live option LTP when NIFTY SL is breached</td></tr>
<tr><td><b>Delta</b></td><td>{signal.delta:.4f}</td></tr>
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

def _trade_entry_bar_utc(trade: dict[str, Any]) -> Optional[pd.Timestamp]:
    """Return the first safe 1m bar boundary after the actual option entry.

    The entry timestamp can fall inside a 1m candle. That candle contains price
    action that happened before the option was purchased, so it must never be
    allowed to trigger a post-entry stop.
    """
    raw = str(trade.get("opened_at") or "").strip()
    if not raw:
        return None
    try:
        ts = pd.Timestamp(raw)
        if ts.tzinfo is None:
            ts = ts.tz_localize(IST)
        else:
            ts = ts.tz_convert(IST)
        return ts.tz_convert("UTC").floor("min") + pd.Timedelta(minutes=1)
    except Exception:
        return None


def _prepare_active_trade_1m_window(
    trade: dict[str, Any],
    option_1m: Optional[pd.DataFrame],
) -> Optional[pd.DataFrame]:
    """Keep only post-entry/new 1m bars and never replay old candles.

    The latest bar is retained on every scan because its OHLC can still evolve.
    Older bars are evaluated only once via ``intrabar_last_checked_at``.
    """
    if option_1m is None or option_1m.empty:
        return None

    work = option_1m.copy().sort_values("timestamp")
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    for column in ("high", "low"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    work = work.dropna(subset=["timestamp", "high", "low"])
    if work.empty:
        return None

    entry_bar = _trade_entry_bar_utc(trade)
    if entry_bar is not None:
        work = work[work["timestamp"] >= entry_bar]

    last_checked_raw = str(trade.get("intrabar_last_checked_at") or "").strip()
    if last_checked_raw:
        try:
            last_checked = pd.Timestamp(last_checked_raw)
            if last_checked.tzinfo is None:
                last_checked = last_checked.tz_localize("UTC")
            else:
                last_checked = last_checked.tz_convert("UTC")
            current_bar_ts = (
                pd.Timestamp(now_ist()).tz_convert("UTC").floor("min")
            )
            # Re-evaluate only the currently-forming 1m bar. A completed bar
            # must never be replayed after the stop has been ratcheted upward,
            # otherwise an old low can falsely trigger the new stop.
            work = work[
                (work["timestamp"] > last_checked)
                | (work["timestamp"] >= current_bar_ts)
            ]
        except Exception:
            pass

    if work.empty:
        return None
    return work.tail(max(ACTIVE_TRADE_INTRABAR_LOOKBACK, 1)).copy()


def apply_dynamic_oi_stop_to_trade(
    trade: dict[str, Any],
    *,
    chain: list[dict[str, Any]],
    spot: float,
    price_session: Optional[pd.DataFrame],
    latest_bar: str = "",
    change_oi_by_strike: Optional[dict[float, dict[str, float]]] = None,
) -> tuple[bool, float, str]:
    """Recalculate the post-T1 SL from CURRENT opposing OI.

    The pre-T1 structural SL is deliberately ignored after T1. Once post-T1 is
    active, only the current OI-derived stop is authoritative. A previous
    *post-T1 OI stop* may ratchet favorably so the scanner never gives back a
    previously secured structural level.
    """
    direction = str(trade.get("direction", "")).upper()
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("Dynamic OI stop requires BULLISH or BEARISH direction.")

    dynamic_stop, dynamic_source = dynamic_oi_stop_after_t1(
        chain,
        float(spot),
        direction,
        price_session,
        entry_underlying=safe_float(trade.get("entry_underlying"), float("nan")),
        change_oi_by_strike=change_oi_by_strike,
    )

    prior_post_t1 = safe_float(trade.get("post_t1_dynamic_stop"), float("nan"))
    if math.isfinite(prior_post_t1):
        effective_stop = (
            min(prior_post_t1, dynamic_stop) if direction == "BEARISH"
            else max(prior_post_t1, dynamic_stop)
        )
    else:
        effective_stop = dynamic_stop

    changed = (not math.isfinite(prior_post_t1)) or abs(effective_stop - prior_post_t1) >= 0.01
    trade["post_t1_dynamic_stop"] = round(float(effective_stop), 2)
    trade["post_t1_dynamic_stop_source"] = dynamic_source
    trade["post_t1_dynamic_stop_updated_at"] = now_ist().isoformat()
    trade["underlying_stop"] = round(float(effective_stop), 2)
    trade["stop_loss"] = round(float(effective_stop), 2)
    if changed and latest_bar:
        trade["underlying_stop_armed_bar"] = str(latest_bar)
    return changed, float(effective_stop), dynamic_source


def _as_ist_timestamp(value: Any) -> Optional[pd.Timestamp]:
    raw = str(value or "").strip()
    if not raw:
        return None
    if raw.upper().endswith(" IST"):
        raw = raw[:-4].strip()
    try:
        stamp = pd.Timestamp(raw)
        if stamp.tzinfo is None:
            stamp = stamp.tz_localize(IST)
        else:
            stamp = stamp.tz_convert(IST)
        return stamp
    except Exception:
        return None


def stagnation_exit_trigger(
    trade: dict[str, Any],
    price_5m: Optional[pd.DataFrame],
    *,
    market_structure: Optional[StructureResult] = None,
) -> tuple[bool, str]:
    """Detect stagnation only when a tight range is not showing aligned continuation.

    Three completed post-entry 5m candles must be consecutive and have a combined
    high-low range <= STAGNATION_RANGE_PCT. Before triggering, the guard checks
    whether the trade direction, live index VWAP side, Change-OI and observed price
    progress still agree. A confirmed aligned move suppresses this time-decay exit.
    """
    if price_5m is None or price_5m.empty:
        return False, "5-minute candles unavailable"
    opened_at = _as_ist_timestamp(trade.get("opened_at"))
    if opened_at is None:
        return False, "trade opening timestamp unavailable"
    bars = filter_completed_candles(price_5m, 5)
    if not bars.empty:
        bars = (bars.sort_values("timestamp")
                .drop_duplicates("timestamp", keep="last")
                .reset_index(drop=True))
    if bars.empty:
        return False, "no completed 5-minute candles"
    bar_start_utc = pd.to_datetime(bars["timestamp"], utc=True, errors="coerce")
    opened_utc = opened_at.tz_convert("UTC")
    # Every counted candle must start at or after entry. A candle that began
    # before entry is excluded even if its close is after the entry timestamp.
    bars = bars.loc[bar_start_utc >= opened_utc].copy()
    required_bars = max(STAGNATION_REQUIRED_BARS, 3)
    if len(bars) < required_bars:
        return False, f"only {len(bars)} eligible completed 5m bars"
    bars = bars.tail(required_bars)
    bar_stamps = pd.to_datetime(bars["timestamp"], utc=True, errors="coerce")
    spacing = bar_stamps.diff().dropna()
    if len(spacing) != len(bars) - 1 or not bool((spacing == pd.Timedelta(minutes=5)).all()):
        return False, "last eligible candles are not consecutive 5-minute bars"
    high = pd.to_numeric(bars["high"], errors="coerce")
    low = pd.to_numeric(bars["low"], errors="coerce")
    close = pd.to_numeric(bars["close"], errors="coerce")
    open_values = pd.to_numeric(bars["open"], errors="coerce") if "open" in bars.columns else close
    if (high.isna().any() or low.isna().any() or close.isna().any()
            or open_values.isna().any() or float(close.mean()) <= 0):
        return False, "5-minute OHLC data invalid"
    range_pct = float((high.max() - low.min()) / close.mean())
    timestamps = pd.to_datetime(bars["timestamp"], utc=True, errors="coerce").dt.tz_convert(IST)
    if range_pct > STAGNATION_RANGE_PCT:
        return False, f"three-bar range {range_pct:.4%} exceeds {STAGNATION_RANGE_PCT:.2%}"

    direction = str(trade.get("direction", "")).upper()
    sign = 1.0 if direction == "BULLISH" else -1.0 if direction == "BEARISH" else 0.0
    closes = close.to_numpy(dtype=float)
    first_close = float(closes[0])
    last_close = float(closes[-1])
    favorable_progress_pct = sign * (last_close - first_close) / first_close if first_close > 0 else 0.0
    close_changes = np.diff(closes)
    favorable_close_steps = int(np.sum(sign * close_changes > 0.0)) if sign else 0
    progress_confirms = (
        favorable_progress_pct >= STAGNATION_MIN_FAVORABLE_PROGRESS_PCT
        or favorable_close_steps == len(close_changes)
    )

    if market_structure is not None and sign != 0.0 and direction in {"BULLISH", "BEARISH"}:
        current_direction = str(getattr(market_structure, "direction", "NEUTRAL")).upper()
        components = getattr(market_structure, "components", {})
        components = components if isinstance(components, dict) else {}
        vwap_side = safe_float(components.get("structure_vwap"), 0.0)
        vwap_value = safe_float(getattr(market_structure, "vwap", float("nan")), float("nan"))
        flow_value = safe_float(components.get("structure_change_oi"), float("nan"))
        flow_conflict = safe_float(components.get("structure_change_oi_conflict"), 1.0)
        latest_close = float(close.iloc[-1])
        vwap_aligned = bool(
            sign * vwap_side > 0.0 and math.isfinite(vwap_value)
            and sign * (latest_close - vwap_value) > 0.0
        )
        coi_aligned = bool(
            math.isfinite(flow_value) and sign * flow_value >= STRUCTURE_CHANGE_OI_CONFIRM
            and flow_conflict < 0.5
        )
        structure_aligned = current_direction == direction and vwap_aligned and coi_aligned
        if structure_aligned and progress_confirms:
            return False, (
                f"STAGNATION_SUPPRESSED_ALIGNED_CONTINUATION direction={direction}; "
                f"range={range_pct:.4%}<={STAGNATION_RANGE_PCT:.2%}; "
                f"favorable_progress={favorable_progress_pct:.4%}; "
                f"favorable_close_steps={favorable_close_steps}/{len(close_changes)}; "
                f"VWAP={vwap_value:.2f}; effective_COI={flow_value:+.3f}; "
                f"from={timestamps.iloc[0].strftime('%H:%M')} "
                f"to={(timestamps.iloc[-1] + pd.Timedelta(minutes=5)).strftime('%H:%M')} IST"
            )

    return True, (
        f"3_CONSECUTIVE_COMPLETED_5M_BARS_STAGNANT_RANGE={range_pct:.4%}<="
        f"{STAGNATION_RANGE_PCT:.2%}; direction={direction or 'UNKNOWN'}; "
        f"favorable_progress={favorable_progress_pct:.4%}; "
        f"aligned_structure={bool(market_structure is not None and sign != 0.0 and current_direction == direction and vwap_aligned and coi_aligned) if market_structure is not None and sign != 0.0 else False}; "
        f"from={timestamps.iloc[0].strftime('%H:%M')} "
        f"to={(timestamps.iloc[-1] + pd.Timedelta(minutes=5)).strftime('%H:%M')} IST"
    )


def force_close_active_trade_at_cutoff(state: dict[str, Any], reason: str = "TIME_CUTOFF_15_15") -> bool:
    """Persist/email an exit decision at cutoff. This scanner does not place broker orders."""
    trade = active_trade_from_state(state)
    if trade is None:
        return True
    try:
        exit_ltp = extract_ltp(get_quote(str(trade["instrument_key"])))
    except ScannerError as exc:
        logger.error("CUTOFF EXIT PENDING: cannot obtain live option LTP; trade retained in state: %s", exc)
        return False
    closed = dict(trade)
    closed.update({
        "status": "CLOSED",
        "outcome": reason,
        "exit_ltp": round(exit_ltp, 2),
        "closed_at": now_ist().isoformat(),
        "exit_reason": reason,
        "exit_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
    })
    state["active_trade"] = None
    state["last_completed_trade"] = closed
    save_state(state)
    send_email(
        f"NIFTY FORCED EXIT - {trade.get('trading_symbol', 'Active position')}",
        f"<p>Intraday cutoff exit signal: {html.escape(reason)}.</p>"
        f"<p>Option: {html.escape(str(trade.get('trading_symbol', '')))}<br>"
        f"Entry: ₹{safe_float(trade.get('entry')):.2f}<br>"
        f"Latest option LTP: ₹{exit_ltp:.2f}<br>"
        f"Time: {html.escape(now_ist().strftime('%Y-%m-%d %H:%M:%S IST'))}</p>"
        "<p>This scanner records exit decisions and sends notifications; it does not submit broker orders.</p>",
    )
    logger.warning("TRADE CLOSED: %s outcome=%s exit_option=%.2f", trade.get("trading_symbol", ""), reason, exit_ltp)
    return True


def monitor_active_trade(
    state: dict[str, Any],
    structure: StructureResult,
    *,
    chain: Optional[list[dict[str, Any]]] = None,
    price_session: Optional[pd.DataFrame] = None,
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
    underlying_t1 = safe_float(trade.get("underlying_target_1"), float("nan"))
    underlying_t2 = safe_float(trade.get("underlying_target_2"), float("nan"))
    underlying_stop = safe_float(trade.get("underlying_stop"), float("nan"))
    t1_hit = bool(trade.get("t1_hit", False))
    intrabar_outcome = None
    intrabar_exit_reference = None
    intrabar_reason = "DISABLED"

    # Current NIFTY spot is the authoritative trigger for structural exits.
    snapshot_for_trade = state.get("market_snapshot") if isinstance(state.get("market_snapshot"), dict) else {}
    spot_now = safe_float(snapshot_for_trade.get("spot"), float("nan"))
    if not math.isfinite(spot_now) or spot_now <= 0:
        try:
            spot_now = extract_ltp(get_quote(NIFTY_KEY))
        except ScannerError:
            spot_now = float("nan")

    underlying_1m = None
    if ACTIVE_TRADE_INTRABAR_MONITOR:
        try:
            underlying_1m_raw = get_intraday_candles(NIFTY_KEY, 1, strict=False)
            underlying_1m = _prepare_active_trade_1m_window(trade, underlying_1m_raw)
        except Exception as exc:
            intrabar_reason = f"1M_MONITOR_ERROR:{exc}"
            logger.info("Active trade NIFTY 1m monitor unavailable: %s", exc)

    # A three-candle stagnation breaker protects open option buys from prolonged theta decay.
    try:
        candles_5m = get_intraday_candles(NIFTY_KEY, 5, strict=False)
        stagnant, stagnation_reason = stagnation_exit_trigger(
            trade, candles_5m, market_structure=structure
        )
        logger.info("STAGNATION EXIT CHECK: %s trigger=%s reason=%s", trade.get("trading_symbol", ""), stagnant, stagnation_reason)
        if stagnant:
            closed = dict(trade)
            closed.update({
                "status": "CLOSED", "outcome": "STAGNATION_EXIT",
                "exit_ltp": round(ltp, 2), "closed_at": now_ist().isoformat(),
                "exit_reason": stagnation_reason,
                "exit_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
            })
            state["active_trade"] = None
            state["last_completed_trade"] = closed
            save_state(state)
            send_email(
                f"NIFTY STAGNATION EXIT - {trade['trading_symbol']}",
                f"<p>Intraday trade closed by the stagnation breaker.</p><p>Option: {html.escape(str(trade['trading_symbol']))}<br>"
                f"Entry: ₹{entry if 'entry' in locals() else safe_float(trade.get('entry')):.2f}<br>"
                f"Current option LTP: ₹{ltp:.2f}<br>Reason: {html.escape(stagnation_reason)}</p>"
                "<p>This scanner records exit decisions and sends notifications; it does not submit broker orders.</p>",
            )
            logger.warning("TRADE CLOSED: %s outcome=STAGNATION_EXIT exit_option=%.2f reason=%s", trade.get("trading_symbol", ""), ltp, stagnation_reason)
            return "CLOSED"
    except Exception as exc:
        logger.info("Stagnation exit check unavailable; continuing with structural exits: %s", exc)

    # First detect T1 from the authoritative NIFTY structural level. The current
    # OI stop is recalculated immediately on the same scan after T1 is reached.
    if not t1_hit and math.isfinite(spot_now) and math.isfinite(underlying_t1):
        direction = str(trade.get("direction", "")).upper()
        t1_hit = (
            spot_now <= underlying_t1 if direction == "BEARISH"
            else spot_now >= underlying_t1
        )
        if t1_hit:
            trade["t1_hit_at"] = now_ist().isoformat()
    if not t1_hit and underlying_1m is not None and not underlying_1m.empty:
        probe_trade = dict(trade)
        probe_trade["t1_hit"] = False
        probe_trade["underlying_stop"] = float("nan")
        probe_trade["underlying_target_2"] = float("nan")
        probe_outcome, probe_ref, probe_reason = _active_trade_intrabar_exit(
            probe_trade,
            underlying_1m=underlying_1m,
            underlying_3m=filter_completed_candles(price_session, 3) if price_session is not None else None,
        )
        if probe_outcome == "T1_HIT":
            t1_hit = True
            trade["t1_hit"] = True
            _set_t1_activation_from_intrabar_reason(trade, probe_reason)
            intrabar_exit_reference = probe_ref
            intrabar_reason = probe_reason

    if t1_hit:
        trade["t1_hit"] = True
        trade.setdefault("t1_hit_at", now_ist().isoformat())

    # Once T1 is reached, CURRENT opposing OI becomes the authoritative dynamic SL.
    if t1_hit and chain and price_session is not None and math.isfinite(spot_now):
        try:
            completed_3m = filter_completed_candles(price_session, 3) if price_session is not None else pd.DataFrame()
            latest_bar = str(completed_3m["timestamp"].iloc[-1]) if not completed_3m.empty else ""
            changed, effective_stop, dynamic_source = apply_dynamic_oi_stop_to_trade(
                trade,
                chain=chain,
                spot=spot_now,
                price_session=price_session,
                latest_bar=latest_bar,
                change_oi_by_strike=(state.get("option_flow_by_strike") if isinstance(state.get("option_flow_by_strike"), dict) else None),
            )
            underlying_stop = effective_stop
            logger.info(
                "DYNAMIC T1 SL: option=%s T1_NIFTY=%.2f current_spot=%.2f source=%s "
                "effective_SL_NIFTY=%.2f changed=%s",
                trade["trading_symbol"],
                underlying_t1,
                spot_now,
                dynamic_source,
                effective_stop,
                changed,
            )
        except ScannerError as exc:
            logger.info("Dynamic post-T1 OI stop unavailable: %s", exc)

    # Now evaluate the effective structural stop/T2. Re-run the NIFTY 1m path
    # after the dynamic stop update so a same-cycle adverse move can be caught.
    if ACTIVE_TRADE_INTRABAR_MONITOR and underlying_1m is not None and not underlying_1m.empty:
        try:
            (
                intrabar_outcome,
                intrabar_exit_reference,
                intrabar_reason,
            ) = _active_trade_intrabar_exit(
                trade,
                underlying_1m=underlying_1m,
                underlying_3m=filter_completed_candles(price_session, 3) if price_session is not None else None,
            )
            trade["intrabar_last_checked_at"] = underlying_1m["timestamp"].max().isoformat()
            logger.info(
                "ACTIVE TRADE STRUCTURE MONITOR: %s outcome=%s reference=%s reason=%s",
                trade["trading_symbol"],
                intrabar_outcome or "NONE",
                f"{intrabar_exit_reference:.2f}" if intrabar_exit_reference is not None else "-",
                intrabar_reason,
            )
        except Exception as exc:
            intrabar_reason = f"1M_MONITOR_ERROR:{exc}"
            logger.info("Active trade NIFTY 1m monitor unavailable: %s", exc)

    # Quote-level structural trigger is a backup when the intrabar path had no bar breach.
    completed_3m_for_quote = (
        filter_completed_candles(price_session, 3)
        if price_session is not None else pd.DataFrame()
    )
    if math.isfinite(spot_now):
        if not t1_hit and math.isfinite(underlying_t1):
            direction = str(trade.get("direction", "")).upper()
            t1_hit = (spot_now <= underlying_t1 if direction == "BEARISH" else spot_now >= underlying_t1)
        direction = str(trade.get("direction", "")).upper()
        t2_reached = (
            spot_now <= underlying_t2 if direction == "BEARISH"
            else spot_now >= underlying_t2
        ) if math.isfinite(underlying_t2) else False
        stop_reached = (
            (spot_now >= underlying_stop if direction == "BEARISH" else spot_now <= underlying_stop)
            and _underlying_stop_confirmation_ready(trade, completed_3m_for_quote)
        ) if math.isfinite(underlying_stop) else False
    else:
        t2_reached = False
        stop_reached = False

    if intrabar_outcome == "STOP_LOSS" or stop_reached:
        outcome = "STOP_LOSS"
    elif intrabar_outcome == "TARGET_2" or t2_reached:
        outcome = "TARGET_2"
    else:
        outcome = ""

    if outcome:
        closed = dict(trade)
        closed.update({
            "status": "CLOSED",
            "outcome": outcome,
            "exit_ltp": round(ltp, 2),
            "closed_at": now_ist().isoformat(),
            "exit_reason": intrabar_reason if intrabar_outcome else "NIFTY_STRUCTURAL_LEVEL",
            "exit_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
        })
        state["active_trade"] = None
        state["last_completed_trade"] = closed
        save_state(state)

        send_email(
            f"NIFTY TRADE {outcome} - {trade['trading_symbol']}",
            (
                f"<p>{html.escape(str(trade['direction']))} trade closed on the NIFTY structural level.</p>"
                f"<p>Option: {html.escape(str(trade['trading_symbol']))}<br>"
                f"Entry: ₹{entry:.2f}<br>"
                f"Live option exit: ₹{ltp:.2f}<br>"
                f"NIFTY T1: {underlying_t1:.2f}<br>"
                f"NIFTY T2: {underlying_t2:.2f}<br>"
                f"NIFTY SL: {underlying_stop:.2f}<br>"
                f"Outcome: {outcome}</p>"
            ),
        )
        logger.info(
            "TRADE CLOSED: %s outcome=%s exit_option=%.2f trigger_nifty=%.2f",
            trade["trading_symbol"], outcome, ltp, spot_now,
        )
        return "CLOSED"

    if t1_hit and not bool(trade.get("t1_notified", False)):
        trade["t1_hit"] = True
        trade["t1_notified"] = True
        send_email(
            f"NIFTY T1 HIT - {trade['trading_symbol']}",
            (
                f"<p>NIFTY T1 reached. Trade remains active toward T2.</p>"
                f"<p>Option: {html.escape(str(trade['trading_symbol']))}<br>"
                f"Entry option LTP: ₹{entry:.2f}<br>"
                f"Current option LTP: ₹{ltp:.2f}<br>"
                f"NIFTY T1: {underlying_t1:.2f}<br>"
                f"Dynamic OI SL: {safe_float(trade.get('underlying_stop')):.2f}</p>"
            ),
        )
    active_direction = str(trade.get("direction", "")).upper()
    last_opposite = int(trade.get("reversal_confirmations", 0) or 0)

    # Enforce the invalidation rule promised by the signal itself. The structural
    # engine remains the entry-direction authority; this check only protects an
    # already-open position when the confirmed continuous structure is lost.
    expected_phase = (
        "CONTINUOUS_BULLISH" if active_direction == "BULLISH"
        else "CONTINUOUS_BEARISH"
    )
    snapshot = state.get("market_snapshot") if isinstance(state.get("market_snapshot"), dict) else {}
    spot_now = safe_float(snapshot.get("spot"), spot_now if math.isfinite(spot_now) else 0.0)
    vwap_now = safe_float(snapshot.get("vwap"), float("nan"))

    vwap_reclaimed_against_trade = False
    if spot_now > 0 and math.isfinite(vwap_now):
        vwap_reclaimed_against_trade = (
            active_direction == "BEARISH" and spot_now > vwap_now
        ) or (
            active_direction == "BULLISH" and spot_now < vwap_now
        )

    trade_intensity = str(trade.get("market_intensity", "NORMAL")).upper()
    snapshot_intensity = str(snapshot.get("market_intensity", "UNKNOWN")).upper()
    snapshot_regime_direction = str(snapshot.get("regime_direction", "NEUTRAL")).upper()
    if trade_intensity == "EXHAUSTION":
        # VWAP opposition is expected at the start of a counter-trend exhaustion
        # scalp. Do not immediately invalidate it merely because the original
        # trend phase is still present; its structural stop/T2 remains authoritative.
        vwap_reclaimed_against_trade = False
        exhaustion_confirmed = bool(
            snapshot_intensity == "EXHAUSTION"
            and snapshot_regime_direction == active_direction
            and snapshot.get("reversal_price_confirmed", False)
        )
        opposing_trend_reasserted = (
            structure.market_phase == ("CONTINUOUS_BEARISH" if active_direction == "BULLISH" else "CONTINUOUS_BULLISH")
            and structure.entry_confirmed
        )
        market_alignment_failure = bool(opposing_trend_reasserted and not exhaustion_confirmed)
        expected_phase = f"EXHAUSTION_{active_direction}"
        current_phase_for_log = f"{snapshot_intensity}_{snapshot_regime_direction}"
    else:
        same_continuous_phase = structure.market_phase == expected_phase
        market_alignment_failure = not same_continuous_phase or vwap_reclaimed_against_trade
        current_phase_for_log = structure.market_phase

    alignment_failures = int(trade.get("market_alignment_failures", 0) or 0)
    if market_alignment_failure:
        alignment_failures += 1
    else:
        alignment_failures = 0
    trade["market_alignment_failures"] = alignment_failures

    logger.info(
        "MARKET INVALIDATION CHECK: active=%s expected_phase=%s current_phase=%s "
        "vwap_reclaimed=%s failures=%d/%d",
        active_direction,
        expected_phase,
        current_phase_for_log,
        vwap_reclaimed_against_trade,
        alignment_failures,
        max(MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED, 1),
    )

    if alignment_failures >= max(MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED, 1):
        closed = dict(trade)
        closed.update(
            {
                "status": "CLOSED",
                "outcome": "MARKET_ALIGNMENT_INVALIDATION",
                "exit_ltp": round(ltp, 2),
                "closed_at": now_ist().isoformat(),
                "exit_reason": (
                    "continuous market phase lost and/or NIFTY reclaimed VWAP"
                ),
                "exit_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
            }
        )
        state["active_trade"] = None
        state["last_completed_trade"] = closed
        save_state(state)

        send_email(
            f"NIFTY MARKET INVALIDATION - {trade['trading_symbol']}",
            (
                f"<p>Trade exited because the confirmed market alignment was lost.</p>"
                f"<p>Active direction: {html.escape(active_direction)}<br>"
                f"Current phase: {html.escape(str(structure.market_phase))}<br>"
                f"NIFTY spot: {spot_now:.2f}<br>"
                f"NIFTY VWAP: {vwap_now:.2f}<br>"
                f"Exit: ₹{ltp:.2f}</p>"
            ),
        )
        logger.info(
            "TRADE CLOSED: %s outcome=MARKET_ALIGNMENT_INVALIDATION exit=%.2f",
            trade["trading_symbol"],
            ltp,
        )
        return "CLOSED"

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

    state["active_trade"] = trade
    save_state(state)

    logger.info(
        "ACTIVE TRADE: %s option_LTP=%.2f NIFTY_T1=%.2f NIFTY_T2=%.2f NIFTY_SL=%.2f "
        "market=%s invalidations=%d/%d",
        trade["trading_symbol"],
        ltp,
        safe_float(trade.get("underlying_target_1"), float("nan")),
        safe_float(trade.get("underlying_target_2"), float("nan")),
        safe_float(trade.get("underlying_stop"), float("nan")),
        structure.direction,
        last_opposite,
        MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED,
    )
    return "ACTIVE"


# =============================================================================
# SCAN
# =============================================================================



def update_continuation_persistence(
    state: dict[str, Any],
    market_phase: str,
    latest_completed_3m_bar: Optional[Any] = None,
    *,
    required_confirmations: Optional[int] = None,
) -> tuple[bool, int]:
    """Track continuous or explicitly confirmed exhaustion setups on distinct 3m bars."""
    phase = str(market_phase or "").upper()
    if phase not in {"CONTINUOUS_BULLISH", "CONTINUOUS_BEARISH", "EXHAUSTION_BULLISH", "EXHAUSTION_BEARISH"}:
        state["continuation_phase"] = ""
        state["continuation_count"] = 0
        state["continuation_last_bar"] = ""
        logger.info(
            "CONTINUATION PERSISTENCE: phase=%s reset=1",
            phase or "NONE",
        )
        return False, 0

    previous_phase = str(state.get("continuation_phase", "")).upper()
    previous_count = int(state.get("continuation_count", 0) or 0)
    current_bar = str(latest_completed_3m_bar or "")

    if previous_phase != phase:
        count = 1
    elif current_bar and current_bar != str(state.get("continuation_last_bar", "")):
        count = previous_count + 1
    elif current_bar:
        # Same completed candle: do not manufacture a second confirmation.
        count = previous_count
    else:
        # When the timestamp is unavailable, remain conservative and do not
        # count the same state repeatedly.
        count = max(previous_count, 1)

    state["continuation_phase"] = phase
    state["continuation_count"] = count
    state["continuation_last_bar"] = current_bar
    required = max(int(required_confirmations or CONTINUATION_CONFIRMATIONS_REQUIRED), 1)
    ready = count >= required

    logger.info(
        "CONTINUATION PERSISTENCE: phase=%s count=%d/%d last_3m_bar=%s ready=%s",
        phase,
        count,
        required,
        current_bar or "UNKNOWN",
        ready,
    )
    return ready, count



def observe_confirmed_structure_persistence(
    state: dict[str, Any],
    structure: StructureResult,
    latest_completed_3m_bar: Optional[Any],
) -> tuple[bool, int]:
    """Record distinct confirmed structure bars before regime/entry vetoes.

    This is observational bookkeeping, not a second entry gate. The primary
    structure engine has already required aligned price action, VWAP, and material
    option Change-OI before setting ``entry_confirmed``. Count the current confirmed
    bar as observed immediately; the entry policy separately asks for an additional
    completed bar only when the setup is a genuine direction change or exhaustion
    reversal. Re-running the scan on the same candle never increments the count.
    """
    direction = str(getattr(structure, "direction", "") or "").upper()
    phase = str(getattr(structure, "market_phase", "") or "").upper()
    expected = f"CONTINUOUS_{direction}" if direction in {"BULLISH", "BEARISH"} else ""
    valid = bool(
        getattr(structure, "entry_confirmed", False)
        and expected
        and phase == expected
    )
    observed_phase = phase if valid else ""
    return update_continuation_persistence(
        state, observed_phase, latest_completed_3m_bar, required_confirmations=1,
    )


def entry_persistence_policy(
    *,
    direction: str,
    market_phase: str,
    entry_confirmed: bool,
    previous_direction: Optional[str],
    local_event_entry: bool = False,
    exhaustion_entry: bool = False,
    opening_fast_track: bool = False,
) -> tuple[int, str]:
    """Return the entry-bar requirement without double-gating confirmed structure.

    A continuous PA/OI-confirmed trend in the same or an unknown prior direction
    needs no extra persistence delay: ``entry_confirmed`` already represents the
    structural engine's multi-factor confirmation. A non-event switch against the
    last known directional state and a counter-trend exhaustion scalp still require
    two distinct completed bars to reduce CE/PE flip-flopping. Confirmed local OI
    breaks/rejections may act immediately because their own completed-bar, flow,
    wall, target/stop, and reward/risk gates are stricter and explicit.
    """
    side = str(direction or "").strip().upper()
    phase = str(market_phase or "").strip().upper()
    prior = str(previous_direction or "").strip().upper()

    if local_event_entry:
        return 1, "confirmed local OI event; event-specific structure and risk gates remain mandatory"
    if exhaustion_entry:
        return max(2, CONTINUATION_CONFIRMATIONS_REQUIRED), "counter-trend exhaustion requires two distinct completed bars"

    continuous_confirmed = bool(
        side in {"BULLISH", "BEARISH"}
        and phase == f"CONTINUOUS_{side}"
        and entry_confirmed
    )
    if continuous_confirmed:
        if prior in {"BULLISH", "BEARISH"} and prior != side:
            return max(2, CONTINUATION_CONFIRMATIONS_REQUIRED), (
                f"confirmed structural direction changed from {prior} to {side}; require two distinct completed bars"
            )
        return 1, "PA/OI engine already confirmed continuous structure; no duplicate persistence delay"

    if opening_fast_track:
        return 1, "confirmed aligned opening structure with strong Change-OI"
    return max(2, CONTINUATION_CONFIRMATIONS_REQUIRED), (
        "fallback persistence policy; structure is not eligible for the continuous-trend fast path"
    )


def _set_t1_activation_from_intrabar_reason(
    trade: dict[str, Any],
    reason: str,
) -> None:
    """Persist the actual 1m bar timestamp that first reached structural T1."""
    try:
        first_part = str(reason).split(";", 1)[0]
        activation_raw = first_part.rsplit("@", 1)[1].strip() if "@" in first_part else ""
        if activation_raw:
            activation_ts = pd.Timestamp(activation_raw)
            if activation_ts.tzinfo is None:
                activation_ts = activation_ts.tz_localize("UTC")
            else:
                activation_ts = activation_ts.tz_convert("UTC")
            trade["t1_hit_at"] = activation_ts.isoformat()
            return
    except Exception:
        pass
    trade["t1_hit_at"] = now_ist().isoformat()


def _underlying_stop_confirmation_ready(
    trade: dict[str, Any],
    underlying_3m: Optional[pd.DataFrame],
) -> bool:
    """Return whether the configured completed-3m confirmation permits an SL exit."""
    stop = safe_float(trade.get("underlying_stop"), float("nan"))
    if not ACTIVE_TRADE_REQUIRE_UNDERLYING_CONFIRMATION or not math.isfinite(stop):
        return True
    if underlying_3m is None or underlying_3m.empty:
        return True

    work = underlying_3m.copy().sort_values("timestamp")
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    work["close"] = pd.to_numeric(work["close"], errors="coerce")
    work = work.dropna(subset=["timestamp", "close"])
    required = max(STRUCTURAL_STOP_CONFIRM_BARS, 1)
    recent = work.tail(required)
    armed_raw = str(trade.get("underlying_stop_armed_bar") or "").strip()
    if armed_raw:
        try:
            armed_ts = pd.Timestamp(armed_raw)
            if armed_ts.tzinfo is None:
                armed_ts = armed_ts.tz_localize("UTC")
            else:
                armed_ts = armed_ts.tz_convert("UTC")
            recent = recent[recent["timestamp"] > armed_ts]
        except Exception:
            pass
    if len(recent) < required:
        return False

    closes = recent["close"].to_numpy(dtype=float)
    direction = str(trade.get("direction", "")).upper()
    return bool(
        np.all(closes >= stop) if direction == "BEARISH"
        else np.all(closes <= stop) if direction == "BULLISH"
        else False
    )


def _active_trade_intrabar_exit(
    trade: dict[str, Any],
    *,
    underlying_1m: Optional[pd.DataFrame] = None,
    underlying_3m: Optional[pd.DataFrame] = None,
) -> tuple[Optional[str], Optional[float], str]:
    """Trigger exits from NIFTY structural levels, never from option premium math."""
    underlying = underlying_1m
    if underlying is None or underlying.empty:
        return None, None, "NO_UNDERLYING_1M_DATA"

    work = underlying.copy().sort_values("timestamp")
    work["timestamp"] = pd.to_datetime(work["timestamp"], utc=True, errors="coerce")
    for column in ("high", "low", "close"):
        work[column] = pd.to_numeric(work[column], errors="coerce")
    work = work.dropna(subset=["timestamp", "high", "low"])
    if work.empty:
        return None, None, "INVALID_UNDERLYING_1M_DATA"

    t1 = safe_float(trade.get("underlying_target_1"), float("nan"))
    t2 = safe_float(trade.get("underlying_target_2"), float("nan"))
    stop = safe_float(trade.get("underlying_stop"), float("nan"))
    direction = str(trade.get("direction", "")).upper()
    t1_already_hit = bool(trade.get("t1_hit", False))

    if underlying_3m is not None and not underlying_3m.empty:
        u3 = underlying_3m.copy().sort_values("timestamp")
        u3["timestamp"] = pd.to_datetime(u3["timestamp"], utc=True, errors="coerce")
        u3["close"] = pd.to_numeric(u3["close"], errors="coerce")
        u3 = u3.dropna(subset=["timestamp", "close"])
    else:
        u3 = pd.DataFrame()

    t1_activation = pd.Timestamp("1900-01-01", tz="UTC")
    if t1_already_hit:
        raw_activation = str(trade.get("t1_hit_at") or "").strip()
        if raw_activation:
            try:
                t1_activation = pd.Timestamp(raw_activation)
                if t1_activation.tzinfo is None:
                    t1_activation = t1_activation.tz_localize("UTC")
                else:
                    t1_activation = t1_activation.tz_convert("UTC")
            except Exception:
                t1_activation = pd.Timestamp("1900-01-01", tz="UTC")

    for _, bar in work.tail(max(ACTIVE_TRADE_INTRABAR_LOOKBACK, 1)).iterrows():
        high = float(bar["high"])
        low = float(bar["low"])
        ts_obj = pd.Timestamp(bar["timestamp"])
        ts = ts_obj.isoformat()

        # T2 can be detected from the complete 1m window because reaching T2
        # implies the T1 level has also been crossed for this directional trade.
        if math.isfinite(t2):
            if direction == "BEARISH" and low <= t2:
                return "TARGET_2", t2, f"NIFTY_1M_LOW={low:.2f}@{ts};T2_NIFTY={t2:.2f}"
            if direction == "BULLISH" and high >= t2:
                return "TARGET_2", t2, f"NIFTY_1M_HIGH={high:.2f}@{ts};T2_NIFTY={t2:.2f}"

        # Initial SL is active before T1. After T1, only bars after the T1
        # activation timestamp may trigger the dynamically recalculated stop.
        stop_active = math.isfinite(stop)
        if t1_already_hit and ts_obj <= t1_activation:
            stop_active = False

        if stop_active:
            stop_confirmed = _underlying_stop_confirmation_ready(trade, u3)
            stop_reference = ""
            if stop_confirmed and math.isfinite(stop) and not u3.empty:
                closes = u3["close"].tail(max(STRUCTURAL_STOP_CONFIRM_BARS, 1)).to_numpy(dtype=float)
                if len(closes):
                    stop_reference = f"NIFTY_3M_CLOSE={closes[-1]:.2f}"
            if stop_confirmed:
                if direction == "BEARISH" and high >= stop:
                    return "STOP_LOSS", stop, f"NIFTY_1M_HIGH={high:.2f}@{ts};{stop_reference};SL_NIFTY={stop:.2f}"
                if direction == "BULLISH" and low <= stop:
                    return "STOP_LOSS", stop, f"NIFTY_1M_LOW={low:.2f}@{ts};{stop_reference};SL_NIFTY={stop:.2f}"

        if not t1_already_hit and math.isfinite(t1):
            if direction == "BEARISH" and low <= t1:
                return "T1_HIT", t1, f"NIFTY_1M_LOW={low:.2f}@{ts};T1_NIFTY={t1:.2f}"
            if direction == "BULLISH" and high >= t1:
                return "T1_HIT", t1, f"NIFTY_1M_HIGH={high:.2f}@{ts};T1_NIFTY={t1:.2f}"

    return None, None, "NO_NIFTY_STRUCTURAL_LEVEL_BREACH"


@dataclass
class MarketDataBundle:
    """Typed result of one market-data ingestion stage."""
    now_time: time
    future: FuturesContract
    index_session: pd.DataFrame
    index_live_quote: dict[str, Any]
    spot: float
    futures_session: pd.DataFrame
    futures_live_quote: dict[str, Any]
    futures_ltp_now: float
    futures_quote_check: dict[str, Any]
    futures_quote_status: str
    futures_analysis_quote: Optional[dict[str, Any]]
    completed_index_3m: pd.DataFrame
    regime_indicator_history: pd.DataFrame
    historical_completed: pd.DataFrame
    futures_3m: pd.DataFrame


def ingest_market_data(state: dict[str, Any], current_time: datetime) -> MarketDataBundle:
    """Fetch index/futures candles, live quotes, indicator history and selected future."""
    now_time = now_ist().time()
    future = get_current_nifty_future(state)

    # -------------------------------------------------------------------------
    # PRIMARY MARKET PRICE FEED = NIFTY INDEX
    # -------------------------------------------------------------------------
    index_session = get_current_session_3m_candles(NIFTY_KEY)
    index_live_quote = get_quote(NIFTY_KEY)
    spot = extract_ltp(index_live_quote)

    # -------------------------------------------------------------------------
    # DERIVATIVES FEED = NIFTY FUTURES PRICE/OI
    # -------------------------------------------------------------------------
    futures_session = get_current_session_3m_candles(future.instrument_key)
    futures_live_quote = get_quote(future.instrument_key)
    futures_ltp_now = extract_ltp(futures_live_quote)
    futures_quote_check = quote_freshness_status(futures_live_quote, now=now_ist())
    futures_quote_status = str(futures_quote_check.get("status", "UNVERIFIED"))
    futures_analysis_quote: Optional[dict[str, Any]] = futures_live_quote
    if futures_quote_status in {"STALE", "FUTURE_TIMESTAMP", "UNAVAILABLE"}:
        futures_analysis_quote = None
        logger.warning(
            "FUTURES LIVE QUOTE EXCLUDED FROM DERIVATIVES CONFIRMATION: status=%s field=%s age_seconds=%s; "
            "NIFTY index remains the primary decision feed.",
            futures_quote_status, futures_quote_check.get("field", "NA"),
            f"{safe_float(futures_quote_check.get('age_seconds'), float('nan')):.1f}"
            if math.isfinite(safe_float(futures_quote_check.get("age_seconds"), float("nan"))) else "NA",
        )
    elif futures_quote_status == "UNVERIFIED":
        logger.warning(
            "FUTURES QUOTE FRESHNESS UNVERIFIED: timestamp field unavailable; quote is retained but not independently freshness-verified."
        )
    else:
        logger.info(
            "FUTURES QUOTE FRESHNESS: status=%s field=%s age_seconds=%.1f timestamp=%s",
            futures_quote_status, futures_quote_check.get("field", "NA"),
            safe_float(futures_quote_check.get("age_seconds"), float("nan")),
            futures_quote_check.get("timestamp", "NA"),
        )

    basis = futures_ltp_now - spot
    basis_pct = basis / spot if spot > 0 else float("nan")
    logger.info(
        "UNDERLYING PRICES: index_spot=%.2f futures_ltp=%.2f basis=%+.2f basis_pct=%+.3f%% "
        "futures_symbol=%s expiry=%s quote_status=%s",
        spot, futures_ltp_now, basis, basis_pct * 100.0 if math.isfinite(basis_pct) else float("nan"),
        future.trading_symbol, future.expiry, futures_quote_status,
    )
    if math.isfinite(basis_pct) and abs(basis_pct) >= FUTURES_BASIS_WARNING_PCT:
        logger.warning(
            "FUTURES BASIS ANOMALY CHECK: basis=%+.2f (%+.3f%%) exceeds diagnostic threshold %.3f%%. "
            "Verify symbol/expiry and quote freshness; basis alone will not veto NIFTY index signals.",
            basis, basis_pct * 100.0, FUTURES_BASIS_WARNING_PCT * 100.0,
        )

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
        if futures_analysis_quote is not None:
            ltp = futures_ltp_now
            opening_ts = pd.Timestamp(now_ist()).tz_convert("UTC")
            futures_session = pd.DataFrame([{
                "timestamp": opening_ts,
                "open": ltp,
                "high": ltp,
                "low": ltp,
                "close": ltp,
                "volume": safe_float(futures_analysis_quote.get("volume"), 0.0),
                "oi": _extract_quote_oi(futures_analysis_quote),
            }])
            logger.warning("FUTURES SESSION: using live futures quote proxy until candles arrive.")
        else:
            futures_session = pd.DataFrame(columns=["timestamp", "open", "high", "low", "close", "volume", "oi"])
            logger.warning("FUTURES SESSION: no reliable live quote/candles; futures context will be unavailable this scan.")

    # NIFTY index is always the price series. If index candles have no usable
    # volume, use timestamp-matched NIFTY futures volume only as the VWAP weight.
    try:
        idx_volume = pd.to_numeric(index_session.get("volume", 0.0), errors="coerce").fillna(0.0)
        if float(idx_volume.sum()) <= 0.0:
            idx = index_session.copy()
            idx["timestamp"] = pd.to_datetime(idx["timestamp"], utc=True, errors="coerce")
            fut = futures_session[["timestamp", "volume"]].copy()
            fut["timestamp"] = pd.to_datetime(fut["timestamp"], utc=True, errors="coerce")
            fut["volume"] = pd.to_numeric(fut["volume"], errors="coerce").fillna(0.0)
            idx = idx.merge(fut, on="timestamp", how="left", suffixes=("", "_fut"))
            idx["volume"] = pd.to_numeric(idx["volume_fut"], errors="coerce").fillna(0.0)
            index_session = idx.drop(columns=["volume_fut"], errors="ignore")
            logger.info("INDEX VWAP: using NIFTY futures volume as weighting proxy; price remains NIFTY index.")
    except Exception as exc:
        logger.warning("VWAP volume-proxy preparation failed: %s", exc)

    completed_index_3m = filter_completed_candles(index_session, 3)

    # Seed ADX and both RSI timeframes from prior-session INDEX candles. The
    # history is cached in state per trading day, avoiding a redundant historical
    # API request on every 3-minute scan. Current-session structure/VWAP still use
    # only today's bars.
    regime_indicator_history = get_regime_indicator_history(state, NIFTY_KEY)

    # Historical futures bars are cached once per trading date and selected
    # futures instrument. Current-session futures candles and live quotes remain
    # fresh on every scan and are never replaced by this historical cache.
    if futures_session.empty and futures_analysis_quote is None:
        # Do not classify a current market regime from stale prior-session futures data.
        historical_completed = pd.DataFrame(columns=["timestamp", "open", "high", "low", "close", "volume", "oi"])
        logger.warning("FUTURES HISTORY SKIPPED: no reliable current-session futures quote or candles.")
    else:
        historical_completed = get_cached_futures_oi_history(
            state, future.instrument_key, now=current_time
        )

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

    return MarketDataBundle(
        now_time=now_time, future=future, index_session=index_session,
        index_live_quote=index_live_quote, spot=spot, futures_session=futures_session,
        futures_live_quote=futures_live_quote, futures_ltp_now=futures_ltp_now,
        futures_quote_check=futures_quote_check, futures_quote_status=futures_quote_status,
        futures_analysis_quote=futures_analysis_quote, completed_index_3m=completed_index_3m,
        regime_indicator_history=regime_indicator_history,
        historical_completed=historical_completed, futures_3m=futures_3m,
    )


@dataclass
class MarketEvaluation:
    """Typed output of structure/regime/local-event evaluation."""
    structure: StructureResult
    market_regime: dict[str, Any]
    local_oi_break: dict[str, Any]
    local_oi_rejection: dict[str, Any]
    local_structure_event: dict[str, Any]
    breakout_watch: dict[str, Any]
    confirmed_local_event_override: bool


def evaluate_market_structure(
    *,
    spot: float,
    index_session: pd.DataFrame,
    futures_3m: pd.DataFrame,
    futures_session: pd.DataFrame,
    chain: list[dict[str, Any]],
    chain_levels: dict[str, Any],
    change_oi_score: float,
    futures_analysis_quote: Optional[dict[str, Any]],
    seed_direction: Optional[str],
    previous_phase: Optional[str],
    previous_snapshot: dict[str, Any],
    regime_indicator_history: pd.DataFrame,
) -> MarketEvaluation:
    """Evaluate the PA/VWAP/Change-OI regime and completed local OI events."""
    structure = build_market_structure(
        spot=spot,
        futures_3m=futures_3m,
        futures_session=futures_session,
        chain_levels=chain_levels,
        change_oi_score=change_oi_score,
        futures_live_quote=futures_analysis_quote,
        previous_direction=seed_direction,
        previous_phase=previous_phase,
        price_session=index_session,
    )
    market_regime = classify_market_regime(
        index_session, spot, structure.vwap, structure.direction,
        structure.support_1, structure.resistance_1,
        indicator_history=regime_indicator_history,
        structure_phase=structure.market_phase,
        structure_change_oi=safe_float(structure.components.get("structure_change_oi"), 0.0),
        structure_vwap_slope=structure.vwap_slope,
        structure_entry_confirmed=structure.entry_confirmed,
    )
    current_oi_structure = chain_levels.get("oi_structure_by_strike", {})
    decision_step = strike_step(sorted(chain_rows(option_chain_atm_window(chain, spot)[0])))
    local_oi_break = detect_confirmed_local_oi_break(
        index_session,
        spot=spot,
        support=structure.support_1,
        resistance=structure.resistance_1,
        previous_snapshot=previous_snapshot,
        chain_levels=chain_levels,
        futures_regime=structure.futures_regime,
        pressure_score=safe_float(chain_levels.get("pressure_score"), 0.0),
        oi_structure_by_strike=current_oi_structure,
        strike_step_value=decision_step,
    )
    local_oi_rejection = detect_confirmed_local_oi_rejection(
        index_session,
        spot=spot,
        support=structure.support_1,
        resistance=structure.resistance_1,
        chain_levels=chain_levels,
        oi_structure_by_strike=current_oi_structure,
        futures_regime=structure.futures_regime,
        pressure_score=safe_float(chain_levels.get("pressure_score"), 0.0),
        strike_step_value=decision_step,
        futures_oi_strength=structure.futures_oi_strength,
    )
    # A confirmed directional break takes priority; otherwise consider a separately
    # confirmed rejection/bounce event. A mere near-wall watch is never an entry.
    local_structure_event = (
        local_oi_break if local_oi_break.get("confirmed") else local_oi_rejection
    )
    if not local_structure_event.get("confirmed"):
        logger.info("LOCAL OI REVERSAL CHECK: %s", local_oi_rejection.get("reason", "NO_CONFIRMED_REVERSAL"))
    completed_for_watch = filter_completed_candles(index_session, 3)
    current_completed_close = (
        safe_float(completed_for_watch["close"].iloc[-1], float("nan"))
        if not completed_for_watch.empty else float("nan")
    )
    breakout_watch = evaluate_local_breakout_watch(
        direction=structure.direction,
        spot=spot,
        current_close=current_completed_close,
        vwap=structure.vwap,
        support=structure.support_1,
        resistance=structure.resistance_1,
        strike_step_value=strike_step(sorted(chain_rows(chain))),
        structure_phase=structure.market_phase,
        structure_entry_confirmed=structure.entry_confirmed,
        effective_change_oi=safe_float(structure.components.get("structure_change_oi"), 0.0),
        futures_regime=structure.futures_regime,
        oi_structure_by_strike=chain_levels.get("oi_structure_by_strike", {}),
        market_intensity=str(market_regime.get("intensity", "UNKNOWN")),
    )
    if breakout_watch.get("armed") and not local_structure_event.get("confirmed"):
        logger.warning(
            "BREAKOUT WATCH ARMED (NOT AN ENTRY): direction=%s wall=%.2f spot=%.2f distance=%.2f "
            "wall_state=%s COI=%+.3f futures=%s; price has not confirmed a close through the wall. "
            "Wait for a completed-bar breakout/hold; the opposing-wall veto remains active.",
            breakout_watch.get("direction", "NEUTRAL"),
            safe_float(breakout_watch.get("level"), float("nan")),
            safe_float(spot), safe_float(breakout_watch.get("distance"), float("nan")),
            breakout_watch.get("wall_state", "UNKNOWN"),
            safe_float(structure.components.get("structure_change_oi"), 0.0),
            structure.futures_regime,
        )
    classified_intensity = str(market_regime.get("intensity", "UNKNOWN")).upper()
    confirmed_local_event_override = is_confirmed_local_directional_event(local_structure_event)
    if local_structure_event.get("confirmed") and (classified_intensity != "SIDEWAYS" or confirmed_local_event_override):
        if local_structure_event.get("warnings"):
            logger.warning("LOCAL OI EVENT WARNING: %s", ",".join(map(str, local_structure_event.get("warnings", []))))
        logger.warning(
            "LOCAL OI EVENT CONFIRMED: kind=%s direction=%s level=%.2f reason=%s",
            local_structure_event.get("kind", "BREAK"),
            local_structure_event.get("direction", "NEUTRAL"),
            safe_float(local_structure_event.get("level"), float("nan")),
            local_structure_event.get("reason", ""),
        )
        market_regime["direction"] = str(local_structure_event["direction"])
        if classified_intensity in {"UNKNOWN", "SIDEWAYS"} and confirmed_local_event_override:
            # ADX describes trend strength, but a properly confirmed local break
            # may still be tradable. Keep the original classification in logs/state.
            market_regime["classified_intensity"] = classified_intensity
            market_regime["structural_break_override"] = True
            market_regime["intensity"] = "NORMAL"
            logger.warning(
                "STRUCTURAL EVENT OVERRIDE: raw_intensity=%s ADX=%s; trade eligibility will still require valid in-window T1/SL and R/R >= %.2f.",
                classified_intensity, market_regime.get("adx"), MIN_STRUCTURAL_ENTRY_REWARD_RISK_RATIO,
            )
        elif classified_intensity == "UNKNOWN":
            market_regime["intensity"] = "NORMAL"
        market_regime["reason"] = (
            str(market_regime.get("reason", "")) + "; " + str(local_structure_event.get("reason", ""))
        ).strip("; ")

    return MarketEvaluation(
        structure=structure, market_regime=market_regime,
        local_oi_break=local_oi_break, local_oi_rejection=local_oi_rejection,
        local_structure_event=local_structure_event, breakout_watch=breakout_watch,
        confirmed_local_event_override=confirmed_local_event_override,
    )


def manage_active_trades(
    state: dict[str, Any],
    *,
    chain: list[dict[str, Any]],
    spot: float,
    structure: StructureResult,
    price_session: pd.DataFrame,
    option_flow_by_strike: dict[str, Any],
) -> bool:
    """Service an existing trade and return True when new-entry evaluation must stop."""
    active_trade = active_trade_from_state(state)
    if active_trade is not None:
        migrated = migrate_active_trade_to_v25(
            active_trade,
            chain=chain,
            spot=spot,
            structure=structure,
            price_session=price_session,
            change_oi_by_strike=option_flow_by_strike,
        )
        if migrated:
            state["active_trade"] = active_trade
            save_state(state)
        monitor_active_trade(
            state,
            structure,
            chain=chain,
            price_session=price_session,
        )
        return True

    return False


def generate_signals(
    *,
    state: dict[str, Any],
    chain: list[dict[str, Any]],
    spot: float,
    regime_direction: str,
    intensity: str,
    is_expiry_day: bool,
    entry_structure: StructureResult,
    option_flow_by_strike: dict[str, Any],
    oi_velocity_by_strike: dict[str, Any],
) -> Optional[OptionCandidate]:
    """Rank local option candidates and apply every existing execution validation."""
    option_micro_metrics = collect_option_premium_vwaps(
        chain, spot, regime_direction, intensity,
        is_expiry_day=is_expiry_day, now=now_ist(),
    )
    try:
        option = select_directional_option(
            chain=chain,
            direction=regime_direction,
            spot=spot,
            change_oi_by_strike=option_flow_by_strike,
            market_intensity=intensity,
            is_expiry_day=is_expiry_day,
            now=now_ist(),
            option_metrics_by_instrument=option_micro_metrics,
            oi_velocity_by_strike=oi_velocity_by_strike,
        )
        validate_continuous_option_entry(
            option=option,
            chain=chain,
            direction=regime_direction,
            market_phase=entry_structure.market_phase,
            spot=spot,
            market_intensity=intensity,
            is_expiry_day=is_expiry_day,
            now=now_ist(),
        )
    except ScannerError as exc:
        logger.warning("NO TRADE: option strike selection rejected all candidates: %s", exc)
        save_state(state)
        return None
    return option


def execute_scan(
    state: Optional[dict[str, Any]] = None,
) -> Optional[Signal]:
    state = state if isinstance(state, dict) else load_state()
    current_time = now_ist()
    today_iso = current_time.date().isoformat()
    # The 15:15 cutoff is evaluated before ordinary market-hours returns, so an
    # active intraday trade still receives its exit routine if a scan starts late.
    if current_time.weekday() < 5 and current_time.time() >= NEW_ENTRY_CUTOFF:
        active = active_trade_from_state(state)
        if active:
            if str(active.get("trade_date", ""))[:10] == today_iso:
                force_close_active_trade_at_cutoff(state, "TIME_CUTOFF_15_15")
            else:
                # Do not let an expired prior-session position remain active in
                # scanner state if its old instrument no longer has a live quote.
                closed = dict(active)
                closed.update({
                    "status": "CLOSED", "outcome": "SESSION_END_CLEANUP",
                    "closed_at": current_time.isoformat(),
                    "exit_reason": "stale position state from a prior trading date",
                })
                state["active_trade"] = None
                state["last_completed_trade"] = closed
                save_state(state)
                logger.warning("STALE ACTIVE TRADE STATE CLEARED for prior session: %s", active.get("trading_symbol", ""))
        logger.info("NEW ENTRY CUTOFF: %s IST; no new positions after %s.", current_time.strftime("%H:%M:%S"), NEW_ENTRY_CUTOFF.strftime("%H:%M"))
        return None

    if not market_window_open():
        logger.info("Outside NSE market hours.")
        return None

    status = get_market_status()
    logger.info("NSE status=%s", status)
    if status != "OPEN":
        return None

    # Directional memory is version-scoped, but compatible same-day OI history
    # is data, not strategy state: preserve it across code upgrades. On a new date,
    # reset both intraday memory and the OI ring because yesterday's OI cannot be
    # used as an intraday velocity baseline.
    state_reset, reset_reason = reset_intraday_memory_if_needed(state, today_iso)
    if state_reset:
        oi_history_count = len(state.get("option_oi_history", [])) if isinstance(state.get("option_oi_history"), list) else 0
        logger.info(
            "STATE RESET: reason=%s; directional memory reset; preserved_OI_history_snapshots=%d; state_file=%s",
            reset_reason, oi_history_count, STATE_FILE.resolve(),
        )
        save_state(state)

    market_data = ingest_market_data(state, current_time)
    now_time = market_data.now_time
    future = market_data.future
    index_session = market_data.index_session
    index_live_quote = market_data.index_live_quote
    spot = market_data.spot
    futures_session = market_data.futures_session
    futures_live_quote = market_data.futures_live_quote
    futures_ltp_now = market_data.futures_ltp_now
    futures_quote_check = market_data.futures_quote_check
    futures_quote_status = market_data.futures_quote_status
    futures_analysis_quote = market_data.futures_analysis_quote
    completed_index_3m = market_data.completed_index_3m
    regime_indicator_history = market_data.regime_indicator_history
    historical_completed = market_data.historical_completed
    futures_3m = market_data.futures_3m

    # Build the option-chain structure directly from current OI and Change-OI.
    expiry, chain = get_option_chain(state)
    api_change_oi_by_strike = fetch_change_oi_by_strike(expiry)
    change_oi_score, change_oi_by_strike, local_change_oi_meta = local_change_oi_confirmation(
        chain, spot, api_change_oi_by_strike, now=now_ist()
    )
    previous_snapshot = state.get("market_snapshot") if isinstance(state.get("market_snapshot"), dict) else {}
    previous_option_snapshot = state.get("option_oi_snapshot") if isinstance(state.get("option_oi_snapshot"), dict) else {}
    chain_levels = chain_oi_support_resistance(
        chain,
        spot,
        change_oi_by_strike,
        previous_option_snapshot=previous_option_snapshot,
        expiry=expiry,
    )
    option_flow_by_strike = chain_levels.get("option_flow_by_strike", {})
    # Use one timestamp for both the velocity-ring record and legacy snapshot so
    # they deduplicate exactly rather than storing near-identical samples.
    oi_snapshot_time = now_ist()
    oi_velocity_by_strike = update_option_oi_velocity_history(state, chain, expiry, now=oi_snapshot_time, spot=spot)
    window_velocity = aggregate_atm_window_coi_velocity(
        chain, spot, oi_velocity_by_strike, now=oi_snapshot_time
    )
    if bool(window_velocity.get("available")):
        primary_score = safe_float(window_velocity.get("score"), 0.0)
        chain_levels["change_flow_score"] = primary_score
        chain_levels["change_flow_bias"] = 1 if primary_score >= STRUCTURE_CHANGE_OI_CONFIRM else -1 if primary_score <= -STRUCTURE_CHANGE_OI_CONFIRM else 0
        chain_levels["pressure_score"] = primary_score
        chain_levels["normalized_diff"] = primary_score
        chain_levels["flow_mode"] = str(window_velocity.get("baseline_mode", "INTRADAY_SNAPSHOT"))
        chain_levels["coi_decision_source"] = str(window_velocity.get("baseline_mode", "UNAVAILABLE"))
        chain_levels["coi_decision_coverage"] = int(window_velocity.get("coverage", 0))
        logger.info(
            "ATM COI VELOCITY PRIMARY: mode=%s coverage=%d/%d call_change=%+.0f put_change=%+.0f "
            "raw_score=%+.3f weight=%.2f effective_score=%+.3f baseline_age_min=%s window=%s",
            window_velocity.get("baseline_mode"), int(window_velocity.get("coverage", 0)),
            int(window_velocity.get("window_count", 0)),
            safe_float(window_velocity.get("call_change_sum"), 0.0),
            safe_float(window_velocity.get("put_change_sum"), 0.0),
            safe_float(window_velocity.get("raw_score"), 0.0),
            safe_float(window_velocity.get("weight"), 1.0), primary_score,
            f"{safe_float(window_velocity.get('baseline_age_minutes'), float('nan')):.1f}"
            if math.isfinite(safe_float(window_velocity.get("baseline_age_minutes"), float("nan"))) else "NA",
            ",".join(f"{x:.0f}" for x in window_velocity.get("window_strikes", [])),
        )
    else:
        # First scan (or incomplete OI history): the already-fetched per-strike
        # API data remains local to ATM +/-4 and is down-weighted until 09:45.
        chain_levels["change_flow_score"] = safe_float(local_change_oi_meta.get("weighted_score"), change_oi_score)
        chain_levels["change_flow_bias"] = int(local_change_oi_meta.get("bias", 0))
        chain_levels["pressure_score"] = safe_float(local_change_oi_meta.get("weighted_score"), 0.0)
        chain_levels["normalized_diff"] = safe_float(local_change_oi_meta.get("weighted_score"), 0.0)
        chain_levels["flow_mode"] = "DAY_CHANGE_API_WARMUP" if now_ist().time() < COI_COLD_START_END else "LOCAL_DAY_CHANGE_FALLBACK"
        chain_levels["coi_decision_source"] = str(local_change_oi_meta.get("source", "UNAVAILABLE"))
        chain_levels["coi_decision_coverage"] = int(local_change_oi_meta.get("coverage", 0))
        logger.warning(
            "ATM COI VELOCITY NOT READY: baseline=%s coverage=%d/%d; using local ATM-window Change-OI fallback only, "
            "not full-chain aggregate.",
            window_velocity.get("baseline_mode", "UNAVAILABLE"),
            int(window_velocity.get("coverage", 0)), int(window_velocity.get("required_coverage", 0)),
        )
    chain_levels["coi_window_atm"] = safe_float(local_change_oi_meta.get("atm_strike"), float("nan"))
    chain_levels["coi_window_strikes"] = list(local_change_oi_meta.get("window_strikes", []))
    chain_levels["previous_support_1"] = safe_float(previous_snapshot.get("support_1"), float("nan"))
    chain_levels["previous_resistance_1"] = safe_float(previous_snapshot.get("resistance_1"), float("nan"))
    previous_direction = str(previous_snapshot.get("direction", "")).upper() or None
    persistent_direction = str(
        state.get("persistent_direction")
        or previous_snapshot.get("persistent_direction", "")
    ).upper() or None
    previous_phase = str(previous_snapshot.get("market_phase", "")).upper() or None

    seed_direction = persistent_direction or previous_direction

    evaluation = evaluate_market_structure(
        spot=spot, index_session=index_session, futures_3m=futures_3m,
        futures_session=futures_session, chain=chain, chain_levels=chain_levels,
        change_oi_score=change_oi_score, futures_analysis_quote=futures_analysis_quote,
        seed_direction=seed_direction, previous_phase=previous_phase,
        previous_snapshot=previous_snapshot,
        regime_indicator_history=regime_indicator_history,
    )
    structure = evaluation.structure
    market_regime = evaluation.market_regime
    local_oi_break = evaluation.local_oi_break
    local_oi_rejection = evaluation.local_oi_rejection
    local_structure_event = evaluation.local_structure_event
    breakout_watch = evaluation.breakout_watch
    confirmed_local_event_override = evaluation.confirmed_local_event_override

    logger.info(
        "REGIME INDICATOR READINESS: history_3m=%d total_seeded_3m=%d current_15m=%d "
        "ADX_period=%d ADX_valid=%s RSI3m_valid=%s RSI15m_valid=%s",
        int(market_regime.get("indicator_history_bars", 0)),
        int(market_regime.get("indicator_3m_bars", 0)),
        int(market_regime.get("indicator_15m_bars", 0)),
        ADX_PERIOD,
        math.isfinite(safe_float(market_regime.get("adx"), float("nan"))),
        math.isfinite(safe_float(market_regime.get("rsi_3m"), float("nan"))),
        math.isfinite(safe_float(market_regime.get("rsi_15m"), float("nan"))),
    )
    is_expiry_day = parse_date(str(expiry)) == now_ist().date()
    tod_window = time_of_day_window(now_ist())
    logger.info(
        "REGIME MATRIX: direction=%s intensity=%s ADX=%s RSI3m=%s RSI15m=%s TOD=%s expiry_day=%s "
        "volume_confirmed=%s divergence=%s structural_override=%s reason=%s",
        market_regime.get("direction"), market_regime.get("intensity"),
        f"{safe_float(market_regime.get('adx'), float('nan')):.2f}" if math.isfinite(safe_float(market_regime.get("adx"), float("nan"))) else "NA",
        f"{safe_float(market_regime.get('rsi_3m'), float('nan')):.2f}" if math.isfinite(safe_float(market_regime.get("rsi_3m"), float("nan"))) else "NA",
        f"{safe_float(market_regime.get('rsi_15m'), float('nan')):.2f}" if math.isfinite(safe_float(market_regime.get("rsi_15m"), float("nan"))) else "NA",
        tod_window, is_expiry_day, market_regime.get("volume_confirmed"),
        market_regime.get("divergence"), market_regime.get("structural_direction_override", False),
        market_regime.get("reason"),
    )

    market_memory = MarketMemory.from_state(state)
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
    market_memory.append_history(history_item, STATE_HISTORY_LIMIT)
    state["market_history"] = market_memory.market_history

    state["market_snapshot"] = MarketSnapshot.from_mapping({
        "timestamp": now_ist().isoformat(),
        "spot": round(spot, 2),
        "futures_ltp": round(futures_ltp_now, 2),
        "basis": round(futures_ltp_now - spot, 2),
        "future": future.trading_symbol,
        "future_expiry": future.expiry,
        "futures_quote_status": futures_quote_status,
        "futures_quote_timestamp": futures_quote_check.get("timestamp", "") or None,
        "futures_quote_age_seconds": round(safe_float(futures_quote_check.get("age_seconds"), float("nan")), 1)
            if math.isfinite(safe_float(futures_quote_check.get("age_seconds"), float("nan"))) else None,
        "futures_regime": structure.futures_regime,
        "scenario_classification": structure.futures_regime if structure.futures_regime in {"LONG_BUILDUP", "SHORT_BUILDUP", "SHORT_COVERING", "LONG_UNWINDING"} else "NEUTRAL",
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
        "direction": (
            str(local_structure_event.get("direction", "")).upper()
            if local_structure_event.get("confirmed") and str(market_regime.get("intensity", "UNKNOWN")).upper() != "SIDEWAYS"
            else structure.direction
        ),
        "pa_oi_structure_direction": structure.direction,
        "persistent_direction": (
            str(local_structure_event.get("direction", "")).upper()
            if local_structure_event.get("confirmed") and str(market_regime.get("intensity", "UNKNOWN")).upper() != "SIDEWAYS"
            else structure.direction if structure.direction in {"BULLISH", "BEARISH"} else seed_direction
        ),
        "score": round(structure.score, 3),
        "confidence": round(structure.confidence, 2),
        "market_phase": structure.market_phase,
        "entry_confirmed": structure.entry_confirmed,
        "reversal_confirmations": structure.reversal_confirmations,
        "confirmation_state": structure.confirmation_state,
        "pcr": structure.pcr if math.isfinite(structure.pcr) else None,
        "pcr_bias": structure.pcr_bias,
        "false_breakout": structure.false_breakout,
        "trap_level": structure.trap_level,
        "entry_trigger": structure.entry_trigger,
        "invalidation_rule": structure.invalidation_rule,
        "support_1": structure.support_1,
        "support_2": structure.support_2,
        "resistance_1": structure.resistance_1,
        "resistance_2": structure.resistance_2,
        "latest_completed_3m_bar": (
            str(completed_index_3m["timestamp"].iloc[-1])
            if not completed_index_3m.empty else ""
        ),
        "components": structure.components,
        "regime_direction": market_regime.get("direction", "NEUTRAL"),
        "market_intensity": market_regime.get("intensity", "UNKNOWN"),
        "near_structural_level": bool(market_regime.get("near_structural_level", False)),
        "reversal_price_confirmed": bool(market_regime.get("reversal_price_confirmed", False)),
        "adx": market_regime.get("adx") if math.isfinite(safe_float(market_regime.get("adx"), float("nan"))) else None,
        "rsi_3m": market_regime.get("rsi_3m") if math.isfinite(safe_float(market_regime.get("rsi_3m"), float("nan"))) else None,
        "rsi_15m": market_regime.get("rsi_15m") if math.isfinite(safe_float(market_regime.get("rsi_15m"), float("nan"))) else None,
        "regime_reason": market_regime.get("reason", ""),
        "tod_window": tod_window,
        "expiry_day": is_expiry_day,
        "oi_structure_by_strike": chain_levels.get("oi_structure_by_strike", {}),
        "local_oi_break": local_oi_break,
        "local_oi_rejection": local_oi_rejection,
        "local_structure_event": local_structure_event,
        "breakout_watch": breakout_watch,
    }).to_mapping()
    state["option_oi_snapshot"] = build_option_oi_snapshot(chain, expiry, now=oi_snapshot_time, spot=spot)
    state["option_flow_by_strike"] = option_flow_by_strike

    # Observe structural persistence before saving the snapshot and before the
    # SIDEWAYS/UNKNOWN/midday entry vetoes. This means a low-ADX scan still records
    # confirmed structural bars; it never authorizes entry by itself. Avoid counting
    # pre-entry opening scans before MIN_ENTRY_TIME.
    if now_time >= MIN_ENTRY_TIME:
        latest_persistence_bar = (
            completed_index_3m["timestamp"].iloc[-1]
            if not completed_index_3m.empty else None
        )
        observed_ready, observed_count = observe_confirmed_structure_persistence(
            state, structure, latest_persistence_bar,
        )
        if str(structure.market_phase).upper() in {"CONTINUOUS_BULLISH", "CONTINUOUS_BEARISH"}:
            logger.info(
                "STRUCTURAL BAR OBSERVED BEFORE REGIME GATES: phase=%s distinct_bars=%d "
                "observed=%s entry_requirement_is_evaluated_separately bar=%s",
                structure.market_phase, observed_count, observed_ready,
                str(latest_persistence_bar or "UNKNOWN"),
            )

    state["persistent_direction"] = (
        str(local_structure_event.get("direction", "")).upper()
        if local_structure_event.get("confirmed") and (str(market_regime.get("intensity", "UNKNOWN")).upper() != "SIDEWAYS" or confirmed_local_event_override)
        else structure.direction if structure.direction in {"BULLISH", "BEARISH"} else (seed_direction or "")
    ) or None
    save_state(state)

    logger.info(
        "PERSISTENT MARKET CONTEXT: persisted=%s immediate_previous=%s",
        state.get("persistent_direction") or "NONE",
        previous_direction or "NONE",
    )
    if local_structure_event.get("confirmed") and (str(market_regime.get("intensity", "UNKNOWN")).upper() != "SIDEWAYS" or confirmed_local_event_override):
        prediction_direction = str(local_structure_event.get("direction", "NEUTRAL")).upper()
        prediction_interpretation = str(local_structure_event.get("reason", "Confirmed local OI event"))
        prediction_score = abs(structure.score) if prediction_direction == "BULLISH" else -abs(structure.score)
        prediction_confidence = min(max(structure.confidence, 60.0), 82.0)
    else:
        prediction_direction = structure.direction
        prediction_interpretation = structure.interpretation
        prediction_score = structure.score
        prediction_confidence = structure.confidence
    logger.info(
        "PREDICTION: %s | %s | confidence=%.1f score=%+.2f",
        prediction_direction, prediction_interpretation, prediction_confidence, prediction_score,
    )

    if manage_active_trades(
        state, chain=chain, spot=spot, structure=structure,
        price_session=index_session, option_flow_by_strike=option_flow_by_strike,
    ):
        return None

    # Prevent stop/exit -> immediate re-entry churn. A fresh 3m candle and a
    # short cooldown are required before another trade can be opened. This is
    # especially important on expiry day when ATM can move by one strike quickly.
    last_completed = state.get("last_completed_trade")
    if isinstance(last_completed, dict):
        closed_at_raw = str(last_completed.get("closed_at", ""))
        try:
            closed_at = pd.Timestamp(closed_at_raw)
            if closed_at.tzinfo is None:
                closed_at = closed_at.tz_localize(IST)
            else:
                closed_at = closed_at.tz_convert(IST)
            elapsed = (pd.Timestamp(now_ist()) - closed_at).total_seconds() / 60.0
            previous_trade_direction = str(last_completed.get("direction", "")).upper()
            current_break_direction = str(local_structure_event.get("direction", "")).upper() if local_structure_event.get("confirmed") else ""
            opposite_confirmed_break = bool(
                current_break_direction in {"BULLISH", "BEARISH"}
                and previous_trade_direction in {"BULLISH", "BEARISH"}
                and current_break_direction != previous_trade_direction
                and str(market_regime.get("intensity", "UNKNOWN")).upper() != "SIDEWAYS"
            )
            if elapsed < max(REENTRY_COOLDOWN_MINUTES, 0) and not opposite_confirmed_break:
                logger.info(
                    "RE-ENTRY COOLDOWN: %.1f/%.1f minutes elapsed after %s; no new trade.",
                    elapsed, max(REENTRY_COOLDOWN_MINUTES, 0), last_completed.get("outcome", "EXIT"),
                )
                return None
            if elapsed < max(REENTRY_COOLDOWN_MINUTES, 0) and opposite_confirmed_break:
                logger.warning(
                    "RE-ENTRY COOLDOWN BYPASSED: confirmed opposite OI structural event %s (%s) after %s; "
                    "completed-bar and derivatives confirmation passed.",
                    current_break_direction, local_structure_event.get("kind", "UNKNOWN"),
                    last_completed.get("outcome", "EXIT"),
                )
        except Exception:
            pass

    completed_session_bars = len(completed_index_3m)
    if REENTRY_REQUIRE_NEW_3M_BAR:
        last_exit_bar = str(last_completed.get("exit_3m_bar", "")) if isinstance(last_completed, dict) else ""
        current_completed_bar = (
            str(completed_index_3m["timestamp"].iloc[-1])
            if completed_session_bars else ""
        )
        if last_exit_bar and current_completed_bar and last_exit_bar == current_completed_bar:
            logger.info("RE-ENTRY WAIT: no new completed 3m bar since the previous exit.")
            return None
    opening_mode = now_time < MIN_ENTRY_TIME or completed_session_bars < 1
    if opening_mode:
        logger.info(
            "OPENING MODE: completed_index_3m_bars=%d time=%s; monitoring structure without forcing a trade.",
            completed_session_bars,
            now_time.strftime("%H:%M:%S"),
        )
        return None

    intensity = str(market_regime.get("intensity", "UNKNOWN")).upper()
    regime_direction = str(market_regime.get("direction", "NEUTRAL")).upper()
    adx_value = safe_float(market_regime.get("adx"), float("nan"))
    if intensity in {"SIDEWAYS", "UNKNOWN"}:
        if (
            structure.direction in {"BULLISH", "BEARISH"}
            and structure.market_phase == f"CONTINUOUS_{structure.direction}"
            and structure.entry_confirmed
        ):
            logger.warning(
                "STRUCTURE/REGIME DISAGREEMENT: structure=%s/%s entry_confirmed=%s; "
                "regime=%s/%s ADX=%s override_eligible=%s override_reason=%s. "
                "No entry until directional consistency is established; risk gates remain unchanged.",
                structure.direction, structure.market_phase, structure.entry_confirmed,
                regime_direction, intensity,
                f"{adx_value:.2f}" if math.isfinite(adx_value) else "NA",
                market_regime.get("structural_direction_override", False),
                market_regime.get("structural_direction_override_reason", market_regime.get("reason", "")),
            )
        logger.info("NO TRADE: market intensity=%s; reason=%s", intensity, market_regime.get("reason", ""))
        return None
    if regime_direction not in {"BULLISH", "BEARISH"}:
        logger.info("NO TRADE: market-regime direction is neutral.")
        return None
    coi_guard = state.get("coi_market_guard")
    if isinstance(coi_guard, dict) and str(coi_guard.get("blocked_direction", "")).upper() == regime_direction:
        logger.warning(
            "NO TRADE: %s counter-trend entry blocked by COI profit-booking guard (%s); waiting for fresh structural writing.",
            regime_direction, coi_guard.get("reason", "PROFIT_BOOKING"),
        )
        return None
    if tod_window == "MIDDAY" and (not math.isfinite(adx_value) or adx_value < MIDDAY_MIN_ADX) and not confirmed_local_event_override:
        logger.info("NO TRADE: midday momentum gate requires ADX >= %.1f; actual=%s.", MIDDAY_MIN_ADX, adx_value)
        return None

    # Exhaustion is the only controlled counter-trend exception. RSI divergence
    # near the matching structural wall is insufficient by itself: the latest
    # completed 3m bar must break the prior bar's extreme, Change-OI must strongly
    # agree with the reversal, and futures positioning must not strongly oppose it.
    flow_value = safe_float(structure.components.get("structure_change_oi"), 0.0)
    reversal_price_confirmed = bool(market_regime.get("reversal_price_confirmed", False))
    if regime_direction == "BULLISH":
        aligned_oi = flow_value >= STRUCTURE_CHANGE_OI_STRONG
        opposing_futures = bool(
            safe_float(structure.components.get("structure_futures_conflict_bullish"), 0.0) > 0.5
            or (structure.futures_bias < 0 and structure.futures_oi_strength >= STRUCTURE_FUTURES_CONFLICT_STRENGTH)
        )
    else:
        aligned_oi = flow_value <= -STRUCTURE_CHANGE_OI_STRONG
        opposing_futures = bool(
            safe_float(structure.components.get("structure_futures_conflict_bearish"), 0.0) > 0.5
            or (structure.futures_bias > 0 and structure.futures_oi_strength >= STRUCTURE_FUTURES_CONFLICT_STRENGTH)
        )
    exhaustion_entry = bool(
        intensity == "EXHAUSTION"
        and market_regime.get("near_structural_level", False)
        and reversal_price_confirmed
        and aligned_oi
        and not opposing_futures
    )
    local_event_matches_regime = bool(
        local_structure_event.get("confirmed")
        and str(local_structure_event.get("direction", "")).upper() == regime_direction
        and (intensity != "SIDEWAYS" or confirmed_local_event_override)
    )
    if intensity == "EXHAUSTION" and not exhaustion_entry and not local_event_matches_regime:
        logger.info(
            "NO TRADE: exhaustion setup not fully confirmed; near_level=%s price_break=%s "
            "flow=%+.3f flow_aligned=%s futures_conflict=%s.",
            market_regime.get("near_structural_level", False), reversal_price_confirmed,
            flow_value, aligned_oi, opposing_futures,
        )
        return None

    local_event_entry = local_event_matches_regime
    if regime_direction != structure.direction and not exhaustion_entry and not local_event_entry:
        logger.info(
            "NO TRADE: regime direction=%s disagrees with PA/OI structure direction=%s.",
            regime_direction, structure.direction,
        )
        return None

    entry_structure = structure
    if local_event_entry:
        local_direction = regime_direction
        local_phase = "CONTINUOUS_BULLISH" if local_direction == "BULLISH" else "CONTINUOUS_BEARISH"
        event_kind = str(local_structure_event.get("kind", "BREAK")).upper()
        event_level = safe_float(local_structure_event.get("level"), float("nan"))
        if event_kind == "RESISTANCE_REJECTION":
            event_invalidation = (
                f"Invalidate bearish resistance-rejection setup if NIFTY closes above rejected resistance "
                f"{event_level:.2f} with bullish price/OI confirmation."
            )
        elif event_kind == "SUPPORT_BOUNCE":
            event_invalidation = (
                f"Invalidate bullish support-bounce setup if NIFTY closes below defended support "
                f"{event_level:.2f} with bearish price/OI confirmation."
            )
        else:
            event_invalidation = (
                f"Exit if NIFTY reclaims the broken OI level {event_level:.2f} "
                f"with opposing price/OI confirmation; this is a local structural break, not a guaranteed full-session trend."
            )
        entry_structure = replace(
            structure,
            direction=local_direction,
            score=abs(structure.score) if local_direction == "BULLISH" else -abs(structure.score),
            confidence=min(max(
                structure.confidence - safe_float(local_structure_event.get("confidence_penalty"), 0.0),
                50.0 if safe_float(local_structure_event.get("confidence_penalty"), 0.0) > 0.0 else 60.0,
            ), 82.0),
            interpretation=f"CONFIRMED LOCAL OI {local_direction} {event_kind} — PRICE BAR + DERIVATIVES CONFIRMATION",
            market_phase=local_phase,
            entry_confirmed=True,
            confirmation_state=f"CONFIRMED_LOCAL_OI_{event_kind}",
            entry_trigger=str(local_structure_event.get("reason", "Confirmed local OI structural event")),
            invalidation_rule=event_invalidation,
            reasons=list(structure.reasons) + [
                f"LOCAL OI EVENT OVERRIDE: direction={local_direction}; kind={event_kind}; "
                f"{local_structure_event.get('reason', '')}."
            ],
        )
    if exhaustion_entry:
        exhaustion_phase = f"EXHAUSTION_{regime_direction}"
        exhaustion_trigger = (
            f"Counter-trend exhaustion scalp: confirmed {regime_direction.lower()} 3m/15m RSI divergence "
            "at an OI structural level, local price reversal through the prior 3m bar extreme, and aligned Change-OI."
        )
        exhaustion_invalidation = (
            "Exit if the underlying breaches the structural stop or the reversal loses its OI/price confirmation; "
            "do not assume an exhaustion signal is a new full-session trend."
        )
        entry_structure = replace(
            structure,
            direction=regime_direction,
            score=2.0 if regime_direction == "BULLISH" else -2.0,
            confidence=min(structure.confidence, 72.0),
            interpretation=f"CONFIRMED EXHAUSTION {regime_direction} — COUNTER-TREND SCALP",
            market_phase=exhaustion_phase,
            entry_confirmed=True,
            confirmation_state="EXHAUSTION_REVERSAL_CONFIRMED",
            entry_trigger=exhaustion_trigger,
            invalidation_rule=exhaustion_invalidation,
            reasons=list(structure.reasons) + [
                f"EXHAUSTION OVERRIDE: divergence={market_regime.get('divergence')}; "
                f"near_level={market_regime.get('near_structural_level')}; "
                f"price_break_confirmed={reversal_price_confirmed}; Change-OI={flow_value:+.3f}; "
                f"futures_conflict={opposing_futures}."
            ],
        )

    allowed_matrix_states = {"CONTINUOUS_BULLISH", "CONTINUOUS_BEARISH"}
    matrix_state = (
        structure.market_phase[:-10]
        if structure.market_phase.endswith("_CONFIRMED")
        else structure.market_phase
    )
    if not exhaustion_entry and not local_event_entry and matrix_state not in allowed_matrix_states:
        logger.info("No entry: PA/OI structure not continuous: %s", structure.market_phase)
        return None
    if not exhaustion_entry and not local_event_entry and not structure.entry_confirmed:
        logger.info(
            "No entry: confirmation/tactical gate failed. direction=%s phase=%s state=%s invalidations=%d/%d PCR_bias=%+d",
            structure.direction, structure.market_phase, structure.confirmation_state,
            structure.reversal_confirmations, MARKET_INVALIDATION_CONFIRMATIONS_REQUIRED, structure.pcr_bias,
        )
        return None

    if now_time < COI_COLD_START_END:
        volume_confirmed = bool(market_regime.get("volume_confirmed", False))
        price_break = safe_float(entry_structure.components.get("structure_price_break"), 0.0)
        directional_break = (price_break > 0.5) if regime_direction == "BULLISH" else (price_break < -0.5)
        current_vwap_slope = safe_float(entry_structure.vwap_slope, 0.0)
        opening_tape_aligned = bool(
            not local_event_entry
            and intensity in {"NORMAL", "STRONG"}
            and regime_direction == entry_structure.direction
            and entry_structure.entry_confirmed
            and abs(safe_float(entry_structure.components.get("structure_change_oi"), 0.0)) >= STRUCTURE_CHANGE_OI_CONFIRM
            and ((regime_direction == "BULLISH" and spot > entry_structure.vwap and current_vwap_slope > 0)
                 or (regime_direction == "BEARISH" and spot < entry_structure.vwap and current_vwap_slope < 0))
        )
        confirmed_event_trigger = bool(local_event_entry and confirmed_local_event_override)
        cold_start_passed = cold_start_entry_gate_passed(
            current_time=now_time,
            volume_confirmed=volume_confirmed,
            directional_break=directional_break,
            opening_tape_aligned=opening_tape_aligned,
            local_event_entry=local_event_entry,
            confirmed_local_event_override=confirmed_local_event_override,
        )
        if not cold_start_passed:
            logger.info(
                "NO TRADE: cold-start requires volume, a confirmed structural event, a structural breakout, "
                "or aligned opening tape; volume_confirmed=%s confirmed_local_event=%s "
                "directional_break=%s tape_aligned=%s COI_weight=%.2f.",
                volume_confirmed, confirmed_event_trigger, directional_break,
                opening_tape_aligned, COI_COLD_START_WEIGHT,
            )
            return None
        if confirmed_event_trigger:
            logger.info(
                "COLD-START GATE PASSED: confirmed local %s in %s direction; "
                "structural targets, opposing-wall checks, execution quality and minimum R/R remain mandatory.",
                str(local_structure_event.get("kind", "STRUCTURAL_EVENT")), regime_direction,
            )

    volatility_unit = max(safe_float(structure.components.get("volatility_unit"), 50.0), 1.0)
    vwap_distance_atr = abs(float(spot) - float(structure.vwap)) / volatility_unit
    latest_3m_move_atr = abs(float(structure.components.get("recent3_movement_atr", 0.0)))
    latest_completed_bar = (
        completed_index_3m["timestamp"].iloc[-1]
        if not completed_index_3m.empty
        else None
    )
    persistence_phase = entry_structure.market_phase
    opening_fast_track = bool(
        now_time < COI_COLD_START_END and not local_event_entry
        and intensity in {"NORMAL", "STRONG"}
        and entry_structure.entry_confirmed
        and abs(safe_float(entry_structure.components.get("structure_change_oi"), 0.0)) >= STRUCTURE_CHANGE_OI_STRONG
    )
    required_persistence, persistence_policy_reason = entry_persistence_policy(
        direction=entry_structure.direction,
        market_phase=persistence_phase,
        entry_confirmed=entry_structure.entry_confirmed,
        previous_direction=previous_direction,
        local_event_entry=local_event_entry,
        exhaustion_entry=exhaustion_entry,
        opening_fast_track=opening_fast_track,
    )
    persistence_ok, persistence_count = update_continuation_persistence(
        state,
        persistence_phase,
        latest_completed_3m_bar=latest_completed_bar,
        required_confirmations=required_persistence,
    )
    logger.info(
        "STRUCTURAL ENTRY CHECK: phase=%s persistence=%d/%d policy=%s support=%.2f resistance=%.2f "
        "ChangeOI=%+.3f VWAP=%.2f; regime=%s/%s prior_direction=%s.",
        persistence_phase,
        persistence_count,
        required_persistence,
        persistence_policy_reason,
        entry_structure.support_1,
        entry_structure.resistance_1,
        flow_value,
        entry_structure.vwap,
        regime_direction,
        intensity,
        previous_direction or "NONE",
    )
    if not persistence_ok:
        logger.info(
            "No entry: %s; requires %d distinct completed-bar confirmation(s), got %d.",
            persistence_policy_reason, max(required_persistence, 1), persistence_count,
        )
        save_state(state)
        return None
    local_event_kind = str(local_structure_event.get("kind", "")).upper() if local_event_entry else ""
    timing_state = (
        "CONFIRMED_EXHAUSTION_REVERSAL" if exhaustion_entry
        else "CONFIRMED_LOCAL_OI_REJECTION" if local_event_kind in {"RESISTANCE_REJECTION", "SUPPORT_BOUNCE"}
        else "CONFIRMED_LOCAL_OI_BREAK" if local_event_entry
        else "STRUCTURAL_CONTINUATION"
    )

    try:
        target_u1, target_u2, stop_u, level_meta = determine_structural_trade_levels(
            chain,
            spot,
            entry_structure,
            index_session,
            change_oi_by_strike=option_flow_by_strike,
        )
    except ScannerError as exc:
        logger.warning("NO TRADE: current ATM-window PA/OI targets or structural stop are invalid: %s", exc)
        save_state(state)
        return None

    logger.info(
        "ENTRY PA/OI LEVELS: T1=%.2f(%s) T2=%.2f(%s) SL=%.2f(%s)",
        target_u1, level_meta.get("t1_source", ""),
        target_u2, level_meta.get("t2_source", ""),
        stop_u, level_meta.get("sl_source", ""),
    )
    rr_ratio, structural_reward, structural_risk = structural_reward_risk_ratio(
        regime_direction, float(spot), float(target_u1), float(stop_u)
    )
    local_event_kind = str(local_structure_event.get("kind", "")).upper() if local_event_entry else ""
    logger.info(
        "STRUCTURAL ENTRY RISK CHECK: direction=%s event=%s reward=%.2f risk=%.2f R/R=%.2f required>=%.2f T1=%.2f SL=%.2f",
        regime_direction, local_event_kind or "CONTINUATION", structural_reward, structural_risk,
        rr_ratio, MIN_STRUCTURAL_ENTRY_REWARD_RISK_RATIO, target_u1, stop_u,
    )
    if (not math.isfinite(rr_ratio) or structural_reward <= 0 or structural_risk <= 0
            or rr_ratio < MIN_STRUCTURAL_ENTRY_REWARD_RISK_RATIO):
        logger.warning(
            "NO TRADE: structural reward/risk is insufficient or invalid; direction=%s event=%s R/R=%.2f required>=%.2f.",
            regime_direction, local_event_kind or "CONTINUATION", rr_ratio,
            MIN_STRUCTURAL_ENTRY_REWARD_RISK_RATIO,
        )
        save_state(state)
        return None

    # A fixed distance veto remains for ordinary continuation setups. Only an
    # actual completed-bar break or wall rejection/bounce that has already passed
    # the nearest-wall target and structural R/R checks may bypass it.
    local_break_risk_valid = bool(local_event_entry and local_event_kind in {"BREAKDOWN", "BREAKOUT"})
    local_rejection_risk_valid = bool(local_event_entry and local_event_kind in {"RESISTANCE_REJECTION", "SUPPORT_BOUNCE"})
    strike_step_for_gate = strike_step(sorted(chain_rows(option_chain_atm_window(chain, spot)[0])))
    guard_support = target_u1 if regime_direction == "BEARISH" else entry_structure.support_1
    guard_resistance = target_u1 if regime_direction == "BULLISH" else entry_structure.resistance_1
    wall_veto = opposing_oi_wall_veto(
        regime_direction, spot, guard_support, guard_resistance,
        strike_step_for_gate,
        confirmed_local_break=local_break_risk_valid,
        confirmed_local_rejection=local_rejection_risk_valid,
    )
    if wall_veto:
        logger.warning("NO TRADE: %s; nearest structural target/stop were validated, but runway remains insufficient without a confirmed matching local event.", wall_veto)
        return None

    option = generate_signals(
        state=state, chain=chain, spot=spot, regime_direction=regime_direction,
        intensity=intensity, is_expiry_day=is_expiry_day, entry_structure=entry_structure,
        option_flow_by_strike=option_flow_by_strike, oi_velocity_by_strike=oi_velocity_by_strike,
    )
    if option is None:
        return None
    target1, target2, stop_loss = target_u1, target_u2, stop_u
    underlying_stop, underlying_target1, underlying_target2 = stop_u, target_u1, target_u2

    setup_label = (
        "CONFIRMED EXHAUSTION COUNTER-TREND SCALP" if exhaustion_entry
        else f"CONFIRMED LOCAL OI {local_event_kind}" if local_event_entry
        else "STRUCTURAL CONTINUATION ENTRY"
    )
    reasons = list(entry_structure.reasons)
    reasons.extend([
        f"Setup type: {setup_label}.",
        f"Entry timing: {timing_state}; index VWAP distance={vwap_distance_atr:.2f} ATR; latest 3m move={latest_3m_move_atr:.2f} ATR; completed index 3m bars={completed_session_bars}.",
        f"Regime matrix: {regime_direction}/{intensity}; ADX={adx_value:.2f}; RSI3m={safe_float(market_regime.get('rsi_3m'), float('nan')):.2f}; time window={tod_window}; {market_regime.get('reason', '')}.",
        f"Permitted strikes={permitted_strikes_for_regime(nearest_strike(spot, sorted(chain_rows(chain))), strike_step(sorted(chain_rows(chain))), regime_direction, intensity, is_expiry_day=is_expiry_day, now=now_ist())}.",
        f"Index spot used for option ATM selection={spot:.2f}; futures LTP={futures_ltp_now:.2f}; futures/index basis={futures_ltp_now - spot:+.2f}; futures quote status={futures_quote_status}; contract={future.trading_symbol} expiry={future.expiry}.",
        f"Selected option metrics: LTP={option.ltp:.2f}, premium VWAP={option.premium_vwap:.2f}, spread={option.spread_pct:.2%}, theta burden={option.theta_burden_pct_day:.2%}/day, volume={option.volume:.0f}, OI={option.oi:.0f}, delta={option.delta:.3f}, flow={option.flow_score:.3f}, VWAP={option.vwap_score:.3f}, COI matrix={option.coi_matrix_label} score={option.oi_momentum_score:+.3f} (push={option.coi_push_score:.3f}, floor={option.coi_floor_score:.3f}, roll={option.coi_roll_score:.3f}, wall penalty={option.coi_wall_penalty:.3f}), call COI={option.call_oi_change_pct_15m:+.2f}%, put COI={option.put_oi_change_pct_15m:+.2f}% (baseline {option.oi_velocity_baseline_minutes:.1f}m, mode={option.coi_baseline_mode}).",
        f"PA/OI structural levels: NIFTY T1={underlying_target1:.2f}, T2={underlying_target2:.2f}, SL={underlying_stop:.2f}; option exit uses live LTP at the structural trigger.",
        "Primary entry alignment: NIFTY price vs VWAP + structural support/resistance + confirming Change-OI.",
        "Futures price/OI and PCR are context only; they do not override the PA/VWAP/Change-OI market structure.",
    ])

    return Signal(
        timestamp=now_ist().strftime("%Y-%m-%d %H:%M:%S IST"),
        direction=entry_structure.direction,
        regime=f"{entry_structure.interpretation} | {regime_direction}/{intensity} | ADX={adx_value:.2f}",
        market_state=entry_structure.market_phase,
        bias="Bullish" if entry_structure.direction == "BULLISH" else "Bearish",
        entry_trigger=entry_structure.entry_trigger,
        invalidation_rule=entry_structure.invalidation_rule,
        confidence=entry_structure.confidence,
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
        theta=option.theta,
        support_1=entry_structure.support_1,
        support_2=entry_structure.support_2,
        resistance_1=entry_structure.resistance_1,
        resistance_2=entry_structure.resistance_2,
        reasons=reasons,
        market_intensity=intensity,
    )

def dispatch_alerts(state: dict[str, Any], signal: Signal) -> None:
    """Persist the signal lock and active-trade record, then print/email alerts."""
    active_trade = {
        "status": "ACTIVE",
        "trade_date": now_ist().date().isoformat(),
        "opened_at": signal.timestamp,
        "direction": signal.direction,
        "regime": signal.regime,
        "market_intensity": signal.market_intensity,
        "confidence": signal.confidence,
        "instrument_key": signal.instrument_key,
        "trading_symbol": signal.trading_symbol,
        "option_type": signal.option_type,
        "strike": signal.strike,
        "entry": signal.entry,
        "entry_underlying": signal.spot,
        "t1_hit": False,
        "t1_hit_at": "",
        "post_t1_dynamic_stop": None,
        "post_t1_dynamic_stop_source": "",
        "post_t1_dynamic_stop_updated_at": "",
        "target_1": signal.target_1,
        "target_2": signal.target_2,
        "stop_loss": signal.stop_loss,
        "underlying_stop": signal.underlying_stop,
        "underlying_target_1": signal.underlying_target_1,
        "underlying_target_2": signal.underlying_target_2,
        "delta": signal.delta,
        "theta": signal.theta,
        "target_engine_version": OPTION_TARGET_ENGINE_VERSION,
        "reversal_confirmations": 0,
        "market_alignment_failures": 0,
        "last_market_direction": signal.direction,
        "last_market_confidence": signal.confidence,
        "last_ltp": signal.entry,
        "entry_3m_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
        "underlying_stop_armed_bar": str((state.get("market_snapshot") or {}).get("latest_completed_3m_bar", "")),
        "intrabar_last_checked_at": signal.timestamp,
    }

    state["active_trade"] = ActiveTradeState.from_mapping(active_trade).to_mapping()
    state["last_signal"] = asdict(signal)
    state["last_signal_hash"] = signal_hash(signal)
    state["last_signal_timestamp"] = signal.timestamp
    save_state(state)

    print(format_engine_output(signal))

    send_email(
        f"NIFTY {signal.direction} {signal.trading_symbol}",
        signal_email_body(signal),
    )

    logger.info(
        "NEW SIGNAL LOCKED: %s | entry_option=%.2f NIFTY_T1=%.2f NIFTY_T2=%.2f NIFTY_SL=%.2f",
        signal.trading_symbol,
        signal.entry,
        signal.underlying_target_1,
        signal.underlying_target_2,
        signal.underlying_stop,
    )


def run_self_tests() -> None:
    """Run deterministic V45 smoke/regression checks without network access."""
    self_test_flow = max(STRUCTURE_CHANGE_OI_CONFIRM, 0.25) + 0.05
    scenarios = [
        ("BULLISH", "CONTINUOUS_BULLISH", 101.0, 100.0, 100.8, 0.8, self_test_flow, True, "NONE", False),
        ("BEARISH", "CONTINUOUS_BEARISH", 99.0, 100.0, 99.2, -0.8, -self_test_flow, True, "NONE", False),
    ]
    for (direction, phase, spot_value, vwap_value, close_value, slope, flow,
         entry_confirmed, divergence, near_level) in scenarios:
        ok, why = structural_direction_override_decision(
            direction=direction, structure_phase=phase, entry_confirmed=entry_confirmed,
            spot=spot_value, vwap=vwap_value, last_completed_close=close_value,
            atr=2.0, vwap_slope=slope, change_oi=flow,
            divergence=divergence, near_structural_level=near_level,
        )
        assert ok, f"{direction} aligned structural override failed: {why}"

    ok, why = structural_direction_override_decision(
        direction="BULLISH", structure_phase="CONTINUOUS_BULLISH", entry_confirmed=True,
        spot=101.0, vwap=100.0, last_completed_close=100.8, atr=2.0,
        vwap_slope=-0.2, change_oi=self_test_flow,
    )
    assert not ok, f"Opposing VWAP slope was incorrectly accepted: {why}"

    ok, why = structural_direction_override_decision(
        direction="BULLISH", structure_phase="CONTINUOUS_BULLISH", entry_confirmed=True,
        spot=101.0, vwap=100.0, last_completed_close=100.8, atr=2.0,
        vwap_slope=0.2, change_oi=self_test_flow,
        divergence="BEARISH", near_structural_level=True,
    )
    assert not ok, f"Opposing confirmed divergence was incorrectly accepted: {why}"

    bullish_strikes = permitted_strikes_for_regime(
        22800.0, 50.0, "BULLISH", "NORMAL", now=datetime(2026, 10, 15, 10, 0, tzinfo=IST),
    )
    bearish_strikes = permitted_strikes_for_regime(
        22800.0, 50.0, "BEARISH", "NORMAL", now=datetime(2026, 10, 15, 10, 0, tzinfo=IST),
    )
    assert bullish_strikes == [22750.0, 22800.0], bullish_strikes
    assert bearish_strikes == [22800.0, 22850.0], bearish_strikes
    assert not permitted_strikes_for_regime(
        22800.0, 50.0, "BULLISH", "SIDEWAYS", now=datetime(2026, 10, 15, 10, 0, tzinfo=IST),
    )

    assert cold_start_entry_gate_passed(
        current_time=time(9, 30), volume_confirmed=False, directional_break=False,
        opening_tape_aligned=False, local_event_entry=True,
        confirmed_local_event_override=True,
    )
    assert not cold_start_entry_gate_passed(
        current_time=time(9, 30), volume_confirmed=False, directional_break=False,
        opening_tape_aligned=False, local_event_entry=False,
        confirmed_local_event_override=False,
    )

    rr, reward, risk = structural_reward_risk_ratio("BULLISH", 100.0, 103.0, 98.0)
    assert abs(rr - 1.5) < 1e-9 and reward == 3.0 and risk == 2.0, (rr, reward, risk)

    persistence_state: dict[str, Any] = {}
    first_ready, first_count = update_continuation_persistence(
        persistence_state, "CONTINUOUS_BULLISH", "2026-10-15T04:24:00Z", required_confirmations=2,
    )
    same_ready, same_count = update_continuation_persistence(
        persistence_state, "CONTINUOUS_BULLISH", "2026-10-15T04:24:00Z", required_confirmations=2,
    )
    second_ready, second_count = update_continuation_persistence(
        persistence_state, "CONTINUOUS_BULLISH", "2026-10-15T04:27:00Z", required_confirmations=2,
    )
    assert (first_ready, first_count) == (False, 1)
    assert (same_ready, same_count) == (False, 1), (same_ready, same_count)
    assert (second_ready, second_count) == (True, 2), (second_ready, second_count)

    # PA/OI-confirmed continuation must not be delayed by a duplicate midday gate.
    assert entry_persistence_policy(
        direction="BULLISH", market_phase="CONTINUOUS_BULLISH", entry_confirmed=True,
        previous_direction="BULLISH",
    )[0] == 1
    assert entry_persistence_policy(
        direction="BULLISH", market_phase="CONTINUOUS_BULLISH", entry_confirmed=True,
        previous_direction=None,
    )[0] == 1
    # A non-event direction flip and counter-trend exhaustion still use two distinct bars.
    assert entry_persistence_policy(
        direction="BEARISH", market_phase="CONTINUOUS_BEARISH", entry_confirmed=True,
        previous_direction="BULLISH",
    )[0] >= 2
    assert entry_persistence_policy(
        direction="BULLISH", market_phase="EXHAUSTION_BULLISH", entry_confirmed=True,
        previous_direction="BEARISH", exhaustion_entry=True,
    )[0] >= 2
    assert entry_persistence_policy(
        direction="BEARISH", market_phase="CONTINUOUS_BEARISH", entry_confirmed=True,
        previous_direction="BULLISH", local_event_entry=True,
    )[0] == 1

    print("V45 SELF-TEST PASSED.")


def main() -> int:
    logger.info("NIFTY SCANNER VERSION: %s", SCANNER_VERSION)
    logger.info("RUNNING SOURCE FILE: %s", Path(__file__).resolve())
    logger.info("STATE STORE: %s (exists=%s)", STATE_FILE, STATE_FILE.exists())

    if "--self-test" in sys.argv:
        try:
            run_self_tests()
            return 0
        except Exception:
            logger.error("V45 self-test failed:\n%s", traceback.format_exc())
            return 1

    try:
        state = load_state()
        signal = execute_scan(state)

        if signal is None:
            logger.info("No actionable setup on this scan.")
            return 0

        dispatch_alerts(state, signal)
        return 0

    except ScannerError as exc:
        logger.error("Scanner error: %s", exc)
        return 1
    except Exception:
        logger.error("Fatal scanner failure:\n%s", traceback.format_exc())
        return 1


if __name__ == "__main__":
    sys.exit(main())
