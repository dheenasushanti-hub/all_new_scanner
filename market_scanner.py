#!/usr/bin/env python3
"""Self-contained NIFTY 50 OI + market-structure scanner v101.0.0.

Deployment model: GitHub Actions runs this one file every ~3 minutes.
Regression tests and documentation are separate and are not embedded here.
This file is consolidated from the tested v101 modules to remove the runtime
requirement for the custom src/nifty_scanner package. It still requires requests.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import logging
import math
import os
import random
import smtplib
import ssl
import sys
import time as time_module
import urllib.error
import urllib.request
from collections import defaultdict
from contextlib import contextmanager
from dataclasses import asdict, dataclass, field, replace
from datetime import date, datetime, time as datetime_time, timedelta
from email.message import EmailMessage
from email.utils import parsedate_to_datetime
from enum import Enum
from math import isfinite, tanh
from pathlib import Path
from statistics import fmean
from typing import Any, Iterator, Optional, Sequence
from urllib.parse import quote as url_quote
from zoneinfo import ZoneInfo

import requests


# Compatibility alias for patching/testing the retry sleep dependency.
time = time_module


# ===== Inlined module: models.py =====

"""Typed domain models for the clean-slate NIFTY OI scanner."""









class Direction(str, Enum):
    BULLISH = "BULLISH"
    BEARISH = "BEARISH"
    MIXED = "MIXED"
    UNKNOWN = "UNKNOWN"


class Regime(str, Enum):
    CONTINUOUS_BULLISH = "CONTINUOUS_BULLISH"
    CONTINUOUS_BEARISH = "CONTINUOUS_BEARISH"
    REVERSAL_BEAR_TO_BULL = "REVERSAL_BEAR_TO_BULL"
    REVERSAL_BULL_TO_BEAR = "REVERSAL_BULL_TO_BEAR"
    SIDEWAYS = "SIDEWAYS"
    TRANSITION = "TRANSITION"
    UNKNOWN = "UNKNOWN"


class SetupKind(str, Enum):
    SUPPORT_BOUNCE = "SUPPORT_BOUNCE"
    RESISTANCE_REJECTION = "RESISTANCE_REJECTION"
    TREND_PULLBACK = "TREND_PULLBACK"
    BREAKOUT_RETEST = "BREAKOUT_RETEST"
    BREAKDOWN_RETEST = "BREAKDOWN_RETEST"
    LIQUIDITY_SWEEP_RECLAIM = "LIQUIDITY_SWEEP_RECLAIM"
    RANGE_EDGE_REVERSAL = "RANGE_EDGE_REVERSAL"


@dataclass(frozen=True)
class Candle:
    start: datetime
    open: float
    high: float
    low: float
    close: float
    volume: float = 0.0
    oi: float = 0.0

    def __post_init__(self) -> None:
        if self.start.tzinfo is None or self.start.utcoffset() is None:
            raise ValueError("Candle timestamp must be timezone-aware")
        values = (self.open, self.high, self.low, self.close, self.volume, self.oi)
        if not all(math.isfinite(float(v)) for v in values):
            raise ValueError("Candle values must be finite")
        if self.low > min(self.open, self.close, self.high) or self.high < max(self.open, self.close, self.low):
            raise ValueError("Invalid OHLC ordering")
        if self.volume < 0 or self.oi < 0:
            raise ValueError("Candle volume and OI cannot be negative")


@dataclass(frozen=True)
class Greeks:
    delta: Optional[float] = None
    gamma: Optional[float] = None
    theta: Optional[float] = None
    vega: Optional[float] = None
    iv: Optional[float] = None


@dataclass(frozen=True)
class OptionQuote:
    instrument_key: str
    expiry: date
    strike: float
    side: str  # CE or PE
    ltp: float
    bid: float
    ask: float
    bid_qty: float
    ask_qty: float
    volume: float
    oi: float
    greeks: Greeks = field(default_factory=Greeks)
    quote_time: Optional[datetime] = None
    previous_session_oi: Optional[float] = None

    def __post_init__(self) -> None:
        if self.side not in {"CE", "PE"}:
            raise ValueError("Option side must be CE or PE")
        for value in (self.strike, self.ltp, self.bid, self.ask, self.bid_qty, self.ask_qty, self.volume, self.oi):
            if not math.isfinite(float(value)):
                raise ValueError("Option quote values must be finite")
        if self.strike <= 0 or min(self.ltp, self.bid, self.ask, self.bid_qty, self.ask_qty, self.volume, self.oi) < 0:
            raise ValueError("Option quote contains negative or zero-invalid values")
        if self.previous_session_oi is not None and (not math.isfinite(float(self.previous_session_oi)) or self.previous_session_oi < 0):
            raise ValueError("Previous-session OI must be finite and nonnegative")
        if self.quote_time is not None and (self.quote_time.tzinfo is None or self.quote_time.utcoffset() is None):
            raise ValueError("Option quote timestamp must be timezone-aware")

    @property
    def mid(self) -> float:
        if self.bid > 0 and self.ask > 0 and self.ask >= self.bid:
            return (self.bid + self.ask) / 2.0
        return self.ltp

    @property
    def spread(self) -> float:
        return self.ask - self.bid if self.bid > 0 and self.ask > 0 else float("inf")

    @property
    def spread_pct(self) -> float:
        mid = self.mid
        return self.spread / mid * 100.0 if mid > 0 and math.isfinite(self.spread) else float("inf")


@dataclass(frozen=True)
class ChainRow:
    strike: float
    expiry: date
    call: Optional[OptionQuote]
    put: Optional[OptionQuote]


@dataclass(frozen=True)
class ChainSnapshot:
    fetched_at: datetime
    session_date: date
    underlying_key: str
    expiry: date
    spot: float
    rows: tuple[ChainRow, ...]
    source_event_time: Optional[datetime] = None

    def __post_init__(self) -> None:
        if self.fetched_at.tzinfo is None or self.fetched_at.utcoffset() is None:
            raise ValueError("Snapshot fetched_at must be timezone-aware")
        if self.source_event_time is not None and (self.source_event_time.tzinfo is None or self.source_event_time.utcoffset() is None):
            raise ValueError("source_event_time must be timezone-aware")
        if not math.isfinite(self.spot) or self.spot <= 0:
            raise ValueError("Snapshot spot must be a finite positive value")
        if not self.rows:
            raise ValueError("Option-chain snapshot cannot be empty")
        strikes = [row.strike for row in self.rows]
        if len(strikes) != len(set(strikes)):
            raise ValueError("Duplicate strikes in option-chain snapshot")
        if any(row.expiry != self.expiry for row in self.rows):
            raise ValueError("Mixed expiries in option-chain snapshot")
        for row in self.rows:
            for expected_side, quote in (("CE", row.call), ("PE", row.put)):
                if quote is not None and (quote.expiry != self.expiry or quote.strike != row.strike or quote.side != expected_side):
                    raise ValueError("Option quote identity does not match its chain row")


@dataclass(frozen=True)
class Instrument:
    instrument_key: str
    segment: str
    name: str
    instrument_type: str
    expiry: Optional[date] = None
    underlying_key: Optional[str] = None
    underlying_symbol: Optional[str] = None
    strike: Optional[float] = None
    lot_size: Optional[int] = None
    tick_size: Optional[float] = None
    weekly: Optional[bool] = None
    trading_symbol: Optional[str] = None


@dataclass(frozen=True)
class Quote:
    instrument_key: str
    last_price: float
    received_at: datetime
    source_time: Optional[datetime] = None
    prev_close: Optional[float] = None
    session_open: Optional[float] = None
    session_high: Optional[float] = None
    session_low: Optional[float] = None
    prev_high: Optional[float] = None
    prev_low: Optional[float] = None
    volume: Optional[float] = None
    bid: Optional[float] = None
    ask: Optional[float] = None
    bid_qty: Optional[float] = None
    ask_qty: Optional[float] = None

    def __post_init__(self) -> None:
        if not self.instrument_key:
            raise ValueError("Quote instrument_key is required")
        if self.received_at.tzinfo is None or self.received_at.utcoffset() is None:
            raise ValueError("Quote receive timestamp must be timezone-aware")
        if self.source_time is not None and (self.source_time.tzinfo is None or self.source_time.utcoffset() is None):
            raise ValueError("Quote source timestamp must be timezone-aware")
        if not math.isfinite(float(self.last_price)) or self.last_price <= 0:
            raise ValueError("Quote last_price must be finite and positive")
        for value in (self.prev_close, self.session_open, self.session_high, self.session_low, self.prev_high, self.prev_low, self.volume, self.bid, self.ask, self.bid_qty, self.ask_qty):
            if value is not None and (not math.isfinite(float(value)) or value < 0):
                raise ValueError("Optional quote fields must be finite and nonnegative")


@dataclass(frozen=True)
class OIChange:
    instrument_key: str
    strike: float
    side: str
    previous_oi: float
    current_oi: float
    delta_oi: float
    delta_pct: Optional[float]
    previous_premium: Optional[float]
    current_premium: float
    premium_delta_pct: Optional[float]
    volume_delta: Optional[float]
    material: bool
    contribution: float
    interpretation: str
    delta_oi_session: Optional[float] = None
    delta_oi_vs_prev_session: Optional[float] = None


@dataclass(frozen=True)
class OIEvidence:
    direction: Direction
    score: float
    confidence: float
    status: str
    age_seconds: float
    interval_seconds: Optional[float]
    changes: tuple[OIChange, ...]
    bullish_score: float
    bearish_score: float
    material_change_count: int
    summary: str
    raw_score: Optional[float] = None
    payload_unchanged: bool = False


@dataclass(frozen=True)
class PriceAnalysis:
    regime: Regime
    direction: Direction
    higher_timeframe_bias: Direction
    execution_structure: str
    setup: Optional[SetupKind]
    support: Optional[float]
    resistance: Optional[float]
    support_source: Optional[str]
    resistance_source: Optional[str]
    atr: Optional[float]
    return_1m: Optional[float]
    return_3m: Optional[float]
    return_5m: Optional[float]
    return_15m: Optional[float]
    trigger_price: Optional[float]
    invalidation_price: Optional[float]
    structure_confidence: float
    reasons: tuple[str, ...]
    levels_above: tuple[Level, ...] = ()
    levels_below: tuple[Level, ...] = ()
    recent_setups: tuple[dict[str, Any], ...] = ()


@dataclass(frozen=True)
class RiskPlan:
    direction: Direction
    entry_underlying: float
    stop_underlying: float
    target1_underlying: float
    target2_underlying: Optional[float]
    risk_points: float
    reward1_points: float
    reward2_points: Optional[float]
    rr1: float
    rr2: Optional[float]
    stop_source: str
    target1_source: str
    target2_source: Optional[str]


@dataclass(frozen=True)
class OptionRisk:
    entry_ask: float
    stop_exit_estimate: float
    target1_exit_estimate: float
    target2_exit_estimate: Optional[float]
    net_risk_per_unit: float
    net_reward1_per_unit: float
    net_reward2_per_unit: Optional[float]
    net_rr1: float
    net_rr2: Optional[float]
    spread_pct: float
    assumptions: tuple[str, ...]


@dataclass(frozen=True)
class ScanResult:
    timestamp: datetime
    session_date: date
    decision: str
    reason_code: str
    reason: str
    oi: OIEvidence
    price: PriceAnalysis
    risk: Optional[RiskPlan] = None
    selected_option: Optional[OptionQuote] = None
    option_risk: Optional[OptionRisk] = None
    expiry: Optional[date] = None
    atm_strike: Optional[float] = None
    strike_offset: Optional[int] = None
    signal_key: Optional[str] = None
    notification_status: str = "NOT_CONFIGURED"
    diagnostics: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        """Return a compact, safe operational record, never the full option chain."""
        def convert(obj: Any) -> Any:
            if isinstance(obj, Enum):
                return obj.value
            if isinstance(obj, (datetime, date)):
                return obj.isoformat()
            if hasattr(obj, "__dataclass_fields__"):
                return {k: convert(v) for k, v in asdict(obj).items()}
            if isinstance(obj, dict):
                return {str(k): convert(v) for k, v in obj.items()}
            if isinstance(obj, (list, tuple)):
                return [convert(v) for v in obj]
            return obj
        top_changes = sorted(self.oi.changes, key=lambda x: abs(x.contribution), reverse=True)[:3]
        price = {
            "regime": self.price.regime, "direction": self.price.direction,
            "higher_timeframe_bias": self.price.higher_timeframe_bias,
            "execution_structure": self.price.execution_structure,
            "setup": self.price.setup, "support": self.price.support,
            "resistance": self.price.resistance, "support_source": self.price.support_source,
            "resistance_source": self.price.resistance_source, "atr": self.price.atr,
            "return_1m": self.price.return_1m, "return_3m": self.price.return_3m,
            "return_5m": self.price.return_5m, "return_15m": self.price.return_15m,
            "trigger_price": self.price.trigger_price, "invalidation_price": self.price.invalidation_price,
            "structure_confidence": self.price.structure_confidence, "reasons": self.price.reasons,
            "nearest_levels_above": self.price.levels_above[:3],
            "nearest_levels_below": self.price.levels_below[:3],
            "recent_confirmed_setups": self.price.recent_setups,
        }
        oi = {
            "direction": self.oi.direction, "score": self.oi.score, "confidence": self.oi.confidence,
            "status": self.oi.status, "age_seconds": self.oi.age_seconds,
            "interval_seconds": self.oi.interval_seconds, "bullish_score": self.oi.bullish_score,
            "bearish_score": self.oi.bearish_score, "material_change_count": self.oi.material_change_count,
            "summary": self.oi.summary, "payload_unchanged": self.oi.payload_unchanged,
            "top_evidence": [{"strike": x.strike, "side": x.side, "delta_oi": x.delta_oi,
                              "delta_pct": x.delta_pct, "premium_delta_pct": x.premium_delta_pct,
                              "material": x.material, "contribution": x.contribution,
                              "interpretation": x.interpretation, "delta_oi_session": x.delta_oi_session,
                              "delta_oi_vs_prev_session": x.delta_oi_vs_prev_session} for x in top_changes],
        }
        return {
            "timestamp": convert(self.timestamp), "session_date": convert(self.session_date),
            "scanner_version": "101.0.0", "decision": self.decision, "reason_code": self.reason_code,
            "reason": self.reason, "expiry": convert(self.expiry), "oi": convert(oi),
            "price": convert(price), "risk": convert(self.risk),
            "selected_option": convert({"instrument_key": self.selected_option.instrument_key,
                "expiry": self.selected_option.expiry, "strike": self.selected_option.strike,
                "side": self.selected_option.side, "ltp": self.selected_option.ltp,
                "bid": self.selected_option.bid, "ask": self.selected_option.ask,
                "bid_qty": self.selected_option.bid_qty, "ask_qty": self.selected_option.ask_qty,
                "volume": self.selected_option.volume, "oi": self.selected_option.oi,
                "greeks": self.selected_option.greeks} if self.selected_option else None),
            "option_risk": convert(self.option_risk), "atm_strike": self.atm_strike,
            "strike_offset": self.strike_offset, "signal_key": self.signal_key,
            "notification_status": self.notification_status, "diagnostics": convert(self.diagnostics),
        }

@dataclass(frozen=True)
class Level:
    price: float
    kind: str
    source: str
    strength: float = 1.0
    observed_at: Optional[datetime] = None


# ===== Inlined module: config.py =====

"""Single source of truth for scanner settings and environment configuration."""









@dataclass(frozen=True)
class Settings:
    api_base_url: str = "https://api.upstox.com"
    analytics_token: str = field(default="", repr=False)
    underlying_query_name: str = "Nifty 50"
    configured_underlying_key: str = ""
    configured_expiry: Optional[date] = None
    force_weekly_expiry: bool = True
    timezone: str = "Asia/Kolkata"
    timeout_seconds: float = 12.0
    retry_attempts: int = 2
    candle_max_age_seconds: int = 150
    option_chain_max_age_seconds: int = 420
    max_quote_candle_divergence_atr: float = 1.8
    oi_material_pct: float = 2.0
    oi_direction_threshold: float = 0.16
    oi_neutral_band: float = 0.06
    oi_score_max_per_strike: float = 1.0
    oi_near_atm_strikes: int = 4
    oi_history_length: int = 4
    oi_fresh_interval_seconds: int = 240
    mixed_oi_min_structure_confidence: float = 0.80
    retained_oi_min_structure_confidence: float = 0.80
    swing_left_bars: int = 2
    swing_right_bars: int = 2
    recent_setup_event_bars: int = 5
    atr_period: int = 14
    opening_range_minutes: int = 15
    support_touch_atr: float = 0.22
    support_reclaim_atr: float = 0.06
    continuation_pullback_atr: float = 0.45
    max_entry_extension_atr: float = 0.9
    stop_buffer_atr: float = 0.12
    max_stop_atr: float = 2.5
    min_underlying_rr: float = 2.0
    min_option_net_rr: float = 2.0
    max_option_spread_pct: float = 2.5
    min_bid_qty: float = 1.0
    min_ask_qty: float = 1.0
    min_option_volume: float = 1.0
    max_option_quote_age_seconds: int = 420
    target2_extension_r: float = 3.0
    max_target2_atr: float = 8.0
    iv_target_shock_points: float = 2.0
    target_horizon_minutes: float = 10.0
    slippage_points_per_side: float = 1.0
    option_round_trip_cost_per_unit: float = 1.0
    state_file: Path = Path("state/market_state_v101.json")
    audit_dir: Path = Path("audit")
    instrument_cache_file: Path = Path(".cache/upstox_nse_instruments.json.gz")
    instrument_cache_ttl_seconds: int = 21600
    enable_email: bool = True
    smtp_host: str = ""
    smtp_port: int = 587
    smtp_use_ssl: bool = False
    email_sender: str = ""
    email_receiver: str = ""
    email_password: str = field(default="", repr=False)
    smtp_starttls: bool = True
    alert_webhook_url: str = ""
    alert_webhook_token: str = field(default="", repr=False)
    webhook_timeout_seconds: float = 8.0
    log_level: str = "INFO"
    refresh_option_quotes: bool = True

    @classmethod
    def from_env(cls) -> "Settings":
        def env_bool(name: str, default: bool) -> bool:
            raw = os.getenv(name)
            if raw is None or not raw.strip():
                return default
            return raw.strip().lower() in {"1", "true", "yes", "y", "on"}

        def env_int(name: str, default: int) -> int:
            raw = os.getenv(name)
            return int(raw) if raw and raw.strip() else default

        def env_float(name: str, default: float) -> float:
            raw = os.getenv(name)
            return float(raw) if raw and raw.strip() else default

        expiry_raw = os.getenv("NIFTY_EXPIRY_DATE", "").strip()
        configured_expiry = date.fromisoformat(expiry_raw) if expiry_raw else None
        token = os.getenv("UPSTOX_ANALYTICS_TOKEN", "").strip() or os.getenv("UPSTOX_ACCESS_TOKEN", "").strip()
        return cls(
            api_base_url=os.getenv("UPSTOX_API_BASE_URL", "https://api.upstox.com").rstrip("/"),
            analytics_token=token,
            underlying_query_name=os.getenv("NIFTY_UNDERLYING_NAME", "Nifty 50").strip(),
            configured_underlying_key=os.getenv("NIFTY_UNDERLYING_KEY", "").strip(),
            configured_expiry=configured_expiry,
            force_weekly_expiry=env_bool("NIFTY_FORCE_WEEKLY_EXPIRY", True),
            timeout_seconds=env_float("UPSTOX_TIMEOUT_SECONDS", 12.0),
            retry_attempts=env_int("UPSTOX_RETRY_ATTEMPTS", 2),
            candle_max_age_seconds=env_int("CANDLE_MAX_AGE_SECONDS", 150),
            option_chain_max_age_seconds=env_int("OPTION_CHAIN_MAX_AGE_SECONDS", 420),
            max_quote_candle_divergence_atr=env_float("MAX_QUOTE_CANDLE_DIVERGENCE_ATR", 1.8),
            oi_material_pct=env_float("OI_MATERIAL_PCT", 2.0),
            oi_direction_threshold=env_float("OI_DIRECTION_THRESHOLD", 0.16),
            oi_neutral_band=env_float("OI_NEUTRAL_BAND", 0.06),
            oi_near_atm_strikes=env_int("OI_NEAR_ATM_STRIKES", 4),
            oi_history_length=env_int("OI_HISTORY_LENGTH", 4),
            oi_fresh_interval_seconds=env_int("OI_FRESH_INTERVAL_SECONDS", 240),
            mixed_oi_min_structure_confidence=env_float("MIXED_OI_MIN_STRUCTURE_CONFIDENCE", 0.80),
            retained_oi_min_structure_confidence=env_float("RETAINED_OI_MIN_STRUCTURE_CONFIDENCE", 0.80),
            swing_left_bars=env_int("SWING_LEFT_BARS", 2),
            swing_right_bars=env_int("SWING_RIGHT_BARS", 2),
            recent_setup_event_bars=env_int("RECENT_SETUP_EVENT_BARS", 5),
            atr_period=env_int("ATR_PERIOD", 14),
            opening_range_minutes=env_int("OPENING_RANGE_MINUTES", 15),
            support_touch_atr=env_float("SUPPORT_TOUCH_ATR", 0.22),
            support_reclaim_atr=env_float("SUPPORT_RECLAIM_ATR", 0.06),
            continuation_pullback_atr=env_float("CONTINUATION_PULLBACK_ATR", 0.45),
            max_entry_extension_atr=env_float("MAX_ENTRY_EXTENSION_ATR", 0.9),
            stop_buffer_atr=env_float("STOP_BUFFER_ATR", 0.12),
            max_stop_atr=env_float("MAX_STOP_ATR", 2.5),
            min_underlying_rr=env_float("MIN_UNDERLYING_RR", 2.0),
            min_option_net_rr=env_float("MIN_OPTION_NET_RR", 2.0),
            max_option_spread_pct=env_float("MAX_OPTION_SPREAD_PCT", 2.5),
            min_bid_qty=env_float("MIN_OPTION_BID_QTY", 1.0),
            min_ask_qty=env_float("MIN_OPTION_ASK_QTY", 1.0),
            min_option_volume=env_float("MIN_OPTION_VOLUME", 1.0),
            max_option_quote_age_seconds=env_int("MAX_OPTION_QUOTE_AGE_SECONDS", 420),
            target2_extension_r=env_float("TARGET2_EXTENSION_R", 3.0),
            max_target2_atr=env_float("MAX_TARGET2_ATR", 8.0),
            iv_target_shock_points=env_float("IV_TARGET_SHOCK_POINTS", 2.0),
            target_horizon_minutes=env_float("TARGET_HORIZON_MINUTES", 10.0),
            slippage_points_per_side=env_float("SLIPPAGE_POINTS_PER_SIDE", 1.0),
            option_round_trip_cost_per_unit=env_float("OPTION_ROUND_TRIP_COST_PER_UNIT", 1.0),
            state_file=Path(os.getenv("STATE_FILE", "state/market_state_v101.json")),
            audit_dir=Path(os.getenv("AUDIT_DIR", "audit")),
            instrument_cache_file=Path(os.getenv("INSTRUMENT_CACHE_FILE", ".cache/upstox_nse_instruments.json.gz")),
            instrument_cache_ttl_seconds=env_int("INSTRUMENT_CACHE_TTL_SECONDS", 21600),
            enable_email=env_bool("ENABLE_EMAIL", True),
            smtp_host=os.getenv("SMTP_HOST", "").strip(),
            smtp_port=env_int("SMTP_PORT", 587),
            smtp_use_ssl=env_bool("SMTP_USE_SSL", False),
            email_sender=os.getenv("EMAIL_SENDER", "").strip() or os.getenv("EMAIL_FROM", "").strip(),
            email_receiver=os.getenv("EMAIL_RECEIVER", "").strip() or os.getenv("EMAIL_TO", "").strip(),
            email_password=os.getenv("EMAIL_PASSWORD", "").strip(),
            smtp_starttls=env_bool("SMTP_STARTTLS", True),
            alert_webhook_url=os.getenv("ALERT_WEBHOOK_URL", "").strip(),
            alert_webhook_token=os.getenv("ALERT_WEBHOOK_TOKEN", "").strip(),
            webhook_timeout_seconds=env_float("WEBHOOK_TIMEOUT_SECONDS", 8.0),
            log_level=os.getenv("LOG_LEVEL", "INFO").upper(),
            refresh_option_quotes=env_bool("REFRESH_OPTION_QUOTES", True),
        )

    def validate(self) -> list[str]:
        errors: list[str] = []
        if not self.analytics_token:
            errors.append("UPSTOX_ANALYTICS_TOKEN (or UPSTOX_ACCESS_TOKEN) is required")
        for name in ("oi_material_pct", "min_underlying_rr", "min_option_net_rr", "max_stop_atr", "timeout_seconds"):
            if getattr(self, name) <= 0:
                errors.append(f"{name} must be positive")
        if self.oi_material_pct != 2.0 and not (0 < self.oi_material_pct <= 20):
            errors.append("oi_material_pct must be in (0, 20]; default is 2.0")
        if self.smtp_host and not (self.email_sender and self.email_receiver):
            errors.append("SMTP_HOST requires EMAIL_SENDER and EMAIL_RECEIVER")
        if not (0.0 <= self.oi_neutral_band < self.oi_direction_threshold <= 1.0):
            errors.append("OI score thresholds are inconsistent")
        for name in ("mixed_oi_min_structure_confidence", "retained_oi_min_structure_confidence"):
            value = getattr(self, name)
            if not 0 <= value <= 1:
                errors.append(f"{name} must be between 0 and 1")
        if self.recent_setup_event_bars < 1 or self.recent_setup_event_bars > 8:
            errors.append("recent_setup_event_bars must be between 1 and 8")
        if self.oi_fresh_interval_seconds <= 0 or self.option_chain_max_age_seconds < self.oi_fresh_interval_seconds:
            errors.append("OI freshness interval must be positive and no greater than option-chain max age")
        return errors


# ===== Inlined module: state_store.py =====

"""Locked, atomic and schema-versioned durable state storage for ephemeral runners."""










try:
    import fcntl
except ImportError:  # pragma: no cover - target deployment is GitHub's Linux runner
    fcntl = None

SCHEMA_VERSION = 101


class StateError(RuntimeError):
    pass


def empty_state(session_date: str) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "scanner_version": "101.0.0",
        "session_date": session_date,
        "previous_chain": None,
        "first_session_chain": None,
        "oi_score_history": [],
        "last_oi_evidence": None,
        "last_processed_candle": None,
        "setup_states": {},
        "notification_events": {},
        "last_scan_at": None,
        "migration_notes": [],
    }


class StateStore:
    def __init__(self, path: Path, lock_timeout_seconds: float = 20.0):
        self.path = path
        self.lock_path = path.with_suffix(path.suffix + ".lock")
        self.lock_timeout_seconds = lock_timeout_seconds
        self._handle = None

    @contextmanager
    def lock(self) -> Iterator[None]:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._handle = open(self.lock_path, "a+b")
        if fcntl is not None:
            import time as time_module
            deadline = time_module.monotonic() + self.lock_timeout_seconds
            while True:
                try:
                    fcntl.flock(self._handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if time_module.monotonic() >= deadline:
                        self._handle.close()
                        self._handle = None
                        raise StateError("STATE_LOCK_TIMEOUT")
                    time_module.sleep(0.2)
        try:
            yield
        finally:
            if self._handle is not None:
                if fcntl is not None:
                    fcntl.flock(self._handle.fileno(), fcntl.LOCK_UN)
                self._handle.close()
                self._handle = None

    def load(self, session_date: str) -> dict[str, Any]:
        if not self.path.exists():
            return empty_state(session_date)
        try:
            state = json.loads(self.path.read_text(encoding="utf-8"))
        except Exception as exc:
            backup = self.path.with_suffix(self.path.suffix + f".corrupt-{int(time_module.time())}.bak")
            try:
                self.path.replace(backup)
            except OSError:
                raise StateError(f"STATE_CORRUPT_AND_BACKUP_FAILED: {exc}") from exc
            return empty_state(session_date)
        if not isinstance(state, dict) or state.get("schema_version") != SCHEMA_VERSION:
            backup = self.path.with_suffix(self.path.suffix + f".incompatible-{int(time_module.time())}.bak")
            try:
                self.path.replace(backup)
            except OSError as exc:
                raise StateError(f"STATE_SCHEMA_INCOMPATIBLE_AND_BACKUP_FAILED: {exc}") from exc
            new = empty_state(session_date)
            new["migration_notes"].append("Incompatible prior schema archived, not silently migrated")
            return new
        if state.get("session_date") != session_date:
            # Keep schema-compatible durable dedupe events but never use yesterday's OI baseline.
            state["session_date"] = session_date
            state["previous_chain"] = None
            state["first_session_chain"] = None
            state["oi_score_history"] = []
            state["last_oi_evidence"] = None
            state["last_processed_candle"] = None
            state["setup_states"] = {}
        for key, default in empty_state(session_date).items():
            state.setdefault(key, default)
        return state

    def save(self, state: dict[str, Any]) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        temp = self.path.with_suffix(self.path.suffix + f".{os.getpid()}.tmp")
        try:
            with open(temp, "w", encoding="utf-8") as handle:
                json.dump(state, handle, ensure_ascii=False, separators=(",", ":"), allow_nan=False)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temp, self.path)
            # Persist rename metadata when the filesystem supports directory fsync.
            try:
                directory_fd = os.open(self.path.parent, os.O_RDONLY)
                try:
                    os.fsync(directory_fd)
                finally:
                    os.close(directory_fd)
            except OSError:
                pass
        except Exception as exc:
            try:
                temp.unlink(missing_ok=True)
            except OSError:
                pass
            raise StateError(f"STATE_SAVE_FAILED: {exc}") from exc


# ===== Inlined module: notifier.py =====

"""Optional email/webhook notification adapter. This package never submits orders."""














class NotificationError(RuntimeError):
    pass


class Notifier:
    def __init__(self, settings: Settings, logger: logging.Logger | None = None):
        self.settings = settings
        self.log = logger or logging.getLogger("nifty_scanner.notifier")

    def configured(self) -> bool:
        email_ready = bool(self.settings.enable_email and self.settings.smtp_host and self.settings.email_sender and self.settings.email_receiver and self.settings.email_password)
        return email_ready or bool(self.settings.alert_webhook_url)

    def send(self, result: dict[str, Any], idempotency_key: str) -> str:
        destinations = []
        errors = []
        if self.settings.alert_webhook_url:
            try:
                self._send_webhook(result, idempotency_key)
                destinations.append("WEBHOOK")
            except Exception as exc:
                errors.append(f"WEBHOOK:{type(exc).__name__}")
        if self.settings.enable_email and all((self.settings.smtp_host, self.settings.email_sender, self.settings.email_receiver, self.settings.email_password)):
            try:
                self._send_email(result, idempotency_key)
                destinations.append("EMAIL")
            except Exception as exc:
                errors.append(f"EMAIL:{type(exc).__name__}")
        if destinations:
            status = "SENT_" + "_AND_".join(destinations)
            if errors:
                status += "_PARTIAL_FAILURE"
            return status
        if not self.configured():
            return "NOT_CONFIGURED"
        return "FAILED:" + ",".join(errors or ["NO_DESTINATION_SUCCEEDED"])

    def _send_webhook(self, result: dict[str, Any], key: str) -> None:
        headers = {"Content-Type": "application/json", "User-Agent": "Nifty-OI-Scanner/101.0.0", "X-Idempotency-Key": key}
        if self.settings.alert_webhook_token:
            headers["Authorization"] = f"Bearer {self.settings.alert_webhook_token}"
        body = json.dumps(result, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
        request = urllib.request.Request(self.settings.alert_webhook_url, data=body, headers=headers, method="POST")
        with urllib.request.urlopen(request, timeout=self.settings.webhook_timeout_seconds) as response:
            if not 200 <= response.status < 300:
                raise NotificationError(f"Webhook returned HTTP {response.status}")

    def _send_email(self, result: dict[str, Any], key: str) -> None:
        message = EmailMessage()
        message["Subject"] = f"NIFTY Scanner {result.get('decision')} — {result.get('selected_option', {}).get('side', '')} {result.get('selected_option', {}).get('strike', '')}"
        message["From"] = self.settings.email_sender
        message["To"] = self.settings.email_receiver
        message["X-Scanner-Signal-Key"] = key
        message.set_content(json.dumps(result, indent=2, ensure_ascii=False, default=str))
        context = ssl.create_default_context()
        if self.settings.smtp_use_ssl:
            with smtplib.SMTP_SSL(self.settings.smtp_host, self.settings.smtp_port, timeout=12, context=context) as server:
                server.login(self.settings.email_sender, self.settings.email_password)
                server.send_message(message)
        else:
            with smtplib.SMTP(self.settings.smtp_host, self.settings.smtp_port, timeout=12) as server:
                server.ehlo()
                if self.settings.smtp_starttls:
                    server.starttls(context=context)
                    server.ehlo()
                server.login(self.settings.email_sender, self.settings.email_password)
                server.send_message(message)


# ===== Inlined module: upstox_client.py =====

"""Upstox read-only API adapter built from current published endpoints.

No order endpoints are implemented. Analytics Token is passed as a Bearer token.
"""

IST = ZoneInfo("Asia/Kolkata")
INSTRUMENT_MASTER_URL = "https://assets.upstox.com/market-quote/instruments/exchange/NSE.json.gz"


class UpstoxError(RuntimeError):
    def __init__(self, code: str, message: str, *, status_code: Optional[int] = None, endpoint: str = ""):
        super().__init__(message)
        self.code = code
        self.status_code = status_code
        self.endpoint = endpoint


class UpstoxClient:
    def __init__(self, settings: Settings, logger: Optional[logging.Logger] = None, session: Optional[requests.Session] = None):
        self.settings = settings
        self.log = logger or logging.getLogger("nifty_scanner.upstox")
        self.session = session or requests.Session()
        self.session.headers.update({
            "Accept": "application/json",
            "Content-Type": "application/json",
            "User-Agent": "Nifty-OI-Scanner/101.0.0 (read-only market analytics)",
        })
        if settings.analytics_token:
            self.session.headers["Authorization"] = f"Bearer {settings.analytics_token}"

    def _request_json(self, method: str, url: str, *, params: Optional[dict[str, Any]] = None, auth: bool = True) -> dict[str, Any]:
        attempts = max(1, self.settings.retry_attempts + 1)
        for attempt in range(attempts):
            try:
                response = self.session.request(method, url, params=params, timeout=self.settings.timeout_seconds)
            except requests.RequestException as exc:
                if attempt + 1 < attempts:
                    time_module.sleep(min(0.5 * (2 ** attempt), 2.0))
                    continue
                raise UpstoxError("API_NETWORK_ERROR", f"Network error calling {url}: {type(exc).__name__}", endpoint=url) from exc
            if response.status_code >= 400:
                message = _safe_api_message(response)
                code = {
                    400: "API_BAD_REQUEST", 401: "API_AUTH_FAILED", 403: "API_PERMISSION_DENIED",
                    404: "API_NOT_FOUND", 408: "API_TIMEOUT", 429: "API_RATE_LIMITED",
                }.get(response.status_code, "API_HTTP_ERROR")
                retryable = response.status_code == 429 or response.status_code in {500, 502, 503, 504}
                if retryable and attempt + 1 < attempts:
                    retry_after = _retry_after(response.headers.get("Retry-After"))
                    wait = min(2.0, retry_after if retry_after is not None else 0.35 * (2 ** attempt) + random.random() * 0.15)
                    self.log.warning("Upstox transient response %s; retry %d/%d after %.2fs for %s", response.status_code, attempt + 1, attempts - 1, wait, urlparse_path(url))
                    time_module.sleep(max(0.0, wait))
                    continue
                # 400/401/403/404 are never retried; no credential or header values are logged.
                raise UpstoxError(code, f"Upstox HTTP {response.status_code} for {urlparse_path(url)}: {message}", status_code=response.status_code, endpoint=urlparse_path(url))
            try:
                payload = response.json()
            except ValueError as exc:
                raise UpstoxError("API_INVALID_JSON", f"Upstox returned non-JSON content for {urlparse_path(url)}", status_code=response.status_code, endpoint=urlparse_path(url)) from exc
            if not isinstance(payload, dict):
                raise UpstoxError("API_INVALID_SHAPE", f"Expected JSON object from {urlparse_path(url)}", endpoint=urlparse_path(url))
            if payload.get("status") == "error":
                error = payload.get("errors") or payload.get("message") or "API returned status=error"
                raise UpstoxError("API_APPLICATION_ERROR", f"Upstox application error for {urlparse_path(url)}: {error}", status_code=response.status_code, endpoint=urlparse_path(url))
            return payload
        raise UpstoxError("API_RETRY_EXHAUSTED", f"Retries exhausted for {urlparse_path(url)}", endpoint=urlparse_path(url))

    def get_instrument_master(self) -> tuple[list[dict[str, Any]], str]:
        path = self.settings.instrument_cache_file
        path.parent.mkdir(parents=True, exist_ok=True)
        now = time_module.time()
        if path.exists():
            age = now - path.stat().st_mtime
            if age <= self.settings.instrument_cache_ttl_seconds:
                rows = _load_gzip_json(path.read_bytes())
                return _normalise_master_rows(rows), "CACHE_FRESH"
        response: Optional[requests.Response] = None
        try:
            # Public instrument master is fetched without the private API Authorization header.
            response = requests.get(INSTRUMENT_MASTER_URL, timeout=self.settings.timeout_seconds, headers={"Accept": "application/gzip, application/json", "User-Agent": "Nifty-OI-Scanner/101.0.0"})
            response.raise_for_status()
            raw = response.content
            rows = _load_gzip_json(raw)
            # Store the canonical compressed source; gzip only if the server returned JSON bytes.
            if raw[:2] != b"\x1f\x8b":
                raw = gzip.compress(raw)
            tmp = path.with_suffix(path.suffix + ".tmp")
            tmp.write_bytes(raw)
            tmp.replace(path)
            return _normalise_master_rows(rows), "DOWNLOADED"
        except (requests.RequestException, ValueError, OSError) as exc:
            # A previous source file can be used for discovery only with an explicit stale status.
            if path.exists() and now - path.stat().st_mtime <= 3 * 86400:
                try:
                    self.log.warning("Using stale instrument master cache (age %.1f hours)", (now - path.stat().st_mtime) / 3600)
                    return _normalise_master_rows(_load_gzip_json(path.read_bytes())), "CACHE_STALE"
                except Exception:
                    pass
            raise UpstoxError("INSTRUMENT_MASTER_UNAVAILABLE", f"Could not load official Upstox NSE instrument master: {type(exc).__name__}", endpoint=INSTRUMENT_MASTER_URL) from exc

    def resolve_underlying(self, rows: Sequence[dict[str, Any]]) -> Instrument:
        if self.settings.configured_underlying_key:
            match = next((r for r in rows if r.get("instrument_key") == self.settings.configured_underlying_key and r.get("segment") == "NSE_INDEX" and r.get("instrument_type") == "INDEX"), None)
            if not match:
                raise UpstoxError("UNDERLYING_KEY_UNVERIFIED", "Configured NIFTY key is absent from the official NSE instrument master")
            return _instrument(match)
        names = {self.settings.underlying_query_name.strip().casefold(), "nifty 50", "nifty50"}
        matches = [r for r in rows if str(r.get("segment", "")).upper() == "NSE_INDEX" and str(r.get("instrument_type", "")).upper() == "INDEX" and str(r.get("name", "")).strip().casefold() in names]
        if len(matches) != 1:
            raise UpstoxError("UNDERLYING_RESOLUTION_FAILED", f"Expected exactly one official NIFTY 50 index row; found {len(matches)}")
        return _instrument(matches[0])

    def resolve_expiry(self, rows: Sequence[dict[str, Any]], underlying: Instrument, today: date) -> tuple[date, str]:
        derivatives = []
        for row in rows:
            if row.get("segment") != "NSE_FO" or row.get("underlying_key") != underlying.instrument_key:
                continue
            if str(row.get("instrument_type", "")).upper() not in {"CE", "PE"}:
                continue
            expiry = _parse_master_expiry(row.get("expiry"))
            if expiry and expiry >= today:
                derivatives.append((expiry, row.get("weekly"), row))
        dates = sorted({d for d, _, _ in derivatives})
        if self.settings.configured_expiry:
            explicit = self.settings.configured_expiry
            if explicit not in dates:
                raise UpstoxError("CONFIGURED_EXPIRY_NOT_FOUND", f"Configured expiry {explicit.isoformat()} is not present in current official instrument metadata")
            if self.settings.force_weekly_expiry and not any(d == explicit and weekly is True for d, weekly, _ in derivatives):
                # An explicit date may be configured to a monthly expiry by user choice; with the
                # default weekly-only guard, require NIFTY_FORCE_WEEKLY_EXPIRY=false to permit it.
                raise UpstoxError("CONFIGURED_EXPIRY_NOT_WEEKLY", "Configured expiry is not marked weekly; set NIFTY_FORCE_WEEKLY_EXPIRY=false only if a monthly expiry is intentional")
            return explicit, "EXPLICIT_CONFIGURED_EXPIRY"
        if self.settings.force_weekly_expiry:
            weekly_dates = sorted({d for d, weekly, _ in derivatives if weekly is True})
            if not weekly_dates:
                raise UpstoxError("NO_VERIFIED_WEEKLY_EXPIRY", "Official instrument master contains no eligible weekly NIFTY options; refusing silent monthly fallback")
            return weekly_dates[0], "NEAREST_VERIFIED_WEEKLY_EXPIRY"
        if not dates:
            raise UpstoxError("NO_ELIGIBLE_EXPIRY", "No future NIFTY option expiry found in official instrument master")
        return dates[0], "NEAREST_ELIGIBLE_EXPIRY_WEEKLY_OR_MONTHLY"

    def resolve_future(self, rows: Sequence[dict[str, Any]], underlying: Instrument, today: date) -> Optional[Instrument]:
        candidates: list[Instrument] = []
        for raw in rows:
            if raw.get("segment") != "NSE_FO":
                continue
            typ = str(raw.get("instrument_type", "")).upper()
            symbol = str(raw.get("underlying_symbol", "")).upper()
            name = str(raw.get("name", "")).upper()
            if typ not in {"FUT", "FUTIDX"} or not (symbol == "NIFTY" or name == "NIFTY"):
                continue
            if raw.get("underlying_key") and raw.get("underlying_key") != underlying.instrument_key:
                continue
            expiry = _parse_master_expiry(raw.get("expiry"))
            if expiry and expiry >= today:
                candidate = dict(raw)
                candidate["expiry"] = expiry.isoformat()
                candidates.append(_instrument(candidate))
        return min(candidates, key=lambda x: x.expiry) if candidates else None

    def fetch_option_chain(self, underlying: Instrument, expiry: date, *, session_date: date, fetched_at: datetime) -> ChainSnapshot:
        url = f"{self.settings.api_base_url}/v2/option/chain"
        payload = self._request_json("GET", url, params={"instrument_key": underlying.instrument_key, "expiry_date": expiry.isoformat()})
        # Capture successful response time (not request start) for snapshot-age calculations.
        fetched_at = max(fetched_at, datetime.now(IST))
        items = payload.get("data")
        if not isinstance(items, list) or not items:
            raise UpstoxError("OPTION_CHAIN_EMPTY", "Option-chain response contains no rows", endpoint="/v2/option/chain")
        rows: list[ChainRow] = []
        spot: Optional[float] = None
        for item in items:
            if not isinstance(item, dict):
                continue
            try:
                row_expiry = date.fromisoformat(str(item.get("expiry", expiry.isoformat()))[:10])
                if row_expiry != expiry:
                    continue
                strike = _finite_positive(item.get("strike_price"), allow_zero=False)
                this_spot = _finite_positive(item.get("underlying_spot_price"), allow_zero=False)
                if this_spot:
                    spot = this_spot
                call = _parse_chain_option(item.get("call_options"), expiry, strike, "CE")
                put = _parse_chain_option(item.get("put_options"), expiry, strike, "PE")
                if call is not None or put is not None:
                    rows.append(ChainRow(strike, expiry, call, put))
            except (TypeError, ValueError, KeyError):
                continue
        if not rows or spot is None:
            raise UpstoxError("OPTION_CHAIN_INVALID", "Option-chain response has no valid matching expiry/strike/spot rows", endpoint="/v2/option/chain")
        rows.sort(key=lambda x: x.strike)
        # Validate monotonically increasing unique strikes.
        strikes = [r.strike for r in rows]
        if len(set(strikes)) != len(strikes):
            raise UpstoxError("OPTION_CHAIN_DUPLICATE_STRIKES", "Option-chain response contains duplicate strikes", endpoint="/v2/option/chain")
        return ChainSnapshot(fetched_at, session_date, underlying.instrument_key, expiry, spot, tuple(rows))

    def fetch_quotes(self, instruments: Sequence[Instrument | str], *, received_at: datetime) -> dict[str, Quote]:
        keys = [i.instrument_key if isinstance(i, Instrument) else i for i in instruments]
        keys = list(dict.fromkeys(k for k in keys if k))
        if not keys:
            return {}
        # Full Market Quotes V3 supports multiple keys in one request. Bound URL length conservatively.
        result: dict[str, Quote] = {}
        for start in range(0, len(keys), 100):
            batch = keys[start:start + 100]
            url = f"{self.settings.api_base_url}/v3/market-quote/quotes"
            payload = self._request_json("GET", url, params={"instrument_key": ",".join(batch)})
            data = payload.get("data", {})
            if not isinstance(data, dict):
                raise UpstoxError("QUOTE_RESPONSE_INVALID", "Market quote data is not an object", endpoint="/v3/market-quote/quotes")
            for key in batch:
                raw = _find_quote_payload(data, key)
                if raw is None:
                    continue
                last = _first_number(raw, "last_price", "ltp", "last_traded_price")
                if last is None or last <= 0:
                    continue
                live = raw.get("live_ohlc") or raw.get("ohlc") or {}
                prev = raw.get("prev_ohlc") or {}
                # V3 timestamp is the market-quote snapshot time; last_trade_time is a separate
                # execution event and may be older in a quiet instrument. Prefer snapshot time.
                source_time = _parse_datetime(raw.get("timestamp") or raw.get("last_trade_time"))
                bid, bid_qty = _best_depth(raw.get("depth"), "buy")
                ask, ask_qty = _best_depth(raw.get("depth"), "sell")
                result[key] = Quote(
                    key, last, received_at, source_time,
                    _first_number(raw, "prev_close_price", "close_price") or _first_number(prev, "close"),
                    _first_number(live, "open"), _first_number(live, "high"), _first_number(live, "low"),
                    _first_number(prev, "high"), _first_number(prev, "low"), _first_number(live, "volume", "vol"),
                    bid, ask, bid_qty, ask_qty,
                )
        missing = set(keys) - set(result)
        if missing:
            raise UpstoxError("QUOTE_MISSING", f"Full quote response omitted {len(missing)} requested instrument(s)", endpoint="/v3/market-quote/quotes")
        return result

    def fetch_intraday_candles(self, instrument_key: str, *, now: datetime) -> list[Candle]:
        encoded = url_quote(instrument_key, safe="")
        url = f"{self.settings.api_base_url}/v3/historical-candle/intraday/{encoded}/minutes/1"
        payload = self._request_json("GET", url)
        candles_raw = (payload.get("data") or {}).get("candles")
        if not isinstance(candles_raw, list):
            raise UpstoxError("CANDLE_RESPONSE_INVALID", "Intraday candle response has no data.candles list", endpoint="/v3/historical-candle/intraday")
        cutoff = now - timedelta(seconds=5)
        candles: dict[datetime, Candle] = {}
        for raw in candles_raw:
            try:
                if not isinstance(raw, (list, tuple)) or len(raw) < 6:
                    continue
                ts = _parse_datetime(raw[0])
                if ts is None or ts + timedelta(minutes=1) > cutoff:
                    continue  # The candle has not demonstrably completed yet.
                if ts.tzinfo is None:
                    ts = ts.replace(tzinfo=IST)
                c = Candle(ts, float(raw[1]), float(raw[2]), float(raw[3]), float(raw[4]), float(raw[5] or 0), float(raw[6] or 0) if len(raw) > 6 else 0.0)
                candles[ts] = c
            except (TypeError, ValueError, OverflowError):
                continue
        out = [candles[k] for k in sorted(candles)]
        if len(out) < 2:
            raise UpstoxError("CANDLE_HISTORY_INSUFFICIENT", "Fewer than two completed intraday candles were returned", endpoint="/v3/historical-candle/intraday")
        # Detect a gap to the latest completed candle. Do not fabricate missing candles.
        latest_age = (now - (out[-1].start + timedelta(minutes=1))).total_seconds()
        if latest_age > self.settings.candle_max_age_seconds:
            raise UpstoxError("CANDLE_STALE", f"Latest completed candle is stale by {latest_age:.0f}s", endpoint="/v3/historical-candle/intraday")
        return out



def _best_depth(depth: Any, side: str) -> tuple[Optional[float], Optional[float]]:
    """Return best positive bid/ask price and quantity from V3 depth; never invent a quote."""
    if not isinstance(depth, dict):
        return None, None
    levels = depth.get(side)
    if not isinstance(levels, list):
        return None, None
    valid: list[tuple[float, float]] = []
    for level in levels:
        if not isinstance(level, dict):
            continue
        price = _float_or_none(level.get("price"))
        quantity = _float_or_none(level.get("quantity"))
        if price is not None and price > 0 and quantity is not None and quantity >= 0:
            valid.append((price, quantity))
    if not valid:
        return None, None
    best = max(valid, key=lambda x: x[0]) if side == "buy" else min(valid, key=lambda x: x[0])
    return best[0], best[1]


def _safe_api_message(response: requests.Response) -> str:
    try:
        payload = response.json()
        # Do not echo arbitrary headers or authorization material.
        text = json.dumps(payload, ensure_ascii=False)
    except ValueError:
        text = response.text
    return text.replace("\n", " ")[:500]


def urlparse_path(url: str) -> str:
    from urllib.parse import urlsplit
    return urlsplit(url).path


def _retry_after(value: Optional[str]) -> Optional[float]:
    if not value:
        return None
    try:
        return max(0.0, min(2.0, float(value)))
    except ValueError:
        try:
            dt = parsedate_to_datetime(value)
            return max(0.0, min(2.0, (dt - datetime.now(dt.tzinfo)).total_seconds()))
        except Exception:
            return None


def _load_gzip_json(raw: bytes) -> list[dict[str, Any]]:
    content = gzip.decompress(raw) if raw[:2] == b"\x1f\x8b" else raw
    value = json.loads(content.decode("utf-8"))
    if isinstance(value, dict):
        value = value.get("data") or value.get("instruments")
    if not isinstance(value, list):
        raise ValueError("Instrument master JSON is not a list")
    return value


def _normalise_master_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    result = []
    for raw in rows:
        if not isinstance(raw, dict):
            continue
        row = dict(raw)
        # Instrument-master expiry examples use epoch milliseconds; normalize to ISO date.
        expiry = _parse_master_expiry(row.get("expiry"))
        if expiry:
            row["expiry"] = expiry.isoformat()
        result.append(row)
    return result


def _parse_master_expiry(value: Any) -> Optional[date]:
    if value is None or value == "":
        return None
    if isinstance(value, (int, float)):
        try:
            return datetime.fromtimestamp(float(value) / 1000, IST).date()
        except (ValueError, OSError, OverflowError):
            return None
    text = str(value).strip()
    try:
        return date.fromisoformat(text[:10])
    except ValueError:
        try:
            numeric = float(text)
            return datetime.fromtimestamp(numeric / 1000, IST).date()
        except (ValueError, OSError, OverflowError):
            return None


def _instrument(row: dict[str, Any]) -> Instrument:
    return Instrument(
        instrument_key=str(row.get("instrument_key", "")), segment=str(row.get("segment", "")),
        name=str(row.get("name", "")), instrument_type=str(row.get("instrument_type", "")),
        expiry=_parse_master_expiry(row.get("expiry")), underlying_key=row.get("underlying_key"),
        underlying_symbol=row.get("underlying_symbol"), strike=_float_or_none(row.get("strike_price")),
        lot_size=int(float(row.get("lot_size") or 0)) if row.get("lot_size") is not None else None,
        tick_size=_float_or_none(row.get("tick_size")), weekly=row.get("weekly") if isinstance(row.get("weekly"), bool) else None,
        trading_symbol=row.get("trading_symbol"),
    )


def _parse_chain_option(raw: Any, expiry: date, strike: float, side: str) -> Optional[OptionQuote]:
    if not isinstance(raw, dict):
        return None
    key = raw.get("instrument_key")
    md = raw.get("market_data") or {}
    greeks_raw = raw.get("option_greeks") or {}
    if not key or not isinstance(md, dict):
        return None
    ltp = _finite_positive(md.get("ltp"), allow_zero=True)
    oi = _finite_positive(md.get("oi"), allow_zero=True)
    bid = _finite_positive(md.get("bid_price"), allow_zero=True)
    ask = _finite_positive(md.get("ask_price"), allow_zero=True)
    if None in (ltp, oi, bid, ask):
        return None
    if ask < bid and bid > 0 and ask > 0:
        # Preserve the crossed market for validation; the quote model rejects it later.
        pass
    def number(name: str) -> Optional[float]:
        return _float_or_none(greeks_raw.get(name))
    greeks = Greeks(number("delta"), number("gamma"), number("theta"), number("vega"), number("iv"))
    previous_session_oi = _finite_positive(md.get("prev_oi"), allow_zero=True)
    return OptionQuote(str(key), expiry, strike, side, ltp, bid, ask, float(md.get("bid_qty") or 0), float(md.get("ask_qty") or 0), float(md.get("volume") or 0), oi, greeks, None, previous_session_oi)


def _find_quote_payload(data: dict[str, Any], instrument_key: str) -> Optional[dict[str, Any]]:
    if instrument_key in data and isinstance(data[instrument_key], dict):
        return data[instrument_key]
    # V3 responses often key data as "NSE_INDEX:Nifty 50". Match a supplied key only if
    # the payload carries a uniquely identifying token field or normalized key.
    normalized = instrument_key.replace("|", ":").casefold()
    candidates = []
    for key, value in data.items():
        if not isinstance(value, dict):
            continue
        if _first_number(value, "last_price", "ltp", "last_traded_price") is None:
            continue
        own_key = str(value.get("instrument_key") or value.get("instrument_token") or "").replace("|", ":").casefold()
        normalized_map_key = str(key).replace("|", ":").casefold()
        if own_key == normalized or normalized_map_key == normalized:
            candidates.append(value)
        elif instrument_key.split("|")[-1].casefold() in {own_key.split(":")[-1], normalized_map_key.split(":")[-1]}:
            candidates.append(value)
    return candidates[0] if len(candidates) == 1 else None


def _parse_datetime(value: Any) -> Optional[datetime]:
    if value is None or value == "":
        return None
    if isinstance(value, (int, float)):
        try:
            # Upstox timestamps in these response fields are typically ISO strings. Numeric timestamps are epoch ms.
            return datetime.fromtimestamp(float(value) / 1000, IST)
        except (ValueError, OSError, OverflowError):
            return None
    text = str(value).strip().replace("Z", "+00:00")
    try:
        dt = datetime.fromisoformat(text)
        return dt if dt.tzinfo else dt.replace(tzinfo=IST)
    except ValueError:
        return None


def _float_or_none(value: Any) -> Optional[float]:
    if value is None or value == "":
        return None
    try:
        number = float(value)
        return number if math.isfinite(number) else None
    except (TypeError, ValueError):
        return None


def _finite_positive(value: Any, *, allow_zero: bool = False) -> Optional[float]:
    number = _float_or_none(value)
    if number is None or number < 0 or (number == 0 and not allow_zero):
        return None
    return number


def _first_number(data: dict[str, Any], *keys: str) -> Optional[float]:
    for key in keys:
        result = _float_or_none(data.get(key))
        if result is not None:
            return result
    return None


# ===== Inlined module: oi_engine.py =====

"""Snapshot-cadence open-interest calculations and probabilistic directional evidence."""











def _pct_change(current: float, previous: Optional[float]) -> Optional[float]:
    if previous is None or previous <= 0:
        return None
    return 100.0 * (current - previous) / previous


def _interpret(side: str, doi: float, dpct: Optional[float], premium_pct: Optional[float]) -> tuple[float, str]:
    """Map OI+pct+premium to a directional contribution, not a claim of trader intent.

    CE premium rise contributes bullish evidence; PE premium rise contributes bearish evidence.
    OI sign distinguishes build-up/unwinding/covering subtype. Contributions are weighted later
    using the absolute OI percentage change and capped as *scores*, never as raw OI values.
    """
    if dpct is None:
        return 0.0, "BASELINE_UNDEFINED"
    if doi == 0:
        return 0.0, "OI_UNCHANGED"
    if premium_pct is None or abs(premium_pct) < 0.05:
        return 0.0, "PREMIUM_DIRECTION_UNCLEAR"
    premium_up = premium_pct > 0
    oi_up = doi > 0
    if side == "CE":
        score = 1.0 if premium_up else -1.0
        if oi_up and premium_up:
            label = "CE_LONG_BUILDUP_CONSISTENT"
        elif oi_up and not premium_up:
            label = "CE_SHORT_BUILDUP_CONSISTENT"
        elif not oi_up and premium_up:
            label = "CE_SHORT_COVERING_CONSISTENT"
        else:
            label = "CE_LONG_UNWINDING_CONSISTENT"
    else:
        score = -1.0 if premium_up else 1.0
        if oi_up and premium_up:
            label = "PE_LONG_BUILDUP_CONSISTENT"
        elif oi_up and not premium_up:
            label = "PE_WRITING_CONSISTENT"
        elif not oi_up and premium_up:
            label = "PE_SHORT_COVERING_CONSISTENT"
        else:
            label = "PE_LONG_UNWINDING_CONSISTENT"
    return score, label


def calculate_oi_evidence(
    current: ChainSnapshot,
    previous: Optional[ChainSnapshot],
    settings: Settings,
    *,
    now: datetime,
    prior_score_history: Optional[list[float]] = None,
    session_baseline: Optional[ChainSnapshot] = None,
) -> OIEvidence:
    if now.tzinfo is None or now.utcoffset() is None:
        raise ValueError("now must be timezone-aware")
    age = max(0.0, (now - current.fetched_at).total_seconds())
    interval: Optional[float] = None
    if age > settings.option_chain_max_age_seconds:
        return OIEvidence(Direction.UNKNOWN, 0.0, 0.0, "STALE", age, None, (), 0.0, 0.0, 0, "OI_STALE")
    if previous is None:
        return OIEvidence(Direction.UNKNOWN, 0.0, 0.0, "MISSING_BASELINE", age, None, (), 0.0, 0.0, 0, "OI_BASELINE_MISSING")
    if previous.session_date != current.session_date or previous.expiry != current.expiry or previous.underlying_key != current.underlying_key:
        return OIEvidence(Direction.UNKNOWN, 0.0, 0.0, "IDENTITY_MISMATCH", age, None, (), 0.0, 0.0, 0, "OI_BASELINE_IDENTITY_MISMATCH")
    interval = (current.fetched_at - previous.fetched_at).total_seconds()
    if interval <= 0:
        return OIEvidence(Direction.UNKNOWN, 0.0, 0.0, "OUT_OF_ORDER", age, interval, (), 0.0, 0.0, 0, "OI_SNAPSHOT_OUT_OF_ORDER")
    # If all quoted market fields are identical, fetch time alone is not evidence of a new
    # market snapshot. The caller may retain a recent prior OI hypothesis, but must not invent deltas.
    if _same_market_payload(current, previous):
        return OIEvidence(Direction.UNKNOWN, 0.0, 0.0, "UNCHANGED", age, interval, (), 0.0, 0.0, 0, "OI_PAYLOAD_UNCHANGED_NO_NEW_DELTA", payload_unchanged=True)

    previous_by_key: dict[tuple[float, str, str], OptionQuote] = {}
    baseline_by_key: dict[tuple[float, str, str], OptionQuote] = {}
    for row in previous.rows:
        for side, quote in (("CE", row.call), ("PE", row.put)):
            if quote:
                previous_by_key[(row.strike, side, quote.instrument_key)] = quote
    if session_baseline is not None and session_baseline.session_date == current.session_date and session_baseline.expiry == current.expiry and session_baseline.underlying_key == current.underlying_key:
        for row in session_baseline.rows:
            for side, quote in (("CE", row.call), ("PE", row.put)):
                if quote:
                    baseline_by_key[(row.strike, side, quote.instrument_key)] = quote
    step = min((b.strike - a.strike for a, b in zip(current.rows, current.rows[1:]) if b.strike > a.strike), default=50.0)
    atm_index = min(range(len(current.rows)), key=lambda i: abs(current.rows[i].strike - current.spot))
    low_index = max(0, atm_index - settings.oi_near_atm_strikes)
    high_index = min(len(current.rows), atm_index + settings.oi_near_atm_strikes + 1)
    rows = current.rows[low_index:high_index]
    changes: list[OIChange] = []
    bullish_raw = 0.0
    bearish_raw = 0.0
    bullish_weights = 0.0
    bearish_weights = 0.0
    total_weight = 0.0
    for row in rows:
        distance_steps = abs(row.strike - current.spot) / step if step > 0 else 0.0
        distance_weight = 1.0 / (1.0 + 0.35 * distance_steps)
        for side, quote in (("CE", row.call), ("PE", row.put)):
            if not quote:
                continue
            old = previous_by_key.get((row.strike, side, quote.instrument_key))
            if old is None:
                continue
            delta = quote.oi - old.oi
            pct = _pct_change(quote.oi, old.oi)
            premium_pct = _pct_change(quote.ltp, old.ltp) if old.ltp > 0 and quote.ltp > 0 else None
            volume_delta: Optional[float] = quote.volume - old.volume
            if volume_delta < 0:
                # Cumulative volume reset is not interpreted as negative traded flow.
                volume_delta = None
            directional, interpretation = _interpret(side, delta, pct, premium_pct)
            magnitude = 0.0
            if pct is not None:
                magnitude = min(abs(pct) / settings.oi_material_pct, settings.oi_score_max_per_strike)
            contribution = directional * magnitude * distance_weight
            base_quote = baseline_by_key.get((row.strike, side, quote.instrument_key))
            session_delta = quote.oi - base_quote.oi if base_quote is not None else None
            prev_session_delta = quote.oi - quote.previous_session_oi if quote.previous_session_oi is not None else None
            changes.append(OIChange(
                instrument_key=quote.instrument_key, strike=row.strike, side=side,
                previous_oi=old.oi, current_oi=quote.oi, delta_oi=delta,
                delta_pct=pct, previous_premium=old.ltp, current_premium=quote.ltp,
                premium_delta_pct=premium_pct, volume_delta=volume_delta,
                material=(pct is not None and abs(pct) >= settings.oi_material_pct),
                contribution=contribution, interpretation=interpretation,
                delta_oi_session=session_delta, delta_oi_vs_prev_session=prev_session_delta,
            ))
            if contribution > 0:
                bullish_raw += contribution
                bullish_weights += abs(contribution)
            elif contribution < 0:
                bearish_raw += abs(contribution)
                bearish_weights += abs(contribution)
            total_weight += distance_weight

    if not changes or total_weight == 0:
        return OIEvidence(Direction.UNKNOWN, 0.0, 0.0, "NO_MATCHED_ROWS", age, interval, tuple(changes), 0.0, 0.0, 0, "OI_NO_MATCHED_CONTRACTS")
    score = (bullish_raw - bearish_raw) / max(total_weight, 1e-9)
    # Persistence damps isolated snapshot reversals. Raw snapshot contribution remains audit-visible.
    history = (prior_score_history or [])[-max(0, settings.oi_history_length - 1):]
    smoothed = (sum(history) + score) / (len(history) + 1)
    if smoothed >= settings.oi_direction_threshold:
        direction = Direction.BULLISH
    elif smoothed <= -settings.oi_direction_threshold:
        direction = Direction.BEARISH
    elif abs(smoothed) <= settings.oi_neutral_band:
        direction = Direction.MIXED
    else:
        direction = Direction.MIXED
    max_strength = max(bullish_raw, bearish_raw)
    confidence = min(1.0, abs(smoothed) / max(settings.oi_direction_threshold * 2, 1e-9))
    material_count = sum(1 for c in changes if c.material)
    status = "FRESH" if interval <= settings.oi_fresh_interval_seconds else "DELAYED"
    # Longer intervals remain usable as the actual multi-minute delta, with reduced confidence.
    if status == "DELAYED":
        confidence *= max(0.35, settings.oi_fresh_interval_seconds / max(interval, 1.0))
    summary = f"OI_{direction.value}; score={smoothed:.3f}; raw={score:.3f}; material_rows={material_count}; interval_s={interval:.0f}; status={status}"
    return OIEvidence(direction, smoothed, confidence, status, age, interval, tuple(changes), bullish_raw, bearish_raw, material_count, summary, score)


def _same_market_payload(current: ChainSnapshot, previous: ChainSnapshot) -> bool:
    """Compare observed contract payloads, ignoring local request timestamps."""
    if current.spot != previous.spot or current.expiry != previous.expiry or current.underlying_key != previous.underlying_key:
        return False
    def quote_map(snapshot: ChainSnapshot) -> dict[tuple[float, str, str], tuple[Any, ...]]:
        result: dict[tuple[float, str, str], tuple[Any, ...]] = {}
        for row in snapshot.rows:
            for side, q in (("CE", row.call), ("PE", row.put)):
                if q:
                    result[(row.strike, side, q.instrument_key)] = (
                        q.oi, q.ltp, q.volume, q.bid, q.ask, q.bid_qty, q.ask_qty,
                        q.greeks.delta, q.greeks.gamma, q.greeks.theta, q.greeks.vega, q.greeks.iv,
                    )
        return result
    return quote_map(current) == quote_map(previous)


def compact_snapshot(snapshot: ChainSnapshot, *, max_rows: int = 31) -> dict[str, Any]:
    """Serialize only the near-spot band needed for next-run comparisons."""
    rows = sorted(snapshot.rows, key=lambda r: abs(r.strike - snapshot.spot))[:max_rows]
    return {
        "fetched_at": snapshot.fetched_at.isoformat(),
        "session_date": snapshot.session_date.isoformat(),
        "underlying_key": snapshot.underlying_key,
        "expiry": snapshot.expiry.isoformat(),
        "spot": snapshot.spot,
        "rows": [{
            "strike": r.strike,
            "expiry": r.expiry.isoformat(),
            "call": _quote_to_dict(r.call),
            "put": _quote_to_dict(r.put),
        } for r in sorted(rows, key=lambda x: x.strike)],
    }


def _quote_to_dict(q: Optional[OptionQuote]) -> Optional[dict[str, Any]]:
    if q is None:
        return None
    return {
        "instrument_key": q.instrument_key, "expiry": q.expiry.isoformat(), "strike": q.strike,
        "side": q.side, "ltp": q.ltp, "bid": q.bid, "ask": q.ask,
        "bid_qty": q.bid_qty, "ask_qty": q.ask_qty, "volume": q.volume, "oi": q.oi,
        "greeks": asdict(q.greeks), "quote_time": q.quote_time.isoformat() if q.quote_time else None,
        "previous_session_oi": q.previous_session_oi,
    }


def snapshot_from_dict(value: dict[str, Any]) -> ChainSnapshot:
    from datetime import date
    fetched = datetime.fromisoformat(value["fetched_at"])
    rows = []
    for r in value["rows"]:
        def make(q: Optional[dict[str, Any]]) -> Optional[OptionQuote]:
            if not q:
                return None
            g = q.get("greeks", {})
            qt = datetime.fromisoformat(q["quote_time"]) if q.get("quote_time") else None
            return OptionQuote(q["instrument_key"], date.fromisoformat(q["expiry"]), float(q["strike"]), q["side"], float(q["ltp"]), float(q["bid"]), float(q["ask"]), float(q["bid_qty"]), float(q["ask_qty"]), float(q["volume"]), float(q["oi"]), Greeks(**g), qt, float(q["previous_session_oi"]) if q.get("previous_session_oi") is not None else None)
        rows.append(ChainRow(float(r["strike"]), date.fromisoformat(r["expiry"]), make(r.get("call")), make(r.get("put"))))
    return ChainSnapshot(fetched, date.fromisoformat(value["session_date"]), value["underlying_key"], date.fromisoformat(value["expiry"]), float(value["spot"]), tuple(rows))


def derive_oi_wall_levels(snapshot: ChainSnapshot, max_strikes: int = 6):
    """Return potential OI friction zones; these are context, never standalone stop levels."""
    rows = sorted(snapshot.rows, key=lambda r: r.strike)
    atm_i = min(range(len(rows)), key=lambda i: abs(rows[i].strike - snapshot.spot))
    left, right = max(0, atm_i - max_strikes), min(len(rows), atm_i + max_strikes + 1)
    band = rows[left:right]
    put_rows = [r for r in band if r.strike <= snapshot.spot and r.put]
    call_rows = [r for r in band if r.strike >= snapshot.spot and r.call]
    levels = []
    if put_rows:
        wall = max(put_rows, key=lambda r: r.put.oi if r.put else -1)
        levels.append(Level(wall.strike, "SUPPORT_CONTEXT", "NEAR_ATM_PUT_OI_WALL", 0.7, snapshot.fetched_at))
    if call_rows:
        wall = max(call_rows, key=lambda r: r.call.oi if r.call else -1)
        levels.append(Level(wall.strike, "RESISTANCE_CONTEXT", "NEAR_ATM_CALL_OI_WALL", 0.7, snapshot.fetched_at))
    return levels


# ===== Inlined module: price_engine.py =====

"""No-look-ahead candle, regime, swing/level and setup analysis."""













def true_ranges(candles: Sequence[Candle]) -> list[float]:
    out: list[float] = []
    prev_close: Optional[float] = None
    for c in candles:
        out.append(max(c.high - c.low, abs(c.high - prev_close), abs(c.low - prev_close)) if prev_close is not None else c.high - c.low)
        prev_close = c.close
    return out


def atr(candles: Sequence[Candle], period: int = 14) -> Optional[float]:
    if len(candles) < period or period < 1:
        return None
    trs = true_ranges(candles)
    value = fmean(trs[:period])
    for tr in trs[period:]:
        value = (value * (period - 1) + tr) / period
    return value if isfinite(value) and value > 0 else None


def ema(values: Sequence[float], period: int) -> Optional[float]:
    if len(values) < period:
        return None
    alpha = 2.0 / (period + 1.0)
    value = fmean(values[:period])
    for x in values[period:]:
        value = alpha * x + (1.0 - alpha) * value
    return value


def returns(candles: Sequence[Candle], bars: int) -> Optional[float]:
    """Close-to-close point change only when the entire requested minute window exists."""
    if bars <= 0 or len(candles) <= bars or candles[-bars - 1].close == 0:
        return None
    window = candles[-bars - 1:]
    for left, right in zip(window, window[1:]):
        if right.start - left.start != timedelta(minutes=1):
            return None
    return candles[-1].close - candles[-bars - 1].close


def aggregate_completed_5m(candles: Sequence[Candle]) -> list[Candle]:
    """Aggregate only complete five consecutive one-minute candles; never fill gaps."""
    groups: dict[datetime, list[Candle]] = defaultdict(list)
    for c in candles:
        local = c.start
        anchor = local.replace(hour=9, minute=15, second=0, microsecond=0)
        if local < anchor:
            continue
        elapsed = int((local - anchor).total_seconds() // 60)
        bucket = anchor + timedelta(minutes=(elapsed // 5) * 5)
        groups[bucket].append(c)
    out: list[Candle] = []
    for bucket, group in sorted(groups.items()):
        group.sort(key=lambda c: c.start)
        if len(group) != 5:
            continue
        expected = [bucket + timedelta(minutes=i) for i in range(5)]
        if [c.start for c in group] != expected:
            continue
        out.append(Candle(bucket, group[0].open, max(c.high for c in group), min(c.low for c in group), group[-1].close, sum(c.volume for c in group), group[-1].oi))
    return out


def confirmed_pivots(candles: Sequence[Candle], left: int = 2, right: int = 2) -> tuple[list[tuple[int, float]], list[tuple[int, float]]]:
    """Return only pivots whose right-side confirmation candles have closed."""
    highs: list[tuple[int, float]] = []
    lows: list[tuple[int, float]] = []
    for i in range(left, len(candles) - right):
        high = candles[i].high
        low = candles[i].low
        prior_highs = [candles[j].high for j in range(i - left, i)]
        later_highs = [candles[j].high for j in range(i + 1, i + right + 1)]
        prior_lows = [candles[j].low for j in range(i - left, i)]
        later_lows = [candles[j].low for j in range(i + 1, i + right + 1)]
        if high > max(prior_highs) and high >= max(later_highs):
            highs.append((i, high))
        if low < min(prior_lows) and low <= min(later_lows):
            lows.append((i, low))
    return highs, lows


def _cluster_levels(levels: list[Level], tolerance: float) -> list[Level]:
    if not levels:
        return []
    levels = sorted(levels, key=lambda x: x.price)
    clusters: list[list[Level]] = [[levels[0]]]
    for level in levels[1:]:
        if abs(level.price - clusters[-1][-1].price) <= tolerance:
            clusters[-1].append(level)
        else:
            clusters.append([level])
    result: list[Level] = []
    for cluster in clusters:
        price = sum(x.price * max(x.strength, 0.01) for x in cluster) / sum(max(x.strength, 0.01) for x in cluster)
        primary = max(cluster, key=lambda x: x.strength)
        result.append(Level(price, primary.kind, "+".join(sorted(set(x.source for x in cluster))), min(3.0, sum(x.strength for x in cluster)), primary.observed_at))
    return result


def _directional_bias(bars: Sequence[Candle], atr_value: Optional[float]) -> Direction:
    """Five-minute context: EMA(9)/EMA(21) plus four-bar movement; unknown until seeded."""
    if len(bars) < 21 or not atr_value:
        return Direction.UNKNOWN
    closes = [c.close for c in bars]
    e9 = ema(closes, 9)
    e21 = ema(closes, 21)
    movement = closes[-1] - closes[-4]
    if e9 is not None and e21 is not None and closes[-1] > e9 > e21 and movement > 0.35 * atr_value:
        return Direction.BULLISH
    if e9 is not None and e21 is not None and closes[-1] < e9 < e21 and movement < -0.35 * atr_value:
        return Direction.BEARISH
    return Direction.MIXED


def analyze_price(
    candles: Sequence[Candle],
    quote: Quote,
    settings: Settings,
    oi_direction: Direction,
    *,
    now: datetime,
    context_levels: Sequence[Level] = (),
    _collect_recent_setups: bool = True,
) -> PriceAnalysis:
    if now.tzinfo is None or now.utcoffset() is None:
        raise ValueError("now must be timezone-aware")
    if not candles:
        return PriceAnalysis(regime=Regime.UNKNOWN, direction=Direction.UNKNOWN, higher_timeframe_bias=Direction.UNKNOWN,
            execution_structure="INSUFFICIENT_CANDLES", setup=None, support=None, resistance=None, support_source=None,
            resistance_source=None, atr=None, return_1m=None, return_3m=None, return_5m=None, return_15m=None,
            trigger_price=None, invalidation_price=None, structure_confidence=0.0,
            reasons=("INSUFFICIENT_COMPLETED_CANDLES",))
    # Enforce completed bars here too; callers cannot accidentally inject a future/incomplete candle.
    candle_tz = candles[0].start.tzinfo
    now_local = now.astimezone(candle_tz)
    complete = [c for c in candles if c.start + timedelta(minutes=1) <= now_local]
    complete.sort(key=lambda c: c.start)
    quality_reasons: list[str] = []
    grouped: dict[datetime, list[Candle]] = defaultdict(list)
    for candle in complete:
        grouped[candle.start].append(candle)
    if any(len(group) > 1 and any(candidate != group[0] for candidate in group[1:]) for group in grouped.values()):
        return PriceAnalysis(regime=Regime.UNKNOWN, direction=Direction.UNKNOWN, higher_timeframe_bias=Direction.UNKNOWN,
            execution_structure="DUPLICATE_CANDLE_CONFLICT", setup=None, support=None, resistance=None, support_source=None,
            resistance_source=None, atr=None, return_1m=None, return_3m=None, return_5m=None, return_15m=None,
            trigger_price=None, invalidation_price=None, structure_confidence=0.0,
            reasons=("CANDLE_DUPLICATE_CONFLICT",))
    if any(len(group) > 1 for group in grouped.values()):
        quality_reasons.append("IDENTICAL_DUPLICATE_CANDLES_DEDUPED")
    candles = [group[0] for _, group in sorted(grouped.items())]
    required = max(settings.atr_period + 5, 25)
    if len(candles) < required:
        return PriceAnalysis(regime=Regime.UNKNOWN, direction=Direction.UNKNOWN, higher_timeframe_bias=Direction.UNKNOWN,
            execution_structure="INSUFFICIENT_CANDLES", setup=None, support=None, resistance=None, support_source=None,
            resistance_source=None, atr=None, return_1m=None, return_3m=None, return_5m=None, return_15m=None,
            trigger_price=None, invalidation_price=None, structure_confidence=0.0,
            reasons=("INSUFFICIENT_COMPLETED_CANDLES", *quality_reasons))
    if candles[-1].start.date() != now.astimezone(candles[-1].start.tzinfo).date():
        return PriceAnalysis(regime=Regime.UNKNOWN, direction=Direction.UNKNOWN, higher_timeframe_bias=Direction.UNKNOWN,
            execution_structure="SESSION_DATE_MISMATCH", setup=None, support=None, resistance=None, support_source=None,
            resistance_source=None, atr=None, return_1m=None, return_3m=None, return_5m=None, return_15m=None,
            trigger_price=None, invalidation_price=None, structure_confidence=0.0,
            reasons=("CANDLE_SESSION_DATE_MISMATCH",))

    day = candles[-1].start.date()
    session = [c for c in candles if c.start.date() == day]
    # Price-pattern and return windows must be genuinely minute-aligned. Never interpolate gaps.
    gap_window_length = min(len(session), max(settings.atr_period + 1, 16))
    recent_window = session[-gap_window_length:]
    if any(right.start - left.start != timedelta(minutes=1) for left, right in zip(recent_window, recent_window[1:])):
        return PriceAnalysis(regime=Regime.UNKNOWN, direction=Direction.UNKNOWN, higher_timeframe_bias=Direction.UNKNOWN,
            execution_structure="CANDLE_GAP_IN_RECENT_WINDOW", setup=None, support=None, resistance=None, support_source=None,
            resistance_source=None, atr=None, return_1m=None, return_3m=None, return_5m=None, return_15m=None,
            trigger_price=None, invalidation_price=None, structure_confidence=0.0,
            reasons=("CANDLE_GAP_IN_RECENT_WINDOW", *quality_reasons))
    atr_value = atr(session, settings.atr_period)
    if atr_value is None:
        atr_value = atr(candles[-settings.atr_period - 2:], settings.atr_period)
    latest = session[-1]
    close = quote.last_price
    r1 = returns(session, 1)
    r3 = returns(session, 3)
    r5 = returns(session, 5)
    r15 = returns(session, 15)
    bars5 = aggregate_completed_5m(session)
    atr5 = atr(bars5, min(14, len(bars5))) if len(bars5) >= 14 else None
    higher_bias = _directional_bias(bars5, atr5) if atr5 else Direction.UNKNOWN
    close_values = [c.close for c in session]
    ema9 = ema(close_values[-min(len(close_values), 40):], 9)
    ema21 = ema(close_values[-min(len(close_values), 60):], 21)
    price_bias = Direction.MIXED
    if ema9 and ema21 and close >= ema9 >= ema21 and (r5 or 0) > 0:
        price_bias = Direction.BULLISH
    elif ema9 and ema21 and close <= ema9 <= ema21 and (r5 or 0) < 0:
        price_bias = Direction.BEARISH

    levels: list[Level] = []
    highs, lows = confirmed_pivots(session, settings.swing_left_bars, settings.swing_right_bars)
    for index, price in highs[-20:]:
        levels.append(Level(price, "RESISTANCE", "CONFIRMED_SWING_HIGH", 1.0, session[index].start))
    for index, price in lows[-20:]:
        levels.append(Level(price, "SUPPORT", "CONFIRMED_SWING_LOW", 1.0, session[index].start))
    session_high = max(c.high for c in session)
    session_low = min(c.low for c in session)
    levels.extend([Level(session_high, "RESISTANCE", "SESSION_HIGH", 1.4, session[-1].start), Level(session_low, "SUPPORT", "SESSION_LOW", 1.4, session[0].start)])
    levels.extend(context_levels)
    if quote.prev_high and quote.prev_high > 0:
        levels.append(Level(quote.prev_high, "RESISTANCE", "PREVIOUS_SESSION_HIGH", 1.2))
    if quote.prev_low and quote.prev_low > 0:
        levels.append(Level(quote.prev_low, "SUPPORT", "PREVIOUS_SESSION_LOW", 1.2))
    # Opening range is valid only after its window completed and candles cover the whole window.
    or_end = datetime.combine(day, datetime_time(9, 15), tzinfo=latest.start.tzinfo) + timedelta(minutes=settings.opening_range_minutes)
    if now >= or_end and session:
        opening = [c for c in session if datetime.combine(day, datetime_time(9, 15), tzinfo=c.start.tzinfo) <= c.start < or_end]
        expected = settings.opening_range_minutes
        if len(opening) >= expected and len({c.start for c in opening}) >= expected:
            levels.append(Level(max(c.high for c in opening), "RESISTANCE", "OPENING_RANGE_HIGH", 1.2, opening[-1].start))
            levels.append(Level(min(c.low for c in opening), "SUPPORT", "OPENING_RANGE_LOW", 1.2, opening[-1].start))
    tol = max((atr_value or 1.0) * 0.12, 2.0)
    clustered = _cluster_levels(levels, tol)
    below = sorted((x for x in clustered if x.price < close), key=lambda x: close - x.price)
    above = sorted((x for x in clustered if x.price > close), key=lambda x: x.price - close)
    support = below[0] if below else None
    resistance = above[0] if above else None

    # Pattern detection uses completed candles only and a bounded recent window.
    lookback = session[-8:]
    setup: Optional[SetupKind] = None
    setup_direction = Direction.UNKNOWN
    trigger: Optional[float] = None
    invalidation: Optional[float] = None
    reasons: list[str] = []
    touch_tol = max((atr_value or 1.0) * settings.support_touch_atr, 2.0)
    reclaim_buffer = max((atr_value or 1.0) * settings.support_reclaim_atr, 1.0)
    # Liquidity sweep/reclaim has priority over a generic bounce/rejection label.
    # It is a deterministic wick-through-and-close-back pattern, not a claim about hidden orders.
    recent3 = session[-3:]
    recent_low3 = min(c.low for c in recent3)
    recent_high3 = max(c.high for c in recent3)
    sweep_supports = [x for x in below if 0 < close - x.price <= max(5.0 * (atr_value or 1.0), 100.0)]
    for level in sweep_supports:
        swept = recent_low3 < level.price - reclaim_buffer
        reclaimed = latest.close >= level.price + reclaim_buffer
        bullish_bar = latest.close > latest.open or latest.close > lookback[-2].close
        if swept and reclaimed and bullish_bar and close - level.price <= settings.max_entry_extension_atr * (atr_value or 1.0):
            setup, setup_direction, trigger, invalidation = SetupKind.LIQUIDITY_SWEEP_RECLAIM, Direction.BULLISH, latest.close, recent_low3
            reasons.append(f"BULLISH_LIQUIDITY_SWEEP_RECLAIM:{level.source}@{level.price:.2f}")
            break
    if setup is None:
        sweep_resistances = [x for x in above if 0 < x.price - close <= max(5.0 * (atr_value or 1.0), 100.0)]
        for level in sweep_resistances:
            swept = recent_high3 > level.price + reclaim_buffer
            reclaimed = latest.close <= level.price - reclaim_buffer
            bearish_bar = latest.close < latest.open or latest.close < lookback[-2].close
            if swept and reclaimed and bearish_bar and level.price - close <= settings.max_entry_extension_atr * (atr_value or 1.0):
                setup, setup_direction, trigger, invalidation = SetupKind.LIQUIDITY_SWEEP_RECLAIM, Direction.BEARISH, latest.close, recent_high3
                reasons.append(f"BEARISH_LIQUIDITY_SWEEP_RECLAIM:{level.source}@{level.price:.2f}")
                break
    if setup is None and support and len(lookback) >= 2:
        # Preserve the most recent touch and use the low of that touch-to-confirmation sequence
        # as invalidation; unrelated older swings must not create an oversized stop.
        touches = [i for i, candle in enumerate(lookback) if candle.low <= support.price + touch_tol]
        touch_index = touches[-1] if touches else None
        sequence = lookback[touch_index:] if touch_index is not None else []
        bars_since_touch = len(lookback) - 1 - touch_index if touch_index is not None else None
        reclaimed = latest.close >= support.price + reclaim_buffer
        bullish_bar = latest.close > latest.open or latest.close > lookback[-2].close
        if touch_index is not None and bars_since_touch is not None and bars_since_touch <= 7 and len(sequence) >= 1 and reclaimed and bullish_bar:
            setup, setup_direction, trigger, invalidation = SetupKind.SUPPORT_BOUNCE, Direction.BULLISH, latest.close, min(c.low for c in sequence)
            reasons.append(f"SUPPORT_BOUNCE:{support.source}@{support.price:.2f};touch_age_bars={bars_since_touch};sequence_low={invalidation:.2f}")
    if setup is None and resistance and len(lookback) >= 2:
        touches = [i for i, candle in enumerate(lookback) if candle.high >= resistance.price - touch_tol]
        touch_index = touches[-1] if touches else None
        sequence = lookback[touch_index:] if touch_index is not None else []
        bars_since_touch = len(lookback) - 1 - touch_index if touch_index is not None else None
        rejected = latest.close <= resistance.price - reclaim_buffer
        bearish_bar = latest.close < latest.open or latest.close < lookback[-2].close
        if touch_index is not None and bars_since_touch is not None and bars_since_touch <= 7 and len(sequence) >= 1 and rejected and bearish_bar:
            setup, setup_direction, trigger, invalidation = SetupKind.RESISTANCE_REJECTION, Direction.BEARISH, latest.close, max(c.high for c in sequence)
            reasons.append(f"RESISTANCE_REJECTION:{resistance.source}@{resistance.price:.2f};touch_age_bars={bars_since_touch};sequence_high={invalidation:.2f}")

    # Breakout/retest: a previous completed bar broke the confirmed pivot, and a later bar retested it.
    if setup is None and above and len(session) >= 8:
        pivot_res = next((x for x in above if x.source.find("CONFIRMED_SWING_HIGH") >= 0), None)
        if pivot_res:
            break_indexes = [i for i, c in enumerate(session[-8:-1]) if c.close > pivot_res.price + reclaim_buffer]
            retested = min(c.low for c in session[-3:]) <= pivot_res.price + touch_tol and latest.close > pivot_res.price + reclaim_buffer
            if break_indexes and retested and close - pivot_res.price <= settings.max_entry_extension_atr * (atr_value or 1.0):
                setup, setup_direction, trigger, invalidation = SetupKind.BREAKOUT_RETEST, Direction.BULLISH, latest.close, min(c.low for c in session[-4:])
                reasons.append(f"BREAKOUT_RETEST:{pivot_res.source}@{pivot_res.price:.2f}")
    if setup is None and below and len(session) >= 8:
        pivot_sup = next((x for x in below if x.source.find("CONFIRMED_SWING_LOW") >= 0), None)
        if pivot_sup:
            break_indexes = [i for i, c in enumerate(session[-8:-1]) if c.close < pivot_sup.price - reclaim_buffer]
            retested = max(c.high for c in session[-3:]) >= pivot_sup.price - touch_tol and latest.close < pivot_sup.price - reclaim_buffer
            if break_indexes and retested and pivot_sup.price - close <= settings.max_entry_extension_atr * (atr_value or 1.0):
                setup, setup_direction, trigger, invalidation = SetupKind.BREAKDOWN_RETEST, Direction.BEARISH, latest.close, max(c.high for c in session[-4:])
                reasons.append(f"BREAKDOWN_RETEST:{pivot_sup.source}@{pivot_sup.price:.2f}")

    # Trend continuation pullback is a separate pattern; it is not inferred from a direction label alone.
    if setup is None and len(session) >= 25 and ema9 and ema21 and atr_value:
        recent = session[-5:]
        pullback_band = settings.continuation_pullback_atr * atr_value
        recent_low = min(c.low for c in recent)
        recent_high = max(c.high for c in recent)
        if price_bias == Direction.BULLISH and recent_low <= ema21 + pullback_band and latest.close > latest.open and latest.close > recent[-2].close and close - latest.low <= settings.max_entry_extension_atr * atr_value:
            setup, setup_direction, trigger, invalidation = SetupKind.TREND_PULLBACK, Direction.BULLISH, latest.close, recent_low
            reasons.append("BULLISH_TREND_PULLBACK_RECLAIM")
        elif price_bias == Direction.BEARISH and recent_high >= ema21 - pullback_band and latest.close < latest.open and latest.close < recent[-2].close and latest.high - close <= settings.max_entry_extension_atr * atr_value:
            setup, setup_direction, trigger, invalidation = SetupKind.TREND_PULLBACK, Direction.BEARISH, latest.close, recent_high
            reasons.append("BEARISH_TREND_PULLBACK_RECLAIM")

    # Regime classification: a confirmed aligned setup takes priority; a range-edge trade
    # can remain a SIDEWAYS regime while carrying a directional setup.
    ret15 = r15 or 0.0
    range12 = max(c.high for c in session[-12:]) - min(c.low for c in session[-12:]) if len(session) >= 12 else float("inf")
    # Sideways is based on compressed range and low directional displacement, not EMA order alone.
    sideways = bool(atr_value and abs(ret15) <= 0.85 * atr_value and range12 <= 4.0 * atr_value)
    if sideways and setup == SetupKind.SUPPORT_BOUNCE:
        setup = SetupKind.RANGE_EDGE_REVERSAL
        reasons.append("SIDEWAYS_RANGE_LOW_BOUNCE")
    elif sideways and setup == SetupKind.RESISTANCE_REJECTION:
        setup = SetupKind.RANGE_EDGE_REVERSAL
        reasons.append("SIDEWAYS_RANGE_HIGH_REJECTION")
    # Inspect the execution bias immediately before the last three candles. This lets the
    # regime label record a bullish-to-bearish (or reverse) transition even when the current
    # 5-minute EMA has already flattened to MIXED.
    prior_session = session[:-3] if len(session) > 35 else []
    prior_exec_bias = Direction.UNKNOWN
    if len(prior_session) >= 25:
        prior_closes = [c.close for c in prior_session]
        prior_ema9 = ema(prior_closes[-min(len(prior_closes), 40):], 9)
        prior_ema21 = ema(prior_closes[-min(len(prior_closes), 60):], 21)
        prior_r5 = returns(prior_session, 5)
        if prior_ema9 and prior_ema21 and prior_closes[-1] >= prior_ema9 >= prior_ema21 and (prior_r5 or 0) > 0:
            prior_exec_bias = Direction.BULLISH
        elif prior_ema9 and prior_ema21 and prior_closes[-1] <= prior_ema9 <= prior_ema21 and (prior_r5 or 0) < 0:
            prior_exec_bias = Direction.BEARISH
    if setup_direction == Direction.BULLISH and oi_direction == Direction.BULLISH and (higher_bias == Direction.BEARISH or prior_exec_bias == Direction.BEARISH):
        regime = Regime.REVERSAL_BEAR_TO_BULL
        reasons.append("REVERSAL_FROM_PRIOR_BEARISH_BIAS")
    elif setup_direction == Direction.BEARISH and oi_direction == Direction.BEARISH and (higher_bias == Direction.BULLISH or prior_exec_bias == Direction.BULLISH):
        regime = Regime.REVERSAL_BULL_TO_BEAR
        reasons.append("REVERSAL_FROM_PRIOR_BULLISH_BIAS")
    elif setup_direction in {Direction.BULLISH, Direction.BEARISH} and setup_direction == oi_direction and sideways:
        regime = Regime.SIDEWAYS
    elif sideways:
        regime = Regime.SIDEWAYS
    elif setup_direction == Direction.BULLISH and oi_direction == Direction.BULLISH:
        regime = Regime.CONTINUOUS_BULLISH
    elif setup_direction == Direction.BEARISH and oi_direction == Direction.BEARISH:
        regime = Regime.CONTINUOUS_BEARISH
    elif price_bias == Direction.BULLISH and oi_direction == Direction.BULLISH:
        regime = Regime.CONTINUOUS_BULLISH
    elif price_bias == Direction.BEARISH and oi_direction == Direction.BEARISH:
        regime = Regime.CONTINUOUS_BEARISH
    else:
        regime = Regime.TRANSITION

    # Structural confidence is a price-only measure. OI confidence is tracked separately and
    # combined only in the decision stage, so an OI-aligned setup cannot inflate structure quality.
    confidence = 0.65 if setup else 0.0
    if setup and price_bias == setup_direction:
        confidence += 0.20
    if setup and higher_bias == setup_direction:
        confidence += 0.15
    confidence = min(1.0, confidence)
    reasons.extend(quality_reasons)
    direction = setup_direction if setup else price_bias
    if not setup:
        reasons.append("NO_CONFIRMED_PRICE_SETUP")
    result = PriceAnalysis(
        regime, direction, higher_bias,
        "SETUP_CONFIRMED" if setup else ("TREND_UP" if price_bias == Direction.BULLISH else "TREND_DOWN" if price_bias == Direction.BEARISH else "RANGE_OR_TRANSITION"),
        setup, support.price if support else None, resistance.price if resistance else None,
        support.source if support else None, resistance.source if resistance else None,
        atr_value, r1, r3, r5, r15, trigger, invalidation, confidence, tuple(reasons),
        tuple(sorted(above, key=lambda x: x.price)), tuple(sorted(below, key=lambda x: x.price, reverse=True)),
    )
    if _collect_recent_setups:
        events = _detect_recent_confirmed_setups(session, quote, settings, now)
        result = replace(result, recent_setups=tuple(events))
    return result


def _detect_recent_confirmed_setups(
    session: Sequence[Candle], quote: Quote, settings: Settings, now: datetime
) -> list[dict[str, object]]:
    """Replay only recent completed candle prefixes to make setup events visible in audit logs.

    Each prefix is analysed with its own historical close and without current OI/context levels,
    so a later candle or OI snapshot cannot create a setup at an earlier timestamp.
    Historical events are diagnostic only; the live risk gate still uses the current quote.
    """
    events: list[dict[str, object]] = []
    start = max(0, len(session) - settings.recent_setup_event_bars)
    for idx in range(start, len(session)):
        candle = session[idx]
        as_of = candle.start + timedelta(minutes=1, microseconds=1)
        if as_of > now.astimezone(candle.start.tzinfo):
            continue
        prefix = list(session[:idx + 1])
        hist_quote = Quote(
            instrument_key=quote.instrument_key, last_price=candle.close, received_at=as_of,
            source_time=candle.start + timedelta(minutes=1), prev_close=quote.prev_close,
            session_open=prefix[0].open, session_high=max(x.high for x in prefix),
            session_low=min(x.low for x in prefix), prev_high=quote.prev_high,
            prev_low=quote.prev_low, volume=sum(x.volume for x in prefix),
        )
        historical = analyze_price(prefix, hist_quote, settings, Direction.UNKNOWN, now=as_of,
                                   context_levels=(), _collect_recent_setups=False)
        if historical.setup is None or historical.direction not in {Direction.BULLISH, Direction.BEARISH}:
            continue
        age_bars = len(session) - idx - 1
        invalidation = historical.invalidation_price
        invalidated = False
        if invalidation is not None and age_bars > 0:
            later = session[idx + 1:]
            if historical.direction == Direction.BULLISH:
                invalidated = any(x.low <= invalidation for x in later)
            else:
                invalidated = any(x.high >= invalidation for x in later)
        trigger = historical.trigger_price if historical.trigger_price is not None else candle.close
        current = quote.last_price
        extension = max(0.0, current - trigger) if historical.direction == Direction.BULLISH else max(0.0, trigger - current)
        atr_value = historical.atr or 0.0
        if invalidated:
            status = "INVALIDATED_AFTER_CONFIRMATION"
        elif age_bars > 0 and atr_value > 0 and extension > settings.max_entry_extension_atr * atr_value:
            status = "MISSED_OR_STALE_SETUP"
        elif age_bars > 0:
            status = "RECENT_CONFIRMED_REVALIDATE_CURRENT_PRICE"
        else:
            status = "CONFIRMED_ON_LATEST_COMPLETED_CANDLE"
        events.append({
            "setup": historical.setup.value, "direction": historical.direction.value,
            "confirmed_at": (candle.start + timedelta(minutes=1)).isoformat(),
            "age_completed_bars": age_bars, "trigger_price": trigger,
            "invalidation_price": invalidation, "support": historical.support,
            "resistance": historical.resistance, "state": status,
            "current_entry_reference": current,
        })
    # At most one event per setup/direction/confirmation time; keep chronological evidence.
    dedup: dict[tuple[object, ...], dict[str, object]] = {}
    for event in events:
        key = (event["setup"], event["direction"], event["confirmed_at"])
        dedup[key] = event
    return list(dedup.values())


# ===== Inlined module: risk_engine.py =====

"""Structural underlying risk plans and conservative option-premium scenario estimates."""









class RiskRejected(ValueError):
    def __init__(self, code: str, message: str):
        super().__init__(message)
        self.code = code


def build_risk_plan(price: PriceAnalysis, direction: Direction, entry: float, settings: Settings, *, tick_size: float = 0.05) -> RiskPlan:
    if direction not in {Direction.BULLISH, Direction.BEARISH}:
        raise RiskRejected("NO_DIRECTION", "Direction must be bullish or bearish")
    if not price.setup or price.invalidation_price is None or not price.atr or price.atr <= 0:
        raise RiskRejected("NO_STRUCTURAL_INVALIDATION", "No confirmed setup-specific invalidation level")
    if not isfinite(entry) or entry <= 0:
        raise RiskRejected("INVALID_ENTRY_PRICE", "Current underlying entry price is invalid")
    if price.trigger_price is not None:
        extension = entry - price.trigger_price if direction == Direction.BULLISH else price.trigger_price - entry
        max_extension = settings.max_entry_extension_atr * price.atr
        if extension > max_extension:
            raise RiskRejected("ENTRY_TOO_EXTENDED", f"Current entry has moved {extension:.2f} points beyond the confirmed trigger; limit is {max_extension:.2f} points")
    buffer = max(tick_size, settings.stop_buffer_atr * price.atr)
    if direction == Direction.BULLISH:
        stop = price.invalidation_price - buffer
        risk = entry - stop
        if risk <= 0:
            raise RiskRejected("INVALID_STOP_SIDE", "Bullish stop must be below current entry")
        if risk > settings.max_stop_atr * price.atr:
            raise RiskRejected("STOP_TOO_WIDE", f"Structural risk {risk:.2f} exceeds {settings.max_stop_atr:.2f} ATR")
        levels = sorted((x for x in price.levels_above if x.price > entry + tick_size), key=lambda x: x.price)
        if not levels:
            raise RiskRejected("NO_OPPOSING_BARRIER", "No valid resistance/target level exists above entry")
        t1 = levels[0]
        reward1 = t1.price - entry
        rr1 = reward1 / risk
        if reward1 <= 0 or rr1 < settings.min_underlying_rr:
            raise RiskRejected("RR_BELOW_2R", f"Nearest resistance {t1.price:.2f} gives {rr1:.2f}R; cannot skip it for a farther target")
        later = next((x for x in levels[1:] if x.price > t1.price + tick_size), None)
        if later:
            t2, t2_source = later.price, later.source
        else:
            ext = max(entry + settings.target2_extension_r * risk, t1.price + max(tick_size, 0.1 * price.atr))
            if (ext - entry) > settings.max_target2_atr * price.atr:
                t2, t2_source = None, None
            else:
                t2, t2_source = ext, "R_MULTIPLE_EXTENSION_ESTIMATE"
        reward2 = t2 - entry if t2 is not None else None
        rr2 = reward2 / risk if reward2 is not None and reward2 > 0 else None
        return RiskPlan(direction, entry, stop, t1.price, t2, risk, reward1, reward2, rr1, rr2, f"SETUP_INVALIDATION:{price.setup.value}", t1.source, t2_source)
    stop = price.invalidation_price + buffer
    risk = stop - entry
    if risk <= 0:
        raise RiskRejected("INVALID_STOP_SIDE", "Bearish stop must be above current entry")
    if risk > settings.max_stop_atr * price.atr:
        raise RiskRejected("STOP_TOO_WIDE", f"Structural risk {risk:.2f} exceeds {settings.max_stop_atr:.2f} ATR")
    levels = sorted((x for x in price.levels_below if x.price < entry - tick_size), key=lambda x: x.price, reverse=True)
    if not levels:
        raise RiskRejected("NO_OPPOSING_BARRIER", "No valid support/target level exists below entry")
    t1 = levels[0]
    reward1 = entry - t1.price
    rr1 = reward1 / risk
    if reward1 <= 0 or rr1 < settings.min_underlying_rr:
        raise RiskRejected("RR_BELOW_2R", f"Nearest support {t1.price:.2f} gives {rr1:.2f}R; cannot skip it for a farther target")
    later = next((x for x in levels[1:] if x.price < t1.price - tick_size), None)
    if later:
        t2, t2_source = later.price, later.source
    else:
        ext = min(entry - settings.target2_extension_r * risk, t1.price - max(tick_size, 0.1 * price.atr))
        if (entry - ext) > settings.max_target2_atr * price.atr:
            t2, t2_source = None, None
        else:
            t2, t2_source = ext, "R_MULTIPLE_EXTENSION_ESTIMATE"
    reward2 = entry - t2 if t2 is not None else None
    rr2 = reward2 / risk if reward2 is not None and reward2 > 0 else None
    return RiskPlan(direction, entry, stop, t1.price, t2, risk, reward1, reward2, rr1, rr2, f"SETUP_INVALIDATION:{price.setup.value}", t1.source, t2_source)


def _scenario_exit(quote: OptionQuote, d_underlying: float, horizon_minutes: float, iv_change_points: float, settings: Settings) -> float:
    g = quote.greeks
    if g.delta is None or g.gamma is None or g.theta is None or g.vega is None:
        raise RiskRejected("GREEKS_MISSING", "Delta, gamma, theta and vega are required for the premium scenario")
    # Upstox Greeks are treated as delta per underlying point, gamma per squared point,
    # theta per calendar day and vega per one IV percentage-point change. This is an explicit
    # scenario approximation, not an exchange-guaranteed future premium.
    elapsed_days = horizon_minutes / 375.0
    projected = quote.mid + g.delta * d_underlying + 0.5 * g.gamma * d_underlying * d_underlying + g.theta * elapsed_days + g.vega * iv_change_points
    return max(0.05, projected)


def calculate_option_risk(quote: OptionQuote, risk: RiskPlan, settings: Settings) -> OptionRisk:
    if quote.bid <= 0 or quote.ask <= 0 or quote.ask < quote.bid:
        raise RiskRejected("NO_VALID_OPTION_QUOTES", "Two-sided, non-crossed positive bid/ask is required")
    if quote.ask_qty < settings.min_ask_qty or quote.bid_qty < settings.min_bid_qty:
        raise RiskRejected("OPTION_DEPTH_TOO_LOW", "Bid/ask depth is below configured minimum")
    if quote.volume < settings.min_option_volume:
        raise RiskRejected("OPTION_LIQUIDITY_TOO_LOW", "Cumulative option volume is below configured minimum")
    if quote.spread_pct > settings.max_option_spread_pct:
        raise RiskRejected("OPTION_SPREAD_TOO_WIDE", f"Spread is {quote.spread_pct:.2f}% of mid")
    g = quote.greeks
    if any(v is None for v in (g.delta, g.gamma, g.theta, g.vega)):
        raise RiskRejected("GREEKS_MISSING", "Delta, gamma, theta and vega are required for the premium-risk scenario")
    entry = quote.ask + settings.slippage_points_per_side
    stop_d = risk.stop_underlying - risk.entry_underlying
    t1_d = risk.target1_underlying - risk.entry_underlying
    t2_d = risk.target2_underlying - risk.entry_underlying if risk.target2_underlying is not None else None
    stop_mid = _scenario_exit(quote, stop_d, settings.target_horizon_minutes, 0.0, settings)
    t1_mid = _scenario_exit(quote, t1_d, settings.target_horizon_minutes, -settings.iv_target_shock_points, settings)
    t2_mid = _scenario_exit(quote, t2_d, settings.target_horizon_minutes, -settings.iv_target_shock_points, settings) if t2_d is not None else None
    half_spread = quote.spread / 2.0
    stop_bid = max(0.05, stop_mid - half_spread - settings.slippage_points_per_side)
    t1_bid = max(0.05, t1_mid - half_spread - settings.slippage_points_per_side)
    t2_bid = max(0.05, t2_mid - half_spread - settings.slippage_points_per_side) if t2_mid is not None else None
    costs = max(0.0, settings.option_round_trip_cost_per_unit)
    risk_net = entry - stop_bid + costs
    reward1_net = t1_bid - entry - costs
    reward2_net = t2_bid - entry - costs if t2_bid is not None else None
    if risk_net <= 0 or reward1_net <= 0:
        raise RiskRejected("OPTION_PREMIUM_GEOMETRY_INVALID", "Projected option premium risk/reward is not positive after costs")
    rr1 = reward1_net / risk_net
    rr2 = reward2_net / risk_net if reward2_net is not None and reward2_net > 0 else None
    if rr1 < settings.min_option_net_rr:
        raise RiskRejected("OPTION_NET_RR_BELOW_2R", f"Option net reward/risk to T1 is {rr1:.2f}R after modeled spread/slippage/costs")
    return OptionRisk(entry, stop_bid, t1_bid, t2_bid, risk_net, reward1_net, reward2_net, rr1, rr2, quote.spread_pct, (
        "Entry uses ask plus configured slippage",
        "Exit uses modeled premium less half-spread and configured slippage",
        f"Target scenario assumes IV decreases by {settings.iv_target_shock_points:.2f} points",
        f"Theta horizon {settings.target_horizon_minutes:.1f} minutes; costs {costs:.2f} premium points round-trip",
        "Greek repricing is a scenario estimate, not a guaranteed future quote",
    ))


# ===== Inlined module: contract_selector.py =====

"""Deterministic CE/PE selection restricted to the configured ATM offsets."""











@dataclass(frozen=True)
class CandidateEvaluation:
    quote: OptionQuote
    offset: int
    option_risk: OptionRisk
    ranking_score: float


@dataclass(frozen=True)
class ContractSelection:
    selected: Optional[CandidateEvaluation]
    atm_strike: float
    evaluations: tuple[CandidateEvaluation, ...]
    rejections: tuple[dict[str, str | float | int], ...]


def select_contract(snapshot: ChainSnapshot, direction: Direction, risk: RiskPlan, settings: Settings, *, now: Optional[datetime] = None) -> ContractSelection:
    if direction not in {Direction.BULLISH, Direction.BEARISH}:
        raise RiskRejected("NO_DIRECTION", "Only directional hypotheses may select an option")
    reference_time = now or snapshot.fetched_at
    if reference_time.tzinfo is None or reference_time.utcoffset() is None:
        raise RiskRejected("OPTION_QUOTE_TIME_NAIVE", "Option quote evaluation timestamp must be timezone-aware")
    rows = sorted(snapshot.rows, key=lambda r: r.strike)
    atm_i = min(range(len(rows)), key=lambda i: abs(rows[i].strike - snapshot.spot))
    atm_strike = rows[atm_i].strike
    if direction == Direction.BULLISH:
        side = "CE"
        offsets = (0, -1, -2)
    else:
        side = "PE"
        offsets = (0, 1, 2)
    evals: list[CandidateEvaluation] = []
    rejects: list[dict[str, str | float | int]] = []
    for offset in offsets:
        idx = atm_i + offset
        if idx < 0 or idx >= len(rows):
            rejects.append({"offset": offset, "reason_code": "STRIKE_OUTSIDE_CHAIN"})
            continue
        row = rows[idx]
        quote = row.call if side == "CE" else row.put
        if quote is None:
            rejects.append({"offset": offset, "reason_code": "CONTRACT_MISSING"})
            continue
        if quote.expiry != snapshot.expiry:
            rejects.append({"offset": offset, "reason_code": "WRONG_EXPIRY"})
            continue
        if quote.quote_time is None:
            rejects.append({"offset": offset, "strike": quote.strike, "reason_code": "OPTION_QUOTE_TIMESTAMP_MISSING"})
            continue
        if quote.quote_time.tzinfo is None or quote.quote_time.utcoffset() is None:
            rejects.append({"offset": offset, "strike": quote.strike, "reason_code": "OPTION_QUOTE_TIMESTAMP_NAIVE"})
            continue
        quote_age = (reference_time - quote.quote_time).total_seconds()
        if quote_age < -5.0:
            rejects.append({"offset": offset, "strike": quote.strike, "reason_code": "OPTION_QUOTE_TIMESTAMP_IN_FUTURE", "detail": f"Quote timestamp is {-quote_age:.1f}s ahead of evaluation"})
            continue
        quote_age = max(0.0, quote_age)
        if quote_age > settings.max_option_quote_age_seconds:
            rejects.append({"offset": offset, "strike": quote.strike, "reason_code": "OPTION_QUOTE_STALE", "quote_age_seconds": round(quote_age, 2), "detail": f"Quote age {quote_age:.1f}s exceeds {settings.max_option_quote_age_seconds}s"})
            continue
        try:
            option_risk = calculate_option_risk(quote, risk, settings)
        except RiskRejected as exc:
            rejects.append({"offset": offset, "strike": quote.strike, "reason_code": exc.code, "detail": str(exc)})
            continue
        # Ranking rewards net RR and liquidity while penalising spreads; candidates remain in allowed bands.
        rr_component = min(option_risk.net_rr1, 4.0) / 4.0
        spread_component = max(0.0, 1.0 - option_risk.spread_pct / settings.max_option_spread_pct)
        depth_ratio = min(quote.bid_qty, quote.ask_qty) / max(settings.min_bid_qty, settings.min_ask_qty, 1.0)
        depth_component = min(1.0, depth_ratio / 10.0)
        volume_component = min(1.0, quote.volume / 100_000.0)
        gdelta = abs(quote.greeks.delta) if quote.greeks.delta is not None else 0.0
        delta_component = max(0.0, 1.0 - abs(gdelta - 0.50) / 0.50)
        proximity_bonus = 0.04 if offset == 0 else 0.02 if abs(offset) == 1 else 0.0
        score = 0.42 * rr_component + 0.23 * spread_component + 0.15 * depth_component + 0.10 * volume_component + 0.10 * delta_component + proximity_bonus
        evals.append(CandidateEvaluation(quote, offset, option_risk, score))
    selected = max(evals, key=lambda e: e.ranking_score) if evals else None
    return ContractSelection(selected, atm_strike, tuple(sorted(evals, key=lambda e: e.ranking_score, reverse=True)), tuple(rejects))


# ===== Inlined module: engine.py =====

"""Authoritative single-pass scan pipeline."""





















IST = ZoneInfo("Asia/Kolkata")


class ScannerEngine:
    def __init__(self, settings: Settings, logger: Optional[logging.Logger] = None, client: Optional[UpstoxClient] = None, notifier: Optional[Notifier] = None):
        self.settings = settings
        self.log = logger or logging.getLogger("nifty_scanner")
        self.client = client or UpstoxClient(settings, self.log)
        self.notifier = notifier or Notifier(settings, self.log)
        self.store = StateStore(settings.state_file)

    def scan(self, *, now: Optional[datetime] = None) -> ScanResult:
        now = now or datetime.now(IST)
        if now.tzinfo is None or now.utcoffset() is None:
            raise ValueError("scan now must be timezone-aware")
        now = now.astimezone(IST)
        session_date = now.date()
        cfg_errors = self.settings.validate()
        if cfg_errors:
            raise UpstoxError("CONFIG_INVALID", "; ".join(cfg_errors))
        with self.store.lock():
            state = self.store.load(session_date.isoformat())
            if not _market_hours(now):
                result = self._blocked_result(now, "OUTSIDE_MARKET_HOURS", "Current IST time is outside weekday NSE regular session hours", None, None)
                state["last_scan_at"] = now.isoformat()
                self.store.save(state)
                self._audit(result)
                return result
            try:
                master_rows, master_status = self.client.get_instrument_master()
                underlying = self.client.resolve_underlying(master_rows)
                expiry, roll_reason = self.client.resolve_expiry(master_rows, underlying, session_date)
                fetched_at = datetime.now(IST)
                chain = self.client.fetch_option_chain(underlying, expiry, session_date=session_date, fetched_at=fetched_at)
                quotes = self.client.fetch_quotes([underlying], received_at=datetime.now(IST))
                spot_quote = quotes[underlying.instrument_key]
                # Futures are optional context; failure must not create a fictitious VWAP or block otherwise valid spot structure.
                future = self.client.resolve_future(master_rows, underlying, session_date)
                future_vwap, future_key, future_status = self._optional_futures_context(future, now)
                candles = self.client.fetch_intraday_candles(underlying.instrument_key, now=now)
                if candles[-1].start.date() != session_date:
                    raise UpstoxError("CANDLE_SESSION_MISMATCH", "Latest completed candle is not from the current trading session")
                candle_close_time = candles[-1].start + timedelta(minutes=1)
                candle_age = max(0.0, (now - candle_close_time).total_seconds())
                if candle_age > self.settings.candle_max_age_seconds:
                    raise UpstoxError("CANDLE_STALE", f"Latest completed candle age is {candle_age:.0f} seconds")
                prev_chain = None
                first_session_chain = None
                if state.get("previous_chain"):
                    try:
                        candidate_prev = snapshot_from_dict(state["previous_chain"])
                        if candidate_prev.session_date == session_date and candidate_prev.expiry == expiry and candidate_prev.underlying_key == underlying.instrument_key and candidate_prev.fetched_at < chain.fetched_at:
                            prev_chain = candidate_prev
                    except Exception as exc:
                        self.log.warning("Discarding unreadable prior snapshot state (%s)", type(exc).__name__)
                if state.get("first_session_chain"):
                    try:
                        candidate_base = snapshot_from_dict(state["first_session_chain"])
                        if candidate_base.session_date == session_date and candidate_base.expiry == expiry and candidate_base.underlying_key == underlying.instrument_key:
                            first_session_chain = candidate_base
                    except Exception as exc:
                        self.log.warning("Discarding unreadable first-session baseline (%s)", type(exc).__name__)
                score_history = state.get("oi_score_history", [])
                prior_scores = [float(x["score"]) if isinstance(x, dict) and "score" in x else float(x) for x in score_history if isinstance(x, (dict, int, float))]
                oi = calculate_oi_evidence(chain, prev_chain, self.settings, now=max(now, chain.fetched_at), prior_score_history=prior_scores, session_baseline=first_session_chain)
                if oi.status == "UNCHANGED":
                    oi = self._retain_last_oi_evidence(oi, state, max(now, chain.fetched_at))
                if master_status == "CACHE_STALE":
                    oi = replace(oi, confidence=oi.confidence * 0.8, summary=oi.summary + "; INSTRUMENT_MASTER_CACHE_STALE")
                context_levels = derive_oi_wall_levels(chain, max_strikes=max(4, self.settings.oi_near_atm_strikes))
                if future_vwap is not None and future_vwap > 0:
                    context_levels.append(Level(future_vwap, "CONTEXT", "VALID_FUTURES_VWAP", 0.65, now))
                price = analyze_price(candles, spot_quote, self.settings, oi.direction, now=now, context_levels=context_levels)
                # Align price to live quote only by source timestamps. Do not veto naturally newer quotes.
                if spot_quote.source_time and abs((spot_quote.source_time - candle_close_time).total_seconds()) <= 60:
                    if price.atr and abs(spot_quote.last_price - candles[-1].close) > self.settings.max_quote_candle_divergence_atr * price.atr:
                        result = ScanResult(now, session_date, "NO_TRADE", "QUOTE_CANDLE_DIVERGENCE", "Quote and completed candle materially diverge despite aligned timestamps", oi, price, expiry=expiry, diagnostics=self._diagnostics(underlying.instrument_key, master_status, roll_reason, candle_age, future_key, future_status, candles[-1].start.isoformat(), spot_quote.last_price))
                        return self._finish_scan(result, state, chain, oi, now, session_date, notify=False)
                result = self._decide(now, session_date, chain, oi, price, spot_quote, expiry, underlying.instrument_key, master_status, roll_reason, candle_age, future_key, future_status, candles[-1].start.isoformat())
                return self._finish_scan(result, state, chain, oi, now, session_date, notify=True)
            except UpstoxError as exc:
                self.log.warning("Scan blocked: %s (%s)", exc.code, str(exc))
                result = self._blocked_result(now, exc.code, str(exc), None, None)
                state["last_scan_at"] = now.isoformat()
                # Critical: failed calls never overwrite the last successful OI snapshot.
                self.store.save(state)
                self._audit(result)
                return result
            except StateError:
                raise
            except Exception as exc:
                self.log.exception("Unexpected scanner failure")
                result = self._blocked_result(now, "UNEXPECTED_INTERNAL_ERROR", f"{type(exc).__name__}: {exc}", None, None)
                # Do not overwrite state on unexpected errors.
                self._audit(result)
                return result

    def _optional_futures_context(self, future, now: datetime):
        if future is None:
            return None, None, "FUTURE_NOT_FOUND"
        try:
            q = self.client.fetch_quotes([future], received_at=datetime.now(IST))[future.instrument_key]
            candles = self.client.fetch_intraday_candles(future.instrument_key, now=now)
            valid = [c for c in candles if c.start.date() == now.date() and c.volume > 0]
            volume = sum(c.volume for c in valid)
            if volume <= 0:
                return None, future.instrument_key, "FUTURE_VOLUME_MISSING"
            # One-minute OHLCV approximation: typical price (H+L+C)/3 weighted by volume.
            # It is not tick-level VWAP; report its method explicitly in diagnostics/docs.
            vwap = sum(((c.high + c.low + c.close) / 3.0) * c.volume for c in valid) / volume
            return vwap, future.instrument_key, "VALID_FUTURES_VWAP"
        except Exception as exc:
            self.log.warning("Futures context unavailable (%s)", type(exc).__name__)
            return None, future.instrument_key, "FUTURE_CONTEXT_UNAVAILABLE"

    def _decide(self, now, session_date, chain, oi, price, spot_quote, expiry, underlying_key, master_status, roll_reason, candle_age, future_key, future_status, last_completed_candle=None) -> ScanResult:
        diagnostics = self._diagnostics(underlying_key, master_status, roll_reason, candle_age, future_key, future_status, last_completed_candle, spot_quote.last_price)
        usable_oi_statuses = {"FRESH", "DELAYED", "RETAINED"}
        if oi.status not in usable_oi_statuses or oi.direction == Direction.UNKNOWN:
            if oi.status == "STALE":
                code = "OI_STALE"
            elif oi.status in {"MISSING_BASELINE", "UNCHANGED"}:
                code = "OI_BASELINE_MISSING" if oi.status == "MISSING_BASELINE" else "OI_UNCHANGED_NO_PRIOR_EVIDENCE"
            else:
                code = "OI_UNAVAILABLE"
            return ScanResult(now, session_date, "NO_TRADE", code, oi.summary, oi, price, expiry=expiry, diagnostics=diagnostics)

        if not price.setup:
            code = "SIDEWAYS_NO_EDGE" if price.regime == Regime.SIDEWAYS else "OI_PRICE_DIVERGENCE" if price.direction not in {Direction.UNKNOWN, oi.direction} else "NO_CONFIRMED_SETUP"
            return ScanResult(now, session_date, "NO_TRADE", code, "No confirmed price setup aligned with current OI direction", oi, price, expiry=expiry, diagnostics=diagnostics)

        # A mixed OI score can only be overridden by an unusually clear price setup with matching
        # higher-timeframe confirmation. OI remains visible as MIXED; it is never relabelled bullish/bearish.
        if oi.direction == Direction.MIXED:
            if (price.direction not in {Direction.BULLISH, Direction.BEARISH}
                    or price.structure_confidence < self.settings.mixed_oi_min_structure_confidence
                    or price.higher_timeframe_bias != price.direction):
                return ScanResult(now, session_date, "NO_TRADE", "OI_MIXED_WAIT_PRICE_CONFIRMATION",
                    "OI evidence is mixed; price setup lacks the configured confidence and matching five-minute bias required for an exception",
                    oi, price, expiry=expiry, diagnostics={**diagnostics, "mixed_oi_override": "REJECTED"})
            trade_direction = price.direction
            diagnostics["mixed_oi_override"] = "STRONG_PRICE_AND_HTF_CONFIRMATION"
        else:
            trade_direction = oi.direction

        if price.direction != trade_direction:
            return ScanResult(now, session_date, "NO_TRADE", "OI_PRICE_DIVERGENCE", "Confirmed setup direction conflicts with current OI direction", oi, price, expiry=expiry, diagnostics=diagnostics)

        min_confidence = 0.60
        if oi.status in {"DELAYED", "RETAINED"}:
            min_confidence = self.settings.retained_oi_min_structure_confidence
            if oi.confidence < 0.15:
                return ScanResult(now, session_date, "NO_TRADE", "OI_RETAINED_CONFIDENCE_TOO_LOW", "Retained/delayed OI evidence has decayed below the minimum confidence", oi, price, expiry=expiry, diagnostics=diagnostics)
        if oi.direction == Direction.MIXED:
            min_confidence = self.settings.mixed_oi_min_structure_confidence
        if price.structure_confidence < min_confidence:
            return ScanResult(now, session_date, "NO_TRADE", "SETUP_CONFIDENCE_LOW", f"Price structure confidence {price.structure_confidence:.2f} is below the required {min_confidence:.2f}", oi, price, expiry=expiry, diagnostics=diagnostics)

        try:
            risk = build_risk_plan(price, trade_direction, spot_quote.last_price, self.settings, tick_size=0.05)
        except RiskRejected as exc:
            return ScanResult(now, session_date, "NO_TRADE", exc.code, str(exc), oi, price, expiry=expiry, diagnostics=diagnostics)
        try:
            selection_chain, quote_refresh_status = self._refresh_selection_quotes(chain, trade_direction)
            diagnostics["option_quote_refresh_status"] = quote_refresh_status
            quote_evaluation_time = datetime.now(IST) if self.settings.refresh_option_quotes else max(now, chain.fetched_at)
            selection = select_contract(selection_chain, trade_direction, risk, self.settings, now=quote_evaluation_time)
        except UpstoxError as exc:
            return ScanResult(now, session_date, "NO_TRADE", "OPTION_QUOTE_REFRESH_FAILED", str(exc), oi, price, risk,
                              expiry=expiry, diagnostics={**diagnostics, "option_quote_refresh_status": "FAILED", "option_quote_refresh_error": exc.code})
        except RiskRejected as exc:
            return ScanResult(now, session_date, "NO_TRADE", exc.code, str(exc), oi, price, risk, expiry=expiry, diagnostics={**diagnostics, "strike_selection": []})
        if selection.selected is None:
            reasons = list(selection.rejections)
            first = reasons[0] if reasons else {"reason_code": "NO_VALID_OPTION_QUOTES"}
            code = str(first.get("reason_code", "NO_VALID_OPTION_QUOTES"))
            return ScanResult(now, session_date, "NO_TRADE", code, str(first.get("detail", "None of the permitted nearby strikes passed all quality gates")), oi, price, risk, expiry=expiry, atm_strike=selection.atm_strike, diagnostics={**diagnostics, "strike_selection": reasons})
        chosen = selection.selected
        side = chosen.quote.side
        reason = f"OI_{oi.direction.value}; {price.setup.value}; net_RR_T1={chosen.option_risk.net_rr1:.2f}; underlying_RR_T1={risk.rr1:.2f}"
        if oi.direction == Direction.MIXED:
            reason += "; STRONG_PRICE_HTF_OVERRIDE"
        if oi.status in {"DELAYED", "RETAINED"}:
            reason += f"; OI_STATUS_{oi.status}"
        signal_key = _signal_key(session_date.isoformat(), side, chosen.quote.instrument_key, expiry.isoformat(), price.setup.value, risk.stop_underlying)
        decision = "QUALIFIED_CE" if side == "CE" else "QUALIFIED_PE"
        return ScanResult(now, session_date, decision, decision, reason, oi, price, risk, chosen.quote, chosen.option_risk, expiry, selection.atm_strike, chosen.offset, signal_key, "PENDING", {**diagnostics, "strike_candidates": [{"strike": e.quote.strike, "side": e.quote.side, "offset": e.offset, "score": round(e.ranking_score, 4), "net_rr1": round(e.option_risk.net_rr1, 3), "spread_pct": round(e.option_risk.spread_pct, 3)} for e in selection.evaluations], "strike_rejections": list(selection.rejections)})

    def _refresh_selection_quotes(self, chain: ChainSnapshot, direction: Direction) -> tuple[ChainSnapshot, str]:
        """Refresh only the three permitted CE/PE candidates from V3 quote snapshots.

        OI/Greeks remain from the option-chain snapshot; LTP and top-of-book execution prices,
        depth and quote timestamp are replaced from the current Full Market Quotes V3 response.
        """
        if not self.settings.refresh_option_quotes:
            return chain, "DISABLED_BY_CONFIGURATION"
        rows = sorted(chain.rows, key=lambda r: r.strike)
        if not rows:
            raise UpstoxError("OPTION_CHAIN_EMPTY", "Cannot refresh option quotes from an empty chain")
        atm_index = min(range(len(rows)), key=lambda i: abs(rows[i].strike - chain.spot))
        offsets = (0, -1, -2) if direction == Direction.BULLISH else (0, 1, 2)
        candidates: dict[str, tuple[int, str]] = {}
        for offset in offsets:
            index = atm_index + offset
            if index < 0 or index >= len(rows):
                continue
            quote = rows[index].call if direction == Direction.BULLISH else rows[index].put
            if quote is not None:
                candidates[quote.instrument_key] = (index, "call" if direction == Direction.BULLISH else "put")
        if not candidates:
            return chain, "NO_PERMITTED_CONTRACTS_IN_CHAIN"
        # `received_at` is local receipt time; each response's `timestamp` becomes source quote time.
        refreshed = self.client.fetch_quotes(list(candidates.keys()), received_at=datetime.now(IST))
        out_rows = list(rows)
        for key, (index, side_attr) in candidates.items():
            live = refreshed.get(key)
            original = getattr(out_rows[index], side_attr)
            if live is None or original is None:
                continue
            updated = replace(
                original,
                ltp=live.last_price,
                bid=float(live.bid or 0.0),
                ask=float(live.ask or 0.0),
                bid_qty=float(live.bid_qty or 0.0),
                ask_qty=float(live.ask_qty or 0.0),
                volume=float(live.volume if live.volume is not None else original.volume),
                quote_time=live.source_time,
            )
            out_rows[index] = replace(out_rows[index], **{side_attr: updated})
        refreshed_snapshot = replace(chain, rows=tuple(out_rows))
        return refreshed_snapshot, "FULL_MARKET_QUOTES_V3_REFRESHED"

    def _retain_last_oi_evidence(self, current, state: dict[str, Any], now: datetime):
        """Carry prior OI direction only while its last informative payload is fresh; no new delta is fabricated."""
        saved = state.get("last_oi_evidence")
        if not isinstance(saved, dict):
            return replace(current, summary="OI payload unchanged and no prior informative OI evidence is available")
        try:
            observed_at = datetime.fromisoformat(saved["observed_at"])
            if observed_at.tzinfo is None or observed_at.utcoffset() is None:
                raise ValueError("naive evidence timestamp")
            age = max(0.0, (now - observed_at).total_seconds())
            if age > self.settings.option_chain_max_age_seconds:
                return replace(current, direction=Direction.UNKNOWN, status="STALE", age_seconds=age, summary="OI_STALE: unchanged payload exceeds max age")
            decay = max(0.35, 1.0 - 0.5 * age / self.settings.option_chain_max_age_seconds)
            direction = Direction(str(saved["direction"]))
            confidence = max(0.0, min(1.0, float(saved.get("confidence", 0.0)) * decay))
            return replace(current, direction=direction, score=float(saved.get("score", 0.0)),
                confidence=confidence, status="RETAINED", age_seconds=age,
                summary=f"OI_RETAINED_UNCHANGED_PAYLOAD; prior_snapshot_at={observed_at.isoformat()}; age_s={age:.0f}; direction={direction.value}",
                raw_score=saved.get("raw_score"))
        except (KeyError, TypeError, ValueError):
            return replace(current, direction=Direction.UNKNOWN, status="UNCHANGED", summary="OI payload unchanged; prior evidence state invalid or unavailable")

    def _finish_scan(self, result, state, chain, oi, now, session_date, *, notify: bool) -> ScanResult:
        # Persist successful current-session snapshots only; no failed/empty responses replace baselines.
        if chain is not None:
            first = state.get("first_session_chain")
            baseline_matches = bool(first and first.get("session_date") == chain.session_date.isoformat()
                                    and first.get("expiry") == chain.expiry.isoformat()
                                    and first.get("underlying_key") == chain.underlying_key)
            if not baseline_matches:
                state["first_session_chain"] = compact_snapshot(chain, max_rows=41)
            # Every successful, identity-matched, chronologically newer response is the next
            # snapshot comparison baseline, even when its values are unchanged. This preserves
            # the true interval for the next delta; retained directional evidence is stored separately.
            should_advance = True
            previous = state.get("previous_chain")
            if isinstance(previous, dict):
                try:
                    prev_time = datetime.fromisoformat(previous["fetched_at"])
                    same_identity = (previous.get("session_date") == chain.session_date.isoformat()
                                     and previous.get("expiry") == chain.expiry.isoformat()
                                     and previous.get("underlying_key") == chain.underlying_key)
                    if same_identity and (prev_time.tzinfo is None or prev_time.utcoffset() is None or chain.fetched_at <= prev_time):
                        should_advance = False
                except (KeyError, TypeError, ValueError):
                    should_advance = True
            if should_advance:
                state["previous_chain"] = compact_snapshot(chain, max_rows=41)
        if oi.status in {"FRESH", "DELAYED"} and oi.direction != Direction.UNKNOWN:
            hist = state.get("oi_score_history", [])
            hist.append({"timestamp": now.isoformat(), "score": oi.raw_score if oi.raw_score is not None else oi.score, "smoothed_score": oi.score, "direction": oi.direction.value})
            state["oi_score_history"] = hist[-self.settings.oi_history_length:]
            state["last_oi_evidence"] = {"observed_at": (chain.fetched_at.isoformat() if chain else now.isoformat()),
                "direction": oi.direction.value, "score": oi.score, "raw_score": oi.raw_score if oi.raw_score is not None else oi.score,
                "confidence": oi.confidence, "summary": oi.summary}
        state["last_scan_at"] = now.isoformat()
        if result.diagnostics.get("last_completed_candle"):
            state["last_processed_candle"] = result.diagnostics["last_completed_candle"]
        active = state.setdefault("setup_states", {}).get("active")
        if result.price.setup is not None and result.price.invalidation_price is not None:
            state["setup_states"]["active"] = {
                "session_date": session_date.isoformat(), "kind": result.price.setup.value,
                "direction": result.price.direction.value, "state": "CONFIRMED_THIS_SCAN",
                "trigger_price": result.price.trigger_price, "invalidation_price": result.price.invalidation_price,
                "created_or_refreshed_at": now.isoformat(), "expires_at": (now + timedelta(minutes=10)).isoformat(),
            }
        elif active and active.get("session_date") == session_date.isoformat():
            try:
                expires = datetime.fromisoformat(active.get("expires_at", ""))
                current_price = result.diagnostics.get("current_spot")
                invalidation = active.get("invalidation_price")
                invalidated = current_price is not None and invalidation is not None and ((active.get("direction") == Direction.BULLISH.value and current_price < invalidation) or (active.get("direction") == Direction.BEARISH.value and current_price > invalidation))
                if now <= expires and not invalidated:
                    active["state"] = "WATCHING_NO_FRESH_TRIGGER"
                    state["setup_states"]["active"] = active
                else:
                    state["setup_states"].pop("active", None)
            except (ValueError, TypeError):
                state["setup_states"].pop("active", None)
        if result.decision.startswith("QUALIFIED_") and result.signal_key:
            events = state.setdefault("notification_events", {})
            existing = events.get(result.signal_key)
            if existing and existing.get("status") in {"SENT", "PREPARED", "FAILED"}:
                result = replace(result, notification_status="DUPLICATE_SUPPRESSED")
            else:
                # Durable pre-send marker prevents concurrent runners from sending the same key.
                events[result.signal_key] = {"status": "PREPARED", "created_at": now.isoformat()}
                self.store.save(state)  # If this fails, do not send an untracked alert.
                if notify and self.notifier.configured():
                    try:
                        status = self.notifier.send(result.to_dict(), result.signal_key)
                        result = replace(result, notification_status=status)
                        events[result.signal_key] = {"status": "SENT" if status.startswith("SENT") else "FAILED", "delivery_status": status, "updated_at": datetime.now(IST).isoformat()}
                    except Exception as exc:
                        result = replace(result, notification_status=f"FAILED:{type(exc).__name__}")
                        events[result.signal_key] = {"status": "FAILED", "delivery_status": result.notification_status, "updated_at": datetime.now(IST).isoformat()}
                else:
                    result = replace(result, notification_status="NOT_CONFIGURED")
                    events[result.signal_key] = {"status": "NOT_CONFIGURED", "updated_at": datetime.now(IST).isoformat()}
        self.store.save(state)
        self._audit(result)
        return result

    def _diagnostics(self, underlying_key, master_status, roll_reason, candle_age, future_key, future_status, last_completed_candle=None, current_spot=None):
        return {"underlying_key": underlying_key, "instrument_master_status": master_status, "expiry_roll_reason": roll_reason, "candle_age_seconds": round(candle_age, 1), "last_completed_candle": last_completed_candle, "current_spot": current_spot, "future_key": future_key, "future_vwap_status": future_status}

    def _blocked_result(self, now, code, message, oi, price):
        oi = oi or OIEvidence(Direction.UNKNOWN, 0.0, 0.0, "MISSING", 0.0, None, (), 0.0, 0.0, 0, "OI unavailable")
        price = price or PriceAnalysis(regime=Regime.UNKNOWN, direction=Direction.UNKNOWN, higher_timeframe_bias=Direction.UNKNOWN,
            execution_structure="DATA_BLOCKED", setup=None, support=None, resistance=None, support_source=None,
            resistance_source=None, atr=None, return_1m=None, return_3m=None, return_5m=None, return_15m=None,
            trigger_price=None, invalidation_price=None, structure_confidence=0.0, reasons=("DATA_BLOCKED",))
        return ScanResult(now, now.date(), "NO_TRADE", code, message, oi, price, diagnostics={"data_blocked": True})

    def _audit(self, result: ScanResult) -> None:
        self.settings.audit_dir.mkdir(parents=True, exist_ok=True)
        path = self.settings.audit_dir / f"market_scan_{result.session_date.isoformat()}.jsonl"
        payload = result.to_dict()
        # Compact, single-line, append-only audit; don't dump entire option chain or credentials.
        line = json.dumps(payload, ensure_ascii=False, separators=(",", ":"), allow_nan=False) + "\n"
        with open(path, "a", encoding="utf-8") as handle:
            handle.write(line)
            handle.flush()


def _market_hours(now: datetime) -> bool:
    if now.weekday() >= 5:
        return False
    clock = now.time().replace(tzinfo=None)
    return datetime_time(9, 15) <= clock <= datetime_time(15, 30)


def _signal_key(session: str, side: str, instrument_key: str, expiry: str, setup: str, stop: float) -> str:
    canonical = f"{session}|{side}|{instrument_key}|{expiry}|{setup}|{round(stop / 5.0) * 5.0:.1f}"
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()[:24]


# ===== Inlined module: cli.py =====

"""CLI entry point. Regression tests live only in tests/, never in this module."""
















IST = ZoneInfo("Asia/Kolkata")


def _configure_logging(level: str) -> None:
    logging.basicConfig(level=getattr(logging, level, logging.INFO), format="%(asctime)s %(levelname)s %(name)s %(message)s", stream=sys.stderr)


def _append_error_audit(settings: Settings, payload: dict) -> None:
    try:
        day = datetime.now(IST).date().isoformat()
        settings.audit_dir.mkdir(parents=True, exist_ok=True)
        with open(settings.audit_dir / f"market_scan_{day}.jsonl", "a", encoding="utf-8") as handle:
            handle.write(json.dumps(payload, ensure_ascii=False, separators=(",", ":"), allow_nan=False) + "\n")
            handle.flush()
    except Exception:
        logging.getLogger("nifty_scanner").exception("Failed to append scanner error audit")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Read-only NIFTY 50 OI, structure and option-risk scanner")
    parser.add_argument("--check-config", action="store_true", help="Validate environment configuration without calling Upstox")
    parser.add_argument("--version", action="version", version="101.0.0")
    args = parser.parse_args(argv)
    settings = Settings.from_env()
    _configure_logging(settings.log_level)
    errors = settings.validate()
    if args.check_config:
        output = {"scanner_version": "101.0.0", "config_valid": not errors, "errors": errors,
                  "state_file": str(settings.state_file), "audit_dir": str(settings.audit_dir),
                  "token_present": bool(settings.analytics_token), "email_configured": bool(settings.smtp_host and settings.email_sender and settings.email_receiver and settings.email_password),
                  "webhook_configured": bool(settings.alert_webhook_url)}
        print(json.dumps(output, separators=(",", ":")))
        return 0 if not errors else 2
    if errors:
        payload = {"timestamp": datetime.now(IST).isoformat(), "scanner_version": "101.0.0", "decision": "NO_TRADE", "reason_code": "CONFIG_INVALID", "message": "; ".join(errors)}
        print(json.dumps(payload, separators=(",", ":")))
        _append_error_audit(settings, payload)
        return 2
    try:
        result = ScannerEngine(settings).scan()
        print(json.dumps(result.to_dict(), ensure_ascii=False, separators=(",", ":"), allow_nan=False))
        return 0 if result.reason_code not in {"STATE_SAVE_FAILED", "UNEXPECTED_INTERNAL_ERROR"} else 1
    except (UpstoxError, StateError) as exc:
        code = getattr(exc, "code", "STATE_ERROR" if isinstance(exc, StateError) else "SCANNER_ERROR")
        payload = {"timestamp": datetime.now(IST).isoformat(), "scanner_version": "101.0.0", "decision": "NO_TRADE", "error_type": type(exc).__name__, "reason_code": code, "message": str(exc)}
        print(json.dumps(payload, ensure_ascii=False, separators=(",", ":"), allow_nan=False))
        _append_error_audit(settings, payload)
        return 1
    except Exception as exc:
        logging.getLogger("nifty_scanner").exception("Fatal unhandled scanner exception")
        payload = {"timestamp": datetime.now(IST).isoformat(), "scanner_version": "101.0.0", "decision": "NO_TRADE", "error_type": type(exc).__name__, "reason_code": "UNEXPECTED_INTERNAL_ERROR", "message": str(exc)}
        print(json.dumps(payload, ensure_ascii=False, separators=(",", ":"), allow_nan=False))
        _append_error_audit(settings, payload)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
