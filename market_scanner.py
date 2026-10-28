#!/usr/bin/env python3
"""NIFTY 50 OI-first intraday market-regime scanner (v99).

Alert-only. No order placement. Python 3.11+, standard library only.
All timestamps are timezone-aware and displayed in Asia/Kolkata.
"""
from __future__ import annotations

import argparse
import base64
import dataclasses
import datetime as dt
import email.message
import contextlib
import hashlib
import json
import logging
import math
import os
import random
import smtplib
import statistics
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence
from zoneinfo import ZoneInfo

VERSION = "99.0.0"
IST = ZoneInfo("Asia/Kolkata")
UTC = dt.timezone.utc
LOG = logging.getLogger("market_scanner_v99")

REASON_CODES: dict[str, str] = {
    "QUALIFIED_CE": "Bullish regime and all underlying/option risk gates pass; CE selected.",
    "QUALIFIED_PE": "Bearish regime and all underlying/option risk gates pass; PE selected.",
    "OI_BASELINE_MISSING": "No prior successful same-session, same-expiry option-chain snapshot.",
    "OI_STALE": "The option-chain evidence is older than the configured maximum age.",
    "OI_MIXED": "Nearby OI/premium flows do not give a sufficiently one-sided hypothesis.",
    "OI_PRICE_DIVERGENCE": "OI hypothesis conflicts with current price structure; no entry.",
    "REVERSAL_WATCH": "OI suggests a possible regime reversal, but price confirmation is not complete.",
    "SIDEWAYS_NO_EDGE": "Sideways/range conditions without a confirmed edge bounce/rejection.",
    "NO_CONFIRMED_SETUP": "Neither a confirmed continuation nor a confirmed reversal setup exists.",
    "RR_BELOW_2R": "Nearest opposing barrier gives less than 2.0:1 underlying reward/risk.",
    "STOP_TOO_WIDE": "Structural stop exceeds the maximum ATR-based risk limit.",
    "NO_TARGET": "No valid opposing target level is available.",
    "NO_T2_TARGET": "No distinct, farther structural level exists for a defensible second target.",
    "OPTION_QUOTES_INVALID": "Selected option has missing, crossed, stale or non-executable quotes.",
    "OPTION_NET_RR_BELOW_2R": "Option premium scenario net of estimated costs fails the 2.0:1 gate.",
    "OPTION_DELTA_OUT_OF_RANGE": "Candidate option delta is outside configured bounds or unavailable.",
    "NO_ELIGIBLE_STRIKE": "No eligible ATM/near-ITM contract passed all gates.",
    "API_AUTH_FAILED": "Upstox authentication failed.",
    "API_RATE_LIMITED": "Upstox rate limit was reached after bounded retries.",
    "API_UNAVAILABLE": "Upstox endpoint failed after bounded retries.",
    "INSTRUMENT_RESOLUTION_FAILED": "NIFTY 50 instrument could not be uniquely and safely resolved.",
    "EXPIRY_RESOLUTION_FAILED": "Configured or nearest weekly expiry could not be resolved from current contracts.",
    "DATA_QUALITY_BLOCK": "Required data is missing, invalid, misaligned or stale.",
    "STATE_CONFLICT": "Concurrent state revision conflict; signal suppressed.",
    "STATE_SAVE_FAILED": "Durable state could not be saved; signal suppressed.",
    "DUPLICATE_SIGNAL": "Signal key already exists in persisted deduplication history.",
    "MARKET_CLOSED": "Current local time is outside the configured trading window.",
    "NOTIFIER_FAILED": "Signal was durably recorded, but notification delivery failed.",
    "CONFIGURATION_OR_STARTUP_ERROR": "Configuration, environment or startup validation failed.",
}


class ScannerError(RuntimeError):
    def __init__(self, code: str, message: str):
        super().__init__(message)
        self.code = code


def now_ist() -> dt.datetime:
    return dt.datetime.now(IST)


def parse_dt(value: Any) -> dt.datetime | None:
    if value is None or value == "":
        return None
    if isinstance(value, (int, float)):
        # Upstox last_trade_time commonly uses milliseconds since epoch.
        value = float(value)
        if value > 10**12:
            value /= 1000.0
        return dt.datetime.fromtimestamp(value, UTC).astimezone(IST)
    if not isinstance(value, str):
        return None
    try:
        parsed = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        try:
            parsed = dt.datetime.fromtimestamp(float(value) / 1000.0, UTC)
        except (ValueError, OverflowError, OSError):
            return None
    if parsed.tzinfo is None:
        return None
    return parsed.astimezone(IST)


def iso(value: dt.datetime | None) -> str | None:
    return value.astimezone(IST).isoformat() if value else None


def as_float(value: Any) -> float | None:
    try:
        v = float(value)
    except (TypeError, ValueError, OverflowError):
        return None
    return v if math.isfinite(v) else None


def clamp(value: float, low: float, high: float) -> float:
    return max(low, min(high, value))


def safe_pct(current: float | None, previous: float | None) -> float | None:
    if current is None or previous is None or previous <= 0:
        return None
    return (current - previous) / previous * 100.0


def jsonable(value: Any) -> Any:
    if dataclasses.is_dataclass(value):
        return {k: jsonable(v) for k, v in dataclasses.asdict(value).items()}
    if isinstance(value, dt.datetime):
        return iso(value)
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, dict):
        return {str(k): jsonable(v) for k, v in value.items()}
    if isinstance(value, (list, tuple, set)):
        return [jsonable(v) for v in value]
    if isinstance(value, float) and not math.isfinite(value):
        return None
    return value


def emit(record: Mapping[str, Any]) -> None:
    print(json.dumps(jsonable(dict(record)), ensure_ascii=False, separators=(",", ":"), sort_keys=True))


@dataclass(frozen=True)
class Config:
    access_token: str
    underlying_key_override: str = ""
    expiry_setting: str = "nearest_weekly"
    oi_change_threshold_pct: float = 2.0
    expected_oi_cadence_seconds: int = 180
    oi_max_age_seconds: int = 420
    quote_max_age_seconds: int = 45
    candle_max_age_seconds: int = 150
    candle_close_buffer_seconds: int = 5
    min_reward_risk: float = 2.0
    max_stop_atr: float = 1.75
    max_option_spread_pct: float = 3.0
    min_quote_quantity: float = 1.0
    min_abs_delta: float = 0.25
    max_abs_delta: float = 0.75
    option_slippage_per_side: float = 0.50
    round_trip_cost_per_unit: float = 2.00
    adverse_iv_points: float = -1.0
    scenario_holding_minutes: float = 30.0
    oi_radius_strikes: int = 6
    max_snapshots: int = 5
    max_candles: int = 500
    max_audit_records: int = 300
    max_dedup_keys: int = 500
    atr_period: int = 14
    pivot_left: int = 2
    pivot_right: int = 2
    state_backend: str = "auto"
    state_file: str = "market_scanner_v99_state.json"
    github_state_repository: str = ""
    github_state_path: str = "data/market_scanner_v99_state.json"
    github_state_branch: str = "main"
    github_state_token: str = ""
    webhook_url: str = ""
    smtp_host: str = ""
    smtp_port: int = 587
    smtp_user: str = ""
    smtp_password: str = ""
    email_from: str = ""
    email_to: str = ""
    market_start: str = "09:20"
    market_end: str = "15:20"
    dry_run: bool = False
    api_timeout_seconds: float = 12.0
    api_retries: int = 3
    state_lock_timeout_seconds: float = 20.0
    require_futures: bool = False

    @classmethod
    def from_env(cls) -> "Config":
        token = os.getenv("UPSTOX_ACCESS_TOKEN", "").strip()
        if not token:
            raise ValueError("UPSTOX_ACCESS_TOKEN is required for a live scan")
        def f(name: str, default: float) -> float:
            v = as_float(os.getenv(name, str(default)))
            if v is None:
                raise ValueError(f"{name} must be finite numeric")
            return v
        def i(name: str, default: int) -> int:
            try:
                return int(os.getenv(name, str(default)))
            except ValueError as exc:
                raise ValueError(f"{name} must be an integer") from exc
        expiry = os.getenv("NIFTY_EXPIRY", "nearest_weekly").strip()
        if expiry != "nearest_weekly":
            dt.date.fromisoformat(expiry)
        cfg = cls(
            access_token=token,
            underlying_key_override=os.getenv("NIFTY_INSTRUMENT_KEY", "").strip(),
            expiry_setting=expiry,
            oi_change_threshold_pct=f("OI_CHANGE_THRESHOLD_PCT", 2.0),
            expected_oi_cadence_seconds=i("EXPECTED_OI_CADENCE_SECONDS", 180),
            oi_max_age_seconds=i("OI_MAX_AGE_SECONDS", 420),
            quote_max_age_seconds=i("QUOTE_MAX_AGE_SECONDS", 45),
            candle_max_age_seconds=i("CANDLE_MAX_AGE_SECONDS", 150),
            candle_close_buffer_seconds=i("CANDLE_CLOSE_BUFFER_SECONDS", 5),
            min_reward_risk=f("MIN_REWARD_RISK", 2.0),
            max_stop_atr=f("MAX_STOP_ATR", 1.75),
            max_option_spread_pct=f("MAX_OPTION_SPREAD_PCT", 3.0),
            min_quote_quantity=f("MIN_QUOTE_QUANTITY", 1.0),
            min_abs_delta=f("MIN_ABS_DELTA", 0.25),
            max_abs_delta=f("MAX_ABS_DELTA", 0.75),
            option_slippage_per_side=f("OPTION_SLIPPAGE_PER_SIDE", 0.50),
            round_trip_cost_per_unit=f("ROUND_TRIP_COST_PER_UNIT", 2.0),
            adverse_iv_points=f("ADVERSE_IV_POINTS", -1.0),
            scenario_holding_minutes=f("OPTION_SCENARIO_HOLDING_MINUTES", 30.0),
            oi_radius_strikes=i("OI_RADIUS_STRIKES", 6),
            max_snapshots=i("MAX_OI_SNAPSHOTS", 5),
            max_candles=i("MAX_CANDLES", 500),
            max_audit_records=i("MAX_AUDIT_RECORDS", 300),
            max_dedup_keys=i("MAX_DEDUP_KEYS", 500),
            atr_period=i("ATR_PERIOD", 14),
            pivot_left=i("PIVOT_LEFT", 2),
            pivot_right=i("PIVOT_RIGHT", 2),
            state_backend=os.getenv("STATE_BACKEND", "auto").strip().lower(),
            state_file=os.getenv("STATE_FILE", "market_scanner_v99_state.json").strip(),
            github_state_repository=os.getenv("GITHUB_STATE_REPOSITORY", "").strip(),
            github_state_path=os.getenv("GITHUB_STATE_PATH", "data/market_scanner_v99_state.json").strip(),
            github_state_branch=os.getenv("GITHUB_STATE_BRANCH", "main").strip() or "main",
            github_state_token=os.getenv("GITHUB_STATE_TOKEN", "").strip(),
            webhook_url=os.getenv("ALERT_WEBHOOK_URL", "").strip(),
            smtp_host=os.getenv("SMTP_HOST", "").strip(),
            smtp_port=i("SMTP_PORT", 587),
            smtp_user=os.getenv("SMTP_USER", "").strip(),
            smtp_password=os.getenv("SMTP_PASSWORD", "").strip(),
            email_from=os.getenv("EMAIL_FROM", "").strip(),
            email_to=os.getenv("EMAIL_TO", "").strip(),
            market_start=os.getenv("MARKET_START", "09:20").strip(),
            market_end=os.getenv("MARKET_END", "15:20").strip(),
            dry_run=os.getenv("SCAN_DRY_RUN", "false").strip().lower() in {"1", "true", "yes", "on"},
            api_timeout_seconds=f("API_TIMEOUT_SECONDS", 12.0),
            api_retries=i("API_RETRIES", 3),
            state_lock_timeout_seconds=f("STATE_LOCK_TIMEOUT_SECONDS", 20.0),
            require_futures=os.getenv("REQUIRE_FUTURES_CONFIRMATION", "false").strip().lower() in {"1", "true", "yes", "on"},
        )
        cfg.validate()
        return cfg

    def validate(self) -> None:
        if self.oi_change_threshold_pct <= 0 or self.min_reward_risk < 2.0:
            raise ValueError("OI threshold must be >0 and minimum RR cannot be below 2.0")
        if self.expected_oi_cadence_seconds <= 0 or self.oi_max_age_seconds < self.expected_oi_cadence_seconds:
            raise ValueError("OI cadence must be positive and maximum age >= one cadence")
        if not (0 <= self.min_abs_delta < self.max_abs_delta <= 1):
            raise ValueError("Delta bounds must satisfy 0 <= min < max <= 1")
        if self.max_option_spread_pct <= 0 or self.max_stop_atr <= 0 or self.api_timeout_seconds <= 0:
            raise ValueError("Spread, stop ATR and API timeout values must be positive")
        if self.max_snapshots < 2 or self.max_candles < max(30, self.atr_period + 2):
            raise ValueError("State history is too short")
        if self.oi_radius_strikes < 2 or self.api_retries < 0:
            raise ValueError("Invalid OI radius or retry count")
        if self.state_backend not in {"auto", "local", "github"}:
            raise ValueError("STATE_BACKEND must be auto, local or github")
        if self.state_backend == "github" and not (self.github_state_repository and self.github_state_token):
            raise ValueError("GitHub state requires GITHUB_STATE_REPOSITORY and GITHUB_STATE_TOKEN")
        for clock in (self.market_start, self.market_end):
            try:
                dt.time.fromisoformat(clock)
            except ValueError as exc:
                raise ValueError(f"Invalid market time: {clock}") from exc


@dataclass(frozen=True)
class Candle:
    timestamp: dt.datetime  # bar start time
    open: float
    high: float
    low: float
    close: float
    volume: float = 0.0

    def validate(self) -> None:
        values = [self.open, self.high, self.low, self.close, self.volume]
        if self.timestamp.tzinfo is None or not all(math.isfinite(x) for x in values):
            raise ValueError("Candle requires aware timestamp and finite values")
        if min(self.open, self.close) < self.low - 1e-8 or max(self.open, self.close) > self.high + 1e-8:
            raise ValueError("Invalid OHLC ordering")
        if self.volume < 0 or self.low > self.high:
            raise ValueError("Invalid candle volume/range")

    @classmethod
    def from_api(cls, row: Sequence[Any]) -> "Candle":
        if len(row) < 6:
            raise ValueError("Candle row has fewer than six fields")
        ts = parse_dt(row[0])
        if ts is None:
            raise ValueError("Candle timestamp invalid or naive")
        c = cls(ts, float(row[1]), float(row[2]), float(row[3]), float(row[4]), float(row[5] or 0))
        c.validate()
        return c


@dataclass(frozen=True)
class OptionLeg:
    instrument_key: str
    expiry: str
    strike: float
    side: str
    oi: float
    volume: float | None
    ltp: float | None
    bid: float | None
    bid_qty: float | None
    ask: float | None
    ask_qty: float | None
    delta: float | None
    gamma: float | None
    theta: float | None
    vega: float | None
    iv: float | None
    tick_size: float = 0.05
    previous_session_oi: float | None = None

    def validate(self) -> None:
        if not self.instrument_key or self.side not in {"CE", "PE"}:
            raise ValueError("Invalid option identity")
        if not self.expiry:
            raise ValueError("Missing expiry")
        for value in (self.strike, self.oi):
            if not math.isfinite(value) or value < 0:
                raise ValueError("Invalid strike/OI")
        if self.volume is not None and (not math.isfinite(self.volume) or self.volume < 0):
            raise ValueError("Invalid volume")
        if self.previous_session_oi is not None and (not math.isfinite(self.previous_session_oi) or self.previous_session_oi < 0):
            raise ValueError("Invalid previous-session OI")


@dataclass(frozen=True)
class Quote:
    instrument_key: str
    price: float
    timestamp: dt.datetime  # Full Market Quotes V3 response snapshot time
    bid: float | None = None
    bid_qty: float | None = None
    ask: float | None = None
    ask_qty: float | None = None
    volume: float | None = None
    last_trade_time: dt.datetime | None = None  # Separate exchange last-trade timestamp when supplied

    def age_seconds(self, at: dt.datetime) -> float:
        return max(0.0, (at.astimezone(IST) - self.timestamp.astimezone(IST)).total_seconds())

    def last_trade_age_seconds(self, at: dt.datetime) -> float | None:
        if self.last_trade_time is None:
            return None
        return max(0.0, (at.astimezone(IST) - self.last_trade_time.astimezone(IST)).total_seconds())


@dataclass(frozen=True)
class Level:
    price: float
    kind: str
    source: str
    strength: float = 1.0


@dataclass(frozen=True)
class OIEvidence:
    label: str
    bull_score: float
    bear_score: float
    confidence: float
    snapshot_at: dt.datetime | None
    interval_seconds: float | None
    age_seconds: float | None
    valid_rows: int
    material_rows: int
    detail: tuple[Mapping[str, Any], ...] = ()
    reason: str = ""


@dataclass(frozen=True)
class PriceFeatures:
    spot: float
    candle_at: dt.datetime
    atr: float | None
    ret_1m: float | None
    ret_3m: float | None
    ret_5m: float | None
    ret_15m: float | None
    efficiency_10m: float | None
    trend: str
    breakout: str | None
    session_low: float
    session_high: float
    nearest_support: Level | None
    nearest_resistance: Level | None
    touched_support: bool
    touched_resistance: bool
    support_bounce: bool
    resistance_rejection: bool
    future_vwap: float | None = None
    future_direction: str = "UNKNOWN"


@dataclass(frozen=True)
class RiskPlan:
    entry: float
    stop: float
    t1: float
    t2: float | None
    risk_points: float
    reward_t1_points: float
    reward_t2_points: float | None
    rr_t1: float
    rr_t2: float | None
    stop_source: str
    t1_source: str
    t2_source: str | None


def request_json(url: str, token: str, timeout: float, retries: int,
                 method: str = "GET", body: Mapping[str, Any] | None = None,
                 extra_headers: Mapping[str, str] | None = None) -> tuple[dict[str, Any], Mapping[str, str]]:
    headers = {"Accept": "application/json", "Content-Type": "application/json", "Authorization": f"Bearer {token}"}
    headers.update(extra_headers or {})
    payload = json.dumps(body).encode() if body is not None else None
    last_error: Exception | None = None
    for attempt in range(retries + 1):
        req = urllib.request.Request(url, data=payload, headers=headers, method=method)
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                if not isinstance(data, dict):
                    raise ScannerError("API_UNAVAILABLE", "Unexpected non-object JSON response")
                return data, dict(resp.headers.items())
        except urllib.error.HTTPError as exc:
            body_text = exc.read().decode("utf-8", "replace")[:400]
            if exc.code in (401, 403):
                raise ScannerError("API_AUTH_FAILED", f"Upstox returned HTTP {exc.code}") from exc
            if exc.code == 429:
                last_error = exc
                if attempt < retries:
                    wait = as_float(exc.headers.get("Retry-After"))
                    time.sleep(min(max(wait if wait is not None else 1.5 * (2 ** attempt), 0.2), 12.0))
                    continue
                raise ScannerError("API_RATE_LIMITED", "Upstox rate limit after retries") from exc
            if 500 <= exc.code < 600 and attempt < retries:
                time.sleep(min(0.5 * (2 ** attempt) + random.random() * 0.1, 4.0))
                last_error = exc
                continue
            raise ScannerError("API_UNAVAILABLE", f"Upstox HTTP {exc.code}: {body_text}") from exc
        except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as exc:
            last_error = exc
            if attempt < retries:
                time.sleep(min(0.5 * (2 ** attempt) + random.random() * 0.1, 4.0))
                continue
    raise ScannerError("API_UNAVAILABLE", f"Upstox request failed after retries ({type(last_error).__name__})")


class UpstoxAPI:
    BASE = "https://api.upstox.com"
    def __init__(self, config: Config):
        self.config = config

    def get(self, path: str, params: Mapping[str, Any] | None = None, v3: bool = False) -> dict[str, Any]:
        query = urllib.parse.urlencode({k: v for k, v in (params or {}).items() if v is not None})
        url = ("https://api.upstox.com" if not v3 else "https://api.upstox.com") + path
        if query:
            url += "?" + query
        data, _ = request_json(url, self.config.access_token, self.config.api_timeout_seconds, self.config.api_retries)
        if data.get("status") not in (None, "success"):
            raise ScannerError("API_UNAVAILABLE", "Upstox returned a non-success status")
        return data

    def resolve_underlying_key(self) -> str:
        override = self.config.underlying_key_override
        if override and not override.startswith("NSE_INDEX|"):
            raise ScannerError("INSTRUMENT_RESOLUTION_FAILED", "NIFTY_INSTRUMENT_KEY must be an NSE_INDEX key and is validated below")
        data = self.get("/v2/instruments/search", {
            "query": "NIFTY 50", "exchanges": "NSE", "segments": "INDEX",
            "instrument_types": "INDEX", "records": 30, "page_number": 1,
        })
        rows = data.get("data") or []
        candidates = []
        for row in rows:
            if not isinstance(row, dict) or row.get("segment") != "NSE_INDEX":
                continue
            key = row.get("instrument_key")
            name = str(row.get("name", "")).strip().upper()
            symbol = str(row.get("trading_symbol", "")).strip().upper()
            short = str(row.get("short_name", "")).strip().upper()
            if key and (name == "NIFTY 50" or short == "NIFTY 50" or symbol == "NIFTY"):
                candidates.append(str(key))
        candidates = sorted(set(candidates))
        if override:
            if override not in candidates:
                raise ScannerError("INSTRUMENT_RESOLUTION_FAILED", "Configured NIFTY_INSTRUMENT_KEY did not match the current official NIFTY 50 instrument search result")
            return override
        if len(candidates) != 1:
            raise ScannerError("INSTRUMENT_RESOLUTION_FAILED", f"Expected exactly one NIFTY 50 NSE index instrument; found {len(candidates)}")
        return candidates[0]

    def resolve_expiry(self, underlying_key: str, today: dt.date) -> tuple[str, list[dict[str, Any]]]:
        data = self.get("/v2/option/contract", {"instrument_key": underlying_key})
        rows = [r for r in data.get("data", []) if isinstance(r, dict) and r.get("underlying_key") == underlying_key]
        valid = []
        for row in rows:
            try:
                expiry = dt.date.fromisoformat(str(row.get("expiry")))
            except ValueError:
                continue
            if expiry < today or not row.get("instrument_key"):
                continue
            valid.append((expiry, row))
        if self.config.expiry_setting != "nearest_weekly":
            wanted = dt.date.fromisoformat(self.config.expiry_setting)
            selected = [r for e, r in valid if e == wanted]
            if not selected:
                raise ScannerError("EXPIRY_RESOLUTION_FAILED", f"Expiry {wanted} not found for NIFTY 50")
            return wanted.isoformat(), selected
        expiries = sorted({e for e, r in valid if r.get("weekly") is True})
        if not expiries:
            raise ScannerError("EXPIRY_RESOLUTION_FAILED", "No future weekly expiry marked weekly=true in option contracts")
        expiry = expiries[0]
        return expiry.isoformat(), [r for e, r in valid if e == expiry]

    def option_chain(self, underlying_key: str, expiry: str) -> tuple[list[OptionLeg], float, dt.datetime]:
        data = self.get("/v2/option/chain", {"instrument_key": underlying_key, "expiry_date": expiry})
        # This is the local receive timestamp, not a claim about the exchange event time.
        fetched = now_ist()
        rows = data.get("data")
        if not isinstance(rows, list) or not rows:
            raise ScannerError("API_UNAVAILABLE", "Upstox returned an empty option chain")
        legs: list[OptionLeg] = []
        spots: list[float] = []
        for row in rows:
            if not isinstance(row, dict) or row.get("underlying_key") != underlying_key or row.get("expiry") != expiry:
                continue
            spot = as_float(row.get("underlying_spot_price"))
            if spot is not None and spot > 0:
                spots.append(spot)
            strike = as_float(row.get("strike_price"))
            if strike is None or strike <= 0:
                continue
            for side, k in (("CE", "call_options"), ("PE", "put_options")):
                node = row.get(k) or {}
                md = node.get("market_data") or {}
                gr = node.get("option_greeks") or {}
                instrument_key = str(node.get("instrument_key") or "")
                if not instrument_key:
                    continue
                def getnum(obj: Mapping[str, Any], key: str) -> float | None:
                    return as_float(obj.get(key))
                oi_value = getnum(md, "oi")
                # A missing OI field is not zero OI. Skip the incomplete leg rather than
                # manufacturing an OI baseline that can create a false percentage/direction.
                if oi_value is None or oi_value < 0:
                    continue
                leg = OptionLeg(
                    instrument_key=instrument_key, expiry=expiry, strike=strike, side=side,
                    oi=oi_value, volume=getnum(md, "volume"),
                    ltp=getnum(md, "ltp"), bid=getnum(md, "bid_price"), bid_qty=getnum(md, "bid_qty"),
                    ask=getnum(md, "ask_price"), ask_qty=getnum(md, "ask_qty"),
                    delta=getnum(gr, "delta"), gamma=getnum(gr, "gamma"), theta=getnum(gr, "theta"),
                    vega=getnum(gr, "vega"), iv=getnum(gr, "iv"),
                    previous_session_oi=getnum(md, "prev_oi"),
                )
                leg.validate()
                legs.append(leg)
        if not legs or not spots:
            raise ScannerError("DATA_QUALITY_BLOCK", "Option chain missing matching NIFTY expiry rows or spot")
        if max(spots) - min(spots) > 2.0:
            raise ScannerError("DATA_QUALITY_BLOCK", "Materially inconsistent spot values within option chain")
        return legs, statistics.median(spots), fetched

    def quote_map(self, instrument_keys: Sequence[str]) -> dict[str, Quote]:
        unique = list(dict.fromkeys(k for k in instrument_keys if k))
        result: dict[str, Quote] = {}
        # Quotes V3 accepts up to 500 instruments; one request per batch here.
        for start in range(0, len(unique), 500):
            batch = unique[start:start + 500]
            if not batch:
                continue
            data = self.get("/v3/market-quote/quotes", {"instrument_key": ",".join(batch)}, v3=True).get("data", {})
            if not isinstance(data, dict):
                continue
            for _, q in data.items():
                if not isinstance(q, dict):
                    continue
                key = str(q.get("instrument_token") or q.get("instrument_key") or "")
                if not key:
                    # Map key can be NSE_FO:SYMBOL; use symbol matching only as a fallback below.
                    key = str(q.get("symbol") or "")
                timestamp = parse_dt(q.get("timestamp"))
                price = as_float(q.get("last_price"))
                if not timestamp or price is None or price <= 0:
                    continue
                depth = q.get("depth") or {}
                buys = depth.get("buy") or []
                sells = depth.get("sell") or []
                buy = buys[0] if buys and isinstance(buys[0], dict) else {}
                sell = sells[0] if sells and isinstance(sells[0], dict) else {}
                quote = Quote(
                    instrument_key=key, price=price, timestamp=timestamp,
                    bid=as_float(buy.get("price")), bid_qty=as_float(buy.get("quantity")),
                    ask=as_float(sell.get("price")), ask_qty=as_float(sell.get("quantity")),
                    volume=as_float(q.get("volume")), last_trade_time=parse_dt(q.get("last_trade_time")),
                )
                token = str(q.get("instrument_token") or "")
                if token:
                    result[token] = quote
        # Refuse to silently pair by response order. Keys must be traceable to requested IDs.
        return result

    def candles_intraday(self, instrument_key: str) -> list[Candle]:
        encoded = urllib.parse.quote(instrument_key, safe="")
        data = self.get(f"/v3/historical-candle/intraday/{encoded}/minutes/1", v3=True)
        raw = (data.get("data") or {}).get("candles") or []
        candles = []
        for row in raw:
            try:
                candles.append(Candle.from_api(row))
            except (ValueError, TypeError, IndexError):
                continue
        # API may return newest-first. Deduplicate by bar-start timestamp.
        return list({c.timestamp: c for c in sorted(candles, key=lambda x: x.timestamp)}.values())

    def prior_session_candles(self, instrument_key: str, today: dt.date) -> list[Candle]:
        # Historical V3 supports minute candles from 2022; search the previous 10 calendar days
        # and select the most recent date with actual candles (handles weekends/holidays).
        to_date = today - dt.timedelta(days=1)
        from_date = today - dt.timedelta(days=10)
        encoded = urllib.parse.quote(instrument_key, safe="")
        try:
            data = self.get(f"/v3/historical-candle/{encoded}/minutes/1/{to_date.isoformat()}/{from_date.isoformat()}", v3=True)
        except ScannerError:
            return []
        raw = (data.get("data") or {}).get("candles") or []
        parsed = []
        for row in raw:
            try:
                c = Candle.from_api(row)
                if c.timestamp.date() < today:
                    parsed.append(c)
            except (ValueError, TypeError, IndexError):
                continue
        if not parsed:
            return []
        latest_day = max(c.timestamp.date() for c in parsed)
        return [c for c in sorted(parsed, key=lambda x: x.timestamp) if c.timestamp.date() == latest_day]

    def resolve_future(self, underlying_key: str, today: dt.date) -> dict[str, Any] | None:
        try:
            data = self.get("/v2/instruments/search", {
                "query": "NIFTY", "exchanges": "NSE", "segments": "FO", "instrument_types": "FUT",
                "expiry": "near_month", "records": 30, "page_number": 1,
            })
        except ScannerError:
            return None
        candidates = []
        for row in data.get("data", []):
            if not isinstance(row, dict) or row.get("underlying_key") != underlying_key:
                continue
            try:
                exp = dt.date.fromisoformat(str(row.get("expiry")))
            except ValueError:
                continue
            if (exp >= today and row.get("instrument_key") and row.get("instrument_type") == "FUT"
                    and row.get("segment") == "NSE_FO"):
                candidates.append((exp, row))
        return min(candidates, key=lambda x: x[0])[1] if candidates else None


# ------------------------- OI-first feature engine -------------------------

def compact_snapshot(legs: Sequence[OptionLeg], expiry: str, fetched_at: dt.datetime, spot: float) -> dict[str, Any]:
    return {
        "expiry": expiry,
        "fetched_at": iso(fetched_at),
        "spot": spot,
        "rows": [
            {"instrument_key": x.instrument_key, "expiry": x.expiry, "strike": x.strike, "side": x.side,
             "oi": x.oi, "volume": x.volume, "ltp": x.ltp,
             "previous_session_oi": x.previous_session_oi}
            for x in legs
        ],
    }


def _flow_vote(side: str, delta_oi: float, premium_pct: float | None) -> float:
    """Probabilistic OI/premium heuristic: + bullish, - bearish; never a proof of intent."""
    if premium_pct is None or abs(premium_pct) < 0.05 or delta_oi == 0:
        return 0.0
    oi_up = delta_oi > 0
    prem_up = premium_pct > 0
    if side == "CE":
        return { (True, True): 1.0, (True, False): -1.0,
                 (False, True): 0.45, (False, False): -0.45 }[(oi_up, prem_up)]
    return { (True, True): -1.0, (True, False): 1.0,
             (False, True): -0.45, (False, False): 0.45 }[(oi_up, prem_up)]


def _oi_strength(pct: float | None, threshold_pct: float) -> tuple[float, bool]:
    """One configurable threshold controls materiality; raw percentage is never clipped."""
    if pct is None:
        return 0.0, False
    material = abs(pct) >= threshold_pct
    # Sub-threshold observations add weak context; material observations ramp up to 1.
    strength = min(1.0, abs(pct) / (threshold_pct * 2.0))
    if not material:
        strength *= 0.35
    return strength, material


def compute_oi_evidence(current: Mapping[str, Any], previous: Mapping[str, Any] | None,
                        at: dt.datetime, cfg: Config, prior_labels: Sequence[str] = (),
                        session_baseline: Mapping[str, Any] | None = None) -> OIEvidence:
    curr_at = parse_dt(current.get("fetched_at"))
    if curr_at is None:
        return OIEvidence("MISSING", 0, 0, 0, None, None, None, 0, 0, (), "CURRENT_SNAPSHOT_TIMESTAMP_MISSING")
    if curr_at > at.astimezone(IST) + dt.timedelta(seconds=5):
        return OIEvidence("MISSING", 0, 0, 0, curr_at, None, None, 0, 0, (), "CURRENT_SNAPSHOT_TIMESTAMP_IN_FUTURE")
    age = max(0.0, (at.astimezone(IST) - curr_at).total_seconds())
    if previous is None or previous.get("expiry") != current.get("expiry"):
        return OIEvidence("MISSING", 0, 0, 0, curr_at, None, age, 0, 0, (), "NO_MATCHING_PRIOR_SNAPSHOT")
    prev_at = parse_dt(previous.get("fetched_at"))
    if prev_at is None or curr_at <= prev_at:
        return OIEvidence("MISSING", 0, 0, 0, curr_at, None, age, 0, 0, (), "DUPLICATE_OR_OUT_OF_ORDER_SNAPSHOT")
    if curr_at.date() != prev_at.date():
        return OIEvidence("MISSING", 0, 0, 0, curr_at, None, age, 0, 0, (), "CROSS_SESSION_SNAPSHOT")
    interval = (curr_at - prev_at).total_seconds()
    prev_by_key = {str(r.get("instrument_key")): r for r in previous.get("rows", []) if r.get("instrument_key")}
    session_by_key = {str(r.get("instrument_key")): r for r in (session_baseline or {}).get("rows", []) if r.get("instrument_key")}
    spot = as_float(current.get("spot"))
    strikes = sorted({as_float(r.get("strike")) for r in current.get("rows", []) if as_float(r.get("strike")) is not None})
    step = statistics.median([b-a for a,b in zip(strikes, strikes[1:]) if b > a]) if len(strikes) > 1 else 50.0
    atm = min(strikes, key=lambda x: abs(x - (spot or x))) if strikes else (spot or 0.0)
    bullish = bearish = 0.0
    detail: list[Mapping[str, Any]] = []
    material_rows = valid_rows = 0
    weighted_total = 0.0
    for row in current.get("rows", []):
        key = str(row.get("instrument_key", ""))
        old = prev_by_key.get(key)
        if not old or old.get("expiry") != current.get("expiry") or old.get("side") != row.get("side"):
            continue
        current_oi = as_float(row.get("oi")); previous_oi = as_float(old.get("oi"))
        if current_oi is None or previous_oi is None or current_oi < 0 or previous_oi < 0:
            continue
        delta_oi = current_oi - previous_oi
        pct = safe_pct(current_oi, previous_oi)
        session_old = session_by_key.get(key)
        session_base_oi = as_float(session_old.get("oi")) if session_old and session_old.get("expiry") == current.get("expiry") and session_old.get("side") == row.get("side") else None
        session_delta = current_oi - session_base_oi if session_base_oi is not None and session_base_oi >= 0 else None
        session_pct = safe_pct(current_oi, session_base_oi)
        previous_session_oi = as_float(row.get("previous_session_oi"))
        vs_prev_session_delta = current_oi - previous_session_oi if previous_session_oi is not None and previous_session_oi >= 0 else None
        vs_prev_session_pct = safe_pct(current_oi, previous_session_oi)
        current_ltp = as_float(row.get("ltp")); previous_ltp = as_float(old.get("ltp"))
        # A zero or missing LTP is not an observed premium move and must not be read as -100%.
        prem_pct = safe_pct(current_ltp, previous_ltp) if current_ltp is not None and current_ltp > 0 and previous_ltp is not None and previous_ltp > 0 else None
        strength, material = _oi_strength(pct, cfg.oi_change_threshold_pct)
        if material:
            material_rows += 1
        # Preserve absolute OI change when percentage change is undefined (e.g. prior OI=0).
        # Such a row is auditable but cannot contribute a normalized directional score.
        volume_now = as_float(row.get("volume")); volume_before = as_float(old.get("volume"))
        volume_increment = (volume_now - volume_before) if volume_now is not None and volume_before is not None else None
        volume_reset = volume_increment is not None and volume_increment < 0
        if volume_reset:
            volume_increment = None
        strike = as_float(row.get("strike")) or atm
        distance = abs(strike - atm) / max(step, 0.01)
        if distance > cfg.oi_radius_strikes:
            continue
        if pct is None:
            detail.append({
                "instrument_key": key, "side": row.get("side"), "strike": strike,
                "oi_delta": delta_oi, "oi_pct": None, "session_oi_delta": session_delta,
                "session_oi_pct": session_pct, "oi_vs_previous_session_delta": vs_prev_session_delta,
                "oi_vs_previous_session_pct": vs_prev_session_pct, "premium_pct": prem_pct,
                "volume_increment": volume_increment, "volume_reset_detected": volume_reset,
                "oi_change_material": False, "vote": 0.0, "weight": 0.0,
                "reason": "ZERO_OR_MISSING_PREVIOUS_OI_BASELINE",
            })
            continue
        vote = _flow_vote(str(row.get("side")), delta_oi, prem_pct)
        distance_weight = 1.0 / (1.0 + distance * 0.45)
        # Positive incremental volume strengthens evidence a little, but it cannot dominate OI/premium.
        volume_weight = 1.0 if volume_increment is not None and volume_increment > 0 else 0.75
        weight = strength * distance_weight * volume_weight
        if vote == 0 or weight <= 0:
            # Keep a compact audit detail even when the premium/OI combination is
            # non-directional. Missing/zero LTP is not converted into a fake -100% move.
            detail.append({
                "instrument_key": key, "side": row.get("side"), "strike": strike,
                "oi_delta": delta_oi, "oi_pct": pct, "session_oi_delta": session_delta,
                "session_oi_pct": session_pct, "oi_vs_previous_session_delta": vs_prev_session_delta,
                "oi_vs_previous_session_pct": vs_prev_session_pct, "premium_pct": prem_pct,
                "volume_increment": volume_increment, "volume_reset_detected": volume_reset,
                "oi_change_material": material, "vote": 0.0, "weight": round(weight, 4),
                "reason": "NO_VALID_PREMIUM_CHANGE_OR_NON_DIRECTIONAL_FLOW",
            })
            continue
        # Each nearby contract contributes a bounded score; a massive single OI row cannot dominate.
        contribution = min(1.0, weight) * abs(vote)
        weighted_total += contribution
        if vote > 0:
            bullish += contribution
        else:
            bearish += contribution
        valid_rows += 1
        detail.append({
            "instrument_key": key, "side": row.get("side"), "strike": strike,
            "oi_delta": delta_oi, "oi_pct": pct, "session_oi_delta": session_delta,
            "session_oi_pct": session_pct, "oi_vs_previous_session_delta": vs_prev_session_delta,
            "oi_vs_previous_session_pct": vs_prev_session_pct, "premium_pct": prem_pct,
            "volume_increment": volume_increment, "volume_reset_detected":volume_reset,
            "oi_change_material": material,
            "vote": vote, "weight": round(weight, 4),
        })
    if age > cfg.oi_max_age_seconds:
        return OIEvidence("STALE", 0, 0, 0, curr_at, interval, age, valid_rows, material_rows,
                          tuple(detail[:80]), "OI_SNAPSHOT_AGE_OVER_LIMIT")
    if weighted_total < 0.5 or valid_rows < 2:
        return OIEvidence("MIXED", 0, 0, 0.25, curr_at, interval, age, valid_rows, material_rows,
                          tuple(detail[:80]), "INSUFFICIENT_DIRECTIONAL_NEAR_ATM_EVIDENCE")
    bull_score = bullish / weighted_total
    bear_score = bearish / weighted_total
    label = "MIXED"
    if bull_score >= 0.62 and bullish >= bearish * 1.5:
        label = "BULLISH"
    elif bear_score >= 0.62 and bearish >= bullish * 1.5:
        label = "BEARISH"
    # Consecutive observations strengthen repeated direction; a flip diminishes confidence.
    recent = [x for x in prior_labels[-2:] if x in {"BULLISH", "BEARISH"}]
    persistence = 1.0
    if label in {"BULLISH", "BEARISH"} and recent:
        persistence = 1.10 if recent[-1] == label else 0.78
        if len(recent) == 2 and recent[0] == recent[1] == label:
            persistence = 1.18
    confidence = clamp(max(bull_score, bear_score) * persistence, 0.0, 1.0)
    # Delayed intervals remain real intervals; they reduce confidence, not alter raw deltas.
    if interval > cfg.expected_oi_cadence_seconds * 1.75:
        confidence *= 0.85
    reason = f"{label}_NEAR_ATM_SIGNED_OI_PREMIUM_FLOW" if label != "MIXED" else "CONFLICTING_NEAR_ATM_FLOWS"
    return OIEvidence(label, bull_score, bear_score, confidence, curr_at, interval, age,
                      valid_rows, material_rows, tuple(detail[:80]), reason)


def oi_context_summary(legs: Sequence[OptionLeg], previous: Mapping[str, Any] | None, spot: float,
                      radius: int, threshold_pct: float) -> dict[str, Any]:
    """Compact near-ATM OI/PCR and potential OI-wall context; no complete chain in routine output."""
    step = infer_strike_step(legs)
    strikes = sorted({x.strike for x in legs})
    atm = min(strikes, key=lambda x: abs(x-spot)) if strikes else spot
    band = [x for x in legs if abs(x.strike-atm) <= radius*step + 0.01]
    prev_rows = {str(r.get("instrument_key")): r for r in (previous or {}).get("rows", []) if r.get("instrument_key")}
    current_call = sum(x.oi for x in band if x.side == "CE")
    current_put = sum(x.oi for x in band if x.side == "PE")
    previous_call = previous_put = 0.0
    current_call_count = current_put_count = 0
    change_zones = []
    for leg in band:
        old = prev_rows.get(leg.instrument_key)
        if not old or old.get("expiry") != leg.expiry or old.get("side") != leg.side:
            continue
        prev_oi = as_float(old.get("oi"))
        if prev_oi is None or prev_oi < 0:
            continue
        if leg.side == "CE":
            previous_call += prev_oi; current_call_count += 1
        else:
            previous_put += prev_oi; current_put_count += 1
        delta = leg.oi-prev_oi
        pct = safe_pct(leg.oi, prev_oi)
        if pct is not None:
            change_zones.append({"strike":leg.strike,"side":leg.side,"delta_oi":delta,"pct":pct,
                                 "material":abs(pct) >= threshold_pct})
    near_pcr = current_put/current_call if current_call > 0 else None
    prev_pcr = previous_put/previous_call if previous_call > 0 else None
    # Raw changes are not clipped. Cap selection only limits report size, not the values.
    calls_above = sorted((x for x in legs if x.side == "CE" and x.strike >= spot), key=lambda x:x.oi, reverse=True)[:3]
    puts_below = sorted((x for x in legs if x.side == "PE" and x.strike <= spot), key=lambda x:x.oi, reverse=True)[:3]
    increases = sorted((x for x in change_zones if x["delta_oi"] > 0), key=lambda x:x["delta_oi"], reverse=True)[:3]
    decreases = sorted((x for x in change_zones if x["delta_oi"] < 0), key=lambda x:x["delta_oi"])[:3]
    return {
        "atm_strike":atm,"strike_step":step,"near_atm_radius_strikes":radius,
        "near_atm_call_oi":current_call,"near_atm_put_oi":current_put,"near_atm_pcr":near_pcr,
        "previous_near_atm_call_oi":previous_call if current_call_count else None,
        "previous_near_atm_put_oi":previous_put if current_put_count else None,
        "near_atm_call_oi_delta":current_call-previous_call if current_call_count else None,
        "near_atm_put_oi_delta":current_put-previous_put if current_put_count else None,
        "near_atm_call_oi_change_pct":safe_pct(current_call,previous_call) if current_call_count else None,
        "near_atm_put_oi_change_pct":safe_pct(current_put,previous_put) if current_put_count else None,
        "previous_near_atm_pcr":prev_pcr,"near_atm_pcr_change":near_pcr-prev_pcr if near_pcr is not None and prev_pcr is not None else None,
        "top_call_oi_walls_above_spot":[{"strike":x.strike,"oi":x.oi} for x in calls_above],
        "top_put_oi_walls_below_spot":[{"strike":x.strike,"oi":x.oi} for x in puts_below],
        "largest_oi_increases":increases,"largest_oi_decreases":decreases,
    }


# ------------------------- Candle and structure engine -------------------------

def complete_candles(candles: Sequence[Candle], at: dt.datetime, buffer_seconds: int = 5) -> list[Candle]:
    cutoff = at.astimezone(IST) - dt.timedelta(seconds=buffer_seconds)
    complete = [c for c in candles if c.timestamp.astimezone(IST) + dt.timedelta(minutes=1) <= cutoff]
    by_ts = {c.timestamp: c for c in complete}
    return [by_ts[k] for k in sorted(by_ts)]


def merge_candles(old: Sequence[Mapping[str, Any]], new: Sequence[Candle], limit: int) -> list[dict[str, Any]]:
    merged: dict[str, dict[str, Any]] = {}
    for row in old:
        ts = parse_dt(row.get("timestamp"))
        if ts:
            merged[iso(ts)] = dict(row)
    for c in new:
        merged[iso(c.timestamp)] = {"timestamp": iso(c.timestamp), "open": c.open, "high": c.high,
                                    "low": c.low, "close": c.close, "volume": c.volume}
    keys = sorted(merged, key=lambda s: parse_dt(s) or dt.datetime.min.replace(tzinfo=IST))
    return [merged[k] for k in keys[-limit:]]


def state_candles(rows: Sequence[Mapping[str, Any]]) -> list[Candle]:
    out = []
    for r in rows:
        ts = parse_dt(r.get("timestamp"))
        vals = [as_float(r.get(k)) for k in ("open", "high", "low", "close")]
        vol = as_float(r.get("volume")) or 0.0
        if ts and all(v is not None for v in vals):
            c = Candle(ts, vals[0], vals[1], vals[2], vals[3], vol)  # type: ignore[arg-type]
            try:
                c.validate(); out.append(c)
            except ValueError:
                pass
    return sorted({c.timestamp: c for c in out}.values(), key=lambda c: c.timestamp)


def aggregate_candles(candles: Sequence[Candle], minutes: int = 5) -> list[Candle]:
    groups: dict[dt.datetime, list[Candle]] = {}
    for c in candles:
        floored_minute = (c.timestamp.minute // minutes) * minutes
        ts = c.timestamp.replace(minute=floored_minute, second=0, microsecond=0)
        groups.setdefault(ts, []).append(c)
    output = []
    for ts, rows in sorted(groups.items()):
        rows = sorted(rows, key=lambda x: x.timestamp)
        # Require a complete bucket; a missing minute must not be fabricated by aggregation.
        expected = {ts + dt.timedelta(minutes=i) for i in range(minutes)}
        present = {x.timestamp.replace(second=0, microsecond=0) for x in rows}
        if not expected.issubset(present):
            continue
        output.append(Candle(ts, rows[0].open, max(x.high for x in rows), min(x.low for x in rows), rows[-1].close,
                             sum(x.volume for x in rows)))
    return output


def atr(candles: Sequence[Candle], period: int = 14) -> float | None:
    if len(candles) < period + 1:
        return None
    tr = []
    for i in range(1, len(candles)):
        c, p = candles[i], candles[i - 1]
        tr.append(max(c.high - c.low, abs(c.high - p.close), abs(c.low - p.close)))
    if len(tr) < period:
        return None
    value = sum(tr[:period]) / period
    for x in tr[period:]:
        value = (value * (period - 1) + x) / period
    return value


def returns(candles: Sequence[Candle], n: int) -> float | None:
    if len(candles) <= n:
        return None
    return candles[-1].close - candles[-1-n].close


def efficiency_ratio(candles: Sequence[Candle], n: int = 10) -> float | None:
    if len(candles) < n + 1:
        return None
    points = [c.close for c in candles[-n-1:]]
    denom = sum(abs(b-a) for a,b in zip(points, points[1:]))
    return abs(points[-1] - points[0]) / denom if denom > 0 else 0.0


def pivots(candles: Sequence[Candle], left: int = 2, right: int = 2) -> tuple[list[Level], list[Level]]:
    highs: list[Level] = []; lows: list[Level] = []
    # A pivot is emitted only after all right-side candles have completed.
    for i in range(left, len(candles) - right):
        c = candles[i]
        lset = candles[i-left:i]; rset = candles[i+1:i+right+1]
        if c.high > max(x.high for x in lset) and c.high >= max(x.high for x in rset):
            highs.append(Level(c.high, "RESISTANCE", f"CONFIRMED_SWING_HIGH:{iso(c.timestamp)}", 0.8))
        if c.low < min(x.low for x in lset) and c.low <= min(x.low for x in rset):
            lows.append(Level(c.low, "SUPPORT", f"CONFIRMED_SWING_LOW:{iso(c.timestamp)}", 0.8))
    return highs, lows


def cluster_levels(levels: Sequence[Level], tolerance: float) -> list[Level]:
    if not levels:
        return []
    result: list[Level] = []
    for lev in sorted(levels, key=lambda x: x.price):
        if result and abs(lev.price - result[-1].price) <= tolerance:
            prev = result[-1]
            price = (prev.price * prev.strength + lev.price * lev.strength) / max(prev.strength + lev.strength, 0.01)
            sources = prev.source.split("+")
            if lev.source not in sources:
                sources.append(lev.source)
            result[-1] = Level(price, prev.kind if prev.kind == lev.kind else "COMPOSITE", "+".join(sources[-4:]),
                               min(2.0, prev.strength + lev.strength))
        else:
            result.append(lev)
    return result


def infer_strike_step(legs: Sequence[OptionLeg]) -> float:
    strikes = sorted({x.strike for x in legs if x.strike > 0})
    diffs = [b-a for a,b in zip(strikes, strikes[1:]) if 0 < b-a < 500]
    if not diffs:
        return 50.0
    return statistics.median(diffs)


def build_levels(candles: Sequence[Candle], prior: Sequence[Candle], legs: Sequence[OptionLeg], spot: float,
                 atr_value: float | None, cfg: Config, futures_vwap: float | None = None) -> tuple[list[Level], list[Level], float, float]:
    if not candles:
        raise ScannerError("DATA_QUALITY_BLOCK", "No completed underlying candles")
    step = infer_strike_step(legs)
    tol = max(0.05 * 2, (atr_value or 10.0) * 0.15)
    high_pivots, low_pivots = pivots(candles, cfg.pivot_left, cfg.pivot_right)
    supports = list(low_pivots); resistances = list(high_pivots)
    today = candles[-1].timestamp.date()
    today_rows = [x for x in candles if x.timestamp.date() == today]
    if today_rows:
        supports.append(Level(min(x.low for x in today_rows), "SUPPORT", "CURRENT_SESSION_LOW", 1.3))
        resistances.append(Level(max(x.high for x in today_rows), "RESISTANCE", "CURRENT_SESSION_HIGH", 1.3))
        session_open = min(x.timestamp for x in today_rows)
        first5 = [x for x in today_rows if session_open <= x.timestamp < session_open + dt.timedelta(minutes=5)]
        first15 = [x for x in today_rows if session_open <= x.timestamp < session_open + dt.timedelta(minutes=15)]
        if len(first5) >= 5:
            supports.append(Level(min(x.low for x in first5), "SUPPORT", "OPENING_RANGE_5M_LOW", 0.9))
            resistances.append(Level(max(x.high for x in first5), "RESISTANCE", "OPENING_RANGE_5M_HIGH", 0.9))
        if len(first15) >= 15:
            supports.append(Level(min(x.low for x in first15), "SUPPORT", "OPENING_RANGE_15M_LOW", 0.8))
            resistances.append(Level(max(x.high for x in first15), "RESISTANCE", "OPENING_RANGE_15M_HIGH", 0.8))
    if prior:
        supports.append(Level(min(x.low for x in prior), "SUPPORT", "PRIOR_SESSION_LOW", 1.0))
        resistances.append(Level(max(x.high for x in prior), "RESISTANCE", "PRIOR_SESSION_HIGH", 1.0))
        supports.append(Level(prior[-1].close, "SUPPORT", "PRIOR_SESSION_CLOSE", 0.7))
        resistances.append(Level(prior[-1].close, "RESISTANCE", "PRIOR_SESSION_CLOSE", 0.7))
    if futures_vwap and futures_vwap > 0:
        if futures_vwap < spot:
            supports.append(Level(futures_vwap, "SUPPORT", "FUTURES_VWAP", 0.7))
        elif futures_vwap > spot:
            resistances.append(Level(futures_vwap, "RESISTANCE", "FUTURES_VWAP", 0.7))
    # OI walls are friction zones, not guaranteed support/resistance.
    below = [x for x in legs if x.side == "PE" and x.strike <= spot]
    above = [x for x in legs if x.side == "CE" and x.strike >= spot]
    for side_rows, bucket, kind, prefix in ((below, supports, "SUPPORT", "PUT_OI_WALL"), (above, resistances, "RESISTANCE", "CALL_OI_WALL")):
        if side_rows:
            max_oi = max(x.oi for x in side_rows) or 1.0
            for leg in sorted(side_rows, key=lambda x: x.oi, reverse=True)[:3]:
                strength = 0.35 + 0.65 * (leg.oi / max_oi)
                bucket.append(Level(leg.strike, kind, f"{prefix}:{leg.instrument_key}", strength))
    supports = cluster_levels([x for x in supports if x.price <= spot + tol], tol)
    resistances = cluster_levels([x for x in resistances if x.price >= spot - tol], tol)
    # De-duplicate and do not let a level exactly equal to entry become a fake positive reward target.
    return supports, resistances, step, tol


def price_features(candles: Sequence[Candle], prior: Sequence[Candle], legs: Sequence[OptionLeg], spot: float,
                   quote: Quote, at: dt.datetime, cfg: Config, futures_vwap: float | None,
                   futures_direction: str) -> tuple[PriceFeatures, list[Level], list[Level], float, float]:
    if len(candles) < max(20, cfg.atr_period + 2):
        raise ScannerError("DATA_QUALITY_BLOCK", f"Need at least {max(20, cfg.atr_period+2)} completed candles; have {len(candles)}")
    atr_value = atr(candles, cfg.atr_period)
    if atr_value is None or atr_value <= 0:
        raise ScannerError("DATA_QUALITY_BLOCK", "ATR unavailable or zero")
    supports, resistances, step, tol = build_levels(candles, prior, legs, spot, atr_value, cfg, futures_vwap)
    low_below = [x for x in supports if x.price < spot - max(0.05, step*0.10)]
    high_above = [x for x in resistances if x.price > spot + max(0.05, step*0.10)]
    near_support = min(low_below, key=lambda x: spot-x.price) if low_below else None
    near_resistance = min(high_above, key=lambda x: x.price-spot) if high_above else None
    today = [c for c in candles if c.timestamp.date() == candles[-1].timestamp.date()]
    last_lows = [x.low for x in candles[-4:]]
    last_highs = [x.high for x in candles[-4:]]
    touched_support = bool(near_support and min(last_lows) <= near_support.price + max(tol, atr_value*0.35))
    touched_resistance = bool(near_resistance and max(last_highs) >= near_resistance.price - max(tol, atr_value*0.35))
    r3, r5, r15 = returns(candles,3), returns(candles,5), returns(candles,15)
    eff = efficiency_ratio(candles, 10)
    five_minute_bars = aggregate_candles(candles, 5)
    recent = five_minute_bars[-3:]
    previous5 = five_minute_bars[-6:-3]
    bias = "UNKNOWN"
    if previous5 and len(recent) == 3:
        old_mid = statistics.mean(x.close for x in previous5)
        new_mid = statistics.mean(x.close for x in recent)
        htf_threshold = atr_value * 0.12
        higher_highs = recent[-1].high > recent[0].high and recent[-1].low >= recent[0].low
        lower_lows = recent[-1].low < recent[0].low and recent[-1].high <= recent[0].high
        if new_mid - old_mid > htf_threshold and (r5 or 0) > 0 and higher_highs:
            bias = "BULLISH"
        elif old_mid - new_mid > htf_threshold and (r5 or 0) < 0 and lower_lows:
            bias = "BEARISH"
        else:
            bias = "RANGE"
    if len(candles) >= 6:
        prevwindow = candles[-6:-1]
        breakout = "BULLISH" if candles[-1].close > max(x.high for x in prevwindow) else (
                    "BEARISH" if candles[-1].close < min(x.low for x in prevwindow) else None)
    else:
        breakout = None
    # Confirmed touches require a close back from the level and directionality; no future bar peeking.
    session_low_touched = min(last_lows) <= min(x.low for x in today) + max(tol, atr_value*0.25) if today else False
    session_high_touched = max(last_highs) >= max(x.high for x in today) - max(tol, atr_value*0.25) if today else False
    support_bounce = bool(((near_support and touched_support and candles[-1].close > near_support.price + 0.10*atr_value)
                           or (today and session_low_touched and candles[-1].close > min(x.low for x in today) + 0.10*atr_value))
                          and (r3 or 0) > 0 and candles[-1].close >= candles[-2].close)
    resistance_rejection = bool(((near_resistance and touched_resistance and candles[-1].close < near_resistance.price - 0.10*atr_value)
                                 or (today and session_high_touched and candles[-1].close < max(x.high for x in today) - 0.10*atr_value))
                                and (r3 or 0) < 0 and candles[-1].close <= candles[-2].close)
    features = PriceFeatures(
        spot=spot, candle_at=candles[-1].timestamp, atr=atr_value, ret_1m=returns(candles,1),
        ret_3m=r3, ret_5m=r5, ret_15m=r15, efficiency_10m=eff, trend=bias, breakout=breakout,
        session_low=min(x.low for x in today) if today else candles[-1].low,
        session_high=max(x.high for x in today) if today else candles[-1].high,
        nearest_support=near_support, nearest_resistance=near_resistance,
        touched_support=touched_support, touched_resistance=touched_resistance,
        support_bounce=support_bounce, resistance_rejection=resistance_rejection,
        future_vwap=futures_vwap, future_direction=futures_direction,
    )
    return features, supports, resistances, step, tol


def classify_regime(oi: OIEvidence, px: PriceFeatures, prior_regime: str | None,
                    spot_change_between_oi_snapshots: float | None = None) -> dict[str, Any]:
    """OI-first hypothesis followed by spot/futures confirmation and explicit reversal-watch states."""
    oi_dir = oi.label if oi.label in {"BULLISH", "BEARISH"} else "MIXED"
    atr_value = px.atr or 1.0
    sharp_up = (px.ret_3m or 0.0) >= 0.80 * atr_value and (px.ret_5m or 0.0) > 0
    sharp_down = (px.ret_3m or 0.0) <= -0.80 * atr_value and (px.ret_5m or 0.0) < 0
    # Futures confirms only when its VWAP/direction is available and spot momentum agrees;
    # futures direction alone cannot create a spot entry.
    spot_recent_up = (px.ret_3m or 0.0) > 0 and (px.ret_5m or 0.0) > 0
    spot_recent_down = (px.ret_3m or 0.0) < 0 and (px.ret_5m or 0.0) < 0
    fut_bull_confirms = px.future_direction == "BULLISH" and px.future_vwap is not None and spot_recent_up
    fut_bear_confirms = px.future_direction == "BEARISH" and px.future_vwap is not None and spot_recent_down
    snapshot_move_threshold = max(0.5, atr_value * 0.10)
    snapshot_momentum_bull = (spot_change_between_oi_snapshots is not None
                              and spot_change_between_oi_snapshots >= snapshot_move_threshold)
    snapshot_momentum_bear = (spot_change_between_oi_snapshots is not None
                              and spot_change_between_oi_snapshots <= -snapshot_move_threshold)
    price_bull = (px.trend == "BULLISH" or px.breakout == "BULLISH" or px.support_bounce or sharp_up
                  or fut_bull_confirms or (snapshot_momentum_bull and spot_recent_up))
    price_bear = (px.trend == "BEARISH" or px.breakout == "BEARISH" or px.resistance_rejection or sharp_down
                  or fut_bear_confirms or (snapshot_momentum_bear and spot_recent_down))
    price_range = px.trend == "RANGE" and (px.efficiency_10m is None or px.efficiency_10m < 0.28)
    prior_bull = prior_regime in {"CONTINUOUS_BULLISH", "REVERSAL_BEAR_TO_BULL", "BULLISH_RECLAIM"} or (
        (px.ret_15m or 0.0) >= 0.70 * atr_value and px.resistance_rejection)
    prior_bear = prior_regime in {"CONTINUOUS_BEARISH", "REVERSAL_BULL_TO_BEAR", "BEARISH_REJECTION"} or (
        (px.ret_15m or 0.0) <= -0.70 * atr_value and px.support_bounce)
    # A possible reversal can be warned on OI divergence at a relevant edge before price confirms.
    if prior_bull and oi_dir == "BEARISH" and oi.confidence >= 0.55:
        if price_bear:
            return {"regime":"REVERSAL_BULL_TO_BEAR", "forecast_direction":"BEARISH", "entry_allowed":True,
                    "confidence":min(0.95, 0.55*oi.confidence + 0.45), "reason":"BEARISH_OI_CONFIRMED_BY_SPOT_BREAK_OR_REJECTION"}
        if px.touched_resistance or (px.ret_5m or 0) < 0:
            return {"regime":"REVERSAL_WATCH_BULL_TO_BEAR", "forecast_direction":"BEARISH_WATCH", "entry_allowed":False,
                    "confidence":oi.confidence*0.65, "reason":"BEARISH_OI_DIVERGENCE_NEEDS_SPOT_CONFIRMATION"}
    if prior_bear and oi_dir == "BULLISH" and oi.confidence >= 0.55:
        if price_bull:
            return {"regime":"REVERSAL_BEAR_TO_BULL", "forecast_direction":"BULLISH", "entry_allowed":True,
                    "confidence":min(0.95, 0.55*oi.confidence + 0.45), "reason":"BULLISH_OI_CONFIRMED_BY_SPOT_RECLAIM_OR_BREAK"}
        if px.touched_support or (px.ret_5m or 0) > 0:
            return {"regime":"REVERSAL_WATCH_BEAR_TO_BULL", "forecast_direction":"BULLISH_WATCH", "entry_allowed":False,
                    "confidence":oi.confidence*0.65, "reason":"BULLISH_OI_DIVERGENCE_NEEDS_SPOT_CONFIRMATION"}
    if oi_dir == "BULLISH" and oi.confidence >= 0.55 and price_bull:
        regime = "REVERSAL_BEAR_TO_BULL" if prior_bear else "CONTINUOUS_BULLISH"
        return {"regime":regime, "forecast_direction":"BULLISH", "entry_allowed":True,
                "confidence":min(0.95, 0.55*oi.confidence + 0.45), "reason":"BULLISH_OI_CONFIRMED_BY_SPOT"}
    if oi_dir == "BEARISH" and oi.confidence >= 0.55 and price_bear:
        regime = "REVERSAL_BULL_TO_BEAR" if prior_bull else "CONTINUOUS_BEARISH"
        return {"regime":regime, "forecast_direction":"BEARISH", "entry_allowed":True,
                "confidence":min(0.95, 0.55*oi.confidence + 0.45), "reason":"BEARISH_OI_CONFIRMED_BY_SPOT"}
    # Range entries are considered only after a bounce/rejection at an identified edge.
    if price_range and oi_dir == "BULLISH":
        if px.support_bounce:
            return {"regime":"SIDEWAYS_SUPPORT_BOUNCE", "forecast_direction":"BULLISH", "entry_allowed":True,
                    "confidence":min(0.70, oi.confidence*0.75), "reason":"RANGE_EDGE_SUPPORT_BOUNCE_WITH_BULLISH_OI"}
        return {"regime":"SIDEWAYS_OI_BULLISH_WAIT_EDGE", "forecast_direction":"NEUTRAL", "entry_allowed":False,
                "confidence":oi.confidence*0.5, "reason":"SIDEWAYS_REQUIRES_SUPPORT_BOUNCE"}
    if price_range and oi_dir == "BEARISH":
        if px.resistance_rejection:
            return {"regime":"SIDEWAYS_RESISTANCE_REJECTION", "forecast_direction":"BEARISH", "entry_allowed":True,
                    "confidence":min(0.70, oi.confidence*0.75), "reason":"RANGE_EDGE_RESISTANCE_REJECTION_WITH_BEARISH_OI"}
        return {"regime":"SIDEWAYS_OI_BEARISH_WAIT_EDGE", "forecast_direction":"NEUTRAL", "entry_allowed":False,
                "confidence":oi.confidence*0.5, "reason":"SIDEWAYS_REQUIRES_RESISTANCE_REJECTION"}
    if price_range and oi_dir == "MIXED":
        if px.support_bounce and oi.bull_score >= 0.55:
            return {"regime":"SIDEWAYS_SUPPORT_BOUNCE", "forecast_direction":"BULLISH", "entry_allowed":True,
                    "confidence":0.55, "reason":"RANGE_EDGE_SUPPORT_BOUNCE_WITH_BULLISH_OI"}
        if px.resistance_rejection and oi.bear_score >= 0.55:
            return {"regime":"SIDEWAYS_RESISTANCE_REJECTION", "forecast_direction":"BEARISH", "entry_allowed":True,
                    "confidence":0.55, "reason":"RANGE_EDGE_REJECTION_WITH_BEARISH_OI"}
        return {"regime":"SIDEWAYS", "forecast_direction":"NEUTRAL", "entry_allowed":False,
                "confidence":0.5, "reason":"LOW_EFFICIENCY_OR_CONFLICTED_OI_RANGE"}
    if (oi_dir == "BULLISH" and price_bear) or (oi_dir == "BEARISH" and price_bull):
        return {"regime":"TRANSITION", "forecast_direction":"NEUTRAL", "entry_allowed":False,
                "confidence":min(oi.confidence, 0.5), "reason":"OI_PRICE_DIVERGENCE"}
    return {"regime":"TRANSITION" if oi_dir != "MIXED" else "UNKNOWN", "forecast_direction":"NEUTRAL",
            "entry_allowed":False, "confidence":oi.confidence*0.5, "reason":"NO_CONFIRMED_DIRECTIONAL_EDGE"}


def risk_plan(direction: str, spot: float, px: PriceFeatures, supports: Sequence[Level], resistances: Sequence[Level],
              tol: float, min_rr: float, max_stop_atr: float) -> tuple[RiskPlan | None, str]:
    if px.atr is None or px.atr <= 0:
        return None, "DATA_QUALITY_BLOCK"
    buf = max(0.05, px.atr * 0.10)
    if direction == "BULLISH":
        support = [x for x in supports if x.price < spot - 0.05]
        resistance = sorted([x for x in resistances if x.price > spot + max(0.05, tol*0.25)], key=lambda x:x.price)
        if not support or not resistance:
            return None, "NO_TARGET"
        stop_level = max(support, key=lambda x:x.price)
        stop = stop_level.price - buf
        targets = resistance
    else:
        resistance = [x for x in resistances if x.price > spot + 0.05]
        support = sorted([x for x in supports if x.price < spot - max(0.05, tol*0.25)], key=lambda x:x.price, reverse=True)
        if not resistance or not support:
            return None, "NO_TARGET"
        stop_level = min(resistance, key=lambda x:x.price)
        stop = stop_level.price + buf
        targets = support
    risk = abs(spot - stop)
    if risk <= 0:
        return None, "DATA_QUALITY_BLOCK"
    if risk > px.atr * max_stop_atr:
        return None, "STOP_TOO_WIDE"
    t1_level = targets[0]
    if direction == "BULLISH":
        reward1 = t1_level.price - spot
        t2_candidates = [x for x in targets[1:] if x.price > t1_level.price + tol]
    else:
        reward1 = spot - t1_level.price
        t2_candidates = [x for x in targets[1:] if x.price < t1_level.price - tol]
    if reward1 <= 0:
        return None, "NO_TARGET"
    rr1 = reward1 / risk
    # Critical rule: T1 is the nearest barrier. T2 cannot rescue a sub-2R T1.
    if rr1 + 1e-9 < min_rr:
        return None, "RR_BELOW_2R"
    if not t2_candidates:
        return None, "NO_T2_TARGET"
    t2 = t2_candidates[0].price
    reward2 = (t2 - spot) if direction == "BULLISH" else (spot-t2)
    rr2 = reward2 / risk if reward2 > 0 else None
    return RiskPlan(spot, stop, t1_level.price, t2, risk, reward1, reward2, rr1, rr2,
                    stop_level.source, t1_level.source, t2_candidates[0].source if t2_candidates else None), "OK"


def select_option(legs: Sequence[OptionLeg], quotes: Mapping[str, Quote], direction: str, spot: float,
                  at: dt.datetime, risk: RiskPlan, cfg: Config, step: float) -> tuple[dict[str, Any] | None, str]:
    # Strike offsets are exactly as requested: CE ATM/ATM-1/ATM-2; PE ATM/ATM+1/ATM+2.
    strikes = sorted({x.strike for x in legs})
    if not strikes:
        return None, "NO_ELIGIBLE_STRIKE"
    atm = min(strikes, key=lambda x: abs(x-spot))
    target_offsets = [0, -1, -2] if direction == "BULLISH" else [0, 1, 2]
    candidates = []
    expected_strikes = [atm + off*step for off in target_offsets]
    side = "CE" if direction == "BULLISH" else "PE"
    for off, strike in zip(target_offsets, expected_strikes):
        # Match against actual chain strikes, never construct a contract key or guess an ID.
        matched_strike = min(strikes, key=lambda x: abs(x-strike))
        if abs(matched_strike - strike) > max(0.01, step*0.20):
            continue
        matching = [x for x in legs if x.side == side and x.strike == matched_strike]
        for leg in matching:
            q = quotes.get(leg.instrument_key)
            if not q or q.age_seconds(at) > cfg.quote_max_age_seconds or q.timestamp > at + dt.timedelta(seconds=5):
                continue
            if q.bid is None or q.ask is None or q.bid <= 0 or q.ask < q.bid or q.ask <= 0:
                continue
            if (q.bid_qty or 0) < cfg.min_quote_quantity or (q.ask_qty or 0) < cfg.min_quote_quantity:
                continue
            mid = (q.bid+q.ask)/2
            spread_pct = (q.ask-q.bid)/mid*100 if mid > 0 else math.inf
            if spread_pct > cfg.max_option_spread_pct:
                continue
            if leg.delta is None or not (cfg.min_abs_delta <= abs(leg.delta) <= cfg.max_abs_delta):
                continue
            if (leg.side == "CE" and leg.delta <= 0) or (leg.side == "PE" and leg.delta >= 0):
                continue
            # Greeks scenario: delta + gamma + theta + adverse IV shift. Theta is assumed per calendar day.
            if None in (leg.gamma, leg.theta, leg.vega, leg.iv) or leg.iv is None or leg.iv <= 0:
                continue
            if leg.gamma is None or leg.gamma < 0 or leg.vega is None or leg.vega < 0:
                continue
            entry = q.ask + cfg.option_slippage_per_side
            hold_fraction_day = cfg.scenario_holding_minutes / (24*60)
            def scenario(underlying_target: float) -> float:
                move = underlying_target - spot
                # Exits are projected from the current executable BID, not from LTP or ask.
                # This is still a Greeks sensitivity scenario, not a full option-pricing model.
                return (q.bid + leg.delta*move + 0.5*(leg.gamma or 0.0)*move*move
                        + (leg.theta or 0.0)*hold_fraction_day + (leg.vega or 0.0)*cfg.adverse_iv_points)
            prem_stop_model = scenario(risk.stop)
            prem_t1_model = scenario(risk.t1)
            prem_t2_model = scenario(risk.t2) if risk.t2 is not None else None
            prem_stop = max(0.01, prem_stop_model-cfg.option_slippage_per_side)
            prem_t1 = max(0.01, prem_t1_model-cfg.option_slippage_per_side)
            prem_t2 = max(0.01, prem_t2_model-cfg.option_slippage_per_side) if prem_t2_model is not None else None
            costs = cfg.round_trip_cost_per_unit
            risk_cash = entry - prem_stop + costs
            reward_cash = prem_t1 - entry - costs
            net_rr = reward_cash/risk_cash if risk_cash > 0 and reward_cash > 0 else 0.0
            candidates.append({
                "instrument_key": leg.instrument_key, "expiry": leg.expiry, "strike": leg.strike, "side": leg.side,
                "trading_symbol": f"NIFTY {leg.strike:g} {leg.side} {leg.expiry}", "atm_offset": off,
                "atm_strike": atm, "delta": leg.delta, "gamma": leg.gamma, "theta": leg.theta,
                "vega": leg.vega, "iv": leg.iv, "quote_timestamp": iso(q.timestamp),
                "last_trade_time": iso(q.last_trade_time),
                "last_trade_age_seconds": round(q.last_trade_age_seconds(at), 2) if q.last_trade_age_seconds(at) is not None else None,
                "quote_age_seconds": round(q.age_seconds(at), 2), "bid": q.bid, "ask": q.ask,
                "bid_qty": q.bid_qty, "ask_qty": q.ask_qty, "spread_pct": round(spread_pct, 3),
                "premium_entry_estimate": round(entry, 2), "premium_sl_estimate": round(max(0.01, prem_stop), 2),
                "premium_t1_estimate": round(max(0.01, prem_t1), 2),
                "premium_t2_estimate": round(max(0.01, prem_t2), 2) if prem_t2 is not None else None,
                "option_net_rr_t1": round(net_rr, 3), "cost_assumption_per_unit": round(costs, 2),
                "scenario_method": "delta+gamma+theta+vega sensitivity; estimate, not exact repricing",
            })
    if not candidates:
        return None, "NO_ELIGIBLE_STRIKE"
    # Preference order honors ATM, then first ITM, then second ITM unless risk-adjusted quality is worse.
    # Penalize distance offset but prefer the candidate with sound net RR and narrower spread.
    order = {0:0, -1:1, -2:2, 1:1, 2:2}
    candidates.sort(key=lambda x: (-(x["option_net_rr_t1"] >= cfg.min_reward_risk), order.get(x["atm_offset"], 9),
                                   x["spread_pct"], -min(x["bid_qty"] or 0, x["ask_qty"] or 0)))
    selected = candidates[0]
    if selected["option_net_rr_t1"] < cfg.min_reward_risk:
        return None, "OPTION_NET_RR_BELOW_2R"
    selected["candidate_rankings"] = [{k:v for k,v in c.items() if k not in {"candidate_rankings"}} for c in candidates]
    return selected, "OK"


# ------------------------------ Durable state ------------------------------

def default_state() -> dict[str, Any]:
    return {"schema_version": 99, "scanner_version": VERSION, "session_date": None, "expiry": None,
            "chain_snapshots": [], "session_oi_baseline": None, "candles": [], "oi_evidence_history": [], "last_regime": None,
            "regime_episode_id": None, "last_processed_candle": None, "candle_sequence": [],
            "processed_candle_count": 0, "last_signal_key": None, "dedup_keys": [], "audit": [], "updated_at": None}


class LocalState:
    def __init__(self, path: str):
        self.path = Path(path)
        self.sha = None
    def load(self) -> dict[str, Any]:
        if not self.path.exists():
            return default_state()
        try:
            state = json.loads(self.path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise ScannerError("STATE_SAVE_FAILED", f"State JSON invalid/unreadable: {type(exc).__name__}") from exc
        if not isinstance(state, dict):
            raise ScannerError("STATE_SAVE_FAILED", "State root must be JSON object")
        # Clean-slate schema. Do not silently misinterpret older v96/v98 fields as v99 data.
        if state.get("schema_version") != 99:
            LOG.warning("Existing state schema %r is incompatible; starting a new v99 session state", state.get("schema_version"))
            return default_state()
        return state
    def save(self, state: dict[str, Any], revision: Any = None) -> None:
        state["schema_version"] = 99
        state["scanner_version"] = VERSION
        data = json.dumps(jsonable(state), separators=(",", ":"), sort_keys=True).encode()
        self.path.parent.mkdir(parents=True, exist_ok=True)
        fd, temp_name = tempfile.mkstemp(prefix=self.path.name+".", suffix=".tmp", dir=str(self.path.parent))
        try:
            with os.fdopen(fd, "wb") as f:
                f.write(data); f.flush(); os.fsync(f.fileno())
            os.replace(temp_name, self.path)
        finally:
            if os.path.exists(temp_name):
                os.unlink(temp_name)


class GitHubState:
    """Optimistic concurrency via GitHub Contents API SHA; failures suppress notifications."""
    def __init__(self, config: Config):
        self.config = config
        self.sha: str | None = None
    def _url(self) -> str:
        owner_repo = self.config.github_state_repository.strip("/")
        path = urllib.parse.quote(self.config.github_state_path.strip("/"), safe="/")
        return f"https://api.github.com/repos/{owner_repo}/contents/{path}?ref={urllib.parse.quote(self.config.github_state_branch)}"
    def load(self) -> dict[str, Any]:
        headers = {"Authorization": f"Bearer {self.config.github_state_token}", "Accept":"application/vnd.github+json", "X-GitHub-Api-Version":"2022-11-28"}
        try:
            data, _ = request_json(self._url(), self.config.github_state_token, self.config.api_timeout_seconds, 1, extra_headers=headers)
            self.sha = data.get("sha")
            content = base64.b64decode(data.get("content", "")).decode()
            state = json.loads(content)
            if not isinstance(state, dict) or state.get("schema_version") != 99:
                return default_state()
            return state
        except ScannerError as exc:
            # A missing file is a valid first run only for HTTP 404; request_json wraps it as API_UNAVAILABLE.
            if "HTTP 404" in str(exc):
                self.sha = None
                return default_state()
            raise ScannerError("STATE_SAVE_FAILED", "Cannot load durable GitHub state") from exc
        except Exception as exc:
            raise ScannerError("STATE_SAVE_FAILED", "Cannot decode GitHub state") from exc
    def save(self, state: dict[str, Any], revision: Any = None) -> None:
        state["schema_version"] = 99; state["scanner_version"] = VERSION
        url = self._url().split("?",1)[0]
        body = {"message":f"Update NIFTY scanner v99 state {now_ist().isoformat()}",
                "content":base64.b64encode(json.dumps(jsonable(state), separators=(",", ":"), sort_keys=True).encode()).decode(),
                "branch":self.config.github_state_branch}
        if self.sha:
            body["sha"] = self.sha
        headers = {"Authorization":f"Bearer {self.config.github_state_token}", "Accept":"application/vnd.github+json",
                   "X-GitHub-Api-Version":"2022-11-28"}
        try:
            out, _ = request_json(url, self.config.github_state_token, self.config.api_timeout_seconds, 0,
                                  method="PUT", body=body, extra_headers=headers)
            self.sha = ((out.get("content") or {}).get("sha")) or self.sha
        except ScannerError as exc:
            raise ScannerError("STATE_CONFLICT", "Concurrent or failed GitHub state commit; alert suppressed") from exc


@contextlib.contextmanager
def local_state_lock(path: str, timeout_seconds: float):
    """Serialize local runs on the same persistent filesystem using an advisory file lock."""
    try:
        import fcntl  # Unix/GitHub Actions runner
    except ImportError:
        yield
        return
    lock_path = Path(path).with_suffix(Path(path).suffix + ".lock")
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with open(lock_path, "a+", encoding="utf-8") as handle:
        deadline = time.monotonic() + timeout_seconds
        while True:
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if time.monotonic() >= deadline:
                    raise ScannerError("STATE_CONFLICT", "Timed out waiting for local state lock")
                time.sleep(0.1)
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def create_state_store(cfg: Config) -> LocalState | GitHubState:
    backend = cfg.state_backend
    if backend == "auto":
        backend = "github" if cfg.github_state_repository and cfg.github_state_token else "local"
    return GitHubState(cfg) if backend == "github" else LocalState(cfg.state_file)


def append_audit(state: dict[str, Any], item: Mapping[str, Any], limit: int) -> None:
    audit = state.setdefault("audit", [])
    audit.append(jsonable(dict(item)))
    state["audit"] = audit[-limit:]

def update_candle_cursor(state: dict[str, Any], completed: Sequence[Candle]) -> int:
    """Process all unseen completed candles in chronological order; never emit retroactive fills."""
    cursor = parse_dt(state.get("last_processed_candle"))
    unseen = [c for c in sorted(completed, key=lambda x: x.timestamp) if cursor is None or c.timestamp > cursor]
    sequence = list(state.get("candle_sequence", []))
    prior_close = as_float(sequence[-1].get("close")) if sequence else None
    for candle in unseen:
        direction = "UP" if prior_close is not None and candle.close > prior_close else (
                   "DOWN" if prior_close is not None and candle.close < prior_close else "FLAT")
        sequence.append({"timestamp":iso(candle.timestamp),"open":candle.open,"high":candle.high,
                         "low":candle.low,"close":candle.close,"direction":direction})
        prior_close = candle.close
        state["last_processed_candle"] = iso(candle.timestamp)
    state["candle_sequence"] = sequence[-30:]
    state["processed_candle_count"] = int(state.get("processed_candle_count", 0)) + len(unseen)
    return len(unseen)


def regime_direction(regime: str | None) -> str | None:
    if regime in {"CONTINUOUS_BULLISH", "REVERSAL_BEAR_TO_BULL", "SIDEWAYS_SUPPORT_BOUNCE", "BULLISH_RECLAIM"}:
        return "BULLISH"
    if regime in {"CONTINUOUS_BEARISH", "REVERSAL_BULL_TO_BEAR", "SIDEWAYS_RESISTANCE_REJECTION", "BEARISH_REJECTION"}:
        return "BEARISH"
    return None


def stable_signal_key(session_date: str, expiry: str, episode_id: str, direction: str) -> str:
    """One alert per directional episode, not one alert per newly completed minute."""
    raw = f"{session_date}|{expiry}|{episode_id}|{direction}"
    return hashlib.sha256(raw.encode()).hexdigest()[:24]


# ------------------------------ Signal pipeline ------------------------------
def market_open(at: dt.datetime, start: str, end: str) -> bool:
    local = at.astimezone(IST)
    start_t = dt.time.fromisoformat(start); end_t = dt.time.fromisoformat(end)
    return local.weekday() < 5 and start_t <= local.time().replace(tzinfo=None) <= end_t


def futures_vwap(candles: Sequence[Candle]) -> float | None:
    valid = [c for c in candles if c.volume > 0]
    volume = sum(c.volume for c in valid)
    if volume <= 0:
        return None
    return sum(((c.high+c.low+c.close)/3.0)*c.volume for c in valid) / volume


def future_direction(candles: Sequence[Candle], vwap: float | None) -> str:
    if not candles or vwap is None or len(candles) < 4:
        return "UNKNOWN"
    delta = candles[-1].close - candles[-4].close
    if delta > 0 and candles[-1].close > vwap:
        return "BULLISH"
    if delta < 0 and candles[-1].close < vwap:
        return "BEARISH"
    return "MIXED"


def scan_once(cfg: Config, api: UpstoxAPI, store: LocalState | GitHubState, at: dt.datetime | None = None) -> dict[str, Any]:
    now = (at or now_ist()).astimezone(IST)
    state = store.load()
    state_revision = getattr(store, "sha", None)
    if not market_open(now, cfg.market_start, cfg.market_end):
        result = {"timestamp": iso(now), "scanner_version": VERSION, "decision":"NO_TRADE", "reason_code":"MARKET_CLOSED"}
        emit(result); return result
    try:
        underlying_key = api.resolve_underlying_key()
        expiry, contract_meta = api.resolve_expiry(underlying_key, now.date())
        legs, chain_spot, fetched_at = api.option_chain(underlying_key, expiry)
        metadata_by_key = {str(x.get("instrument_key")): x for x in contract_meta if x.get("instrument_key")}
        validated_legs = []
        for leg in legs:
            meta = metadata_by_key.get(leg.instrument_key)
            if not meta:
                continue
            meta_strike = as_float(meta.get("strike_price"))
            if (str(meta.get("expiry")) != expiry or str(meta.get("instrument_type")) != leg.side
                    or meta_strike is None or abs(meta_strike-leg.strike) > 0.01):
                continue
            validated_legs.append(leg)
        if len(validated_legs) < 6:
            raise ScannerError("DATA_QUALITY_BLOCK", "Option-chain contracts could not be identity-validated against option-contract metadata")
        legs = validated_legs
        # Refresh both current spot quote and completed candles; never substitute one timestamp for another.
        spot_quote_map = api.quote_map([underlying_key])
        spot_quote = spot_quote_map.get(underlying_key)
        if not spot_quote:
            # Some API response maps do not expose an instrument_token; use exact key alias only.
            raise ScannerError("DATA_QUALITY_BLOCK", "No timestamped full-market quote for NIFTY 50")
        if spot_quote.age_seconds(now) > cfg.quote_max_age_seconds:
            raise ScannerError("DATA_QUALITY_BLOCK", "NIFTY spot quote is stale")
        candles_new = complete_candles(api.candles_intraday(underlying_key), now, cfg.candle_close_buffer_seconds)
        state_date = state.get("session_date")
        if state_date != now.date().isoformat():
            # Clear per-session OI sequence/regime, preserve only dedup keys for the date namespace.
            state["session_date"] = now.date().isoformat()
            state["chain_snapshots"] = []; state["session_oi_baseline"] = None; state["candles"] = []; state["oi_evidence_history"] = []
            state["last_regime"] = None; state["regime_episode_id"] = None; state["expiry"] = None
            state["last_processed_candle"] = None; state["candle_sequence"] = []; state["processed_candle_count"] = 0
        if state.get("expiry") not in (None, expiry):
            state["chain_snapshots"] = []; state["session_oi_baseline"] = None; state["oi_evidence_history"] = []; state["last_regime"] = None
            state["regime_episode_id"] = None
        state["expiry"] = expiry
        merged_candle_rows = merge_candles(state.get("candles", []), candles_new, cfg.max_candles)
        candles = state_candles(merged_candle_rows)
        # Catch up over every missed minute, but only evaluate/enter at the current timestamp below.
        processed_new_candles = update_candle_cursor(state, candles)
        if not candles:
            raise ScannerError("DATA_QUALITY_BLOCK", "No completed NIFTY 1-minute candles")
        candle_age = (now - (candles[-1].timestamp + dt.timedelta(minutes=1))).total_seconds()
        if candle_age > cfg.candle_max_age_seconds:
            raise ScannerError("DATA_QUALITY_BLOCK", f"Latest completed candle stale by {candle_age:.1f}s")
        prior = api.prior_session_candles(underlying_key, now.date())
        future_meta = api.resolve_future(underlying_key, now.date())
        fvwap = None; fdir = "UNKNOWN"; future_rows: list[Candle] = []
        if future_meta:
            try:
                future_rows = complete_candles(api.candles_intraday(str(future_meta["instrument_key"])), now, cfg.candle_close_buffer_seconds)
                fvwap = futures_vwap(future_rows)
                fdir = future_direction(future_rows, fvwap)
            except (ScannerError, KeyError):
                if cfg.require_futures:
                    raise ScannerError("DATA_QUALITY_BLOCK", "Futures confirmation was required but unavailable")
        elif cfg.require_futures:
            raise ScannerError("DATA_QUALITY_BLOCK", "Futures contract could not be resolved")
        if at is None:
            # Revalidate all inputs against the actual end-of-fetch evaluation timestamp.
            now = now_ist()
        if spot_quote.timestamp > now + dt.timedelta(seconds=5) or spot_quote.age_seconds(now) > cfg.quote_max_age_seconds:
            raise ScannerError("DATA_QUALITY_BLOCK", "NIFTY spot quote is stale or timestamped in the future at evaluation time")
        if not market_open(now, cfg.market_start, cfg.market_end):
            raise ScannerError("MARKET_CLOSED", "Market closed before evaluation finished")
        chain_snapshot = compact_snapshot(legs, expiry, fetched_at, chain_spot)
        snapshots = state.get("chain_snapshots", [])
        prev_snapshot = snapshots[-1] if snapshots else None
        oi_summary = oi_context_summary(legs, prev_snapshot, chain_spot, cfg.oi_radius_strikes, cfg.oi_change_threshold_pct)
        # OI-first: calculate directional flow hypothesis before deriving price regime/setup.
        prior_labels = [x.get("label") for x in state.get("oi_evidence_history", [])]
        session_baseline = state.get("session_oi_baseline")
        oi = compute_oi_evidence(chain_snapshot, prev_snapshot, now, cfg, prior_labels, session_baseline)
        previous_chain_spot = as_float(prev_snapshot.get("spot")) if prev_snapshot else None
        spot_change_between_oi_snapshots = (chain_spot - previous_chain_spot) if previous_chain_spot is not None else None
        if session_baseline is None:
            # First valid chain received this session establishes the distinct session OI baseline.
            state["session_oi_baseline"] = chain_snapshot
        # Use timestamped live spot quote for entry; chain spot is a separate snapshot and is cross-checked.
        if abs(spot_quote.price - chain_spot) > max(2.0, (atr(candles, cfg.atr_period) or 20.0) * 0.75):
            raise ScannerError("DATA_QUALITY_BLOCK", "Spot quote and option-chain underlying price materially diverge")
        px, supports, resistances, strike_step, tol = price_features(candles, prior, legs, spot_quote.price,
                                                                     spot_quote, now, cfg, fvwap, fdir)
        prior_regime = state.get("last_regime")
        regime = classify_regime(oi, px, prior_regime, spot_change_between_oi_snapshots)
        confirmed_regimes = {"CONTINUOUS_BULLISH","CONTINUOUS_BEARISH","REVERSAL_BULL_TO_BEAR","REVERSAL_BEAR_TO_BULL",
                             "SIDEWAYS_SUPPORT_BOUNCE","SIDEWAYS_RESISTANCE_REJECTION","BULLISH_RECLAIM","BEARISH_REJECTION"}
        if regime["regime"] in confirmed_regimes and regime_direction(regime["regime"]) is not None:
            previous_episode_direction = regime_direction(prior_regime)
            next_episode_direction = regime_direction(regime["regime"])
            if not state.get("regime_episode_id") or previous_episode_direction != next_episode_direction:
                episode_seed = f"{now.date().isoformat()}|{expiry}|{next_episode_direction}|{iso(candles[-1].timestamp)}"
                state["regime_episode_id"] = hashlib.sha256(episode_seed.encode()).hexdigest()[:20]
        direction = regime["forecast_direction"] if regime["forecast_direction"] in {"BULLISH", "BEARISH"} else None
        decision = {"timestamp":iso(now), "scanner_version":VERSION, "decision":"NO_TRADE", "reason_code":"NO_CONFIRMED_SETUP",
                    "session_date":now.date().isoformat(), "underlying_key":underlying_key, "expiry":expiry,
                    "snapshot_fetched_at":iso(fetched_at), "oi_snapshot_age_seconds":oi.age_seconds,
                    "oi_snapshot_interval_seconds":oi.interval_seconds,
                    "spot_change_between_oi_snapshots_points":spot_change_between_oi_snapshots,
                    "spot_change_between_oi_snapshots_pct":safe_pct(chain_spot, previous_chain_spot),
                    "oi_label":oi.label,
                    "oi_bull_score":round(oi.bull_score,4), "oi_bear_score":round(oi.bear_score,4),
                    "oi_confidence":round(oi.confidence,4), "oi_rows_used":oi.valid_rows,
                    "oi_material_rows":oi.material_rows, "oi_reason":oi.reason, "oi_context":oi_summary,
                    "spot":spot_quote.price, "spot_quote_timestamp":iso(spot_quote.timestamp),
                    "option_chain_spot":chain_spot,"spot_chain_discrepancy_points":round(spot_quote.price-chain_spot,3),
                    "last_completed_candle_timestamp":iso(candles[-1].timestamp), "last_completed_candle_age_seconds":round(candle_age,1),
                    "higher_timeframe_trend":px.trend, "regime":regime["regime"],
                    "forecast_direction":regime["forecast_direction"], "regime_confidence":round(regime["confidence"],3),
                    "regime_reason":regime["reason"], "entry_allowed_by_regime":regime["entry_allowed"],
                    "price_returns_points":{"1m":px.ret_1m,"3m":px.ret_3m,"5m":px.ret_5m,"15m":px.ret_15m},
                    "atr":px.atr,"efficiency_ratio_10m":px.efficiency_10m,
                    "session_low":px.session_low,"session_high":px.session_high,
                    "nearest_support":{"price":px.nearest_support.price,"source":px.nearest_support.source} if px.nearest_support else None,
                    "nearest_resistance":{"price":px.nearest_resistance.price,"source":px.nearest_resistance.source} if px.nearest_resistance else None,
                    "support_bounce_confirmed":px.support_bounce,"resistance_rejection_confirmed":px.resistance_rejection,
                    "breakout":px.breakout,"futures_vwap":fvwap,"futures_direction":fdir,
                    "option_selection":None,"underlying_risk_plan":None,
                    "oi_top_contributors":sorted(
                        [{k:v for k,v in row.items() if k in {"instrument_key","side","strike","oi_delta","oi_pct","premium_pct","vote","weight","reason"}}
                         for row in oi.detail], key=lambda row: abs(as_float(row.get("weight")) or 0.0), reverse=True)[:5],
                    "notes":"Forecast is a probabilistic hypothesis; alert-only, no orders submitted."}
        # A failed or missing OI baseline blocks directional option selection; don't reuse previous deltas as new.
        if oi.label == "STALE":
            decision["reason_code"] = "OI_STALE"
        elif oi.label == "MISSING":
            decision["reason_code"] = "OI_BASELINE_MISSING"
        elif oi.label == "MIXED" and regime["regime"] == "SIDEWAYS":
            decision["reason_code"] = "SIDEWAYS_NO_EDGE"
        elif regime["regime"].startswith("REVERSAL_WATCH"):
            decision["reason_code"] = "REVERSAL_WATCH"
        elif regime["regime"] == "TRANSITION" and regime["reason"] == "OI_PRICE_DIVERGENCE":
            decision["reason_code"] = "OI_PRICE_DIVERGENCE"
        # Need a fresh OI label and confirmed setup direction before entry planning.
        if oi.label in {"BULLISH", "BEARISH"} and oi.age_seconds is not None and oi.age_seconds <= cfg.oi_max_age_seconds and regime["entry_allowed"] and direction:
            plan, risk_status = risk_plan(direction, spot_quote.price, px, supports, resistances, tol, cfg.min_reward_risk, cfg.max_stop_atr)
            if not plan:
                decision["reason_code"] = risk_status if risk_status in REASON_CODES else "NO_CONFIRMED_SETUP"
                decision["risk_rejection"] = risk_status
            else:
                # Quote actual contracts using a fresh full-market quote request. Keys must map exactly.
                side = "CE" if direction == "BULLISH" else "PE"
                atm = min({x.strike for x in legs}, key=lambda x: abs(x-spot_quote.price))
                offsets = [0,-1,-2] if side == "CE" else [0,1,2]
                wanted = []
                for off in offsets:
                    expected = atm + off*strike_step
                    match = min(legs, key=lambda x: abs(x.strike-expected))
                    if abs(match.strike-expected) <= strike_step*0.20:
                        wanted.extend(x.instrument_key for x in legs if x.side == side and x.strike == match.strike)
                quote_map = api.quote_map(wanted)
                # quote_map uses exact instrument_token IDs. Refuse to fall back to stale option-chain bid/ask.
                selected, select_status = select_option(legs, quote_map, direction, spot_quote.price, now, plan, cfg, strike_step)
                if not selected:
                    decision["reason_code"] = select_status if select_status in REASON_CODES else "NO_ELIGIBLE_STRIKE"
                else:
                    episode_id = state.get("regime_episode_id")
                    if not episode_id:
                        # A qualified regime without an episode marker is not allowed to create an unstable key.
                        episode_seed = f"{now.date().isoformat()}|{expiry}|{regime['regime']}|{iso(candles[-1].timestamp)}"
                        episode_id = hashlib.sha256(episode_seed.encode()).hexdigest()[:20]
                        state["regime_episode_id"] = episode_id
                    key = stable_signal_key(now.date().isoformat(), expiry, str(episode_id), direction)
                    decision.update({"decision":"QUALIFIED", "reason_code":"QUALIFIED_CE" if side == "CE" else "QUALIFIED_PE",
                                     "signal_key":key,"direction":direction,"setup_regime":regime["regime"],
                                     "underlying_risk_plan":jsonable(plan),"option_selection":selected,
                                     "entry_spot_quote":spot_quote.price,"selected_strike":selected["strike"],
                                     "selected_side":side,"selected_offset_from_atm":selected["atm_offset"],
                                     "T1":plan.t1,"T2":plan.t2,"SL":plan.stop})
        # Do not carry prior regime forward from a watch/unknown condition. Only confirmed directional regimes persist.
        if regime["regime"] in {"CONTINUOUS_BULLISH","CONTINUOUS_BEARISH","REVERSAL_BULL_TO_BEAR","REVERSAL_BEAR_TO_BULL",
                                 "SIDEWAYS_SUPPORT_BOUNCE","SIDEWAYS_RESISTANCE_REJECTION","BULLISH_RECLAIM","BEARISH_REJECTION"}:
            state["last_regime"] = regime["regime"]
        state["candles"] = merged_candle_rows
        snapshots.append(chain_snapshot)
        state["chain_snapshots"] = snapshots[-cfg.max_snapshots:]
        state.setdefault("oi_evidence_history", []).append({"timestamp":iso(now),"label":oi.label,
                                                             "bull_score":oi.bull_score,"bear_score":oi.bear_score,
                                                             "confidence":oi.confidence})
        state["oi_evidence_history"] = state["oi_evidence_history"][-cfg.max_snapshots:]
        if decision.get("signal_key"):
            dedup = state.setdefault("dedup_keys", [])
            if decision["signal_key"] in dedup:
                decision["decision"] = "NO_TRADE"; decision["reason_code"] = "DUPLICATE_SIGNAL"
                for k in ("signal_key", "option_selection", "underlying_risk_plan", "selected_strike", "selected_side", "T1", "T2", "SL"):
                    decision.pop(k, None)
            else:
                dedup.append(decision["signal_key"]); state["dedup_keys"] = dedup[-cfg.max_dedup_keys:]
                state["last_signal_key"] = decision["signal_key"]
        state["updated_at"] = iso(now)
        append_audit(state, {"timestamp":iso(now),"decision":decision.get("decision"),"reason_code":decision.get("reason_code"),
                             "regime":decision.get("regime"),"oi_label":oi.label,"spot":spot_quote.price,
                             "signal_key":decision.get("signal_key"),"expiry":expiry}, cfg.max_audit_records)
        try:
            store.save(state, state_revision)
        except ScannerError as exc:
            emit({"timestamp":iso(now),"scanner_version":VERSION,"decision":"NO_TRADE","reason_code":exc.code,
                  "error":"State commit failed; any new signal was suppressed."})
            return {"decision":"NO_TRADE","reason_code":exc.code}
        # Notify only after durable state commit. The scanner never places orders.
        if decision.get("decision") == "QUALIFIED" and not cfg.dry_run:
            try:
                notify(cfg, decision)
                decision["notification_status"] = "SENT" if (cfg.webhook_url or cfg.smtp_host) else "NOT_CONFIGURED"
            except Exception as exc:
                decision["notification_status"] = "FAILED"
                decision["notification_error_type"] = type(exc).__name__
                decision["reason_code"] = "NOTIFIER_FAILED"
        elif decision.get("decision") == "QUALIFIED":
            decision["notification_status"] = "DRY_RUN"
        emit(decision)
        return decision
    except ScannerError as exc:
        result = {"timestamp":iso(now),"scanner_version":VERSION,"decision":"NO_TRADE","reason_code":exc.code,
                  "error_type":type(exc).__name__}
        LOG.warning("scan blocked: %s", exc.code)
        emit(result)
        return result


def notify(cfg: Config, signal: Mapping[str, Any]) -> None:
    text = json.dumps(jsonable(dict(signal)), indent=2, sort_keys=True)
    if cfg.webhook_url:
        request = urllib.request.Request(cfg.webhook_url, data=json.dumps({"text":text,"signal":jsonable(dict(signal))}).encode(),
                                         headers={"Content-Type":"application/json"}, method="POST")
        with urllib.request.urlopen(request, timeout=cfg.api_timeout_seconds) as response:
            if not 200 <= response.status < 300:
                raise RuntimeError(f"Webhook returned HTTP {response.status}")
    if cfg.smtp_host and cfg.email_from and cfg.email_to:
        msg = email.message.EmailMessage()
        msg["Subject"] = f"NIFTY v99 {signal.get('reason_code')} — {signal.get('selected_side')} {signal.get('selected_strike')}"
        msg["From"] = cfg.email_from; msg["To"] = cfg.email_to
        msg.set_content(text)
        with smtplib.SMTP(cfg.smtp_host, cfg.smtp_port, timeout=cfg.api_timeout_seconds) as smtp:
            smtp.starttls()
            if cfg.smtp_user:
                smtp.login(cfg.smtp_user, cfg.smtp_password)
            smtp.send_message(msg)


def print_environment() -> None:
    names = ["UPSTOX_ACCESS_TOKEN","NIFTY_INSTRUMENT_KEY (optional; otherwise discovered)","NIFTY_EXPIRY (nearest_weekly or YYYY-MM-DD)",
             "STATE_BACKEND","STATE_FILE","GITHUB_STATE_REPOSITORY","GITHUB_STATE_PATH","GITHUB_STATE_BRANCH","GITHUB_STATE_TOKEN",
             "ALERT_WEBHOOK_URL","SMTP_HOST","SMTP_PORT","SMTP_USER","SMTP_PASSWORD","EMAIL_FROM","EMAIL_TO","SCAN_DRY_RUN"]
    print("\n".join(names))


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="NIFTY 50 OI-first regime scanner v99 (alerting only)")
    parser.add_argument("--print-reason-codes", action="store_true")
    parser.add_argument("--show-env", action="store_true")
    parser.add_argument("--dry-run", action="store_true", help="Do not send notifications")
    args = parser.parse_args(argv)
    logging.basicConfig(level=os.getenv("LOG_LEVEL", "WARNING"), format="%(asctime)s %(levelname)s %(message)s")
    if args.print_reason_codes:
        print(json.dumps(REASON_CODES, indent=2, sort_keys=True)); return 0
    if args.show_env:
        print_environment(); return 0
    try:
        cfg = Config.from_env()
        if args.dry_run:
            cfg = dataclasses.replace(cfg, dry_run=True)
        store = create_state_store(cfg)
        api = UpstoxAPI(cfg)
        # GitHub Contents commits use SHA optimistic concurrency. Local stores are locked on persistent filesystems.
        if isinstance(store, LocalState):
            with local_state_lock(cfg.state_file, cfg.state_lock_timeout_seconds):
                scan_once(cfg, api, store)
        else:
            scan_once(cfg, api, store)
        return 0
    except Exception as exc:
        emit({"timestamp":iso(now_ist()),"scanner_version":VERSION,"decision":"NO_TRADE",
              "reason_code":"CONFIGURATION_OR_STARTUP_ERROR","error_type":type(exc).__name__,"message":str(exc)[:200]})
        return 2

if __name__ == "__main__":
    raise SystemExit(main())
