#!/usr/bin/env python3
"""NIFTY 50 intraday OI + market-structure scanner v102.0.0.

Single-file runtime for a GitHub Actions workflow dispatched about every three
minutes. It never places orders. Tests and documentation are separate files.

Design contract:
- signed OI changes are computed only between consecutive successful,
  same-session, same-expiry, identity-matched option-chain snapshots;
- one-minute candles are price observations, never a source of fabricated OI;
- a historical setup must pass a current-price/fresh-quote revalidation;
- the nearest valid opposing barrier is always T1 and cannot be bypassed;
- a trade requires both underlying RR and conservative option-net RR >= 2.0;
- state is written atomically before notification is attempted;
- failures produce explicit reason codes and never silently reuse stale data.

Sources of truth for the API adapter are documented in RESEARCH_NOTES_v102.md.
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
import shutil
import smtplib
import ssl
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass, field
from datetime import date, datetime, time as dtime, timedelta, timezone
from email.message import EmailMessage
from pathlib import Path
from statistics import median
from typing import Any, Iterable, Mapping, Optional, Sequence
from zoneinfo import ZoneInfo

VERSION = "102.0.0"
SCHEMA_VERSION = 102
IST = ZoneInfo("Asia/Kolkata")
UTC = timezone.utc
API_BASE = "https://api.upstox.com"
INSTRUMENTS_URL = "https://assets.upstox.com/market-quote/instruments/exchange/NSE.json.gz"
LOG = logging.getLogger("nifty_scanner")


# ---------- Configuration and errors ----------

class ScannerError(RuntimeError):
    def __init__(self, code: str, message: str, *, retryable: bool = False):
        super().__init__(message)
        self.code = code
        self.retryable = retryable


@dataclass(frozen=True)
class Config:
    token: str
    state_file: Path = Path("state/market_state_v102.json")
    audit_dir: Path = Path("audit")
    instrument_cache: Path = Path(".cache/upstox_nse.json.gz")
    explicit_expiry: Optional[date] = None
    request_timeout: float = 12.0
    max_retries: int = 2
    instrument_cache_hours: int = 12
    oi_material_threshold_pct: float = 2.0
    min_underlying_rr: float = 2.0
    min_option_net_rr: float = 2.0
    max_oi_age_seconds: int = 720
    expected_oi_interval_seconds: int = 180
    max_quote_age_seconds: int = 120
    max_candle_age_seconds: int = 150
    max_spread_pct: float = 3.0
    min_bid_qty: float = 1.0
    min_ask_qty: float = 1.0
    min_option_volume: float = 1.0
    min_abs_delta: float = 0.30
    max_abs_delta: float = 0.80
    max_entry_extension_atr: float = 0.80
    pivot_left: int = 2
    pivot_right: int = 2
    support_lookback_candles: int = 8
    setup_max_age_minutes: int = 3
    setup_state_ttl_minutes: int = 12
    strike_offsets_ce: tuple[int, ...] = (0, -1, -2)
    strike_offsets_pe: tuple[int, ...] = (0, 1, 2)
    iv_shock_points: float = 1.0
    expected_hold_minutes: float = 15.0
    annual_risk_free_rate: float = 0.06
    option_slippage_points: float = 1.0
    transaction_cost_rate: float = 0.0018
    min_level_strength: float = 1.0
    level_cluster_atr_fraction: float = 0.12
    stop_buffer_atr_fraction: float = 0.10
    minimum_stop_points: float = 5.0
    max_stop_atr: float = 2.5
    min_oi_direction_confidence: float = 0.56
    min_oi_score_margin: float = 0.12
    min_mixed_price_confirmation: float = 0.78
    email_sender: str = ""
    email_receiver: str = ""
    email_password: str = ""
    email_username: str = ""
    smtp_host: str = ""
    smtp_port: int = 465
    webhook_url: str = ""

    def __post_init__(self) -> None:
        if not self.token or not self.token.strip():
            raise ScannerError("CONFIG_TOKEN_MISSING", "Set UPSTOX_ANALYTICS_TOKEN in GitHub Secrets.")
        positive = {
            "request_timeout": self.request_timeout,
            "oi_material_threshold_pct": self.oi_material_threshold_pct,
            "min_underlying_rr": self.min_underlying_rr,
            "min_option_net_rr": self.min_option_net_rr,
            "max_oi_age_seconds": self.max_oi_age_seconds,
            "expected_oi_interval_seconds": self.expected_oi_interval_seconds,
            "max_quote_age_seconds": self.max_quote_age_seconds,
            "max_candle_age_seconds": self.max_candle_age_seconds,
            "max_spread_pct": self.max_spread_pct,
            "max_entry_extension_atr": self.max_entry_extension_atr,
            "setup_max_age_minutes": self.setup_max_age_minutes,
            "setup_state_ttl_minutes": self.setup_state_ttl_minutes,
            "expected_hold_minutes": self.expected_hold_minutes,
            "minimum_stop_points": self.minimum_stop_points,
            "max_stop_atr": self.max_stop_atr,
        }
        for name, value in positive.items():
            if not math.isfinite(float(value)) or float(value) <= 0:
                raise ScannerError("CONFIG_INVALID", f"{name} must be a finite number greater than zero")
        if self.min_underlying_rr < 2.0 or self.min_option_net_rr < 2.0:
            raise ScannerError("CONFIG_INVALID", "MIN_UNDERLYING_RR and MIN_OPTION_NET_RR cannot be set below the hard 2.0:1 minimum")
        if self.min_abs_delta < 0 or self.max_abs_delta > 1 or self.min_abs_delta >= self.max_abs_delta:
            raise ScannerError("CONFIG_INVALID", "Delta limits must satisfy 0 <= min_abs_delta < max_abs_delta <= 1")
        if self.max_retries < 0 or self.max_retries > 5:
            raise ScannerError("CONFIG_INVALID", "max_retries must be between 0 and 5")
        if self.setup_state_ttl_minutes < self.setup_max_age_minutes:
            raise ScannerError("CONFIG_INVALID", "setup_state_ttl_minutes must be at least setup_max_age_minutes")
        if self.smtp_port < 1 or self.smtp_port > 65535:
            raise ScannerError("CONFIG_INVALID", "SMTP_PORT must be between 1 and 65535")
        for name, value in {
            "min_oi_direction_confidence": self.min_oi_direction_confidence,
            "min_oi_score_margin": self.min_oi_score_margin,
            "min_mixed_price_confirmation": self.min_mixed_price_confirmation,
        }.items():
            if not math.isfinite(float(value)) or not 0.0 <= float(value) <= 1.0:
                raise ScannerError("CONFIG_INVALID", f"{name} must be between 0 and 1")
        nonnegative = {
            "min_bid_qty": self.min_bid_qty, "min_ask_qty": self.min_ask_qty,
            "min_option_volume": self.min_option_volume, "option_slippage_points": self.option_slippage_points,
            "transaction_cost_rate": self.transaction_cost_rate, "iv_shock_points": self.iv_shock_points,
            "annual_risk_free_rate": self.annual_risk_free_rate, "stop_buffer_atr_fraction": self.stop_buffer_atr_fraction,
            "level_cluster_atr_fraction": self.level_cluster_atr_fraction,
        }
        for name, value in nonnegative.items():
            if not math.isfinite(float(value)) or float(value) < 0:
                raise ScannerError("CONFIG_INVALID", f"{name} must be a finite nonnegative number")

    @classmethod
    def from_env(cls) -> "Config":
        token = os.getenv("UPSTOX_ANALYTICS_TOKEN", "").strip() or os.getenv("UPSTOX_ACCESS_TOKEN", "").strip()
        if not token:
            raise ScannerError("CONFIG_TOKEN_MISSING", "Set UPSTOX_ANALYTICS_TOKEN in GitHub Secrets.")

        def int_env(name: str, default: int) -> int:
            try:
                value = int(os.getenv(name, str(default)))
                if value < 0:
                    raise ValueError
                return value
            except ValueError as exc:
                raise ScannerError("CONFIG_INVALID", f"{name} must be a nonnegative integer") from exc

        def float_env(name: str, default: float) -> float:
            try:
                value = float(os.getenv(name, str(default)))
                if not math.isfinite(value) or value < 0:
                    raise ValueError
                return value
            except ValueError as exc:
                raise ScannerError("CONFIG_INVALID", f"{name} must be a finite nonnegative number") from exc

        expiry_raw = os.getenv("OPTION_EXPIRY", "").strip()
        try:
            expiry = date.fromisoformat(expiry_raw) if expiry_raw else None
        except ValueError as exc:
            raise ScannerError("CONFIG_INVALID", "OPTION_EXPIRY must be YYYY-MM-DD") from exc

        return cls(
            token=token,
            state_file=Path(os.getenv("STATE_FILE", "state/market_state_v102.json")),
            audit_dir=Path(os.getenv("AUDIT_DIR", "audit")),
            instrument_cache=Path(os.getenv("INSTRUMENT_CACHE_FILE", ".cache/upstox_nse.json.gz")),
            explicit_expiry=expiry,
            request_timeout=float_env("REQUEST_TIMEOUT_SECONDS", 12.0),
            max_retries=int_env("API_MAX_RETRIES", 2),
            instrument_cache_hours=int_env("INSTRUMENT_CACHE_HOURS", 12),
            oi_material_threshold_pct=float_env("OI_MATERIAL_THRESHOLD_PCT", 2.0) or 2.0,
            min_underlying_rr=float_env("MIN_UNDERLYING_RR", 2.0) or 2.0,
            min_option_net_rr=float_env("MIN_OPTION_NET_RR", 2.0) or 2.0,
            max_oi_age_seconds=int_env("MAX_OI_AGE_SECONDS", 720),
            expected_oi_interval_seconds=max(30, int_env("EXPECTED_OI_INTERVAL_SECONDS", 180)),
            max_quote_age_seconds=int_env("MAX_QUOTE_AGE_SECONDS", 120),
            max_candle_age_seconds=int_env("MAX_CANDLE_AGE_SECONDS", 150),
            max_spread_pct=float_env("MAX_SPREAD_PCT", 3.0),
            min_bid_qty=float_env("MIN_BID_QTY", 1.0),
            min_ask_qty=float_env("MIN_ASK_QTY", 1.0),
            min_option_volume=float_env("MIN_OPTION_VOLUME", 1.0),
            min_abs_delta=float_env("MIN_ABS_DELTA", 0.30),
            max_abs_delta=float_env("MAX_ABS_DELTA", 0.80),
            max_entry_extension_atr=float_env("MAX_ENTRY_EXTENSION_ATR", 0.80),
            setup_max_age_minutes=int_env("SETUP_MAX_AGE_MINUTES", 3),
            setup_state_ttl_minutes=int_env("SETUP_STATE_TTL_MINUTES", 12),
            iv_shock_points=float_env("IV_SHOCK_POINTS", 1.0),
            expected_hold_minutes=float_env("EXPECTED_HOLD_MINUTES", 15.0),
            annual_risk_free_rate=float_env("ANNUAL_RISK_FREE_RATE", 0.06),
            option_slippage_points=float_env("OPTION_SLIPPAGE_POINTS", 1.0),
            transaction_cost_rate=float_env("TRANSACTION_COST_RATE", 0.0018),
            min_oi_direction_confidence=float_env("MIN_OI_DIRECTION_CONFIDENCE", 0.56),
            min_oi_score_margin=float_env("MIN_OI_SCORE_MARGIN", 0.12),
            min_mixed_price_confirmation=float_env("MIN_MIXED_PRICE_CONFIRMATION", 0.78),
            email_sender=(os.getenv("EMAIL_SENDER", "").strip() or os.getenv("EMAIL_FROM", "").strip()),
            email_receiver=(os.getenv("EMAIL_RECEIVER", "").strip() or os.getenv("EMAIL_TO", "").strip()),
            email_password=os.getenv("EMAIL_PASSWORD", "").strip(),
            email_username=os.getenv("EMAIL_USERNAME", "").strip(),
            smtp_host=os.getenv("SMTP_HOST", "").strip(),
            smtp_port=int_env("SMTP_PORT", 465),
            webhook_url=os.getenv("ALERT_WEBHOOK_URL", "").strip(),
        )


# ---------- Time, JSON and atomic state helpers ----------

def now_ist() -> datetime:
    return datetime.now(IST)


def parse_datetime(value: Any) -> Optional[datetime]:
    if value is None or value == "":
        return None
    if isinstance(value, (int, float)):
        # Milliseconds are the convention in Upstox candle/quote timestamps.
        seconds = float(value) / (1000.0 if abs(float(value)) > 10**11 else 1.0)
        return datetime.fromtimestamp(seconds, tz=UTC).astimezone(IST)
    if not isinstance(value, str):
        return None
    try:
        dt = datetime.fromisoformat(value.replace("Z", "+00:00"))
        if dt.tzinfo is None or dt.utcoffset() is None:
            return None
        return dt.astimezone(IST)
    except ValueError:
        return None


def parse_expiry(value: Any) -> Optional[date]:
    if value is None or value == "":
        return None
    if isinstance(value, (int, float)):
        parsed = parse_datetime(value)
        return parsed.date() if parsed else None
    try:
        return date.fromisoformat(str(value)[:10])
    except ValueError:
        return None


def json_safe(value: Any) -> Any:
    if isinstance(value, datetime):
        return value.astimezone(IST).isoformat()
    if isinstance(value, date):
        return value.isoformat()
    if isinstance(value, Path):
        return str(value)
    if hasattr(value, "__dataclass_fields__"):
        return json_safe(asdict(value))
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple, set)):
        return [json_safe(v) for v in value]
    if isinstance(value, float) and not math.isfinite(value):
        return None
    return value


def _reject_non_finite(value: Any, path: str = "$") -> None:
    """Reject NaN/Infinity before persistence; silently converting them hides bugs."""
    if isinstance(value, float) and not math.isfinite(value):
        raise ValueError(f"Non-finite numeric value at {path}")
    if hasattr(value, "__dataclass_fields__"):
        _reject_non_finite(asdict(value), path)
    elif isinstance(value, Mapping):
        for key, child in value.items():
            _reject_non_finite(child, f"{path}.{key}")
    elif isinstance(value, (list, tuple, set)):
        for index, child in enumerate(value):
            _reject_non_finite(child, f"{path}[{index}]")


def atomic_write_json(path: Path, payload: Mapping[str, Any]) -> None:
    _reject_non_finite(payload)
    path.parent.mkdir(parents=True, exist_ok=True)
    data = json.dumps(json_safe(dict(payload)), separators=(",", ":"), sort_keys=True, allow_nan=False).encode("utf-8")
    fd, temporary = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except Exception:
        try:
            os.unlink(temporary)
        except OSError:
            pass
        raise


def read_state(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {"schema_version": SCHEMA_VERSION, "scanner_version": VERSION}
    try:
        raw = path.read_bytes()
        if len(raw) > 2_000_000:
            raise ScannerError("STATE_TOO_LARGE", f"State file exceeds 2 MB: {path}")
        state = json.loads(raw.decode("utf-8"))
        if not isinstance(state, dict):
            raise ValueError("state root is not an object")
        _reject_non_finite(state)
        if state.get("schema_version") != SCHEMA_VERSION:
            old_schema = str(state.get("schema_version", "unknown"))
            backup = path.with_name(path.name + f".schema-{old_schema}.backup")
            if backup.exists():
                backup = path.with_name(path.name + f".schema-{old_schema}.{datetime.now(UTC).strftime('%Y%m%dT%H%M%SZ')}.backup")
            try:
                shutil.copy2(path, backup)
            except OSError as exc:
                raise ScannerError("STATE_BACKUP_FAILED", f"Cannot preserve incompatible state before reset: {exc}") from exc
            LOG.warning("State schema %r is incompatible with v%s; old state copied to %s; starting clean state.", old_schema, VERSION, backup)
            return {"schema_version": SCHEMA_VERSION, "scanner_version": VERSION, "migration_note": "incompatible_state_not_reused", "migration_backup": str(backup)}
        return state
    except ScannerError:
        raise
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise ScannerError("STATE_READ_FAILED", f"Could not safely read state file: {exc}") from exc


def append_jsonl(path: Path, record: Mapping[str, Any]) -> None:
    _reject_non_finite(record)
    path.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps(json_safe(dict(record)), separators=(",", ":"), sort_keys=True, allow_nan=False) + "\n"
    with path.open("a", encoding="utf-8") as stream:
        stream.write(line)
        stream.flush()
        os.fsync(stream.fileno())


# ---------- HTTP client: bounded retry, no hidden auth behaviour ----------

class UpstoxClient:
    def __init__(self, token: str, timeout: float = 12.0, max_retries: int = 2, opener: Any = None):
        self.token = token
        self.timeout = timeout
        self.max_retries = max_retries
        self.opener = opener or urllib.request.urlopen

    def get_bytes(self, url: str, *, authenticated: bool = False) -> bytes:
        headers = {"Accept": "application/json", "User-Agent": f"NiftyMarketScanner/{VERSION}"}
        if authenticated:
            headers["Authorization"] = f"Bearer {self.token}"
        last_error: Optional[Exception] = None
        for attempt in range(self.max_retries + 1):
            request = urllib.request.Request(url, headers=headers, method="GET")
            try:
                with self.opener(request, timeout=self.timeout) as response:
                    status = getattr(response, "status", 200)
                    body = response.read()
                    if status >= 400:
                        raise ScannerError(f"API_HTTP_{status}", f"HTTP {status} from {urllib.parse.urlparse(url).path}")
                    return body
            except urllib.error.HTTPError as exc:
                body = ""
                try:
                    body = exc.read(600).decode("utf-8", errors="replace")
                except Exception:
                    pass
                if exc.code == 429 or 500 <= exc.code < 600:
                    last_error = ScannerError("API_RATE_LIMIT" if exc.code == 429 else "API_SERVER_ERROR", f"HTTP {exc.code} from {urllib.parse.urlparse(url).path}: {body[:240]}", retryable=True)
                    if attempt < self.max_retries:
                        retry_after = exc.headers.get("Retry-After", "") if exc.headers else ""
                        try:
                            delay = min(max(float(retry_after), 0.25), 3.0)
                        except (TypeError, ValueError):
                            delay = min(0.5 * (2 ** attempt) + random.random() * 0.2, 3.0)
                        time.sleep(delay)
                        continue
                    break
                if exc.code in (401, 403):
                    code = "API_AUTH_FAILED" if exc.code == 401 else "API_PERMISSION_DENIED"
                    raise ScannerError(code, f"HTTP {exc.code} from {urllib.parse.urlparse(url).path}: {body[:300]}") from exc
                raise ScannerError("API_HTTP_ERROR", f"HTTP {exc.code} from {urllib.parse.urlparse(url).path}: {body[:300]}") from exc
            except (urllib.error.URLError, TimeoutError, OSError) as exc:
                last_error = ScannerError("API_NETWORK_ERROR", f"Network error calling {urllib.parse.urlparse(url).path}: {exc}", retryable=True)
                if attempt < self.max_retries:
                    time.sleep(min(0.5 * (2 ** attempt) + random.random() * 0.2, 3.0))
                    continue
                break
        raise last_error or ScannerError("API_REQUEST_FAILED", "API request failed")

    def get_json(self, url: str) -> dict[str, Any]:
        raw = self.get_bytes(url, authenticated=True)
        try:
            data = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ScannerError("API_INVALID_JSON", f"Invalid JSON from {urllib.parse.urlparse(url).path}") from exc
        if not isinstance(data, dict):
            raise ScannerError("API_INVALID_RESPONSE", f"Expected JSON object from {urllib.parse.urlparse(url).path}")
        if data.get("status") == "error":
            errors = data.get("errors") or data.get("error") or "provider returned status=error"
            raise ScannerError("API_PROVIDER_ERROR", f"API provider error: {str(errors)[:300]}")
        return data


# ---------- Official instrument master ----------

class InstrumentMaster:
    def __init__(self, client: UpstoxClient, cache_path: Path, cache_hours: int = 12):
        self.client = client
        self.cache_path = cache_path
        self.cache_seconds = max(60, cache_hours * 3600)
        self.rows: list[dict[str, Any]] = []

    def load(self, now: datetime) -> list[dict[str, Any]]:
        cached_content: Optional[bytes] = None
        cache_is_fresh = False
        try:
            if self.cache_path.exists():
                cached_content = self.cache_path.read_bytes()
                cache_is_fresh = now.timestamp() - self.cache_path.stat().st_mtime <= self.cache_seconds
        except OSError:
            cached_content = None
            cache_is_fresh = False
        content: Optional[bytes] = cached_content if cache_is_fresh else None
        if content is None:
            try:
                downloaded = self.client.get_bytes(INSTRUMENTS_URL, authenticated=False)
            except ScannerError:
                # Use a stale cache only as a metadata fallback; expiry resolution
                # still validates the requested date and refuses a silent monthly roll.
                if cached_content is None:
                    raise
                LOG.warning("Official instrument master download failed; using stale cached metadata subject to expiry validation")
                content = cached_content
            else:
                try:
                    decompressed = gzip.decompress(downloaded)
                except (OSError, EOFError) as exc:
                    raise ScannerError("INSTRUMENT_MASTER_INVALID", "Official instrument master was not a valid gzip file") from exc
                parsed = self._decode_rows(decompressed)
                if len(parsed) < 100:
                    raise ScannerError("INSTRUMENT_MASTER_INVALID", "Official instrument master unexpectedly contains fewer than 100 rows")
                self.cache_path.parent.mkdir(parents=True, exist_ok=True)
                tmp_fd, tmp_name = tempfile.mkstemp(prefix=self.cache_path.name + ".", dir=str(self.cache_path.parent))
                try:
                    with os.fdopen(tmp_fd, "wb") as out:
                        out.write(downloaded)
                        out.flush()
                        os.fsync(out.fileno())
                    os.replace(tmp_name, self.cache_path)
                except Exception:
                    try:
                        os.unlink(tmp_name)
                    except OSError:
                        pass
                    raise
                self.rows = parsed
                return parsed
        if content is not None:
            try:
                decompressed = gzip.decompress(content)
            except (OSError, EOFError):
                raise ScannerError("INSTRUMENT_MASTER_INVALID", "Cached instrument master is corrupt")
            self.rows = self._decode_rows(decompressed)
            if len(self.rows) < 100:
                raise ScannerError("INSTRUMENT_MASTER_INVALID", "Cached instrument master is incomplete")
            return self.rows
        raise ScannerError("INSTRUMENT_MASTER_UNAVAILABLE", "No usable official instrument master")

    @staticmethod
    def _decode_rows(raw: bytes) -> list[dict[str, Any]]:
        try:
            payload = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ScannerError("INSTRUMENT_MASTER_INVALID", "Instrument master JSON is malformed") from exc
        rows = payload if isinstance(payload, list) else payload.get("data") if isinstance(payload, dict) else None
        if not isinstance(rows, list):
            raise ScannerError("INSTRUMENT_MASTER_INVALID", "Instrument master does not contain a list of instruments")
        return [item for item in rows if isinstance(item, dict)]

    def resolve_index(self) -> dict[str, Any]:
        candidates = []
        for row in self.rows:
            if str(row.get("segment", "")).upper() != "NSE_INDEX" or str(row.get("instrument_type", "")).upper() != "INDEX":
                continue
            names = " ".join(str(row.get(k, "")) for k in ("name", "trading_symbol", "short_name")).casefold()
            compact = " ".join(names.split())
            if compact.strip() in {"nifty 50", "nifty fifty"} or "nifty 50" in compact:
                if row.get("instrument_key"):
                    candidates.append(row)
        # Multiple rows can exist; prefer exact trading symbol, then exact name. Never guess a literal key.
        if not candidates:
            raise ScannerError("NIFTY_INSTRUMENT_NOT_FOUND", "NIFTY 50 index was not found in the official NSE instrument master")
        candidates.sort(key=lambda r: (str(r.get("trading_symbol", "")).casefold() != "nifty 50", str(r.get("name", "")).casefold() != "nifty 50"))
        if len({str(x.get("instrument_key")) for x in candidates}) > 1 and candidates[0].get("trading_symbol", "").casefold() != "nifty 50":
            raise ScannerError("NIFTY_INSTRUMENT_AMBIGUOUS", "Multiple NIFTY 50 index instruments found; cannot safely choose")
        return candidates[0]

    def _options_for_index(self, index_key: str, asof: date) -> list[dict[str, Any]]:
        result = []
        for row in self.rows:
            if str(row.get("segment", "")).upper() != "NSE_FO":
                continue
            if str(row.get("instrument_type", "")).upper() not in {"CE", "PE"}:
                continue
            if str(row.get("underlying_key", "")) != index_key:
                continue
            expiry = parse_expiry(row.get("expiry"))
            if expiry is None or expiry < asof:
                continue
            if not isinstance(row.get("strike_price"), (int, float)) or not row.get("instrument_key"):
                continue
            item = dict(row)
            item["_expiry_date"] = expiry
            item["_weekly"] = row.get("weekly") is True or str(row.get("weekly", "")).casefold() == "true"
            result.append(item)
        return result

    def resolve_expiry(self, index_key: str, asof: date, explicit_expiry: Optional[date]) -> date:
        contracts = self._options_for_index(index_key, asof)
        expiries = sorted({r["_expiry_date"] for r in contracts})
        if explicit_expiry:
            if explicit_expiry < asof or explicit_expiry not in expiries:
                raise ScannerError("EXPIRY_NOT_FOUND", f"Configured expiry {explicit_expiry} is not an eligible NIFTY option expiry in instrument master")
            return explicit_expiry
        weekly = sorted({r["_expiry_date"] for r in contracts if r["_weekly"]})
        if not weekly:
            raise ScannerError("WEEKLY_EXPIRY_NOT_FOUND", "No eligible weekly NIFTY option expiry is identified in current instrument metadata; refusing to silently choose monthly")
        return weekly[0]

    def resolve_future(self, index_key: str, asof: date) -> Optional[dict[str, Any]]:
        futures = []
        for row in self.rows:
            if str(row.get("segment", "")).upper() != "NSE_FO" or str(row.get("instrument_type", "")).upper() != "FUT":
                continue
            if str(row.get("underlying_key", "")) != index_key:
                continue
            underlying = str(row.get("underlying_symbol", row.get("name", ""))).casefold()
            if "nifty" not in underlying:
                continue
            exp = parse_expiry(row.get("expiry"))
            if exp is None or exp < asof:
                continue
            if row.get("instrument_key"):
                futures.append((exp, row))
        if not futures:
            return None
        futures.sort(key=lambda item: item[0])
        return dict(futures[0][1])

    def option_instruments(self, index_key: str, expiry: date) -> list[dict[str, Any]]:
        options = self._options_for_index(index_key, expiry)
        chosen = [r for r in options if r["_expiry_date"] == expiry]
        if not chosen:
            raise ScannerError("OPTION_CONTRACTS_NOT_FOUND", f"No current NIFTY contracts for expiry {expiry}")
        return chosen


# ---------- Normalized domain models ----------

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
        vals = (self.open, self.high, self.low, self.close, self.volume, self.oi)
        if not all(math.isfinite(float(v)) for v in vals):
            raise ValueError("Candle values must be finite")
        if self.low > min(self.open, self.close) or self.high < max(self.open, self.close) or self.low > self.high:
            raise ValueError("Invalid OHLC ordering")
        if self.volume < 0 or self.oi < 0:
            raise ValueError("Negative volume/OI is invalid")

    @property
    def close_time(self) -> datetime:
        return self.start + timedelta(minutes=1)

    def to_dict(self) -> dict[str, Any]:
        return {"timestamp": self.start.isoformat(), "open": self.open, "high": self.high, "low": self.low, "close": self.close, "volume": self.volume, "oi": self.oi}


@dataclass(frozen=True)
class OptionRecord:
    instrument_key: str
    expiry: date
    strike: float
    side: str
    ltp: float
    oi: float
    volume: float
    previous_session_oi: Optional[float]
    chain_bid: float
    chain_ask: float
    chain_bid_qty: float
    chain_ask_qty: float
    delta: Optional[float]
    gamma: Optional[float]
    theta: Optional[float]
    vega: Optional[float]
    iv: Optional[float]

    def to_dict(self) -> dict[str, Any]:
        return json_safe(asdict(self))


@dataclass(frozen=True)
class OptionQuote:
    instrument_key: str
    timestamp: Optional[datetime]
    ltp: float
    bid: float
    ask: float
    bid_qty: float
    ask_qty: float
    volume: float
    oi: float
    strike: float
    side: str
    expiry: date
    delta: Optional[float]
    gamma: Optional[float]
    theta: Optional[float]
    vega: Optional[float]
    iv: Optional[float]

    @property
    def mid(self) -> float:
        return (self.bid + self.ask) / 2 if self.bid > 0 and self.ask >= self.bid else 0.0

    @property
    def spread_pct(self) -> float:
        return (self.ask - self.bid) / self.mid * 100 if self.mid > 0 else math.inf


@dataclass(frozen=True)
class PriceLevel:
    price: float
    side: str  # SUPPORT or RESISTANCE
    source: str
    strength: float


@dataclass(frozen=True)
class Setup:
    kind: str
    direction: str  # BULLISH or BEARISH
    trigger: float
    invalidation: float
    confirmed_at: datetime
    source_level: Optional[float]
    source: str
    price_confidence: float


# ---------- Candle/chain/quote API normalization ----------

def instrument_path_key(key: str) -> str:
    return urllib.parse.quote(key, safe="")


def fetch_candles(client: UpstoxClient, instrument_key: str, now: datetime, *, minutes: int = 1) -> list[Candle]:
    url = f"{API_BASE}/v3/historical-candle/intraday/{instrument_path_key(instrument_key)}/minutes/{minutes}"
    payload = client.get_json(url)
    data = payload.get("data") or {}
    raw_candles = data.get("candles") if isinstance(data, dict) else None
    if not isinstance(raw_candles, list):
        raise ScannerError("CANDLE_DATA_MISSING", f"No candle list returned for {instrument_key}")
    result: list[Candle] = []
    seen: set[datetime] = set()
    for row in raw_candles:
        if not isinstance(row, (list, tuple)) or len(row) < 5:
            continue
        ts = parse_datetime(row[0])
        if ts is None:
            continue
        if ts.astimezone(IST).date() != now.astimezone(IST).date():
            continue
        try:
            candle = Candle(ts, float(row[1]), float(row[2]), float(row[3]), float(row[4]), float(row[5] or 0) if len(row) > 5 else 0.0, float(row[6] or 0) if len(row) > 6 else 0.0)
        except (TypeError, ValueError, OverflowError):
            continue
        # A candle stamped at 12:57 represents 12:57–12:58; never use it before it closes.
        if candle.close_time > now.astimezone(IST):
            continue
        if candle.start in seen:
            continue
        seen.add(candle.start)
        result.append(candle)
    result.sort(key=lambda c: c.start)
    if not result:
        raise ScannerError("CANDLE_DATA_MISSING", f"No completed intraday candles returned for {instrument_key}")
    return result


def fetch_daily_candles(client: UpstoxClient, instrument_key: str, now: datetime) -> list[Candle]:
    to_date = now.astimezone(IST).date() - timedelta(days=1)
    from_date = to_date - timedelta(days=20)
    path = f"{API_BASE}/v3/historical-candle/{instrument_path_key(instrument_key)}/days/1/{to_date.isoformat()}/{from_date.isoformat()}"
    try:
        payload = client.get_json(path)
    except ScannerError as exc:
        LOG.warning("Prior-session daily candles unavailable (%s); prior-session levels will be omitted", exc.code)
        return []
    raw = (payload.get("data") or {}).get("candles")
    if not isinstance(raw, list):
        return []
    candles: list[Candle] = []
    for row in raw:
        if not isinstance(row, (list, tuple)) or len(row) < 5:
            continue
        ts = parse_datetime(row[0])
        if not ts or ts.date() >= now.astimezone(IST).date():
            continue
        try:
            candles.append(Candle(ts, float(row[1]), float(row[2]), float(row[3]), float(row[4]), float(row[5] or 0) if len(row) > 5 else 0.0, float(row[6] or 0) if len(row) > 6 else 0.0))
        except (TypeError, ValueError):
            continue
    candles.sort(key=lambda c: c.start)
    return candles


def parse_option_chain(payload: Mapping[str, Any], expiry: date, fetched_at: datetime) -> tuple[float, list[OptionRecord]]:
    raw = payload.get("data")
    if not isinstance(raw, list) or not raw:
        raise ScannerError("OPTION_CHAIN_EMPTY", "Upstox returned an empty option chain")
    spot_candidates = []
    records: list[OptionRecord] = []
    for row in raw:
        if not isinstance(row, dict):
            continue
        row_exp = parse_expiry(row.get("expiry"))
        if row_exp is not None and row_exp != expiry:
            continue
        spot = row.get("underlying_spot_price")
        if isinstance(spot, (int, float)) and math.isfinite(float(spot)) and float(spot) > 0:
            spot_candidates.append(float(spot))
        strike_raw = row.get("strike_price")
        try:
            strike = float(strike_raw)
        except (TypeError, ValueError):
            continue
        if not math.isfinite(strike) or strike <= 0:
            continue
        for side, node_name in (("CE", "call_options"), ("PE", "put_options")):
            node = row.get(node_name)
            if not isinstance(node, dict) or not node.get("instrument_key"):
                continue
            md = node.get("market_data") or {}
            gr = node.get("option_greeks") or {}
            try:
                ltp = float(md.get("ltp") or 0)
                oi = float(md.get("oi") or 0)
                volume = float(md.get("volume") or 0)
                bid = float(md.get("bid_price") or 0)
                ask = float(md.get("ask_price") or 0)
                bid_qty = float(md.get("bid_qty") or 0)
                ask_qty = float(md.get("ask_qty") or 0)
                prev_oi_raw = md.get("prev_oi")
                prev_oi = float(prev_oi_raw) if prev_oi_raw is not None else None
                if prev_oi is not None and (not math.isfinite(prev_oi) or prev_oi < 0):
                    prev_oi = None
            except (TypeError, ValueError):
                continue
            if any(not math.isfinite(x) for x in (ltp, oi, volume, bid, ask, bid_qty, ask_qty)) or min(ltp, oi, volume, bid, ask, bid_qty, ask_qty) < 0:
                continue
            def greek(name: str) -> Optional[float]:
                try:
                    val = gr.get(name)
                    value = float(val) if val is not None else None
                    return value if value is not None and math.isfinite(value) else None
                except (TypeError, ValueError):
                    return None
            records.append(OptionRecord(str(node["instrument_key"]), expiry, strike, side, ltp, oi, volume, prev_oi, bid, ask, bid_qty, ask_qty, greek("delta"), greek("gamma"), greek("theta"), greek("vega"), greek("iv")))
    if not spot_candidates or not records:
        raise ScannerError("OPTION_CHAIN_INVALID", "Option chain lacks a valid spot price or option rows")
    spot = median(spot_candidates)
    records = [r for r in records if r.expiry == expiry]
    return spot, records


def parse_full_quotes(payload: Mapping[str, Any], requested: Sequence[str]) -> dict[str, dict[str, Any]]:
    data = payload.get("data")
    if not isinstance(data, dict):
        raise ScannerError("MARKET_QUOTES_INVALID", "Full Market Quotes response has no data object")
    normalize = lambda s: str(s).replace(":", "|").strip().casefold()
    want = {normalize(key): key for key in requested}
    result: dict[str, dict[str, Any]] = {}
    for response_key, quote in data.items():
        if not isinstance(quote, dict):
            continue
        instrument_key = quote.get("instrument_token") or quote.get("instrument_key") or response_key
        normalized = normalize(instrument_key)
        target = want.get(normalized)
        if not target:
            # Some versions return the resolved trading symbol as dictionary key; try normalized response key too.
            target = want.get(normalize(response_key))
        if target:
            result[target] = quote
    return result


def get_full_quotes(client: UpstoxClient, instrument_keys: Sequence[str]) -> dict[str, dict[str, Any]]:
    keys = sorted(set(key for key in instrument_keys if key))
    if not keys:
        raise ScannerError("MARKET_QUOTES_INVALID", "No instrument keys supplied to quote endpoint")
    if len(keys) > 500:
        raise ScannerError("MARKET_QUOTES_LIMIT", "Full Market Quotes supports at most 500 instruments per request")
    query = urllib.parse.urlencode({"instrument_key": ",".join(keys)})
    payload = client.get_json(f"{API_BASE}/v3/market-quote/quotes?{query}")
    return parse_full_quotes(payload, keys)


# ---------- OI computation: raw deltas are never clipped ----------

def _snapshot_rows(records: Sequence[OptionRecord], spot: float, width_steps: int = 16) -> list[dict[str, Any]]:
    strikes = sorted({r.strike for r in records})
    if not strikes:
        return []
    atm = min(strikes, key=lambda strike: abs(strike - spot))
    i = strikes.index(atm)
    selected_strikes = set(strikes[max(0, i - width_steps): min(len(strikes), i + width_steps + 1)])
    return [r.to_dict() for r in records if r.strike in selected_strikes]


def _lookup_records(records: Sequence[Mapping[str, Any]]) -> dict[str, Mapping[str, Any]]:
    return {str(r.get("instrument_key")): r for r in records if r.get("instrument_key")}


def _weighted_direction(oi_delta: float, oi_pct: Optional[float], premium_pct: Optional[float], side: str, threshold: float) -> tuple[float, str]:
    """Return signed directional contribution and qualitative positioning heuristic.

    Positive is bullish, negative is bearish. Interpretation is heuristic, not
    proof of buyer/seller intent. Actual delta and percent remain untouched.
    """
    if oi_pct is None or premium_pct is None or abs(oi_delta) < 0.5 or abs(premium_pct) < 0.05:
        return 0.0, "INSUFFICIENT_CHANGE"
    oi_up = oi_delta > 0
    premium_up = premium_pct > 0
    magnitude = min(abs(oi_pct) / max(threshold, 1e-9), 1.5) / 1.5
    magnitude *= min(abs(premium_pct) / 1.5, 1.0)
    # New-position signatures are weighted somewhat more than unwinds; signed
    # OI still matters in the contribution magnitude and label.
    strength = 1.0 if oi_up else 0.65
    if side == "CE":
        bullish = premium_up
        label = "CALL_LONG_BUILDUP" if oi_up and premium_up else "CALL_WRITING_LIKELY" if oi_up else "CALL_SHORT_COVERING_LIKELY" if premium_up else "CALL_LONG_UNWINDING_LIKELY"
    else:
        bullish = not premium_up
        label = "PUT_LONG_BUILDUP" if oi_up and premium_up else "PUT_WRITING_LIKELY" if oi_up else "PUT_SHORT_COVERING_LIKELY" if premium_up else "PUT_LONG_UNWINDING_LIKELY"
    # OI decrease + premium direction is weaker evidence than fresh OI buildup.
    return (1.0 if bullish else -1.0) * magnitude * strength, label



def _chain_premium_proxy(ltp: Any, bid: Any, ask: Any) -> tuple[Optional[float], str, float]:
    """Prefer a valid two-sided chain midpoint; use LTP only as lower-confidence fallback."""
    try:
        last = float(ltp)
        bid_value = float(bid)
        ask_value = float(ask)
    except (TypeError, ValueError, OverflowError):
        return None, "UNAVAILABLE", 0.0
    if not all(math.isfinite(x) for x in (last, bid_value, ask_value)):
        return None, "UNAVAILABLE", 0.0
    if bid_value > 0 and ask_value >= bid_value and ask_value > 0:
        mid = (bid_value + ask_value) / 2.0
        spread_pct = (ask_value - bid_value) / mid * 100.0 if mid > 0 else math.inf
        # Very wide books are poor premium-change proxies; mark fallback explicitly.
        if mid > 0 and spread_pct <= 15.0:
            return mid, "CHAIN_MID", 1.0
    if last > 0:
        return last, "LTP_FALLBACK_NO_EVENT_TIMESTAMP", 0.60
    return None, "UNAVAILABLE", 0.0

def calculate_oi_evidence(
    current_records: Sequence[OptionRecord],
    previous_snapshot: Optional[Mapping[str, Any]],
    session_baseline: Optional[Mapping[str, Any]],
    spot: float,
    fetched_at: datetime,
    config: Config,
) -> dict[str, Any]:
    """Compute exact snapshot deltas and a breadth/activity-aware OI hypothesis.

    The raw per-contract percentage is never clipped. Only the score contribution
    is capped. The direction is a positioning heuristic based on OI change,
    premium change, and option side; it is not proof of participant intent.
    """
    current_session = fetched_at.astimezone(IST).date().isoformat()
    current_expiry = current_records[0].expiry.isoformat() if current_records else None
    previous_rows = _lookup_records(previous_snapshot.get("rows", [])) if previous_snapshot else {}
    baseline_rows = _lookup_records(session_baseline.get("rows", [])) if session_baseline else {}
    previous_time = parse_datetime(previous_snapshot.get("fetched_at")) if previous_snapshot else None
    previous_same = bool(
        current_records and previous_snapshot and previous_time and previous_time < fetched_at
        and previous_snapshot.get("session_date") == current_session
        and previous_snapshot.get("expiry") == current_expiry
    )
    baseline_same = bool(
        current_records and session_baseline
        and session_baseline.get("session_date") == current_session
        and session_baseline.get("expiry") == current_expiry
    )
    if not previous_same:
        previous_rows = {}
    if not baseline_same:
        baseline_rows = {}

    strikes = sorted({r.strike for r in current_records})
    step_values = [round(b - a, 6) for a, b in zip(strikes, strikes[1:]) if b > a]
    step = median(step_values) if step_values else 50.0
    current_near = [r for r in current_records if abs(r.strike - spot) <= step * 15]
    if not current_near:
        current_near = list(current_records)

    per_contract: list[dict[str, Any]] = []
    weighted_sum = 0.0
    total_direction_weight = 0.0
    activity_oi_pct: list[tuple[float, float]] = []
    activity_premium_pct: list[tuple[float, float]] = []
    contributing_contract_count = 0
    paired_contract_count = 0
    aggregate_delta_ce = aggregate_prev_ce = 0.0
    aggregate_delta_pe = aggregate_prev_pe = 0.0
    session_delta_call = session_delta_put = 0.0
    session_baseline_count = 0
    pcr_rows_call = pcr_rows_put = 0.0
    call_oi_by_strike: dict[float, float] = defaultdict(float)
    put_oi_by_strike: dict[float, float] = defaultdict(float)
    call_delta_by_strike: dict[float, float] = defaultdict(float)
    put_delta_by_strike: dict[float, float] = defaultdict(float)

    for rec in current_near:
        prev = previous_rows.get(rec.instrument_key)
        base = baseline_rows.get(rec.instrument_key)
        delta_oi = delta_pct = delta_volume = premium_pct = None
        premium_change_source = "UNAVAILABLE"
        premium_source_quality = 0.0
        prev_oi_value: Optional[float] = None
        if (prev and previous_same and prev.get("expiry") == rec.expiry.isoformat()
                and prev.get("side") == rec.side and float(prev.get("strike", -1)) == rec.strike):
            try:
                prev_oi_value = float(prev.get("oi", 0) or 0)
                prev_volume = float(prev.get("volume", 0) or 0)
            except (TypeError, ValueError):
                prev_oi_value = None
            if prev_oi_value is not None and math.isfinite(prev_oi_value) and prev_oi_value >= 0:
                delta_oi = rec.oi - prev_oi_value
                delta_pct = 100.0 * delta_oi / prev_oi_value if prev_oi_value > 0 else None
                current_premium, current_source, current_quality = _chain_premium_proxy(rec.ltp, rec.chain_bid, rec.chain_ask)
                previous_premium, previous_source, previous_quality = _chain_premium_proxy(prev.get("ltp", 0), prev.get("chain_bid", 0), prev.get("chain_ask", 0))
                if current_premium is not None and previous_premium is not None and previous_premium > 0 and current_source == previous_source:
                    premium_pct = 100.0 * (current_premium - previous_premium) / previous_premium
                    premium_change_source = current_source
                    premium_source_quality = min(current_quality, previous_quality)
                elif current_source != previous_source:
                    premium_change_source = "SOURCE_MISMATCH"
                if math.isfinite(prev_volume) and prev_volume >= 0:
                    # Cumulative volume resets are missing data, not negative turnover.
                    delta_volume = rec.volume - prev_volume if rec.volume >= prev_volume else None
                paired_contract_count += 1
                if rec.side == "CE":
                    aggregate_delta_ce += delta_oi
                    aggregate_prev_ce += prev_oi_value
                    call_delta_by_strike[rec.strike] += delta_oi
                else:
                    aggregate_delta_pe += delta_oi
                    aggregate_prev_pe += prev_oi_value
                    put_delta_by_strike[rec.strike] += delta_oi

        previous_session_delta = None
        previous_session_delta_pct = None
        if rec.previous_session_oi is not None:
            try:
                prev_session_oi = float(rec.previous_session_oi)
                if math.isfinite(prev_session_oi) and prev_session_oi >= 0:
                    previous_session_delta = rec.oi - prev_session_oi
                    previous_session_delta_pct = 100.0 * previous_session_delta / prev_session_oi if prev_session_oi > 0 else None
            except (TypeError, ValueError, OverflowError):
                pass

        session_delta = None
        if (base and baseline_same and base.get("expiry") == rec.expiry.isoformat()
                and base.get("side") == rec.side and float(base.get("strike", -1)) == rec.strike):
            try:
                baseline_oi = float(base.get("oi", 0) or 0)
                if math.isfinite(baseline_oi) and baseline_oi >= 0:
                    session_delta = rec.oi - baseline_oi
                    session_baseline_count += 1
                    if rec.side == "CE":
                        session_delta_call += session_delta
                    else:
                        session_delta_put += session_delta
            except (TypeError, ValueError):
                session_delta = None

        contribution = 0.0
        flow_label = "FIRST_SNAPSHOT_OR_NO_PREVIOUS_BASELINE"
        if delta_oi is not None and delta_pct is not None and premium_pct is not None:
            contribution, flow_label = _weighted_direction(
                delta_oi, delta_pct, premium_pct, rec.side, config.oi_material_threshold_pct
            )
            distance_steps = abs(rec.strike - spot) / max(step, 1e-6)
            proximity_weight = 1.0 / (1.0 + 0.22 * distance_steps)
            volume_weight = 1.05 if delta_volume is not None and delta_volume > 0 else 0.85
            effective = contribution * proximity_weight * volume_weight * premium_source_quality
            weighted_sum += effective
            total_direction_weight += abs(effective)
            if abs(effective) > 1e-9:
                contributing_contract_count += 1
                activity_oi_pct.append((abs(delta_pct), proximity_weight))
                activity_premium_pct.append((abs(premium_pct), proximity_weight * premium_source_quality))

        per_contract.append({
            "instrument_key": rec.instrument_key, "expiry": rec.expiry.isoformat(), "strike": rec.strike,
            "side": rec.side, "oi": rec.oi, "delta_oi_snapshot": delta_oi,
            "delta_oi_pct_snapshot": delta_pct, "delta_oi_session": session_delta,
            "delta_oi_vs_prev_session": previous_session_delta,
            "delta_oi_vs_prev_session_pct": previous_session_delta_pct,
            "delta_volume_snapshot": delta_volume, "premium_change_pct_snapshot": premium_pct,
            "premium_change_source": premium_change_source,
            "material_oi_change": delta_pct is not None and abs(delta_pct) >= config.oi_material_threshold_pct,
            "flow_interpretation": flow_label, "directional_contribution": contribution,
            "distance_from_spot_points": rec.strike - spot,
        })
        if abs(rec.strike - spot) <= step * 10:
            if rec.side == "CE":
                pcr_rows_call += rec.oi
            else:
                pcr_rows_put += rec.oi
        if rec.side == "CE":
            call_oi_by_strike[rec.strike] += rec.oi
        else:
            put_oi_by_strike[rec.strike] += rec.oi

    directional_balance = weighted_sum / total_direction_weight if total_direction_weight > 1e-9 else 0.0
    def weighted_average(items: Sequence[tuple[float, float]]) -> Optional[float]:
        denominator = sum(weight for _, weight in items)
        return sum(value * weight for value, weight in items) / denominator if denominator > 0 else None

    average_abs_oi_pct = weighted_average(activity_oi_pct)
    average_abs_premium_pct = weighted_average(activity_premium_pct)
    oi_activity_factor = min(1.0, (average_abs_oi_pct or 0.0) / max(config.oi_material_threshold_pct, 1e-9))
    # Premium movement reference is an engineering calibration (1.5%); it does
    # not replace or alter the single configurable 2.0% OI materiality threshold.
    premium_activity_factor = min(1.0, (average_abs_premium_pct or 0.0) / 1.5)
    breadth_factor = min(1.0, contributing_contract_count / 4.0)
    interval_seconds = (fetched_at - previous_time).total_seconds() if previous_same and previous_time else None
    expected_interval = max(30, config.expected_oi_interval_seconds)
    interval_factor = min(1.0, expected_interval / max(interval_seconds, float(expected_interval))) if interval_seconds and interval_seconds > 0 else 0.0
    activity_factor = math.sqrt(max(0.0, oi_activity_factor * premium_activity_factor)) * breadth_factor * interval_factor
    confidence = abs(directional_balance) * activity_factor
    score = directional_balance * activity_factor
    bull_score = max(0.0, score)
    bear_score = max(0.0, -score)
    margin = abs(directional_balance)
    if not previous_same:
        label = "MISSING"
    elif (contributing_contract_count < 3 or confidence < config.min_oi_direction_confidence
          or margin < config.min_oi_score_margin):
        label = "MIXED"
    else:
        label = "BULLISH" if directional_balance > 0 else "BEARISH"

    def aggregate_pct(delta: float, baseline_oi: float) -> Optional[float]:
        return 100.0 * delta / baseline_oi if baseline_oi > 0 else None

    def walls(source: Mapping[float, float], side: str) -> list[dict[str, Any]]:
        ordered = sorted(source.items(), key=lambda pair: pair[1], reverse=True)
        out: list[dict[str, Any]] = []
        max_oi = ordered[0][1] if ordered else 0.0
        for strike, oi_value in ordered[:3]:
            if oi_value <= 0 or max_oi <= 0:
                continue
            out.append({"strike": strike, "oi": oi_value, "relative_strength": oi_value / max_oi, "side": side})
        return out

    def positional_zones(source: Mapping[float, float], deltas: Mapping[float, float], side: str, position: str, metric: str) -> list[dict[str, Any]]:
        if position == "ABOVE":
            candidates = [(strike, value) for strike, value in source.items() if strike > spot]
        else:
            candidates = [(strike, value) for strike, value in source.items() if strike < spot]
        if metric == "FASTEST_CHANGE":
            candidates.sort(key=lambda pair: abs(deltas.get(pair[0], 0.0)), reverse=True)
        else:
            candidates.sort(key=lambda pair: pair[1], reverse=True)
        max_metric = max((abs(deltas.get(k, 0.0)) if metric == "FASTEST_CHANGE" else v for k, v in candidates), default=0.0)
        result: list[dict[str, Any]] = []
        for strike, oi_value in candidates[:3]:
            delta_value = deltas.get(strike)
            measure = abs(delta_value or 0.0) if metric == "FASTEST_CHANGE" else oi_value
            if measure <= 0 or max_metric <= 0:
                continue
            result.append({"strike": strike, "oi": oi_value, "delta_oi_snapshot": delta_value,
                           "relative_strength": measure / max_metric, "option_side": side,
                           "position_vs_spot": position, "zone_metric": metric, "distance_points": strike - spot})
        return result

    oi_zones = {
        "highest_call_oi_above_spot": positional_zones(call_oi_by_strike, call_delta_by_strike, "CE", "ABOVE", "HIGHEST_OI"),
        "highest_call_oi_below_spot": positional_zones(call_oi_by_strike, call_delta_by_strike, "CE", "BELOW", "HIGHEST_OI"),
        "highest_put_oi_above_spot": positional_zones(put_oi_by_strike, put_delta_by_strike, "PE", "ABOVE", "HIGHEST_OI"),
        "highest_put_oi_below_spot": positional_zones(put_oi_by_strike, put_delta_by_strike, "PE", "BELOW", "HIGHEST_OI"),
        "fastest_call_oi_change_above_spot": positional_zones(call_oi_by_strike, call_delta_by_strike, "CE", "ABOVE", "FASTEST_CHANGE"),
        "fastest_call_oi_change_below_spot": positional_zones(call_oi_by_strike, call_delta_by_strike, "CE", "BELOW", "FASTEST_CHANGE"),
        "fastest_put_oi_change_above_spot": positional_zones(put_oi_by_strike, put_delta_by_strike, "PE", "ABOVE", "FASTEST_CHANGE"),
        "fastest_put_oi_change_below_spot": positional_zones(put_oi_by_strike, put_delta_by_strike, "PE", "BELOW", "FASTEST_CHANGE"),
    }

    return {
        "label": label, "score": score, "directional_balance": directional_balance,
        "bull_score": bull_score, "bear_score": bear_score, "confidence": confidence,
        "score_margin": margin, "snapshot_time": fetched_at.isoformat(),
        "snapshot_interval_seconds": interval_seconds,
        "snapshot_status": "FRESH_FETCHED_SOURCE_EVENT_TIME_NOT_PROVIDED_BY_CHAIN_RESPONSE",
        "compared_to_previous_successful_snapshot": previous_same,
        "contracts_compared": paired_contract_count,
        "contributing_contract_count": contributing_contract_count,
        "material_contract_count": sum(1 for r in per_contract if r["material_oi_change"]),
        "average_abs_delta_oi_pct": average_abs_oi_pct,
        "average_abs_premium_change_pct": average_abs_premium_pct,
        "premium_mid_comparison_count": sum(1 for r in per_contract if r["premium_change_source"] == "CHAIN_MID"),
        "premium_ltp_fallback_count": sum(1 for r in per_contract if r["premium_change_source"] == "LTP_FALLBACK_NO_EVENT_TIMESTAMP"),
        "premium_source_mismatch_count": sum(1 for r in per_contract if r["premium_change_source"] == "SOURCE_MISMATCH"),
        "oi_activity_factor": oi_activity_factor,
        "premium_activity_factor": premium_activity_factor,
        "breadth_factor": breadth_factor,
        "interval_factor": interval_factor,
        "aggregate_delta_call_oi_snapshot": aggregate_delta_ce if previous_same else None,
        "aggregate_delta_put_oi_snapshot": aggregate_delta_pe if previous_same else None,
        "aggregate_delta_call_oi_pct_snapshot": aggregate_pct(aggregate_delta_ce, aggregate_prev_ce) if previous_same else None,
        "aggregate_delta_put_oi_pct_snapshot": aggregate_pct(aggregate_delta_pe, aggregate_prev_pe) if previous_same else None,
        "aggregate_pe_minus_ce_delta_oi": (aggregate_delta_pe - aggregate_delta_ce) if previous_same else None,
        "session_baseline_contracts_matched": session_baseline_count,
        "session_delta_call_oi_nearby": session_delta_call if session_baseline_count else None,
        "session_delta_put_oi_nearby": session_delta_put if session_baseline_count else None,
        "nearby_pcr": pcr_rows_put / pcr_rows_call if pcr_rows_call > 0 else None,
        "call_oi_walls": walls(call_oi_by_strike, "CALL_OI_POTENTIAL_RESISTANCE"),
        "put_oi_walls": walls(put_oi_by_strike, "PUT_OI_POTENTIAL_SUPPORT"),
        "oi_zones_above_below_spot": oi_zones,
        "features": per_contract,
    }


# ---------- Price structure and regimes ----------

def true_ranges(candles: Sequence[Candle]) -> list[float]:
    result: list[float] = []
    previous_close: Optional[float] = None
    for candle in candles:
        tr = candle.high - candle.low
        if previous_close is not None:
            tr = max(tr, abs(candle.high - previous_close), abs(candle.low - previous_close))
        result.append(max(0.0, tr))
        previous_close = candle.close
    return result


def atr(candles: Sequence[Candle], period: int = 14) -> Optional[float]:
    trs = true_ranges(candles)
    if len(trs) < period:
        return median(trs) if trs else None
    value = sum(trs[:period]) / period
    for tr in trs[period:]:
        value = (value * (period - 1) + tr) / period
    return value if value > 0 else None


def ema(values: Sequence[float], period: int) -> Optional[float]:
    if not values:
        return None
    alpha = 2.0 / (period + 1.0)
    value = float(values[0])
    for item in values[1:]:
        value = alpha * float(item) + (1.0 - alpha) * value
    return value


def aggregate_candles(candles: Sequence[Candle], size_minutes: int, now: datetime) -> list[Candle]:
    groups: dict[datetime, list[Candle]] = defaultdict(list)
    for c in candles:
        minute = c.start.astimezone(IST).replace(second=0, microsecond=0)
        bucket_minute = minute.minute - (minute.minute % size_minutes)
        bucket = minute.replace(minute=bucket_minute)
        if bucket + timedelta(minutes=size_minutes) <= now.astimezone(IST):
            groups[bucket].append(c)
    bars: list[Candle] = []
    for bucket, items in sorted(groups.items()):
        items.sort(key=lambda x: x.start)
        # Do not aggregate incomplete/gapped buckets into synthetic bars.
        expected = [bucket + timedelta(minutes=i) for i in range(size_minutes)]
        timestamps = [item.start.astimezone(IST) for item in items]
        if timestamps != expected:
            continue
        bars.append(Candle(bucket, items[0].open, max(x.high for x in items), min(x.low for x in items), items[-1].close, sum(x.volume for x in items), items[-1].oi))
    return bars


def price_regime(candles_1m: Sequence[Candle], candles_5m: Sequence[Candle]) -> dict[str, Any]:
    if len(candles_1m) < 20 or len(candles_5m) < 5:
        return {"regime": "UNKNOWN", "higher_timeframe_bias": "UNKNOWN", "execution_direction": "UNKNOWN", "efficiency_ratio": None, "atr_1m": atr(candles_1m), "atr_5m": atr(candles_5m), "reason": "INSUFFICIENT_COMPLETED_CANDLES"}
    c5 = list(candles_5m)
    closes5 = [c.close for c in c5]
    recent = closes5[-6:]
    net = recent[-1] - recent[0]
    path = sum(abs(b - a) for a, b in zip(recent, recent[1:]))
    efficiency = abs(net) / path if path > 0 else 0.0
    atr5 = atr(c5, 14) or median([c.high - c.low for c in c5[-5:]])
    e8, e21 = ema(closes5[-30:], 8), ema(closes5[-50:], 21)
    up_count = sum(1 for a, b in zip(recent, recent[1:]) if b > a)
    down_count = sum(1 for a, b in zip(recent, recent[1:]) if b < a)
    if e8 is not None and e21 is not None and closes5[-1] > e8 > e21 and net > max(atr5 * 0.55, 1.0) and up_count >= 3:
        htf = "BULLISH"
    elif e8 is not None and e21 is not None and closes5[-1] < e8 < e21 and net < -max(atr5 * 0.55, 1.0) and down_count >= 3:
        htf = "BEARISH"
    elif efficiency < 0.22:
        htf = "SIDEWAYS"
    else:
        htf = "TRANSITION"
    c1 = list(candles_1m)
    closes1 = [c.close for c in c1]
    e8_1 = ema(closes1[-25:], 8)
    momentum = closes1[-1] - closes1[-4]
    atr1 = atr(c1, 14)
    if e8_1 is not None and closes1[-1] > e8_1 and momentum > 0:
        exec_dir = "BULLISH"
    elif e8_1 is not None and closes1[-1] < e8_1 and momentum < 0:
        exec_dir = "BEARISH"
    else:
        exec_dir = "MIXED"
    if htf == "BULLISH" and exec_dir == "BULLISH":
        regime = "CONTINUOUS_BULLISH"
    elif htf == "BEARISH" and exec_dir == "BEARISH":
        regime = "CONTINUOUS_BEARISH"
    elif htf == "BEARISH" and exec_dir == "BULLISH":
        regime = "REVERSAL_BEAR_TO_BULL_WATCH"
    elif htf == "BULLISH" and exec_dir == "BEARISH":
        regime = "REVERSAL_BULL_TO_BEAR_WATCH"
    elif htf == "SIDEWAYS":
        regime = "SIDEWAYS"
    else:
        regime = "TRANSITION"
    return {"regime": regime, "higher_timeframe_bias": htf, "execution_direction": exec_dir, "efficiency_ratio": efficiency, "atr_1m": atr1, "atr_5m": atr5, "momentum_3m_points": momentum, "ema8_1m": e8_1, "ema8_5m": e8, "ema21_5m": e21, "reason": "COMPLETED_CANDLE_STRUCTURE"}


def confirmed_pivots(candles: Sequence[Candle], left: int = 2, right: int = 2) -> tuple[list[tuple[int, float]], list[tuple[int, float]]]:
    lows: list[tuple[int, float]] = []
    highs: list[tuple[int, float]] = []
    # A pivot is used only once the right-side candles have closed.
    for i in range(left, len(candles) - right):
        window = candles[i - left:i + right + 1]
        low = candles[i].low
        high = candles[i].high
        if low <= min(c.low for j, c in enumerate(window) if j != left) and sum(1 for c in window if c.low == low) == 1:
            lows.append((i, low))
        if high >= max(c.high for j, c in enumerate(window) if j != left) and sum(1 for c in window if c.high == high) == 1:
            highs.append((i, high))
    return lows, highs


def valid_futures_vwap(futures_candles: Sequence[Candle]) -> Optional[float]:
    numerator = 0.0
    denominator = 0.0
    for c in futures_candles:
        if c.volume <= 0:
            continue
        typical = (c.high + c.low + c.close) / 3.0
        numerator += typical * c.volume
        denominator += c.volume
    return numerator / denominator if denominator > 0 else None


def build_levels(
    candles: Sequence[Candle], previous_daily: Sequence[Candle], oi_evidence: Mapping[str, Any], futures_vwap: Optional[float],
    atr1: Optional[float], config: Config,
) -> list[PriceLevel]:
    if not candles:
        return []
    levels: list[PriceLevel] = []
    tick = 0.05  # NIFTY index price levels are analytical levels, not tradable contracts.
    tol = max(tick * 2, (atr1 or 0) * config.level_cluster_atr_fraction)
    latest = candles[-1]
    day = latest.start.astimezone(IST).date()
    session = [c for c in candles if c.start.astimezone(IST).date() == day]
    if session:
        # Today's extreme is a level only when it occurred before the current candle.
        prior_session = session[:-1]
        if prior_session:
            levels.append(PriceLevel(min(c.low for c in prior_session), "SUPPORT", "SESSION_LOW", 2.0))
            levels.append(PriceLevel(max(c.high for c in prior_session), "RESISTANCE", "SESSION_HIGH", 2.0))
        opening5 = [c for c in session if c.start.astimezone(IST).time() < dtime(9, 20)]
        opening15 = [c for c in session if c.start.astimezone(IST).time() < dtime(9, 30)]
        if len(opening5) >= 5:
            levels.extend([PriceLevel(min(c.low for c in opening5), "SUPPORT", "OPENING_RANGE_5M_LOW", 1.8), PriceLevel(max(c.high for c in opening5), "RESISTANCE", "OPENING_RANGE_5M_HIGH", 1.8)])
        if len(opening15) >= 15:
            levels.extend([PriceLevel(min(c.low for c in opening15), "SUPPORT", "OPENING_RANGE_15M_LOW", 1.6), PriceLevel(max(c.high for c in opening15), "RESISTANCE", "OPENING_RANGE_15M_HIGH", 1.6)])
    if previous_daily:
        prev = max((c for c in previous_daily if c.start.astimezone(IST).date() < day), key=lambda c: c.start, default=None)
        if prev:
            levels.extend([PriceLevel(prev.high, "RESISTANCE", "PREVIOUS_SESSION_HIGH", 2.2), PriceLevel(prev.low, "SUPPORT", "PREVIOUS_SESSION_LOW", 2.2), PriceLevel(prev.close, "SUPPORT" if prev.close <= latest.close else "RESISTANCE", "PREVIOUS_SESSION_CLOSE", 1.5)])
    lows, highs = confirmed_pivots(candles, config.pivot_left, config.pivot_right)
    for idx, value in lows[-8:]:
        levels.append(PriceLevel(value, "SUPPORT", f"CONFIRMED_SWING_LOW_{candles[idx].start.astimezone(IST).strftime('%H%M')}", 1.5))
    for idx, value in highs[-8:]:
        levels.append(PriceLevel(value, "RESISTANCE", f"CONFIRMED_SWING_HIGH_{candles[idx].start.astimezone(IST).strftime('%H%M')}", 1.5))
    if futures_vwap is not None and math.isfinite(futures_vwap):
        levels.append(PriceLevel(futures_vwap, "SUPPORT" if futures_vwap <= latest.close else "RESISTANCE", "FUTURES_VWAP_CONTEXT_ONLY", 0.8))
    for wall in oi_evidence.get("put_oi_walls", [])[:3]:
        if float(wall.get("relative_strength", 0)) >= 0.7:
            levels.append(PriceLevel(float(wall["strike"]), "SUPPORT", "OI_PUT_WALL_POTENTIAL_ONLY", 0.8 + float(wall.get("relative_strength", 0)) * 0.3))
    for wall in oi_evidence.get("call_oi_walls", [])[:3]:
        if float(wall.get("relative_strength", 0)) >= 0.7:
            levels.append(PriceLevel(float(wall["strike"]), "RESISTANCE", "OI_CALL_WALL_POTENTIAL_ONLY", 0.8 + float(wall.get("relative_strength", 0)) * 0.3))
    # Cluster nearby levels while preserving each level's provenance in source text.
    out: list[PriceLevel] = []
    for side in ("SUPPORT", "RESISTANCE"):
        items = sorted((x for x in levels if x.side == side), key=lambda x: x.price)
        clusters: list[list[PriceLevel]] = []
        for item in items:
            if clusters and abs(item.price - median([v.price for v in clusters[-1]])) <= tol:
                clusters[-1].append(item)
            else:
                clusters.append([item])
        for cluster in clusters:
            strength = min(4.0, sum(x.strength for x in cluster))
            price = sum(x.price * x.strength for x in cluster) / sum(x.strength for x in cluster)
            sources = "+".join(dict.fromkeys(x.source for x in cluster))
            out.append(PriceLevel(price, side, sources, strength))
    return sorted(out, key=lambda x: x.price)


def _level_has_structural_provenance(level: PriceLevel) -> bool:
    """Only structural evidence may define a hard T1 barrier.

    Futures VWAP and OI walls are useful context, but cannot by themselves be
    promoted to guaranteed support/resistance. A clustered level remains valid
    when at least one non-context source independently supports it.
    """
    context_only = {
        "FUTURES_VWAP_CONTEXT_ONLY",
        "OI_PUT_WALL_POTENTIAL_ONLY",
        "OI_CALL_WALL_POTENTIAL_ONLY",
    }
    sources = {part.strip() for part in level.source.split("+") if part.strip()}
    return bool(sources - context_only)


def _nearest_level(levels: Sequence[PriceLevel], side: str, price: float, minimum_strength: float = 1.0) -> Optional[PriceLevel]:
    candidates = [
        x for x in levels
        if x.side == side and x.strength >= minimum_strength
        and _level_has_structural_provenance(x)
        and ((x.price > price + 1e-6) if side == "RESISTANCE" else (x.price < price - 1e-6))
    ]
    if not candidates:
        return None
    return min(candidates, key=lambda x: x.price) if side == "RESISTANCE" else max(candidates, key=lambda x: x.price)


def detect_setup(candles: Sequence[Candle], levels: Sequence[PriceLevel], structure: Mapping[str, Any], config: Config) -> Optional[Setup]:
    if len(candles) < 3:
        return None
    current = candles[-1]
    previous = candles[-2]
    atr1 = float(structure.get("atr_1m") or atr(candles) or 0.0)
    if atr1 <= 0:
        return None
    buffer = max(config.minimum_stop_points * 0.15, atr1 * 0.05)
    # Evaluate only recently completed candles. No future candles are used.
    recent = list(candles[-(config.support_lookback_candles + 1):])
    supports = [x for x in levels if x.side == "SUPPORT" and x.strength >= 1.0]
    resistances = [x for x in levels if x.side == "RESISTANCE" and x.strength >= 1.0]
    setups: list[Setup] = []
    for level in supports:
        touched = [(i, c) for i, c in enumerate(recent[:-1]) if c.low <= level.price + max(buffer, atr1 * 0.12) and c.low >= level.price - max(atr1 * 0.7, buffer)]
        swept = [(i, c) for i, c in enumerate(recent[:-1]) if c.low < level.price - buffer and c.close > level.price]
        reclaimed = current.close >= level.price + buffer and current.close > current.open and current.close > previous.close
        if reclaimed and (touched or swept):
            touched_candles = [c for _, c in (swept if swept else touched)]
            invalidation = min(c.low for c in touched_candles + [current])
            kind = "LIQUIDITY_SWEEP_RECLAIM" if swept else "RANGE_EDGE_REVERSAL" if structure.get("regime") == "SIDEWAYS" else "TREND_CONTINUATION_PULLBACK" if structure.get("higher_timeframe_bias") == "BULLISH" else "SUPPORT_BOUNCE"
            confidence = min(0.95, 0.58 + 0.08 * (current.close > previous.high) + 0.08 * (current.close > level.price + 2 * buffer) + 0.05 * (structure.get("higher_timeframe_bias") == "BULLISH"))
            setups.append(Setup(kind, "BULLISH", current.close, invalidation, current.close_time, level.price, level.source, confidence))
    for level in resistances:
        touched = [(i, c) for i, c in enumerate(recent[:-1]) if c.high >= level.price - max(buffer, atr1 * 0.12) and c.high <= level.price + max(atr1 * 0.7, buffer)]
        swept = [(i, c) for i, c in enumerate(recent[:-1]) if c.high > level.price + buffer and c.close < level.price]
        rejected = current.close <= level.price - buffer and current.close < current.open and current.close < previous.close
        if rejected and (touched or swept):
            touched_candles = [c for _, c in (swept if swept else touched)]
            invalidation = max(c.high for c in touched_candles + [current])
            kind = "LIQUIDITY_SWEEP_RECLAIM" if swept else "RANGE_EDGE_REVERSAL" if structure.get("regime") == "SIDEWAYS" else "TREND_CONTINUATION_PULLBACK" if structure.get("higher_timeframe_bias") == "BEARISH" else "RESISTANCE_REJECTION"
            confidence = min(0.95, 0.58 + 0.08 * (current.close < previous.low) + 0.08 * (current.close < level.price - 2 * buffer) + 0.05 * (structure.get("higher_timeframe_bias") == "BEARISH"))
            setups.append(Setup(kind, "BEARISH", current.close, invalidation, current.close_time, level.price, level.source, confidence))
    # Breakout/retest requires a prior close through a level, a retest and a
    # completed confirming candle. It does not jump directly at an old breakout.
    for level in resistances:
        crossed = any(c.close > level.price + buffer for c in recent[:-1])
        retested = current.low <= level.price + max(buffer, atr1 * 0.12) and current.low >= level.price - max(atr1 * 0.6, buffer)
        if crossed and retested and current.close > level.price + buffer and current.close > current.open:
            setups.append(Setup("BREAKOUT_RETEST", "BULLISH", current.close, min(current.low, level.price - buffer), current.close_time, level.price, level.source, 0.78))
    for level in supports:
        crossed = any(c.close < level.price - buffer for c in recent[:-1])
        retested = current.high >= level.price - max(buffer, atr1 * 0.12) and current.high <= level.price + max(atr1 * 0.6, buffer)
        if crossed and retested and current.close < level.price - buffer and current.close < current.open:
            setups.append(Setup("BREAKDOWN_RETEST", "BEARISH", current.close, max(current.high, level.price + buffer), current.close_time, level.price, level.source, 0.78))
    if not setups:
        return None
    # Prefer confirmed sweep/reclaim, then retest, then bounce/rejection.
    priority = {"LIQUIDITY_SWEEP_RECLAIM": 0, "BREAKOUT_RETEST": 1, "BREAKDOWN_RETEST": 1, "SUPPORT_BOUNCE": 2, "RESISTANCE_REJECTION": 2, "TREND_CONTINUATION_PULLBACK": 3}
    return sorted(setups, key=lambda s: (priority.get(s.kind, 9), -s.price_confidence))[0]


# ---------- Risk planning and option pricing ----------
def black_scholes_price(spot: float, strike: float, years: float, volatility: float, rate: float, side: str) -> float:
    """European option approximation, used only for scenarios and calibrated to market mid."""
    if spot <= 0 or strike <= 0 or years <= 0 or volatility <= 0:
        return max(0.0, spot - strike) if side == "CE" else max(0.0, strike - spot)
    sqrt_t = math.sqrt(years)
    d1 = (math.log(spot / strike) + (rate + 0.5 * volatility**2) * years) / (volatility * sqrt_t)
    d2 = d1 - volatility * sqrt_t
    cdf = lambda x: 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))
    if side == "CE":
        return max(0.0, spot * cdf(d1) - strike * math.exp(-rate * years) * cdf(d2))
    return max(0.0, strike * math.exp(-rate * years) * cdf(-d2) - spot * cdf(-d1))


def years_to_expiry(expiry: date, now: datetime) -> float:
    expiry_close = datetime.combine(expiry, dtime(15, 30), tzinfo=IST)
    seconds = max(60.0, (expiry_close - now.astimezone(IST)).total_seconds())
    return seconds / (365.0 * 24 * 3600)


def price_option_scenario(quote: OptionQuote, current_spot: float, scenario_spot: float, now: datetime, config: Config, *, adverse_iv_points: float) -> Optional[float]:
    """Reprice via Black-Scholes, anchored to observed market mid, including gamma/theta/vega effects.

    IV is a percentage-point field in Upstox's chain response. We do not treat
    a missing/implausible IV as zero; the option fails closed instead.
    """
    if quote.iv is None or not (1.0 <= quote.iv <= 100.0) or quote.mid <= 0:
        return None
    iv = quote.iv / 100.0
    shocked_iv = max(0.01, min(1.0, (quote.iv - adverse_iv_points) / 100.0))
    years = years_to_expiry(quote.expiry, now)
    remaining_years = max(1.0 / (365 * 24 * 3600), years - config.expected_hold_minutes / (365.0 * 24 * 60))
    base = black_scholes_price(current_spot, quote.strike, years, iv, config.annual_risk_free_rate, quote.side)
    changed = black_scholes_price(scenario_spot, quote.strike, remaining_years, shocked_iv, config.annual_risk_free_rate, quote.side)
    # Local calibration preserves the observed market mid despite model basis error.
    return max(0.0, quote.mid + changed - base)


def choose_targets_and_stop(entry: float, setup: Setup, levels: Sequence[PriceLevel], structure: Mapping[str, Any], config: Config) -> dict[str, Any]:
    atr1 = float(structure.get("atr_1m") or 0.0)
    if atr1 <= 0:
        raise ScannerError("ATR_UNAVAILABLE", "ATR is not available for structural risk calculation")
    stop_buffer = max(config.minimum_stop_points, atr1 * config.stop_buffer_atr_fraction)
    if setup.direction == "BULLISH":
        stop = setup.invalidation - stop_buffer
        risk = entry - stop
        t1_level = _nearest_level(levels, "RESISTANCE", entry, config.min_level_strength)
        t2_level = _nearest_level([l for l in levels if not (t1_level and abs(l.price - t1_level.price) < max(2.0, atr1 * 0.10))], "RESISTANCE", (t1_level.price if t1_level else entry), config.min_level_strength) if t1_level else None
    else:
        stop = setup.invalidation + stop_buffer
        risk = stop - entry
        t1_level = _nearest_level(levels, "SUPPORT", entry, config.min_level_strength)
        t2_level = _nearest_level([l for l in levels if not (t1_level and abs(l.price - t1_level.price) < max(2.0, atr1 * 0.10))], "SUPPORT", (t1_level.price if t1_level else entry), config.min_level_strength) if t1_level else None
    if risk <= 0 or not math.isfinite(risk):
        raise ScannerError("INVALID_STRUCTURAL_STOP", "Structural stop is not on the risk side of current entry")
    if risk > atr1 * config.max_stop_atr:
        raise ScannerError("STOP_TOO_WIDE", f"Structural risk {risk:.2f} points exceeds {config.max_stop_atr:.2f} ATR ({atr1:.2f})")
    if t1_level is None:
        raise ScannerError("NO_VALID_T1", "No valid opposing resistance/support exists; refusing to fabricate a target")
    reward1 = t1_level.price - entry if setup.direction == "BULLISH" else entry - t1_level.price
    rr1 = reward1 / risk if reward1 > 0 else 0.0
    if rr1 + 1e-9 < config.min_underlying_rr:
        raise ScannerError("RR_BELOW_2R", f"Nearest opposing barrier {t1_level.price:.2f} provides {rr1:.2f}R; minimum is {config.min_underlying_rr:.2f}R")
    if t2_level is not None:
        t2 = t2_level.price
        t2_source = t2_level.source
    else:
        # T2 is explicitly an R-multiple projection only after structural T1
        # passes; it never substitutes for or bypasses T1.
        t2 = entry + (3.0 * risk if setup.direction == "BULLISH" else -3.0 * risk)
        t2_source = "3R_PROJECTION_NOT_A_STRUCTURAL_BARRIER"
    if setup.direction == "BULLISH" and t2 <= t1_level.price:
        t2 = t1_level.price + max(atr1, risk * 0.5)
        t2_source = "ABOVE_T1_ATR_PROJECTION"
    elif setup.direction == "BEARISH" and t2 >= t1_level.price:
        t2 = t1_level.price - max(atr1, risk * 0.5)
        t2_source = "BELOW_T1_ATR_PROJECTION"
    return {"entry_underlying": entry, "stop_underlying": stop, "t1_underlying": t1_level.price, "t1_source": t1_level.source, "t2_underlying": t2, "t2_source": t2_source, "risk_points": risk, "reward_t1_points": reward1, "underlying_rr": rr1, "stop_buffer_points": stop_buffer, "atr_1m": atr1}


def option_quote_from_full(record: OptionRecord, raw: Mapping[str, Any]) -> OptionQuote:
    depth = raw.get("depth") or {}
    buys_raw = depth.get("buy") if isinstance(depth, dict) else []
    sells_raw = depth.get("sell") if isinstance(depth, dict) else []

    def valid_levels(values: Any) -> list[dict[str, float]]:
        levels: list[dict[str, float]] = []
        for item in values or []:
            if not isinstance(item, Mapping):
                continue
            try:
                price = float(item.get("price") or 0)
                quantity = float(item.get("quantity") or 0)
            except (TypeError, ValueError, OverflowError):
                continue
            if math.isfinite(price) and math.isfinite(quantity) and price > 0 and quantity > 0:
                levels.append({"price": price, "quantity": quantity})
        return levels

    buys = valid_levels(buys_raw)
    sells = valid_levels(sells_raw)
    bid = max((x["price"] for x in buys), default=0.0)
    ask = min((x["price"] for x in sells), default=0.0)
    bid_qty = sum(x["quantity"] for x in buys if x["price"] == bid) if bid > 0 else 0.0
    ask_qty = sum(x["quantity"] for x in sells if x["price"] == ask) if ask > 0 else 0.0

    def finite_or(value: Any, fallback: float) -> float:
        try:
            number = float(value)
            return number if math.isfinite(number) and number >= 0 else fallback
        except (TypeError, ValueError, OverflowError):
            return fallback

    ltp = finite_or(raw.get("last_price"), record.ltp)
    volume = finite_or(raw.get("volume"), record.volume)
    oi = finite_or(raw.get("oi"), record.oi)
    return OptionQuote(
        record.instrument_key, parse_datetime(raw.get("timestamp")), ltp, bid, ask, bid_qty, ask_qty,
        volume, oi, record.strike, record.side, record.expiry, record.delta, record.gamma,
        record.theta, record.vega, record.iv,
    )


def select_option_and_risk(
    direction: str, spot: float, spot_quote_time: Optional[datetime], chain_records: Sequence[OptionRecord], full_quotes: Mapping[str, Mapping[str, Any]],
    expiry: date, now: datetime, plan: Mapping[str, Any], structure: Mapping[str, Any], config: Config,
) -> dict[str, Any]:
    if direction not in {"BULLISH", "BEARISH"}:
        raise ScannerError("DIRECTION_INVALID", "Option selector requires a directional setup")
    strike_grid = sorted({r.strike for r in chain_records})
    step_values = sorted({b - a for a, b in zip(strike_grid, strike_grid[1:]) if b > a})
    if not step_values:
        raise ScannerError("STRIKE_GRID_INVALID", "Cannot infer strike interval from option-chain data")
    strike_step = median(step_values)
    strikes = sorted({r.strike for r in chain_records})
    atm = min(strikes, key=lambda s: abs(s - spot))
    side = "CE" if direction == "BULLISH" else "PE"
    offsets = config.strike_offsets_ce if side == "CE" else config.strike_offsets_pe
    by_id = {r.instrument_key: r for r in chain_records}
    candidates: list[dict[str, Any]] = []
    rejections: Counter[str] = Counter()
    for offset in offsets:
        target_strike = atm + offset * strike_step
        record = min((r for r in chain_records if r.side == side), key=lambda r: abs(r.strike - target_strike), default=None)
        if record is None or abs(record.strike - target_strike) > max(0.51, strike_step * 0.15):
            rejections["STRIKE_NOT_IN_CHAIN"] += 1
            continue
        raw_quote = full_quotes.get(record.instrument_key)
        if raw_quote is None:
            rejections["QUOTE_MISSING"] += 1
            continue
        quote = option_quote_from_full(record, raw_quote)
        if quote.timestamp is None:
            rejections["QUOTE_TIMESTAMP_MISSING"] += 1
            continue
        quote_age = (now.astimezone(IST) - quote.timestamp).total_seconds()
        if quote_age < -5 or quote_age > config.max_quote_age_seconds:
            rejections["QUOTE_STALE"] += 1
            continue
        if quote.bid <= 0 or quote.ask <= 0 or quote.ask < quote.bid:
            rejections["INVALID_BID_ASK"] += 1
            continue
        if quote.bid_qty < config.min_bid_qty or quote.ask_qty < config.min_ask_qty:
            rejections["INSUFFICIENT_DEPTH"] += 1
            continue
        if quote.volume < config.min_option_volume:
            rejections["LOW_OPTION_VOLUME"] += 1
            continue
        if quote.spread_pct > config.max_spread_pct:
            rejections["SPREAD_TOO_WIDE"] += 1
            continue
        if quote.delta is None or not (config.min_abs_delta <= abs(quote.delta) <= config.max_abs_delta):
            rejections["DELTA_OUT_OF_RANGE"] += 1
            continue
        if quote.iv is None or not (1 <= quote.iv <= 100):
            rejections["INVALID_IV"] += 1
            continue
        entry = quote.ask + config.option_slippage_points
        stop_model = price_option_scenario(quote, spot, float(plan["stop_underlying"]), now, config, adverse_iv_points=config.iv_shock_points)
        t1_model = price_option_scenario(quote, spot, float(plan["t1_underlying"]), now, config, adverse_iv_points=config.iv_shock_points)
        t2_model = price_option_scenario(quote, spot, float(plan["t2_underlying"]), now, config, adverse_iv_points=config.iv_shock_points)
        if stop_model is None or t1_model is None or t2_model is None:
            rejections["PREMIUM_SCENARIO_UNAVAILABLE"] += 1
            continue
        half_spread = (quote.ask - quote.bid) / 2.0
        stop_exit = max(0.0, stop_model - half_spread - config.option_slippage_points)
        t1_exit = max(0.0, t1_model - half_spread - config.option_slippage_points)
        t2_exit = max(0.0, t2_model - half_spread - config.option_slippage_points)
        entry_cost = entry * config.transaction_cost_rate
        stop_cost = stop_exit * config.transaction_cost_rate
        t1_cost = t1_exit * config.transaction_cost_rate
        t2_cost = t2_exit * config.transaction_cost_rate
        premium_risk = (entry - stop_exit) + entry_cost + stop_cost
        net_reward1 = (t1_exit - entry) - entry_cost - t1_cost
        net_reward2 = (t2_exit - entry) - entry_cost - t2_cost
        net_rr1 = net_reward1 / premium_risk if premium_risk > 0 and net_reward1 > 0 else 0.0
        net_rr2 = net_reward2 / premium_risk if premium_risk > 0 and net_reward2 > 0 else 0.0
        if premium_risk <= 0 or net_reward1 <= 0:
            rejections["OPTION_NET_REWARD_NONPOSITIVE"] += 1
            continue
        if net_rr1 < config.min_option_net_rr:
            rejections["OPTION_NET_RR_BELOW_2R"] += 1
            continue
        # Rank valid contracts by net RR first, then prefer a delta closer to 0.55 and tighter spread.
        rank = (net_rr1, -abs(abs(quote.delta) - 0.55), -quote.spread_pct, -abs(offset))
        candidates.append({
            "instrument_key": quote.instrument_key, "strike": quote.strike, "side": quote.side, "expiry": quote.expiry.isoformat(),
            "trading_offset_from_atm": offset, "atm_strike": atm, "strike_interval": strike_step,
            "entry_option_ask_plus_slippage": entry, "option_stop_estimate": stop_exit,
            "option_t1_estimate": t1_exit, "option_t2_estimate": t2_exit,
            "net_option_rr_t1": net_rr1, "net_option_rr_t2": net_rr2,
            "spread_points": quote.ask - quote.bid, "spread_pct": quote.spread_pct, "bid_qty": quote.bid_qty, "ask_qty": quote.ask_qty,
            "quote_timestamp": quote.timestamp.isoformat(), "quote_age_seconds": quote_age,
            "ltp": quote.ltp, "bid": quote.bid, "ask": quote.ask, "volume": quote.volume, "oi": quote.oi,
            "delta": quote.delta, "gamma": quote.gamma, "theta": quote.theta, "vega": quote.vega, "iv_percent": quote.iv,
            "pricing_method": "BLACK_SCHOLES_REPRICE_CALIBRATED_TO_LIVE_MID_WITH_IV_SHOCK_AND_SPREAD_SLIPPAGE_COSTS",
            "estimated_round_trip_cost_rate_each_side": config.transaction_cost_rate,
            "entry_slippage_points_per_side": config.option_slippage_points,
            "_rank": rank,
        })
    if not candidates:
        reason = rejections.most_common(1)[0][0] if rejections else "NO_VALID_OPTION_QUOTES"
        details = ", ".join(f"{k}:{v}" for k, v in rejections.most_common(4))
        raise ScannerError(reason, f"No eligible {side} contract among allowed ATM offsets. {details}")
    candidates.sort(key=lambda c: c["_rank"], reverse=True)
    selected = candidates[0]
    selected.pop("_rank", None)
    selected["candidate_count_passed"] = len(candidates)
    selected["candidate_count_rejected"] = sum(rejections.values())
    selected["rejection_counts"] = dict(rejections)
    selected["spot_quote_timestamp"] = spot_quote_time.isoformat() if spot_quote_time else None
    return selected


# ---------- Setup authorization and single decision pipeline ----------

def stabilize_oi_evidence(evidence: dict[str, Any], state: dict[str, Any], session_date: date, expiry: date) -> None:
    """Apply 2-of-3 snapshot persistence without hiding the raw current score.

    A first opposite snapshot is labelled as a transition watch (stable label
    MIXED); two consecutive direction observations are enough to change the
    stable directional label. Raw deltas/scores are never rewritten.
    """
    raw_label = str(evidence.get("label", "MISSING"))
    evidence["raw_label"] = raw_label
    history = [x for x in state.get("oi_evidence_history", [])
               if x.get("session_date") == session_date.isoformat() and x.get("expiry") == expiry.isoformat()]
    prior = [str(x.get("raw_label", x.get("label", "MISSING"))) for x in history[-2:]]
    if raw_label not in {"BULLISH", "BEARISH"} or not evidence.get("compared_to_previous_successful_snapshot"):
        evidence["label"] = "MISSING" if not evidence.get("compared_to_previous_successful_snapshot") else "MIXED"
        evidence["persistence_count"] = 0
        evidence["transition_status"] = "NO_DIRECTIONAL_PERSISTENCE"
    else:
        same_prior = sum(1 for label in prior if label == raw_label)
        evidence["persistence_count"] = 1 + same_prior
        previous_directional = next((x for x in reversed(prior) if x in {"BULLISH", "BEARISH"}), None)
        if same_prior >= 1:
            evidence["label"] = raw_label
            evidence["transition_status"] = "DIRECTION_PERSISTENT"
        else:
            evidence["label"] = "MIXED"
            evidence["transition_status"] = "REVERSAL_WATCH" if previous_directional and previous_directional != raw_label else "WAITING_FOR_SECOND_SNAPSHOT"
        evidence["previous_directional_label"] = previous_directional
    history.append({"timestamp": evidence.get("snapshot_time"), "session_date": session_date.isoformat(), "expiry": expiry.isoformat(), "label": raw_label, "raw_label": raw_label, "stable_label": evidence.get("label"), "score": evidence.get("score"), "confidence": evidence.get("confidence")})
    state["oi_evidence_history"] = history[-5:]


def advance_setup_watch(
    candles: Sequence[Candle], previous_processed: Optional[datetime], previous_daily: Sequence[Candle],
    state: dict[str, Any], config: Config,
) -> Optional[Setup]:
    """Walk newly completed candles chronologically and persist the most recent setup.

    Historical candle patterns update state only; they do not become historical
    fills. A later gate revalidates any watch against the current live quote.
    """
    pending = _setup_from_state(state.get("setup_watch"))
    for i, candle in enumerate(candles):
        if previous_processed is not None and candle.start <= previous_processed:
            continue
        if pending is not None:
            age = (candle.close_time - pending.confirmed_at).total_seconds()
            breached = (pending.direction == "BULLISH" and candle.low <= pending.invalidation) or (pending.direction == "BEARISH" and candle.high >= pending.invalidation)
            if age > config.setup_state_ttl_minutes * 60 or breached:
                pending = None
                state["setup_watch"] = None
        prefix = candles[:i + 1]
        atr_value = atr(prefix)
        prefix_levels = build_levels(prefix, previous_daily, _empty_oi(), None, atr_value, config)
        prefix_structure = price_regime(prefix, aggregate_candles(prefix, 5, candle.close_time))
        candidate = detect_setup(prefix, prefix_levels, prefix_structure, config)
        if candidate is not None:
            pending = candidate
            state["setup_watch"] = {"direction": candidate.direction, "kind": candidate.kind,
                                    "confirmed_at": candidate.confirmed_at.isoformat(), "trigger": candidate.trigger,
                                    "invalidation": candidate.invalidation, "source_level": candidate.source_level,
                                    "source": candidate.source, "price_confidence": candidate.price_confidence}
    return pending


def authorize_direction(oi: Mapping[str, Any], setup: Setup, structure: Mapping[str, Any], config: Config) -> None:
    label = oi.get("label", "MISSING")
    age = oi.get("oi_age_seconds")
    if label in {"MISSING", "UNKNOWN"} or not oi.get("compared_to_previous_successful_snapshot"):
        raise ScannerError("OI_BASELINE_MISSING", "At least two successful, same-session OI snapshots are required before directional qualification")
    if age is not None and age > config.max_oi_age_seconds:
        raise ScannerError("OI_STALE", f"Last successful OI snapshot is {age:.0f}s old")
    expected = "BULLISH" if setup.direction == "BULLISH" else "BEARISH"
    if label == expected:
        if float(oi.get("confidence") or 0) < config.min_oi_direction_confidence:
            raise ScannerError("OI_LOW_CONFIDENCE", f"OI directional confidence is below {config.min_oi_direction_confidence:.2f}")
        return
    if label == "MIXED":
        if setup.price_confidence < config.min_mixed_price_confirmation or structure.get("execution_direction") != setup.direction:
            raise ScannerError("OI_MIXED_WAIT_PRICE_CONFIRMATION", "OI is mixed; a strong completed-candle trigger aligned with execution direction is required")
        return
    if label == "MISSING":
        raise ScannerError("OI_BASELINE_MISSING", "No usable current-session OI evidence")
    raise ScannerError("OI_PRICE_DIRECTION_CONFLICT", f"Confirmed price setup is {setup.direction}, but OI evidence is {label}")


def _option_record_from_state(row: Mapping[str, Any]) -> OptionRecord:
    return OptionRecord(
        instrument_key=str(row["instrument_key"]), expiry=parse_expiry(row.get("expiry")) or date.min,
        strike=float(row["strike"]), side=str(row["side"]), ltp=float(row.get("ltp", 0)), oi=float(row.get("oi", 0)),
        volume=float(row.get("volume", 0)), previous_session_oi=float(row["previous_session_oi"]) if row.get("previous_session_oi") is not None else None,
        chain_bid=float(row.get("chain_bid", 0)), chain_ask=float(row.get("chain_ask", 0)), chain_bid_qty=float(row.get("chain_bid_qty", 0)), chain_ask_qty=float(row.get("chain_ask_qty", 0)),
        delta=float(row["delta"]) if row.get("delta") is not None else None, gamma=float(row["gamma"]) if row.get("gamma") is not None else None,
        theta=float(row["theta"]) if row.get("theta") is not None else None, vega=float(row["vega"]) if row.get("vega") is not None else None,
        iv=float(row["iv"]) if row.get("iv") is not None else None,
    )


def _snapshot_payload(records: Sequence[OptionRecord], spot: float, session_date: date, expiry: date, fetched_at: datetime) -> dict[str, Any]:
    return {"session_date": session_date.isoformat(), "expiry": expiry.isoformat(), "fetched_at": fetched_at.isoformat(), "spot": spot, "rows": _snapshot_rows(records, spot)}


def _quote_timestamp(raw: Mapping[str, Any]) -> Optional[datetime]:
    return parse_datetime(raw.get("timestamp"))


def _spot_from_full_quote(raw: Mapping[str, Any]) -> tuple[float, Optional[datetime], Mapping[str, Any]]:
    try:
        spot = float(raw.get("last_price"))
    except (TypeError, ValueError):
        spot = 0.0
    if not math.isfinite(spot) or spot <= 0:
        raise ScannerError("SPOT_QUOTE_INVALID", "Full market quote returned an invalid NIFTY spot")
    return spot, _quote_timestamp(raw), raw


def _recent_current_snapshot(state: Mapping[str, Any], session_date: date, expiry: date) -> Optional[Mapping[str, Any]]:
    for snapshot in reversed(state.get("chain_snapshots", [])):
        if snapshot.get("session_date") == session_date.isoformat() and snapshot.get("expiry") == expiry.isoformat():
            return snapshot
    return None


def _first_session_baseline(state: Mapping[str, Any], session_date: date, expiry: date) -> Optional[Mapping[str, Any]]:
    baseline = state.get("session_oi_baseline")
    if baseline and baseline.get("session_date") == session_date.isoformat() and baseline.get("expiry") == expiry.isoformat():
        return baseline
    return None


def _setup_from_state(raw: Optional[Mapping[str, Any]]) -> Optional[Setup]:
    if not isinstance(raw, Mapping):
        return None
    confirmed = parse_datetime(raw.get("confirmed_at"))
    try:
        if confirmed is None:
            return None
        direction = str(raw.get("direction", ""))
        kind = str(raw.get("kind", ""))
        if direction not in {"BULLISH", "BEARISH"} or not kind:
            return None
        return Setup(kind, direction, float(raw["trigger"]), float(raw["invalidation"]), confirmed,
                     float(raw["source_level"]) if raw.get("source_level") is not None else None,
                     str(raw.get("source", "PERSISTED_SETUP")), float(raw.get("price_confidence", 0.0)))
    except (KeyError, TypeError, ValueError):
        return None


def _nearest_quote_key(full_quotes: Mapping[str, Mapping[str, Any]], instrument_key: str) -> Optional[Mapping[str, Any]]:
    return full_quotes.get(instrument_key)


def _build_live_records(records: Sequence[OptionRecord], instrument_rows: Sequence[Mapping[str, Any]], spot: float, step_limit: int = 6) -> tuple[list[OptionRecord], list[str]]:
    strikes = sorted({r.strike for r in records})
    if not strikes:
        return [], []
    atm = min(strikes, key=lambda s: abs(s - spot))
    index = strikes.index(atm)
    step_values = [b - a for a, b in zip(strikes, strikes[1:]) if b > a]
    step = median(step_values) if step_values else 50.0
    eligible_strikes = set(strikes[max(0, index - step_limit):min(len(strikes), index + step_limit + 1)])
    selected = [r for r in records if r.strike in eligible_strikes]
    return selected, [r.instrument_key for r in selected]


def _levels_summary(levels: Sequence[PriceLevel], spot: float) -> dict[str, Any]:
    below = sorted((x for x in levels if x.side == "SUPPORT" and x.price < spot), key=lambda x: x.price, reverse=True)
    above = sorted((x for x in levels if x.side == "RESISTANCE" and x.price > spot), key=lambda x: x.price)
    return {
        "nearest_support": {"price": below[0].price, "source": below[0].source, "strength": below[0].strength} if below else None,
        "nearest_resistance": {"price": above[0].price, "source": above[0].source, "strength": above[0].strength} if above else None,
        "support_count": len(below), "resistance_count": len(above),
    }


def _market_open(now: datetime) -> bool:
    local = now.astimezone(IST)
    if local.weekday() >= 5:
        return False
    t = local.time()
    return dtime(9, 15) <= t <= dtime(15, 30)


def _empty_oi(status: str = "MISSING") -> dict[str, Any]:
    return {"label": status, "score": 0.0, "bull_score": 0.0, "bear_score": 0.0, "confidence": 0.0, "score_margin": 0.0, "snapshot_status": "MISSING", "compared_to_previous_successful_snapshot": False, "features": [], "call_oi_walls": [], "put_oi_walls": []}


def run_scan(config: Config, *, now: Optional[datetime] = None, client: Optional[UpstoxClient] = None, master: Optional[InstrumentMaster] = None, dry_run: bool = False) -> dict[str, Any]:
    """Run one idempotent scan and return a compact structured decision."""
    if now is None:
        now = now_ist()
    if now.tzinfo is None or now.utcoffset() is None:
        raise ScannerError("TIMEZONE_INVALID", "Scan evaluation time must be timezone-aware")
    now = now.astimezone(IST)
    session_date = now.date()
    base_result: dict[str, Any] = {"scanner_version": VERSION, "schema_version": SCHEMA_VERSION, "timestamp": now.isoformat(), "session_date": session_date.isoformat(), "decision": "NO_TRADE", "reason_code": "UNINITIALIZED"}
    if not _market_open(now):
        return {**base_result, "regime": "UNKNOWN", "oi_label": "MISSING", "reason_code": "MARKET_CLOSED", "decision": "NO_TRADE"}
    state = read_state(config.state_file)
    previous_processed = parse_datetime(state.get("last_processed_candle")) if state.get("session_date") == session_date.isoformat() else None
    if state.get("session_date") != session_date.isoformat():
        # Never use yesterday's OI as the previous intraday snapshot.
        state = {"schema_version": SCHEMA_VERSION, "scanner_version": VERSION, "session_date": session_date.isoformat(), "chain_snapshots": [], "session_oi_baseline": None, "seen_signal_keys": [], "pending_notifications": [], "last_processed_candle": None, "setup_watch": None}
    else:
        state.setdefault("chain_snapshots", [])
        state.setdefault("seen_signal_keys", [])
        state.setdefault("pending_notifications", [])
    client = client or UpstoxClient(config.token, config.request_timeout, config.max_retries)
    master = master or InstrumentMaster(client, config.instrument_cache, config.instrument_cache_hours)
    index_row: Optional[dict[str, Any]] = None
    expiry: Optional[date] = None
    chain_records: list[OptionRecord] = []
    spot_chain = 0.0
    chain_time: Optional[datetime] = None
    prior_snapshot: Optional[Mapping[str, Any]] = None
    baseline: Optional[Mapping[str, Any]] = None
    oi = _empty_oi()
    chain_refresh_ok = False
    chain_refresh_error: Optional[ScannerError] = None
    try:
        master.load(now)
        index_row = master.resolve_index()
        index_key = str(index_row["instrument_key"])
        expiry = master.resolve_expiry(index_key, session_date, config.explicit_expiry)
        option_instruments = master.option_instruments(index_key, expiry)
        chain_url = f"{API_BASE}/v2/option/chain?{urllib.parse.urlencode({'instrument_key': index_key, 'expiry_date': expiry.isoformat()})}"
        prior_snapshot = _recent_current_snapshot(state, session_date, expiry)
        baseline = _first_session_baseline(state, session_date, expiry)
        try:
            chain_payload = client.get_json(chain_url)
            chain_time = now_ist()
            spot_chain, chain_records = parse_option_chain(chain_payload, expiry, chain_time)
            oi = calculate_oi_evidence(chain_records, prior_snapshot, baseline, spot_chain, chain_time, config)
            stabilize_oi_evidence(oi, state, session_date, expiry)
            # Fetch/receive time is distinct from the actual interval between snapshots.
            oi["oi_age_seconds"] = max(0.0, (now_ist() - chain_time).total_seconds())
            oi["source_refresh_status"] = "SUCCESS"
            oi["source_refresh_error"] = None
            chain_snapshot = _snapshot_payload(chain_records, spot_chain, session_date, expiry, chain_time)
            # First successful snapshot sets the session baseline; subsequent
            # successful observations are kept in fetch order, never replaced by errors.
            old_baseline = state.get("session_oi_baseline") or {}
            if old_baseline.get("session_date") != session_date.isoformat() or old_baseline.get("expiry") != expiry.isoformat():
                state["session_oi_baseline"] = chain_snapshot
            existing_snapshots = state.get("chain_snapshots", [])
            if not existing_snapshots or existing_snapshots[-1].get("fetched_at") != chain_snapshot["fetched_at"]:
                existing_snapshots.append(chain_snapshot)
            state["chain_snapshots"] = existing_snapshots[-5:]
            state["last_successful_snapshot_at"] = chain_time.isoformat()
            state["latest_oi_evidence"] = {k: v for k, v in oi.items() if k != "features"}
            # Persist the successful observation before later market-data calls.
            # This survives a subsequent quote/candle failure or interrupted job.
            atomic_write_json(config.state_file, state)
            chain_refresh_ok = True
        except ScannerError as chain_exc:
            chain_refresh_error = chain_exc
            # A failed refresh never creates an OI delta. Retain last successful
            # same-session evidence for context while continuing to update spot
            # structure. Entries remain blocked because current Greeks/IV are not fresh.
            prior_snapshot = _recent_current_snapshot(state, session_date, expiry)
            if prior_snapshot is not None:
                chain_time = parse_datetime(prior_snapshot.get("fetched_at"))
                try:
                    spot_chain = float(prior_snapshot.get("spot") or 0.0)
                    chain_records = [_option_record_from_state(r) for r in prior_snapshot.get("rows", []) if isinstance(r, Mapping)]
                except (TypeError, ValueError, KeyError) as fallback_exc:
                    LOG.warning("Previous option snapshot could not be normalized (%s)", type(fallback_exc).__name__)
                    chain_records = []
                    spot_chain = 0.0
                retained = state.get("latest_oi_evidence") or _empty_oi()
                oi = dict(retained)
                age = max(0.0, (now - chain_time).total_seconds()) if chain_time else float(config.max_oi_age_seconds + 1)
                original_confidence = float(oi.get("confidence") or 0.0)
                decay = max(0.0, 1.0 - age / max(1.0, config.max_oi_age_seconds))
                oi.update({
                    "oi_age_seconds": age,
                    "stored_confidence_before_age_decay": original_confidence,
                    "confidence": original_confidence * decay,
                    "confidence_decay_factor": decay,
                    "snapshot_status": "RETAINED_AFTER_REFRESH_FAILURE",
                    "source_refresh_status": "FAILED_RETAINED_LAST_SUCCESSFUL_SNAPSHOT",
                    "source_refresh_error": chain_exc.code,
                    "current_snapshot_delta_available": False,
                })
            else:
                oi = _empty_oi("MISSING")
                oi.update({"source_refresh_status": "FAILED_NO_SESSION_BASELINE", "source_refresh_error": chain_exc.code, "current_snapshot_delta_available": False, "oi_age_seconds": None})
        # Fetch index and nearest current futures candles even if chain refresh failed.
        index_candles = fetch_candles(client, index_key, now, minutes=1)
        latest_close_time = index_candles[-1].close_time
        candle_age = (now - latest_close_time).total_seconds()
        if candle_age < -1 or candle_age > config.max_candle_age_seconds:
            raise ScannerError("CANDLES_STALE", f"Latest completed candle age is {candle_age:.0f}s")
        daily_candles = fetch_daily_candles(client, index_key, now)
        future_row = master.resolve_future(index_key, session_date)
        futures_candles: list[Candle] = []
        future_key = str(future_row.get("instrument_key")) if future_row else ""
        if future_key:
            try:
                futures_candles = fetch_candles(client, future_key, now, minutes=1)
            except ScannerError as exc:
                LOG.warning("Futures context unavailable (%s); VWAP remains unavailable", exc.code)
        futures_vwap = valid_futures_vwap(futures_candles)
        bars_5m = aggregate_candles(index_candles, 5, now)
        structure = price_regime(index_candles, bars_5m)
        spot_quote_keys = [index_key] + ([future_key] if future_key else [])
        live_records, _ = _build_live_records(chain_records, option_instruments, spot_chain, step_limit=6)
        all_quote_keys = spot_quote_keys + [r.instrument_key for r in live_records]
        full_quotes = get_full_quotes(client, all_quote_keys)
        raw_spot_quote = full_quotes.get(index_key)
        if raw_spot_quote is None:
            raise ScannerError("SPOT_QUOTE_MISSING", "Full Market Quotes did not return NIFTY 50 index quote")
        spot, spot_quote_time, _ = _spot_from_full_quote(raw_spot_quote)
        if spot_quote_time is None:
            raise ScannerError("SPOT_QUOTE_TIMESTAMP_MISSING", "NIFTY 50 live quote has no source timestamp")
        spot_age = (now - spot_quote_time).total_seconds()
        if spot_age < -5 or spot_age > config.max_quote_age_seconds:
            raise ScannerError("SPOT_QUOTE_STALE", f"NIFTY spot quote age is {spot_age:.0f}s")
        divergence = abs(spot - index_candles[-1].close)
        spot_context = {"spot": spot, "spot_quote_timestamp": spot_quote_time.isoformat(), "spot_quote_age_seconds": spot_age, "latest_completed_candle_time": index_candles[-1].start.isoformat(), "latest_candle_close": index_candles[-1].close, "spot_vs_last_close_points": divergence}
        levels = build_levels(index_candles, daily_candles, oi, futures_vwap, structure.get("atr_1m"), config)
        level_summary = _levels_summary(levels, spot)
        # Reconstruct setup state chronologically from every candle not yet
        # processed by the prior workflow run. This is not historical execution.
        tracked_setup = advance_setup_watch(index_candles, previous_processed, daily_candles, state, config)
        current_setup = detect_setup(index_candles, levels, structure, config)
        setup = current_setup or tracked_setup
        detected_new_setup = current_setup is not None
        state["last_processed_candle"] = index_candles[-1].start.isoformat()
        # Quote-derived current market context, not a fabricated index VWAP.
        futures_quote = full_quotes.get(future_key) if future_key else None
        futures_price = float(futures_quote.get("last_price")) if futures_quote and futures_quote.get("last_price") is not None else None
        basis = futures_price - spot if futures_price is not None else None
        if futures_quote and futures_quote.get("timestamp"):
            futures_quote_time = parse_datetime(futures_quote.get("timestamp"))
        else:
            futures_quote_time = None
        future_context = {"instrument_key": future_key or None, "trading_symbol": future_row.get("trading_symbol") if future_row else None, "expiry": parse_expiry(future_row.get("expiry")).isoformat() if future_row and parse_expiry(future_row.get("expiry")) else None, "price": futures_price, "quote_timestamp": futures_quote_time.isoformat() if futures_quote_time else None, "basis_points": basis, "vwap": futures_vwap, "vwap_valid": futures_vwap is not None and any(c.volume > 0 for c in futures_candles)}
        base_result.update({"expiry": expiry.isoformat(), "underlying_key": index_key, "spot": spot, "spot_context": spot_context, "oi": {k: v for k, v in oi.items() if k != "features"}, "oi_label": oi.get("label", "MISSING"), "option_chain_status": oi.get("source_refresh_status", "SUCCESS" if chain_refresh_ok else "UNKNOWN"), "option_chain_error": chain_refresh_error.code if chain_refresh_error else None, "structure": structure, "regime": structure.get("regime"), "levels": level_summary, "futures": future_context, "setup": json_safe(setup) if setup else None, "decision": "NO_TRADE", "reason_code": "NO_CONFIRMED_SETUP"})
        if not setup:
            base_result["reason_code"] = "OI_BASELINE_MISSING" if not oi.get("compared_to_previous_successful_snapshot") else "NO_CONFIRMED_SETUP"
            # Keep an existing watch until TTL or explicit invalidation; it is
            # evidence for later diagnostics, not automatic entry authorization.
            prior_watch = _setup_from_state(state.get("setup_watch"))
            if prior_watch is not None:
                age = (now - prior_watch.confirmed_at).total_seconds()
                invalidated = (prior_watch.direction == "BULLISH" and spot <= prior_watch.invalidation) or (prior_watch.direction == "BEARISH" and spot >= prior_watch.invalidation)
                if age > config.setup_state_ttl_minutes * 60 or invalidated:
                    state["setup_watch"] = None
        else:
            setup_age = (now - setup.confirmed_at).total_seconds()
            base_result["setup_age_seconds"] = setup_age
            base_result["setup_direction"] = setup.direction
            base_result["setup_kind"] = setup.kind
            if detected_new_setup or not state.get("setup_watch"):
                state["setup_watch"] = {"direction": setup.direction, "kind": setup.kind, "confirmed_at": setup.confirmed_at.isoformat(), "trigger": setup.trigger, "invalidation": setup.invalidation, "source_level": setup.source_level, "source": setup.source, "price_confidence": setup.price_confidence}
            if setup_age < -1 or setup_age > config.setup_max_age_minutes * 60:
                raise ScannerError("MISSED_OR_STALE_SETUP", f"Setup confirmation is {setup_age:.0f}s old; no backdated entry allowed")
            extension = abs(spot - setup.trigger)
            if structure.get("atr_1m") and extension > float(structure["atr_1m"]) * config.max_entry_extension_atr:
                raise ScannerError("ENTRY_TOO_EXTENDED", f"Current spot is {extension:.2f} points from setup trigger")
            if not chain_refresh_ok:
                detail = chain_refresh_error.code if chain_refresh_error else "UNKNOWN_REFRESH_FAILURE"
                raise ScannerError("OPTION_CHAIN_REFRESH_FAILED", f"Price structure was evaluated, but a fresh option chain/Greeks snapshot is required before entry; latest refresh failed with {detail}")
            authorize_direction(oi, setup, structure, config)
            plan = choose_targets_and_stop(spot, setup, levels, structure, config)
            base_result["risk_plan"] = plan
            selected = select_option_and_risk(setup.direction, spot, spot_quote_time, chain_records, full_quotes, expiry, now, plan, structure, config)
            signal_key_raw = f"{session_date}|{expiry}|{setup.direction}|{selected['instrument_key']}|{setup.kind}|{setup.confirmed_at.isoformat()}"
            signal_key = hashlib.sha256(signal_key_raw.encode()).hexdigest()[:24]
            if signal_key in state.get("seen_signal_keys", []):
                base_result["reason_code"] = "DUPLICATE_SIGNAL_SUPPRESSED"
                base_result["decision"] = "NO_TRADE"
            else:
                base_result.update({"decision": "QUALIFIED", "reason_code": "QUALIFIED_CE" if setup.direction == "BULLISH" else "QUALIFIED_PE", "signal_key": signal_key, "selected_contract": selected, "risk_plan": plan, "setup": json_safe(setup), "candidate_offsets_allowed": list(config.strike_offsets_ce if setup.direction == "BULLISH" else config.strike_offsets_pe), "notification_status": "PENDING" if (config.webhook_url or (config.smtp_host and config.email_sender and config.email_receiver and config.email_password)) else "NOT_CONFIGURED"})
                state.setdefault("seen_signal_keys", []).append(signal_key)
                state["seen_signal_keys"] = state["seen_signal_keys"][-500:]
                state["last_signal"] = {"signal_key": signal_key, "timestamp": now.isoformat(), "decision": base_result["decision"], "contract": selected, "risk_plan": plan}
                state.setdefault("pending_notifications", []).append({"signal_key": signal_key, "payload": base_result.copy(), "attempts": 0, "created_at": now.isoformat()})
                state["pending_notifications"] = state["pending_notifications"][-20:]
        state["last_decision"] = {k: base_result.get(k) for k in ("timestamp", "decision", "reason_code", "signal_key", "spot", "oi_label", "regime")}
        state["schema_version"] = SCHEMA_VERSION
        state["scanner_version"] = VERSION
        state["session_date"] = session_date.isoformat()
        state["expiry"] = expiry.isoformat()
        if chain_refresh_ok:
            state["latest_oi_evidence"] = {k: v for k, v in oi.items() if k != "features"}
            if chain_time is not None:
                state["last_successful_snapshot_at"] = chain_time.isoformat()
        state["last_processed_candle"] = index_candles[-1].start.isoformat()
        # Save state before writing audit/sending alert. On save failure, no alert is sent.
        atomic_write_json(config.state_file, state)
        # Notification is attempted only after the signal/dedup key is durable.
        _deliver_pending_notifications(config, state, dry_run=dry_run)
        if base_result.get("signal_key"):
            if base_result["signal_key"] in state.get("delivered_signal_keys", []):
                base_result["notification_status"] = "SENT"
            else:
                pending_match = next((x for x in state.get("pending_notifications", []) if x.get("signal_key") == base_result["signal_key"]), None)
                base_result["notification_status"] = (pending_match or {}).get("status", "NOT_CONFIGURED")
                if pending_match and pending_match.get("last_error"):
                    base_result["notification_error"] = pending_match["last_error"]
        # Persist delivery status before adding the final audit record.
        atomic_write_json(config.state_file, state)
        audit_file = config.audit_dir / f"market_scan_{session_date.isoformat()}.jsonl"
        append_jsonl(audit_file, base_result)
        return json_safe(base_result)
    except ScannerError as exc:
        base_result.update({"decision": "NO_TRADE", "error_type": "ScannerError", "reason_code": exc.code, "message": str(exc), "expiry": expiry.isoformat() if expiry else None, "underlying_key": index_row.get("instrument_key") if index_row else None, "oi_label": oi.get("label", "MISSING"), "regime": base_result.get("regime", "UNKNOWN"), "spot": base_result.get("spot", spot_chain or None)})
        # Preserve the last good baseline/snapshots on API errors; do not replace them with empty data.
        try:
            state["schema_version"] = SCHEMA_VERSION
            state["scanner_version"] = VERSION
            state["session_date"] = session_date.isoformat()
            state["last_decision"] = {k: base_result.get(k) for k in ("timestamp", "decision", "reason_code", "signal_key", "spot", "oi_label", "regime")}
            atomic_write_json(config.state_file, state)
            append_jsonl(config.audit_dir / f"market_scan_{session_date.isoformat()}.jsonl", base_result)
        except Exception as persistence_error:
            LOG.error("Could not persist blocked scan (%s); alerts suppressed", persistence_error)
            base_result["reason_code"] = "STATE_SAVE_FAILED"
            base_result["message"] = f"{exc}; state/audit persistence also failed"
        return json_safe(base_result)
    except Exception as exc:
        LOG.exception("Unexpected scanner failure")
        base_result.update({"decision": "NO_TRADE", "error_type": type(exc).__name__, "reason_code": "UNEXPECTED_ERROR", "message": str(exc)[:500]})
        try:
            state["schema_version"] = SCHEMA_VERSION
            state["scanner_version"] = VERSION
            state["session_date"] = session_date.isoformat()
            state["last_decision"] = {k: base_result.get(k) for k in ("timestamp", "decision", "reason_code", "signal_key", "spot", "oi_label", "regime")}
            atomic_write_json(config.state_file, state)
            append_jsonl(config.audit_dir / f"market_scan_{session_date.isoformat()}.jsonl", base_result)
        except Exception:
            base_result["reason_code"] = "STATE_SAVE_FAILED"
        return json_safe(base_result)


def _deliver_pending_notifications(config: Config, state: dict[str, Any], *, dry_run: bool = False) -> None:
    pending = state.get("pending_notifications", [])
    if not pending:
        return
    remaining = []
    for item in pending:
        if item.get("attempts", 0) >= 3:
            item["status"] = "FAILED_MAX_ATTEMPTS"
            remaining.append(item)
            continue
        payload = item.get("payload") or {}
        if dry_run:
            item["status"] = "DRY_RUN_NOT_SENT"
            remaining.append(item)
            continue
        errors = []
        sent = False
        if config.webhook_url:
            try:
                body = json.dumps(json_safe(payload), separators=(",", ":")).encode("utf-8")
                request = urllib.request.Request(config.webhook_url, data=body, headers={"Content-Type": "application/json", "User-Agent": f"NiftyMarketScanner/{VERSION}"}, method="POST")
                with urllib.request.urlopen(request, timeout=10) as response:
                    if 200 <= getattr(response, "status", 200) < 300:
                        sent = True
                    else:
                        errors.append(f"webhook HTTP {response.status}")
            except Exception as exc:
                errors.append(f"webhook {type(exc).__name__}")
        if not sent and config.smtp_host and config.email_sender and config.email_receiver and config.email_password:
            try:
                message = EmailMessage()
                message["Subject"] = f"NIFTY v{VERSION} {payload.get('reason_code')} — {payload.get('selected_contract', {}).get('side')} {payload.get('selected_contract', {}).get('strike')}"
                message["From"] = config.email_sender
                message["To"] = config.email_receiver
                message.set_content(json.dumps(json_safe(payload), indent=2))
                username = config.email_username or config.email_sender
                if config.smtp_port == 465:
                    with smtplib.SMTP_SSL(config.smtp_host, config.smtp_port, timeout=15, context=ssl.create_default_context()) as smtp:
                        smtp.login(username, config.email_password)
                        smtp.send_message(message)
                else:
                    with smtplib.SMTP(config.smtp_host, config.smtp_port, timeout=15) as smtp:
                        smtp.starttls(context=ssl.create_default_context())
                        smtp.login(username, config.email_password)
                        smtp.send_message(message)
                sent = True
            except Exception as exc:
                errors.append(f"email {type(exc).__name__}: {str(exc)[:180]}")
        item["attempts"] = int(item.get("attempts", 0)) + 1
        item["last_attempt_at"] = now_ist().isoformat()
        if sent:
            item["status"] = "SENT"
            state.setdefault("delivered_signal_keys", []).append(item.get("signal_key"))
            state["delivered_signal_keys"] = state["delivered_signal_keys"][-500:]
        else:
            item["status"] = "FAILED" if errors else "NOT_CONFIGURED"
            item["last_error"] = "; ".join(errors) if errors else "No webhook or complete SMTP configuration"
            remaining.append(item)
    state["pending_notifications"] = remaining[-20:]


# ---------- CLI ----------

def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="NIFTY 50 intraday OI + price-structure scanner (no order execution)")
    parser.add_argument("--version", action="version", version=VERSION)
    parser.add_argument("--dry-run", action="store_true", help="Evaluate a scan but do not send queued notifications")
    parser.add_argument("--config-check", action="store_true", help="Validate required configuration without calling APIs")
    args = parser.parse_args(argv)
    logging.basicConfig(level=os.getenv("LOG_LEVEL", "INFO").upper(), format="%(asctime)s %(levelname)s %(message)s")
    try:
        config = Config.from_env()
        if args.config_check:
            print(json.dumps({"version": VERSION, "config": "valid", "state_file": str(config.state_file), "audit_dir": str(config.audit_dir), "notification_configured": bool(config.webhook_url or (config.smtp_host and config.email_sender and config.email_receiver and config.email_password))}))
            return 0
        result = run_scan(config, dry_run=args.dry_run)
        print(json.dumps(json_safe(result), separators=(",", ":"), sort_keys=True))
        return 0 if result.get("reason_code") not in {"UNEXPECTED_ERROR", "STATE_SAVE_FAILED", "API_AUTH_FAILED", "API_PERMISSION_DENIED", "API_HTTP_ERROR", "API_HTTP_403", "API_HTTP_401"} else 1
    except ScannerError as exc:
        result = {"scanner_version": VERSION, "timestamp": now_ist().isoformat(), "decision": "NO_TRADE", "reason_code": exc.code, "error_type": "ScannerError", "message": str(exc)}
        print(json.dumps(result, separators=(",", ":"), sort_keys=True))
        return 1
    except Exception as exc:
        LOG.exception("Fatal configuration/CLI failure")
        print(json.dumps({"scanner_version": VERSION, "timestamp": now_ist().isoformat(), "decision": "NO_TRADE", "reason_code": "UNEXPECTED_ERROR", "error_type": type(exc).__name__, "message": str(exc)[:500]}, separators=(",", ":"), sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
