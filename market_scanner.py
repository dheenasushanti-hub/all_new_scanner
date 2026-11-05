#!/usr/bin/env python3
"""NIFTY scenario engine v116.0.0 — complete standalone analytical scanner.

Completed price bars -> protected structure -> conditional forward scenarios ->
independent setup watches -> fixed risk plan -> one quoted option contract ->
chronological position management -> durable state and notification claims.

Python 3.11+ standard library only. See README.md for configuration,
migration, installation and the precise scope of the supplied validation.
This executable does not submit broker orders or claim calibrated win odds.
"""
from __future__ import annotations


# scanner/__init__.py
__version__ = '116.0.0'


# scanner/core.py
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta, timezone
from math import isfinite
from statistics import median
from typing import Any
IST = timezone(timedelta(hours=5, minutes=30))

class DataError(ValueError):
    pass

def finite_json_float(value):
    """Reject numeric overflow as well as literal NaN/Infinity at ingress."""
    number = float(value)
    if not isfinite(number):
        raise ValueError('Non-finite numeric JSON')
    return number

@dataclass(frozen=True)
class Candle:
    start: datetime
    open: float
    high: float
    low: float
    close: float
    volume: float = 0.0

    def __post_init__(self):
        if self.start.tzinfo is None or self.start.second or self.start.microsecond:
            raise DataError('Candle timestamps must be timezone-aware minute starts')
        vals = (self.open, self.high, self.low, self.close, self.volume)
        if not all((isfinite(v) for v in vals)) or min(self.open, self.high, self.low, self.close) <= 0:
            raise DataError('Invalid candle prices')
        if self.high < max(self.open, self.close, self.low) or self.low > min(self.open, self.close, self.high) or self.volume < 0:
            raise DataError('Invalid candle OHLC or volume')

@dataclass(frozen=True)
class Config:
    max_risk: float = 30.0
    min_rr: float = 1.25
    max_quote_age: float = 45.0
    max_spread_pct: float = 2.0
    max_entry_extension_atr: float = 0.75
    min_bars: int = 6
    min_wall_fraction: float = 0.65
    strike_step: float = 50.0
    stop_buffer: float = 1.0
    no_progress_minutes: int = 12
    premium_hard_loss_pct: float = 25.0
    premium_runner_drawdown_pct: float = 18.0
    watch_minutes: int = 8
    min_stop_atr: float = 0.6
    max_entry_risk_fraction: float = 0.5
    runner_progress_atr: float = 0.3
    forecast_horizon_minutes: int = 15
    session_exit_lead_minutes: int = 20
    entry_cutoff_lead_minutes: int = 30
    # v116 configuration, documented engineering choices; not fitted probabilities.
    oi_nearby_points: float = 400.0
    oi_material_change_fraction: float = 0.005
    oi_horizon_max_seconds: int = 3600
    min_option_volume: float = 1.0
    target_clearance_atr: float = 0.12
    min_intraday_projection_atr: float = 1.25
    max_option_iv: float = 200.0
    max_premium_cost_ratio: float = 0.65

    def __post_init__(self):
        for field in (self.max_risk, self.min_rr, self.max_quote_age, self.max_spread_pct, self.max_entry_extension_atr, self.min_wall_fraction, self.strike_step, self.stop_buffer, self.premium_hard_loss_pct, self.premium_runner_drawdown_pct, self.min_stop_atr, self.runner_progress_atr, self.oi_nearby_points, self.oi_material_change_fraction, self.oi_horizon_max_seconds, self.min_option_volume, self.target_clearance_atr, self.min_intraday_projection_atr, self.max_option_iv, self.max_premium_cost_ratio):
            if not isfinite(field) or field <= 0:
                raise DataError('Invalid strategy configuration')
        if any((not isinstance(v, int) or isinstance(v, bool) for v in (self.min_bars, self.no_progress_minutes, self.watch_minutes))) or self.min_wall_fraction > 1 or self.max_premium_cost_ratio >= 1 or self.oi_material_change_fraction >= 1 or self.min_bars < 6 or (self.no_progress_minutes < 1) or (self.watch_minutes < 1) or (not 0 < self.max_entry_risk_fraction <= 1) or (max(self.premium_hard_loss_pct, self.premium_runner_drawdown_pct) >= 100):
            raise DataError('Invalid strategy configuration')
        if self.max_risk > 30 or self.min_rr < 1.25:
            raise DataError('Approved risk limits cannot be weakened')
        if not isinstance(self.forecast_horizon_minutes, int) or isinstance(self.forecast_horizon_minutes, bool) or (not 3 <= self.forecast_horizon_minutes <= 60):
            raise DataError('Invalid forecast horizon')
        if any((not isinstance(v, int) or isinstance(v, bool) for v in (self.session_exit_lead_minutes, self.entry_cutoff_lead_minutes))) or self.session_exit_lead_minutes < 3 or self.entry_cutoff_lead_minutes < self.session_exit_lead_minutes + 3:
            raise DataError('Entry and exit windows must leave a monitoring interval')

def normalize_candles(raw: list[list[Any]], now: datetime) -> list[Candle]:
    if now.tzinfo is None:
        raise DataError('naive evaluation time')
    today = now.astimezone(IST).date()
    by_time: dict[datetime, Candle] = {}
    for row in raw:
        if len(row) < 5:
            raise DataError('Malformed candle')
        t = datetime.fromisoformat(str(row[0]).replace('Z', '+00:00'))
        if t.tzinfo is None:
            raise DataError('Candle timestamp has no timezone')
        t = t.astimezone(IST)
        if t.date() != today or t + timedelta(minutes=1) > now.astimezone(IST):
            continue
        c = Candle(t, *(float(v) for v in row[1:5]), float(row[5] or 0) if len(row) > 5 else 0.0)
        if t in by_time and by_time[t] != c:
            raise DataError('Conflicting duplicate candles')
        by_time[t] = c
    return [by_time[t] for t in sorted(by_time)]

def validate_latest_start(latest_start: datetime, now: datetime) -> None:
    if latest_start.tzinfo is None or now.tzinfo is None:
        raise DataError('NAIVE_CANDLE_TIME')
    expected = now.astimezone(IST).replace(second=0, microsecond=0) - timedelta(minutes=1)
    if latest_start != expected:
        raise DataError('LATEST_COMPLETED_CANDLE_MISSING')

def validate_candles(bars: list[Candle], now: datetime, minimum: int=9) -> None:
    if len(bars) < minimum:
        raise DataError('INSUFFICIENT_CANDLES')
    validate_latest_start(bars[-1].start, now)
    for a, b in zip(bars, bars[1:]):
        if b.start - a.start != timedelta(minutes=1):
            raise DataError('CANDLE_GAP')

def contiguous_tail(bars: list[Candle]) -> tuple[list[Candle], int]:
    """Discard pre-gap history; management separately checks its full open interval."""
    cut = 0
    for i in range(1, len(bars)):
        if bars[i].start - bars[i - 1].start != timedelta(minutes=1):
            cut = i
    return (bars[cut:], cut)

def aggregate(bars: list[Candle], n: int) -> list[Candle]:
    groups: dict[datetime, list[Candle]] = {}
    for b in bars:
        start = b.start.replace(hour=9, minute=15, second=0, microsecond=0)
        elapsed = int((b.start - start).total_seconds() // 60)
        if elapsed < 0:
            continue
        slot = start + timedelta(minutes=elapsed // n * n)
        groups.setdefault(slot, []).append(b)
    result = []
    for t, g in sorted(groups.items()):
        if len(g) == n and all((c.start == t + timedelta(minutes=i) for i, c in enumerate(g))):
            result.append(Candle(t, g[0].open, max((x.high for x in g)), min((x.low for x in g)), g[-1].close, sum((x.volume for x in g))))
    return result

def atr(bars: list[Candle], n: int=14) -> float:
    ranges = []
    for i, c in enumerate(bars):
        prev = bars[i - 1].close if i else c.open
        ranges.append(max(c.high - c.low, abs(c.high - prev), abs(c.low - prev)))
    return sum(ranges[-n:]) / len(ranges[-n:]) if ranges else 0.0

def pivots(bars: list[Candle]) -> tuple[list[tuple[datetime, float]], list[tuple[datetime, float]]]:
    """Confirmed with one complete right-hand bar, so never see the future."""
    lows = []
    highs = []
    for i in range(2, len(bars) - 1):
        x = bars[i]
        if x.low < min(bars[i - 2].low, bars[i - 1].low) and x.low <= bars[i + 1].low:
            lows.append((x.start, x.low))
        if x.high > max(bars[i - 2].high, bars[i - 1].high) and x.high >= bars[i + 1].high:
            highs.append((x.start, x.high))
    return (lows, highs)

def classify_flow(old_oi: float, new_oi: float, old_price: float, new_price: float, side: str) -> str:
    """Price/OI pattern only; it does not identify initiators or participant positions."""
    if side not in {'CE', 'PE'} or not all((isfinite(x) for x in (old_oi, new_oi, old_price, new_price))) or min(old_oi, new_oi, old_price, new_price) <= 0:
        return 'UNAVAILABLE'
    dp = (new_price - old_price) / old_price
    doi = (new_oi - old_oi) / old_oi
    if abs(dp) < 0.005 or abs(doi) < 0.005:
        return 'UNCHANGED_OR_NOISY'
    return {(True, True): 'LONG_BUILDUP_HYPOTHESIS', (True, False): 'SHORT_COVERING_HYPOTHESIS', (False, True): 'SHORT_BUILDUP_HYPOTHESIS', (False, False): 'LONG_UNWINDING_HYPOTHESIS'}[dp > 0, doi > 0]

# v116 STRATEGY RESEARCH IMPLEMENTATION.
# All regime inference, setups, watches, risk and contract ranking below were
# designed independently of the previous release's trading functions.
# Provider, wire format and persistence facilities are retained for compatibility.

def oi_context(chain: list[dict[str, Any]], spot: float, config: Config) -> dict[str, Any]:
    """All material, near-spot OI concentrations are *candidate* levels.

    CE OI is potential resistance; PE OI potential support. No directional
    inference from OI magnitude alone. OI has no timestamp at the option-chain
    row level: freshness is measured using a captured receipt time.
    """
    output = {'put_support': None, 'call_resistance': None, 'walls': [],
              'meaning': 'Candidate CE resistance / PE support, subject to price test and comparability'}
    for side, label in (('PE','put_support'), ('CE','call_resistance')):
        subset = [r for r in chain if r.get('side') == side
                  and abs(float(r['strike'])-spot) <= config.oi_nearby_points
                  and float(r.get('oi') or 0) > 0]
        if not subset:
            continue
        peak = max(float(r['oi']) for r in subset)
        typical = median(float(r['oi']) for r in subset)
        # A uniform chain is not an OI concentration. Prevent ordinary
        # strikes being mistaken for strong barriers in range or trend days.
        if peak < max(1,typical)*1.20 and len(subset)>=4:
            continue
        candidates=[]
        for r in subset:
            strike=float(r['strike']); oi=float(r['oi']); strength=oi/peak
            if strength < config.min_wall_fraction:
                continue
            candidates.append({'strike': strike,'side':side,'oi':oi,
                               'relative_to_side_max':round(strength,5),
                               'interpretation':'POTENTIAL_SUPPORT' if side=='PE' else 'POTENTIAL_RESISTANCE',
                               'location':'BELOW' if strike < spot else 'ABOVE' if strike > spot else 'AT_SPOT'})
        candidates.sort(key=lambda x:(abs(x['strike']-spot),-x['oi']))
        output['walls'].extend(candidates[:6])
        preferred=[c for c in candidates if (c['strike']<=spot if side=='PE' else c['strike']>=spot)]
        if preferred:
            output[label]=dict(preferred[0])
    output['walls'].sort(key=lambda x:(x['side'], x['strike']))
    return output



def _structure_at(bars: list[Candle]) -> dict[str, Any]:
    """Causal one-pass 3m structure; a boundary can only move upon defended pivots.

    A single 3m close through the defended boundary creates a *pending* break;
    acceptance requires later independent completed candles beyond the level.
    No OI or 15m observation may flip the protected regime by itself.
    """
    if len(bars) < 6:
        raise DataError('OPENING_CANDLE_WARMUP')
    if any(y.start-x.start != timedelta(minutes=1) for x,y in zip(bars,bars[1:])):
        raise DataError('CANDLE_GAP')
    threes = aggregate(bars,3)
    fifteens = aggregate(bars,15)
    if len(threes) < 2:
        raise DataError('COMPLETED_3M_UNAVAILABLE')
    first = threes[:2]
    direction = 'RANGE'
    beginning = first[0].start
    established_at = None
    reversal = None
    pending = None
    support = min(x.low for x in first)
    resistance = max(x.high for x in first)
    boundary_source = 'OPENING_TWO_3M_EXTREMES'
    price_atr = max(atr(bars[:6]), 1.0)
    displacement = first[-1].close-first[0].open
    open_threshold = max(2.0,0.8*price_atr)
    if abs(displacement) >= open_threshold and (first[1].close-first[0].close)*displacement >= 0:
        direction = 'BULLISH' if displacement > 0 else 'BEARISH'
        established_at = (first[-1].start+timedelta(minutes=3)).isoformat()
    prior = first[:]
    pending_accepts = 0
    last_reason = 'OPENING_STRUCTURE' if direction != 'RANGE' else 'OPENING_RANGE'
    # Fold each completed 3m without looking at the remainder of the session.
    for i in range(2,len(threes)):
        c = threes[i]
        end = c.start+timedelta(minutes=3)
        history = threes[:i+1]
        window_atr = max(atr(history[-6:]),1.0)
        buffer = max(1.0,0.12*window_atr)
        # A three-bar confirmed swing uses only the immediately completed right bar.
        confirmed_low = history[-2].low if len(history)>=3 and history[-2].low < history[-3].low and history[-2].low <= history[-1].low else None
        confirmed_high = history[-2].high if len(history)>=3 and history[-2].high > history[-3].high and history[-2].high >= history[-1].high else None
        if direction == 'RANGE':
            # Range must first break on a closed 3m bar, then demonstrate acceptance.
            side = 'BULLISH' if c.close > resistance+buffer else 'BEARISH' if c.close < support-buffer else None
            if side:
                if pending and pending['direction'] == side:
                    pending_accepts += 1
                else:
                    pending = {'direction':side,'level':resistance if side=='BULLISH' else support,
                               'first_at':end.isoformat(),'type':'RANGE_BREAK'}
                    pending_accepts = 0
                if pending_accepts>=1:
                    direction=side
                    established_at=end.isoformat()
                    last_reason='RANGE_BREAK_ACCEPTED'
                    pending=None
                    pending_accepts=0
                    boundary_source='CONFIRMED_RANGE_BOUNDARY'
            else:
                if pending and ((pending['direction']=='BULLISH' and c.close<=resistance) or
                                (pending['direction']=='BEARISH' and c.close>=support)):
                    pending=None
                    pending_accepts=0
                    last_reason='FALSE_RANGE_BREAK'
                if pending is None:
                    support=min(support,c.low)
                    resistance=max(resistance,c.high)
            continue
        sign = 1 if direction=='BULLISH' else -1
        level = support if sign==1 else resistance
        crossed = sign*(c.close-level)<-buffer
        reclaimed = sign*(c.close-level)>buffer
        if crossed:
            next_direction = 'BEARISH' if sign==1 else 'BULLISH'
            if pending is None or pending['direction']!=next_direction:
                pending={'direction':next_direction,'level':level,'first_at':end.isoformat(),
                         'type':'PROTECTED_BOUNDARY_BREAK'}
                pending_accepts=0
                last_reason='PROTECTED_BREAK_PENDING'
            else:
                pending_accepts+=1
            if pending_accepts>=1:
                # Independent subsequent completed 3m acceptance: not a single wick.
                old = direction
                direction=next_direction
                reversal={'direction':direction,'old_direction':old,'level':level,
                          'confirmed_at':end.isoformat(),'evidence':'TWO_SEPARATE_CLOSED_3M_BEYOND_DEFENDED_LEVEL'}
                established_at=end.isoformat()
                last_reason='SUPPORT_BREAK_CONFIRMED' if old=='BULLISH' else 'RESISTANCE_BREAK_CONFIRMED'
                boundary_source='ACCEPTED_REVERSAL_PIVOT'
                pending=None
                pending_accepts=0
                if direction=='BULLISH':
                    support=min(x.low for x in history[-2:])
                    resistance=max(x.high for x in history[-4:])
                else:
                    resistance=max(x.high for x in history[-2:])
                    support=min(x.low for x in history[-4:])
            continue
        if pending and reclaimed:
            last_reason='FALSE_PROTECTED_BREAK_RECLAIMED'
            pending=None
            pending_accepts=0
        # Only a significant, fully defended new swing can ratchet protected levels.
        if pending is None and established_at and end > datetime.fromisoformat(established_at):
            if direction=='BULLISH' and confirmed_low is not None and confirmed_low > support:
                impulse_high=max(x.high for x in history[-4:-1])
                significance=impulse_high-confirmed_low
                if significance >= max(5,0.9*window_atr) and c.close>history[-2].high+buffer:
                    support=confirmed_low
                    boundary_source='DEFENDED_CONFIRMED_3M_HIGHER_LOW'
                    last_reason='SUPPORT_ADVANCED_AFTER_IMPULSE'
            elif direction=='BEARISH' and confirmed_high is not None and confirmed_high < resistance:
                impulse_low=min(x.low for x in history[-4:-1])
                significance=confirmed_high-impulse_low
                if significance >= max(5,0.9*window_atr) and c.close<history[-2].low-buffer:
                    resistance=confirmed_high
                    boundary_source='DEFENDED_CONFIRMED_3M_LOWER_HIGH'
                    last_reason='RESISTANCE_ADVANCED_AFTER_IMPULSE'
    last3=threes[-1]
    recent3='BULLISH' if last3.close>last3.open and last3.close>threes[-2].close else 'BEARISH' if last3.close<last3.open and last3.close<threes[-2].close else 'MIXED'
    if direction=='BULLISH':
        phase = 'BULL_SUPPORT_TEST' if pending else 'BULL_TREND' if recent3=='BULLISH' else 'BULL_PULLBACK'
    elif direction=='BEARISH':
        phase = 'BEAR_RESISTANCE_TEST' if pending else 'BEAR_TREND' if recent3=='BEARISH' else 'BEAR_BOUNCE'
    else:
        phase='RANGE'
    low_piv,high_piv=pivots(threes)
    long_low,long_high=pivots(fifteens)
    context='DEVELOPING'
    if len(fifteens)>=2:
        context='BULLISH' if fifteens[-1].close>fifteens[-2].close else 'BEARISH' if fifteens[-1].close<fifteens[-2].close else 'SIDEWAYS'
    return {'engine_revision':1160,'direction':direction,'state':phase,'support':support,
            'resistance':resistance,'boundary_source':boundary_source,'pending_break':pending,
            'break_confirmed':reversal is not None and last_reason in ('SUPPORT_BREAK_CONFIRMED','RESISTANCE_BREAK_CONFIRMED'),
            'last_reversal':reversal,'reason':last_reason,'established_at':established_at,
            'established_confirmed_at':established_at,'recent_3m':recent3,
            'atr_1m':max(atr(bars),1.0),'atr_3m':max(atr(threes),1.0),
            'last_3m':last3.start.isoformat(),'last_3m_close':last3.close,
            'context_15m':context,'confirmed_pivot_low':low_piv[-1][1] if low_piv else None,
            'confirmed_pivot_high':high_piv[-1][1] if high_piv else None,
            'confirmed_15m_pivot_low':long_low[-1][1] if long_low else None,
            'confirmed_15m_pivot_high':long_high[-1][1] if long_high else None,
            'processed_1m':bars[-1].start.isoformat(),'history_start':bars[0].start.isoformat(),
            'buffer':max(1.0,0.12*max(atr(threes[-6:]),1.0)),
            'price_efficiency':abs(bars[-1].close-bars[0].open)/max(1,sum(abs(b.close-b.open) for b in bars))}


def update_structure(bars, old=None):
    """Cold start and hot scan give identical as-of regime from complete session bars.

    `old` is never used as a strategy seed: obsolete states cannot contaminate
    new calculations. The source candle range must be continuous.
    """
    return _structure_at(bars)


def forecast_market(bars, structure, spot, oi, futures=None):
    d=structure['direction']; pending=structure.get('pending_break')
    boundary=structure.get('support') if d=='BULLISH' else structure.get('resistance') if d=='BEARISH' else None
    if not structure.get('boundary_trusted',True):
        primary='SESSION_STRUCTURE_INCOMPLETE'
    elif pending:
        primary='DEFENDED_BOUNDARY_UNDER_TEST_WAIT_ACCEPTANCE'
    elif d=='BULLISH':
        primary='BULLISH_CONTINUATION' if structure.get('recent_3m')==d else 'BULLISH_PULLBACK_RECOVERY_CONDITIONAL'
    elif d=='BEARISH':
        primary='BEARISH_CONTINUATION' if structure.get('recent_3m')==d else 'BEARISH_BOUNCE_REJECTION_CONDITIONAL'
    else:
        primary='RANGE_RECLAIM_OR_REJECTION'
    evidence=[]; cautions=[]; scenarios=[]
    mixed_oi=oi.get('price_oi_interpretation') or {}
    evidence.extend(mixed_oi.get('evidence') or [])
    cautions.extend(mixed_oi.get('cautions') or [])
    if d in ('BULLISH','BEARISH'):
        evidence.append('DEFENDED_PRICE_STRUCTURE_'+d)
        if structure.get('recent_3m')==d:evidence.append('LAST_COMPLETED_3M_ALIGNED')
        else:cautions.append('WAIT_FOR_PRICE_RESUMPTION')
        if structure.get('context_15m')==d:evidence.append('COMPLETED_15M_ALIGNED')
        elif structure.get('context_15m')!='DEVELOPING':cautions.append('15M_MIXED_OR_OPPOSED')
        wall=oi.get('put_support' if d=='BULLISH' else 'call_resistance') or {}
        if oi.get('fresh_snapshot') and float(wall.get('oi_change') or 0)>0:evidence.append('NEAR_DEFENDED_OI_WALL_STRENGTHENS')
        pattern=(futures or {}).get('price_oi_pattern')
        supportive={'LONG_BUILDUP_HYPOTHESIS','SHORT_COVERING_HYPOTHESIS'} if d=='BULLISH' else {'SHORT_BUILDUP_HYPOTHESIS','LONG_UNWINDING_HYPOTHESIS'}
        if pattern in supportive:evidence.append('FUTURES_PRICE_OI_HYPOTHESIS_COMPATIBLE')
        elif pattern and pattern not in ('UNAVAILABLE','UNCHANGED_OR_NOISY'):cautions.append('FUTURES_FLOW_MIXED')
        alt='BEARISH' if d=='BULLISH' else 'BULLISH'
        scenarios=[{'direction':d,'condition':'PROTECTED_LEVEL_HOLDS_AND_NEW_COMPLETED_3M_PLUS_1M_TRIGGER','boundary':boundary,'action':'WATCH_CONTINUATION'},
                   {'direction':alt,'condition':'TWO_SEPARATE_COMPLETED_3M_CLOSES_BEYOND_PROTECTED_LEVEL','boundary':boundary,'action':'REASSESS_AFTER_CONFIRMED_REVERSAL'}]
    else:
        for wall,side in (('put_support','BULLISH'),('call_resistance','BEARISH')):
            if oi.get(wall):scenarios.append({'direction':side,'boundary':oi[wall]['strike'],'condition':'PRICE_RETEST_AND_1M_RECLAIM_OR_REJECTION_WITH_3M_CONFIRMATION','action':'WATCH_RANGE_SETUP'})
    if not structure.get('boundary_trusted',True):cautions.append('SESSION_OPENING_HISTORY_MISSING')
    if pending:cautions.append('NO_COUNTERTREND_ENTRY_WHILE_BREAK_IS_UNCONFIRMED')
    return {'as_of':(bars[-1].start+timedelta(minutes=1)).isoformat(),
            'primary_scenario':primary,'directional_thesis':d,'protected_boundary':boundary,
            'invalidation_requires':'TWO_SEPARATE_CLOSED_3M_ACCEPTANCES_BEYOND_DEFENDED_PRICE_LEVEL',
            'entry_readiness':'ASSESS_TRIGGER' if structure.get('boundary_trusted',True) and not pending and structure.get('recent_3m')==d and d!='RANGE' else 'WAIT',
            'supporting_evidence':evidence,'cautions':cautions,'scenarios':scenarios,
            'evidence_strength':'PRICE_CONFIRMED' if evidence else 'DEVELOPING',
            'strength_is_probability':False,'spot':spot,'put_support':oi.get('put_support'),
            'call_resistance':oi.get('call_resistance')}


def enrich_oi_context(context, comparison, bars, spot, fresh=True, config=None):
    """Price tests + matched OI changes inform candidate barriers; no OI-only trade.

    Soft OI concentrations remain VISIBLE to risk rather than being discarded
    simply because they do not meet the stronger hard-confirmation threshold.
    """
    config=config or Config()
    output=dict(context, fresh_snapshot=bool(fresh), comparability=comparison.get('status'))
    matched=comparison.get('nearby_changes') or []
    baseline=comparison.get('session_baseline_oi_changes') or []
    index={(x.get('side'),float(x['strike'])):x for x in matched}
    baseline_index={(x.get('side'),float(x['strike'])):x for x in baseline}
    band=max(2.0,0.2*atr(bars))
    expanded=[]
    for row in context.get('walls',[]):
        wall=dict(row); side=wall['side']; strike=wall['strike']
        near=index.get((side,strike)); longer=baseline_index.get((side,strike))
        change=near.get('oi_change') if near else None
        wall.update(oi_change=change,
                    oi_change_pct=100*change/near['previous_oi'] if near and near.get('previous_oi') else None,
                    session_oi_change=longer.get('oi_change') if longer else None,
                    pattern=near.get('classification') if near else 'UNAVAILABLE')
        recent=bars[-12:]
        tests=sum(1 for c in recent if c.low<=strike+band and c.close>=strike+band*0.25) if side=='PE' else sum(1 for c in recent if c.high>=strike-band and c.close<=strike-band*0.25)
        wall['price_test_count']=tests
        wall['price_rejection_confirmed']=tests>=2
        wall['hard_barrier']=bool(fresh and near and float(near.get('previous_oi') or 0)>0
            and change/near['previous_oi']>=config.oi_material_change_fraction and tests>=2)
        # A dominant, near-spot wall is a real potential obstacle even without
        # directional confirmation. It can be cleared by accepted price action.
        wall['barrier_status']='CONFIRMED' if wall['hard_barrier'] else 'POTENTIAL'
        expanded.append(wall)
    output['walls']=expanded
    for label,side in (('put_support','PE'),('call_resistance','CE')):
        item=output.get(label)
        output[label]=next((x for x in expanded if item and x['strike']==item['strike'] and x['side']==side),None)
    output['oi_horizons']=comparison.get('horizons',[])
    return output



def price_oi_evidence(context, comparison, structure, spot):
    """Interpret matched OI by PRICE LOCATION and DEFENDED thesis only.

    Positive CE OI near a rejected overhead level can reinforce resistance;
    positive PE OI near defended support can reinforce support. The opposite
    can reflect absorption, hedges or unwinding: no participant intent inferred.
    """
    price_thesis=structure.get('direction')
    report={'bias':'NEUTRAL','evidence':[],'cautions':[],'horizon_count':len(comparison.get('horizons') or []),
            'source_quality':comparison.get('status','BASELINE_ONLY'),
            'participant_intent_inferred':False}
    votes={'BULLISH':0.0,'BEARISH':0.0}
    for w in context.get('walls',[]):
        oi=float(w.get('oi') or 0)
        relative=float(w.get('relative_to_side_max') or 0)
        change=w.get('oi_change')
        if change is None or not oi:continue
        interval_change=float(change)/max(1.,oi)
        if abs(interval_change)<0.005:continue
        strike=float(w['strike'])
        price_near=abs(spot-strike)<=max(20.,context.get('atr_1m',1.)*1.5)
        if not price_near:continue
        if w['side']=='PE' and spot>=strike:
            if interval_change>0 and w.get('price_test_count',0)>0:
                report['evidence'].append('PE_OI_INCREASE_AT_HELD_SUPPORT')
                votes['BULLISH']+=min(relative,1.)
            elif interval_change<0 and spot-strike<context.get('atr_1m',1.)*0.6:
                report['cautions'].append('NEARBY_PE_SUPPORT_OI_DECREASES')
        elif w['side']=='CE' and spot<=strike:
            if interval_change>0 and w.get('price_test_count',0)>0:
                report['evidence'].append('CE_OI_INCREASE_AT_REJECTED_RESISTANCE')
                votes['BEARISH']+=min(relative,1.)
            elif interval_change<0 and strike-spot<context.get('atr_1m',1.)*0.6:
                report['cautions'].append('OVERHEAD_CE_OI_DECREASES')
    if votes['BULLISH']>votes['BEARISH']+0.5:report['bias']='BULLISH_SUPPORT_HYPOTHESIS'
    elif votes['BEARISH']>votes['BULLISH']+0.5:report['bias']='BEARISH_RESISTANCE_HYPOTHESIS'
    if price_thesis=='BULLISH' and report['bias']=='BEARISH_RESISTANCE_HYPOTHESIS':
        report['cautions'].append('OI_RESISTANCE_VS_BULLISH_STRUCTURE_PRICE_CONFIRMATION_REQUIRED')
    if price_thesis=='BEARISH' and report['bias']=='BULLISH_SUPPORT_HYPOTHESIS':
        report['cautions'].append('OI_SUPPORT_VS_BEARISH_STRUCTURE_PRICE_CONFIRMATION_REQUIRED')
    report['votes']=votes
    return report

def _candidate_at(bars, structure, config, context):
    """Generate conditional price triggers from completed 1m and closed 3m only."""
    if len(bars)<config.min_bars or len(aggregate(bars,3))<2:return []
    c,p=bars[-1],bars[-2]
    d=structure['direction']; a=max(atr(bars),1.0)
    t=(c.start+timedelta(minutes=1)).isoformat()
    threes=aggregate(bars,3)
    last_completed=(threes[-1].start+timedelta(minutes=3))
    if c.start+timedelta(minutes=1)-last_completed>timedelta(minutes=5):return []
    results=[]
    for side in ('BULLISH','BEARISH'):
        sign=1 if side=='BULLISH' else -1
        trend=d==side and not structure.get('pending_break')
        if d in ('BULLISH','BEARISH') and not trend:continue
        three=threes[-1]
        if side=='BULLISH':
            three_aligned=three.close>three.open and three.close>=threes[-2].close
            body=c.close-c.open
            momentum=(c.close>p.high and c.close>=p.close)
            recovery=(c.low<=p.low+0.15*a and c.close>p.high and p.close<=p.open)
            price_stop=min(x.low for x in bars[-3:])-config.stop_buffer
            level=context.get('put_support') or {}
            wall=level.get('strike')
            wall_reclaim=wall is not None and min(x.low for x in bars[-4:])<=wall+0.3*a and c.close>wall+0.1*a and c.close>p.high
            boundary=structure.get('support')
        else:
            three_aligned=three.close<three.open and three.close<=threes[-2].close
            body=c.open-c.close
            momentum=(c.close<p.low and c.close<=p.close)
            recovery=(c.high>=p.high-0.15*a and c.close<p.low and p.close>=p.open)
            price_stop=max(x.high for x in bars[-3:])+config.stop_buffer
            level=context.get('call_resistance') or {}
            wall=level.get('strike')
            wall_reclaim=wall is not None and max(x.high for x in bars[-4:])>=wall-0.3*a and c.close<wall-0.1*a and c.close<p.low
            boundary=structure.get('resistance')
        if body<max(0.4,0.1*a) or not three_aligned:continue
        if trend and boundary is not None and sign*(c.close-boundary)<=0:continue
        if trend:
            kinds=[]
            if momentum:
                prev_range=bars[-6:-1]
                prior_extreme=max(x.high for x in prev_range) if sign==1 else min(x.low for x in prev_range)
                kinds.append('TREND_BREAKOUT' if sign*(c.close-prior_extreme)>0 else 'OPENING_MOMENTUM' if len(bars)<=12 else 'TREND_CONTINUATION')
            if recovery or wall_reclaim:
                kinds.append('TREND_SUPPORT_RECLAIM' if sign==1 else 'TREND_RESISTANCE_REJECTION')
            protected=structure.get('support' if sign==1 else 'resistance')
            if protected is not None and any((x.low < protected if sign==1 else x.high > protected) for x in bars[-4:-1]) and sign*(c.close-protected)>0 and momentum:
                kinds.insert(0,'FALSE_BREAK_RECLAIM' if sign==1 else 'FALSE_BREAK_REJECTION')
            if structure.get('reason')=='RANGE_BREAK_ACCEPTED' and momentum:
                kinds.insert(0,'ACCEPTED_RANGE_BREAKOUT' if sign==1 else 'ACCEPTED_RANGE_BREAKDOWN')
            recent_reversal=structure.get('last_reversal') or {}
            if recent_reversal.get('direction')==side and datetime.fromisoformat(t)-datetime.fromisoformat(recent_reversal['confirmed_at'])<=timedelta(minutes=8) and momentum:
                kinds.insert(0,'CONFIRMED_REVERSAL')
        else:
            kinds=[]
            if wall_reclaim or recovery:
                kinds=['RANGE_SUPPORT_RECLAIM' if sign==1 else 'RANGE_RESISTANCE_REJECTION']
            # 3m accepted range-break is *not* yet a trend until structure flips.
        for kind in dict.fromkeys(kinds):
            # Tactical stop is a real observed candle extreme; never clamp to 30.
            invalid=price_stop
            if side=='BULLISH' and invalid>=c.close or side=='BEARISH' and invalid<=c.close:continue
            results.append({'direction':side,'kind':kind,'trigger':c.close,
                            'confirmed_at':t,'invalidation':invalid,
                            'atr_1m':a,'stop_role':'RECENT_COMPLETED_1M_PRICE_EXTREME',
                            'protected_thesis_boundary':boundary,'three_confirmed_at':last_completed.isoformat(),
                            'evidence':['COMPLETE_1M_TRIGGER','COMPLETED_3M_DIRECTION','PROTECTED_REGIME_OR_RANGE_LEVEL']})
    return results


def make_setups(bars, structure, spot, config, context):
    result=[]
    for back in range(min(3,len(bars)-config.min_bars+1)):
        prefix=bars[:len(bars)-back] if back else bars
        asof=_structure_at(prefix)
        # Current chain was captured after earlier candles; do not backdate it.
        # Reconstructed historical signals may only use completed price bars.
        historical_context = context if not back else {}
        for setup in _candidate_at(prefix,asof,config,historical_context):
            # A later completed candle cannot validate an earlier setup if its stop was touched.
            follow=bars[len(prefix):]
            sign=1 if setup['direction']=='BULLISH' else -1
            if any(c.low<=setup['invalidation'] if sign==1 else c.high>=setup['invalidation'] for c in follow):continue
            result.append(setup)
    return result


def make_setup(bars, structure, spot, config, context=None):
    choices=make_setups(bars,structure,spot,config,context or {})
    return choices[0] if choices else None


def gate_candidate(setup, structure):
    d=setup.get('direction'); thesis=structure.get('direction')
    if d not in ('BULLISH','BEARISH'):return False,'INVALID_DIRECTION'
    if structure.get('pending_break'):return False,'PROTECTED_BOUNDARY_BREAK_UNCONFIRMED'
    if thesis=='RANGE':
        return (bool(str(setup.get('kind','')).startswith('RANGE_')),
                'RANGE_PRICE_CONFIRMED' if str(setup.get('kind','')).startswith('RANGE_') else 'UNCONFIRMED_RANGE_DIRECTION')
    if thesis!=d:return False,'PROTECTED_THESIS_OPPOSES_ENTRY'
    level=structure.get('support' if d=='BULLISH' else 'resistance')
    if level is not None and setup.get('trigger') is not None and (1 if d=='BULLISH' else -1)*(float(setup['trigger'])-float(level))<=0:
        return False,'PROTECTED_LEVEL_NOT_RECLAIMED'
    return True,'ALIGNED_WITH_DEFENDED_STRUCTURE'


def refresh_setup_watches(bars, structure, spot, now, prior, config, context, fresh_candidates=None):
    fresh=list(fresh_candidates) if fresh_candidates is not None else make_setups(bars,structure,spot,config,context)
    bykey={}
    for row in fresh+list(prior or []):
        if not isinstance(row,dict) or not all(k in row for k in ('confirmed_at','direction','invalidation','trigger','kind')):continue
        key=(row['confirmed_at'],row['direction'],row['kind'],round(float(row['trigger']),3))
        bykey.setdefault(key,dict(row))
    eligible=[]; retained=[]; diagnostics=[]
    for s in sorted(bykey.values(),key=lambda r:r['confirmed_at'],reverse=True):
        try:
            at=datetime.fromisoformat(s['confirmed_at']); age=(now-at).total_seconds()
            sign=1 if s['direction']=='BULLISH' else -1
            follow=[c for c in bars if c.start>=at]
            allowed,gate=gate_candidate(s,structure)
            reason=None
            if age<0 or age>60*config.watch_minutes:reason='WATCH_EXPIRED'
            elif bars[0].start>at:reason='WATCH_HISTORY_UNAVAILABLE'
            elif any(c.low<=s['invalidation'] if sign==1 else c.high>=s['invalidation'] for c in follow):reason='WATCH_STOP_TOUCHED'
            elif sign*(spot-s['invalidation'])<=0:reason='WATCH_STOP_BREACHED_LIVE'
            elif not allowed:reason=gate
            if reason:
                diagnostics.append({'setup':s,'reason':reason,'age_seconds':age});continue
            retained.append(s)
            extension=sign*(spot-float(s['trigger']))
            r=sign*(spot-float(s['invalidation']))
            three_end=datetime.fromisoformat(structure['last_3m'])+timedelta(minutes=3)
            prior_confirmed=datetime.fromisoformat(s.get('three_confirmed_at',s['confirmed_at']))
            if structure.get('recent_3m')!=s['direction']:
                reason='WAIT_FOR_NEW_COMPLETED_3M_ALIGNMENT'
            elif three_end<prior_confirmed:
                reason='SETUP_3M_CONFIRMATION_MISSING'
            elif extension < -max(0.5,0.15*atr(bars)):
                reason='TRIGGER_NOT_RECLAIMED'
            elif extension>config.max_entry_extension_atr*max(atr(bars),1):
                reason='STALE_ENTRY_CHASE_LIMIT'
            elif r<=0 or extension>config.max_entry_risk_fraction*r:
                reason='ENTRY_RISK_EXTENSION_LIMIT'
            else:
                eligible.append(s);reason='PRICE_STRUCTURE_AND_3M_READY'
            diagnostics.append({'setup':s,'reason':reason,'age_seconds':age})
        except (KeyError,ValueError,TypeError):
            diagnostics.append({'setup':s,'reason':'INVALID_SAVED_WATCH'})
    return eligible,retained[:30],diagnostics


def build_level_book(bars, structure, oi, spot, prior_day=None, futures=None):
    """Causal multi-source level inventory; source and significance always audited.

    Opening 6m, previous session OHLC, confirmed 3m/15m pivots, defended thesis,
    relevant option OI concentrations and *validated* futures price VWAP.
    These are candidates; OI is not promoted to a confirmed price rejection.
    """
    threes=aggregate(bars,3); fifteens=aggregate(bars,15)
    data=[]
    def add(price, source, kind='PRICE', weight=1.0, **extra):
        if price is None:return
        try:
            x=float(price)
            if x>0 and isfinite(x):data.append({'price':x,'source':source,'kind':kind,'significance':weight,**extra})
        except (TypeError,ValueError):return
    if len(bars)>=6:
        add(max(x.high for x in bars[:6]),'OPENING_SIX_MINUTE_HIGH',weight=2.2)
        add(min(x.low for x in bars[:6]),'OPENING_SIX_MINUTE_LOW',weight=2.2)
    if prior_day:
        for field in ('high','low','close'):
            add(prior_day.get(field),'PREVIOUS_SESSION_'+field.upper(),weight=1.7 if field!='close' else 1.25)
    add(structure.get('support'),'PROTECTED_SUPPORT',weight=2.7)
    add(structure.get('resistance'),'PROTECTED_RESISTANCE',weight=2.7)
    for label in ('confirmed_pivot_low','confirmed_pivot_high','confirmed_15m_pivot_low','confirmed_15m_pivot_high'):
        add(structure.get(label),label.upper(),weight=1.85 if '15m' in label else 1.5)
    lows, highs=pivots(threes)
    for _,price in lows[-5:]:add(price,'CONFIRMED_3M_PIVOT_SUPPORT',weight=1.4)
    for _,price in highs[-5:]:add(price,'CONFIRMED_3M_PIVOT_RESISTANCE',weight=1.4)
    # Completed 15m context is optional at the open; 09:21 eligibility intact.
    if len(fifteens)>=2:
        add(max(x.high for x in fifteens[-2:]),'COMPLETED_15M_CONTEXT_HIGH',weight=1.25)
        add(min(x.low for x in fifteens[-2:]),'COMPLETED_15M_CONTEXT_LOW',weight=1.25)
    for wall in oi.get('walls',[]):
        add(wall.get('strike'),'OI_'+str(wall.get('side')),kind='OI',
            weight=1.0+float(wall.get('relative_to_side_max') or 0),
            oi=float(wall.get('oi') or 0), price_rejection_confirmed=bool(wall.get('price_rejection_confirmed')),
            hard_barrier=bool(wall.get('hard_barrier')),
            oi_change=wall.get('oi_change'),barrier_status=wall.get('barrier_status','POTENTIAL'))
    f=futures or {}
    if f.get('status') not in ('UNAVAILABLE','STALE'):
        add(f.get('candle_vwap_estimate'),'FUTURES_COMPLETED_CANDLE_VWAP_ESTIMATE',weight=1.15)
    data.sort(key=lambda x:(x['price'],-x['significance']))
    # Deduplicate identical source/price (not different independent evidence).
    unique=[];seen=set()
    for x in data:
        key=(x['source'],round(x['price'],2))
        if key not in seen:unique.append(x);seen.add(key)
    opening=(max(x.high for x in bars[:6])-min(x.low for x in bars[:6])) if len(bars)>=6 else 0.0
    impulse=(max(x.high for x in bars[-9:])-min(x.low for x in bars[-9:])) if bars else 0.0
    return {'levels':unique,'opening_range_height':opening,
            'recent_impulse_height':impulse,'atr_1m':max(atr(bars),1.0),
            'level_source_count':len(unique)}


def contextual_futures_alignment(futures, structure, spot):
    """Futures confirms/conflicts price thesis, but cannot by itself reverse it."""
    d=structure.get('direction');f=futures or {};pattern=f.get('price_oi_pattern')
    if not f or f.get('status') in ('UNAVAILABLE','STALE'):
        return {'status':'UNAVAILABLE','trade_veto':False}
    supportive={'BULLISH':{'LONG_BUILDUP_HYPOTHESIS','SHORT_COVERING_HYPOTHESIS'},
                'BEARISH':{'SHORT_BUILDUP_HYPOTHESIS','LONG_UNWINDING_HYPOTHESIS'}}
    alignment='NEUTRAL'
    if pattern in supportive.get(d,set()):alignment='SUPPORTIVE_HYPOTHESIS'
    elif pattern not in (None,'UNAVAILABLE','UNCHANGED_OR_NOISY') and d in supportive:
        alignment='CONFLICTING_HYPOTHESIS'
    vwap=f.get('candle_vwap_estimate')
    location='UNKNOWN'
    if vwap is not None and f.get('price'):
        location='ABOVE' if float(f['price'])>float(vwap) else 'BELOW'
    return {'status':'OBSERVED','alignment':alignment,'vwap_location':location,
            'pattern':pattern,'price_basis_points':float(f['price'])-spot if f.get('price') else None,
            'trade_veto':False,'certainty':'HYPOTHESIS_NOT_PARTICIPANT_INTENT'}

def risk_plan(setup,spot,context,config):
    """Real structural stop; nearest material obstruction; never clip to eligibility.

    In a true directional breakout the price must have ALREADY accepted above
    a barrier before it is excluded. An untested OI wall is a risk flag, not a
    proof of resistance, yet it cannot silently disappear from target analysis.
    """
    d=setup.get('direction')
    if d not in ('BULLISH','BEARISH') or not isfinite(float(spot)) or spot<=0:
        return None,'INVALID_ENTRY'
    sign=1 if d=='BULLISH' else -1
    a=max(1.,float(setup.get('atr_1m') or context.get('atr_1m') or 1))
    raw=float(setup['invalidation'])
    initial=sign*(spot-raw)
    if not isfinite(initial) or initial<=0:return None,'STOP_ON_WRONG_SIDE'
    # Volatility floor expands outward; never compress a genuine structural stop.
    stop=spot-sign*max(initial,config.min_stop_atr*a)
    risk=sign*(spot-stop)
    if risk>config.max_risk+1e-8:return None,'STOP_TOO_WIDE'
    if risk<1:return None,'STOP_TOO_TIGHT_FOR_NOISE'
    minimum=risk*config.min_rr
    levels=context.get('levels') or []
    # Compatibility for isolated callers that supply the former context fields.
    if not levels:
        for name in ('price_resistance','minor_resistance','price_support','minor_support'):
            if context.get(name) is not None:
                levels.append({'price':float(context[name]),'source':name,'kind':'PRICE','significance':2})
        for w in context.get('walls',[]):
            levels.append({'price':float(w['strike']),'source':'OI_'+w['side'],'kind':'OI',
                           'significance':1.0+float(w.get('relative_to_side_max') or 0),
                           'price_rejection_confirmed':w.get('price_rejection_confirmed',False),
                           'hard_barrier':w.get('hard_barrier',False)})
        for side,name in (('CE','call_resistance'),('PE','put_support')):
            w=context.get(name) or {}
            if w.get('strike') is not None:
                levels.append({'price':float(w['strike']),'source':'OI_'+side,'kind':'OI',
                               'significance':1+float(w.get('relative_to_side_max') or 0),
                               'price_rejection_confirmed':w.get('price_rejection_confirmed',False),
                               'hard_barrier':w.get('hard_barrier',False)})
    obstructions=[]
    for level in levels:
        try:
            px=float(level['price'])
            gap=sign*(px-spot)
            if not isfinite(px) or gap<=0.25:continue
            side=str(level.get('source',''))
            if level.get('kind')=='OI' and (('CE' not in side and d=='BULLISH') or ('PE' not in side and d=='BEARISH')):
                continue
            # A strong OI concentration or a confirmed price level is a barrier
            # candidate. Include potential walls in constraints, with uncertainty
            # clearly labelled instead of pretending they are unimportant.
            quality=float(level.get('significance') or 1)
            if level.get('kind')=='OI' and quality<1.5 and not level.get('hard_barrier'):
                continue
            if level.get('kind','PRICE')=='PRICE' and quality<1.4:
                continue
            obstructions.append({**level,'distance':gap})
        except (ValueError,TypeError,KeyError):continue
    obstructions.sort(key=lambda x:(x['distance'],-float(x.get('significance') or 0)))
    target_source='MEASURED_PRICE_SWING_PROJECTION'
    if obstructions:
        first=obstructions[0]
        if first['distance']+1e-8<minimum:
            return None,'TARGET_ROOM_INSUFFICIENT_NEAREST_'+str(first.get('kind','LEVEL'))
        t1=float(first['price']);target_source=str(first.get('source'))
    else:
        # No observed opposing barrier: use bounded continuation projection,
        # not an arbitrary round-number target or invented resistance level.
        opening=float(context.get('opening_range_height') or 0)
        swing=float(context.get('recent_impulse_height') or 0)
        projection=max(minimum,config.min_intraday_projection_atr*a,
                       min(max(opening,swing),3*a) if max(opening,swing)>0 else 0)
        t1=spot+sign*projection
    rr=sign*(t1-spot)/risk
    if rr+1e-8<config.min_rr:return None,'UNDERLYING_RR_BELOW_MINIMUM'
    next_levels=[x for x in obstructions if sign*(float(x['price'])-t1)>max(0.5,0.05*a)]
    t2=float(next_levels[0]['price']) if next_levels else t1+sign*max(risk,a)
    plan={'entry_underlying':spot,'stop_underlying':round(stop,5),'risk_points':round(risk,5),
          't1_underlying':round(t1,5),'t2_underlying':round(t2,5),'underlying_rr':round(rr,5),
          'target_source':target_source,'target_quality':'OBSERVED_OBSTRUCTION' if obstructions else 'CAUSAL_VOLATILITY_PROJECTION',
          'fixed_targets':True,'intermediate_barriers':[dict(x) for x in obstructions if x['distance']<=abs(t2-spot)+0.01],
          'nearest_opposing_level':obstructions[0] if obstructions else None,
          'structural_invalidation_requested':raw,
          'volatility_floor_used':risk>initial+1e-8,
          'projected_target_not_historical_resistance':not bool(obstructions)}
    return plan,'OK'



def select_contract(chain,quotes,direction,scenario,spot,now,expiry,config):
    """Rank liquid current-expiry contracts; deterministic transparent rejection.

    Scenario offsets: range/reversal CE ATM-1,-2, PE ATM+1,+2.
    Trend: ATM or first ITM; the latter is preferred for theta resilience when
    comparable. Volatility is assessed as a sensitivity/ranking input, not a
    deterministic or calibrated premium prediction.
    """
    side='CE' if direction=='BULLISH' else 'PE'
    relevant=[r for r in chain if r.get('side')==side and r.get('expiry')==expiry]
    strikes=sorted({float(r['strike']) for r in relevant})
    if not strikes:return None,[{'reason':'NO_MATCHING_CONTRACTS'}]
    atm=min(strikes,key=lambda x:(abs(x-spot),x))
    offsets=((-1,-2) if side=='CE' else (1,2)) if scenario in ('RANGE','REVERSAL') else ((0,-1) if side=='CE' else (0,1))
    allowed={round(atm+n*config.strike_step,5):n for n in offsets}
    candidate_rows=[r for r in relevant if float(r['strike']) in allowed]
    max_vol=max([float(r.get('volume') or 0) for r in candidate_rows]+[1.0])
    ranked=[];diag=[]
    minutes_remaining=(datetime.fromisoformat(expiry+'T15:30:00+05:30')-now).total_seconds()/60
    if minutes_remaining<=0:return None,[{'reason':'CONTRACT_AFTER_EXPIRY_CUTOFF'}]
    for r in candidate_rows:
        strike=float(r['strike']);key=r.get('instrument_key');q=quotes.get(key)
        def reject(reason):diag.append({'instrument_key':key,'strike':strike,'reason':reason})
        if not q:reject('QUOTE_MISSING');continue
        try:
            stamped=parse_feed_timestamp(q['timestamp']);age=(now-stamped).total_seconds()
            bid=float(q['bid']);ask=float(q['ask']);bq=float(q['bid_qty']);aq=float(q['ask_qty'])
            vol=float(r.get('volume') or 0);lot=float(r['lot_size'])
            # Missing Greeks are not zero: zero would make a contract look
            # artificially safer and less costly in the ranking and stress.
            delta=float(r['delta']);gamma=float(r['gamma']);theta=float(r['theta'])
            raw_vega=r.get('vega');raw_iv=r.get('iv')
            iv=float(raw_iv) if raw_iv is not None else None
            vega=float(raw_vega) if raw_vega is not None else None
            numerics=[bid,ask,bq,aq,vol,lot,delta,gamma,theta]
            if iv is not None:numerics.append(iv)
            if vega is not None:numerics.append(vega)
            if not all(isfinite(x) for x in numerics):reject('NONFINITE_CONTRACT_OR_QUOTE');continue
            if gamma < 0:reject('INVALID_NEGATIVE_GAMMA');continue
            if not -2<=age<=config.max_quote_age:reject('QUOTE_STALE_OR_CLOCK_SKEW');continue
            if lot<=0 or int(lot)!=lot or isinstance(r['lot_size'],bool):reject('INVALID_LIVE_LOT_SIZE');continue
            if min(bid,ask)>0 and ask>=bid and vol>=config.min_option_volume:pass
            else:reject('INVALID_BID_ASK_OR_VOLUME');continue
            if min(bq,aq)<lot:reject('INSUFFICIENT_LIVE_LOT_BID_ASK_DEPTH');continue
            if (side=='CE' and delta<=0) or (side=='PE' and delta>=0) or not 0.30<=abs(delta)<=0.85:
                reject('DELTA_SIGN_OR_RANGE_INVALID');continue
            if iv is not None and not 0<iv<=config.max_option_iv:reject('IMPOSSIBLE_OR_EXTREME_IV');continue
            spread=200*(ask-bid)/(ask+bid)
            if spread>config.max_spread_pct:reject('SPREAD_TOO_WIDE');continue
            # No external IV forecast. The shock is an engineering uncertainty
            # envelope; vega's provider convention is not presumed to be a fill.
            implied_shift=max(0,abs(vega or 0))
            near_expiry=minutes_remaining<390
            theta_cost=max(0,-theta)*15/1440
            iv_stress=implied_shift*1.0
            # A one-lot round-trip cost and ordinary daily theta burden should
            # not overwhelm the option's responsiveness to a 30-point move.
            projected_30pt=30*abs(delta)+.5*gamma*30**2
            total_friction=(ask-bid)+theta_cost+0.25*iv_stress
            if projected_30pt<=total_friction:reject('FRICTION_EXCEEDS_30PT_SENSITIVITY');continue
            stressed_loss=(30*abs(delta)+max(0,gamma)*30**2/2 + theta_cost+iv_stress+ask-bid)
            if stressed_loss/max(ask,0.01)>config.max_premium_cost_ratio:
                reject('OPTION_STRESS_EXCEEDS_PREMIUM_LIMIT');continue
            delta_score=max(0,1-abs(abs(delta)-(0.60 if scenario in ('RANGE','REVERSAL') else 0.56))/0.40)
            spread_score=max(0,1-spread/config.max_spread_pct)
            depth_score=min(1,min(bq,aq)/lot)
            volume_score=min(1,(vol/max_vol)**0.25)
            decay_score=max(0,1-min(1,theta_cost/max(ask,0.01)*25))
            gamma_score=max(0,1-min(1,abs(gamma)*100))
            # Relative vega/IV score acts as caution, never invents a volatility forecast.
            iv_score=0.65 if iv is None else max(0,1-abs(iv-16)/max(30,iv))
            vega_score=0.65 if vega is None else max(0,1-min(1,abs(vega)*1/max(ask,.01)))
            moneyness_score=1 if allowed[strike] in (-1,1) else 0.94
            stress_score=max(0,1-min(1,total_friction/max(projected_30pt,0.01)))
            score=(.25*delta_score+.23*spread_score+.10*depth_score+
                   .07*volume_score+.07*decay_score+.05*gamma_score+
                   .07*iv_score+.05*vega_score+.05*moneyness_score+.06*stress_score)
            candidate={'instrument_key':key,'strike':strike,'expiry':expiry,'side':side,
                       'lot_size':int(lot),'bid':bid,'ask':ask,'bid_qty':bq,'ask_qty':aq,
                       'volume':vol,'delta':delta,'gamma':gamma,'theta':theta,'iv':iv,'vega':vega,
                       'spread_pct':spread,'quote_age_seconds':round(age,3),
                       'quote_timestamp':stamped.isoformat(),'atm':atm,'offset_steps':allowed[strike],
                       'offset':allowed[strike],'selection_regime':scenario,
                       'execution_score':round(score,6),'selection_score':round(score,6),
                       'score_is_probability':False,
                       'stress_30pt_option_premium_loss_estimate':round(stressed_loss,4),
                       'option_friction_estimate':round(total_friction,4),
                       'expiry_minutes_remaining_at_quote':round(minutes_remaining,2),
                       'selection_components':{'delta':round(delta_score,4),'spread':round(spread_score,4),
                            'depth':round(depth_score,4),'volume':round(volume_score,4),
                            'theta':round(decay_score,4),'gamma':round(gamma_score,4),
                            'iv':round(iv_score,4),'vega':round(vega_score,4),
                            'moneyness':round(moneyness_score,4),'stress':round(stress_score,4)}}
            ranked.append((score,candidate))
        except (KeyError,ValueError,TypeError,OverflowError):reject('MALFORMED_CANDIDATE')
    if not ranked:return None,diag or [{'reason':'NO_LIQUID_CANDIDATE'}]
    ranked.sort(key=lambda x:(-x[0],x[1]['spread_pct'],-x[1]['volume'],x[1]['strike']))
    chosen=ranked[0][1]
    for _,r in ranked[1:]:
        diag.append({'reason':'LOWER_COMPOSITE_EXECUTION_QUALITY','strike':r['strike'],
                     'instrument_key':r['instrument_key'],'execution_score':r['execution_score'],
                     'selected_score':chosen['execution_score'],'spread_pct':r['spread_pct'],
                     'delta':r['delta'],'iv':r['iv'],'theta':r['theta']})
    return chosen,diag



def contract_sensitivity(contract,plan,horizon_minutes=15):
    delta=contract.get('delta')
    if delta is None:return {'status':'UNAVAILABLE','reason':'MISSING_DELTA'}
    delta=abs(float(delta)); gamma=float(contract.get('gamma') or 0);theta=float(contract.get('theta') or 0)
    bid,ask=float(contract['bid']),float(contract['ask'])
    risk=float(plan['risk_points']);reward=abs(float(plan['t1_underlying'])-float(plan['entry_underlying']))
    decay=theta*horizon_minutes/1440
    vega=contract.get('vega')
    iv=contract.get('iv')
    iv_uncertainty=abs(float(vega)) if vega is not None else None
    return {'status':'LOCAL_SENSITIVITY_ESTIMATE','horizon_minutes':horizon_minutes,
            'observed_iv':iv,'iv_shock_plus_minus_1_point_premium_sensitivity':iv_uncertainty,
            'estimated_bid_at_underlying_t1':max(0,bid+delta*reward+.5*gamma*reward**2+decay),
            'estimated_bid_at_underlying_stop':max(0,bid-delta*risk+.5*gamma*risk**2+decay),
            'estimated_t1_change_from_entry_ask':bid+delta*reward+.5*gamma*reward**2+decay-ask,
            'estimated_stop_change_from_entry_ask':bid-delta*risk+.5*gamma*risk**2+decay-ask,
            'assumptions':['FIXED_LOCAL_GREEKS','NO_IV_DIRECTION_ASSUMED','DAILY_THETA_DIVIDED_BY_1440','VEGA_CONVENTION_REQUIRES_PROVIDER_CONFIRMATION','OBSERVED_BID_ASK_ONLY'],
            'probability_or_guaranteed_return':False}


# scanner/provider.py
import json
import gzip
import os
import time
from datetime import datetime, date, timezone
from math import isfinite
from urllib.parse import quote, urlencode
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError
from pathlib import Path
INDEX = 'NSE_INDEX|Nifty 50'

class ProviderError(RuntimeError):
    pass

class Upstox:

    def __init__(self, token: str):
        if not token or any((c in token for c in '\r\n')):
            raise ProviderError('UPSTOX_ANALYTICS_TOKEN missing or invalid')
        self._token = token

    def get(self, path: str, params: dict | None=None):
        url = 'https://api.upstox.com' + path + ('?' + urlencode(params) if params else '')
        req = Request(url, headers={'Authorization': 'Bearer ' + self._token, 'Accept': 'application/json', 'User-Agent': 'nifty-scanner/116'})
        for attempt in range(3):
            try:
                with urlopen(req, timeout=12) as r:

                    def reject_constant(value):
                        raise ValueError('Invalid numeric JSON')
                    obj = json.load(r, parse_constant=reject_constant, parse_float=finite_json_float)
                if not isinstance(obj, dict) or obj.get('status') != 'success' or 'data' not in obj:
                    raise ProviderError('Upstox returned an unsuccessful or invalid response')
                return obj['data']
            except HTTPError as e:
                if e.code in (429, 500, 502, 503, 504) and attempt < 2:
                    time.sleep(1 + attempt)
                    continue
                raise ProviderError(f'Upstox request failed HTTP {e.code}') from None
            except (URLError, TimeoutError, OSError, ValueError) as e:
                if attempt < 2:
                    time.sleep(1 + attempt)
                    continue
                raise ProviderError('Upstox request failed or returned invalid JSON') from None
        raise ProviderError('Upstox request failed')

    def session(self, now: datetime):
        data = self.get('/v2/market/timings/' + now.astimezone(IST).date().isoformat())
        matches = [x for x in data if x.get('exchange') == 'NFO'] if isinstance(data, list) else []
        if not matches:
            return None
        sessions = []
        for row in matches:
            start = datetime.fromtimestamp(float(row['start_time']) / 1000, timezone.utc).astimezone(IST)
            end = datetime.fromtimestamp(float(row['end_time']) / 1000, timezone.utc).astimezone(IST)
            if start.date() == now.astimezone(IST).date() and start < end:
                sessions.append((start, end))
        return next(((a, b) for a, b in sessions if a <= now.astimezone(IST) < b), None)

    def candles(self, key=INDEX):
        data = self.get('/v3/historical-candle/intraday/' + quote(key, safe='') + '/minutes/1')
        if not isinstance(data, dict) or not isinstance(data.get('candles'), list):
            raise ProviderError('Invalid candle response')
        return data['candles']

    def previous_session(self, today: date):
        """Prior completed day OHLC from official V3 historical daily candles.

        Optional enrichment, never fabricate previous-session levels if missing.
        Provider may include holidays; choose last strictly earlier session.
        """
        prior=today-timedelta(days=1)
        from_day=today-timedelta(days=15)
        data=self.get('/v3/historical-candle/'+quote(INDEX,safe='')+'/days/1/'+prior.isoformat()+'/'+from_day.isoformat())
        raw=data.get('candles') if isinstance(data,dict) else None
        if not isinstance(raw,list):raise ProviderError('Prior day data malformed')
        good=[]
        for row in raw:
            try:
                t=parse_feed_timestamp(row[0]);d=t.date()
                prices=[float(x) for x in row[1:5]]
                if d<today and all(isfinite(x) and x>0 for x in prices) and prices[1]>=max(prices[0],prices[3]) and prices[2]<=min(prices[0],prices[3]):
                    good.append((d,{'date':d.isoformat(),'open':prices[0], 'high':prices[1],
                                    'low':prices[2],'close':prices[3],'source':'UPSTOX_OFFICIAL_DAILY_COMPLETED'}))
            except (TypeError,ValueError,KeyError,IndexError):continue
        if not good:raise ProviderError('Previous completed session OHLC unavailable')
        return max(good,key=lambda x:x[0])[1]

    def contracts(self, today: date):
        data = self.get('/v2/option/contract', {'instrument_key': INDEX})
        if not isinstance(data, list):
            raise ProviderError('Invalid option contract response')
        rows = []
        for r in data:
            if not isinstance(r, dict):
                raise ProviderError('Malformed contract record')
            if r.get('underlying_key') != INDEX or r.get('instrument_type') not in ('CE', 'PE'):
                continue
            try:
                exp = date.fromisoformat(str(r['expiry']))
            except (ValueError, KeyError):
                continue
            if exp >= today:
                rows.append(r)
        if not rows:
            raise ProviderError('No unexpired NIFTY option contracts')
        expiry = min((date.fromisoformat(r['expiry']) for r in rows)).isoformat()
        return (expiry, [r for r in rows if r['expiry'] == expiry])

    def chain(self, expiry: str, contracts: list[dict]):
        data = self.get('/v2/option/chain', {'instrument_key': INDEX, 'expiry_date': expiry})
        if not isinstance(data, list) or not data:
            raise ProviderError('Empty option chain')
        valid = {r['instrument_key']: (float(r['strike_price']), r['instrument_type']) for r in contracts if r.get('instrument_key') and r.get('strike_price') is not None}
        metadata = {r['instrument_key']: r for r in contracts if r.get('instrument_key')}
        result = []
        seen = set()
        for row in data:
            if not isinstance(row, dict):
                raise ProviderError('Malformed chain record')
            if row.get('underlying_key') != INDEX or row.get('expiry') != expiry:
                raise ProviderError('Chain underlying or expiry mismatch')
            try:
                strike = float(row['strike_price'])
            except (TypeError, ValueError, KeyError):
                raise ProviderError('Invalid strike') from None
            for side, field in (('CE', 'call_options'), ('PE', 'put_options')):
                option = row.get(field) or {}
                key = option.get('instrument_key')
                if not key:
                    continue
                if valid.get(key) != (strike, side) or key in seen:
                    raise ProviderError('Contract identity mismatch')
                seen.add(key)
                market = option.get('market_data') or {}
                greeks = option.get('option_greeks') or {}
                try:
                    oi = float(market.get('oi') or 0)
                    ltp = float(market.get('ltp') or 0)
                    volume = float(market.get('volume') or 0)
                    delta = float(greeks['delta']) if greeks.get('delta') is not None else None
                    gamma = float(greeks['gamma']) if greeks.get('gamma') is not None else None
                    theta = float(greeks['theta']) if greeks.get('theta') is not None else None
                    vega = float(greeks['vega']) if greeks.get('vega') is not None else None
                    iv = float(greeks['iv']) if greeks.get('iv') is not None else None
                    prev_oi = float(market['prev_oi']) if market.get('prev_oi') is not None else None
                except (ValueError, TypeError):
                    raise ProviderError('Invalid OI/greek data') from None
                if not all((isfinite(x) and x >= 0 for x in (oi, ltp, volume))):
                    raise ProviderError('Invalid option chain values')
                if any((x is not None and (not isfinite(x)) for x in (delta, gamma, theta, vega, iv, prev_oi))):
                    raise ProviderError('Invalid option greek data')
                lot = metadata[key].get('lot_size')
                if lot is None or not isfinite(float(lot)) or float(lot) <= 0 or (not float(lot).is_integer()):
                    raise ProviderError('Missing or invalid live lot size')
                result.append({'instrument_key': key, 'expiry': expiry, 'strike': strike, 'side': side, 'oi': oi, 'ltp': ltp, 'volume': volume, 'delta': delta, 'gamma': gamma, 'theta': theta, 'vega':vega, 'iv':iv, 'prev_oi':prev_oi, 'lot_size': lot})
        if len(result) < 4 or not {'CE', 'PE'}.issubset({r['side'] for r in result}):
            raise ProviderError('Incomplete option chain')
        return result

    def quotes(self, keys: list[str]):
        if not keys:
            return {}
        data = self.get('/v2/market-quote/quotes', {'instrument_key': ','.join(dict.fromkeys(keys))})
        if not isinstance(data, dict):
            raise ProviderError('Invalid quote response')
        out = {}
        for q in data.values():
            if not isinstance(q, dict):
                continue
            key = q.get('instrument_token')
            stamp = q.get('timestamp')
            if key not in keys or not stamp:
                continue
            try:
                price = float(q.get('last_price') or 0)
                buys = (q.get('depth') or {}).get('buy') or []
                sells = (q.get('depth') or {}).get('sell') or []
                b = buys[0] if buys else {}
                a = sells[0] if sells else {}
                numeric = {name: float(q[name]) if q.get(name) is not None else None for name in ('oi', 'average_price')}
                for name, value in numeric.items():
                    if value is not None and (not isfinite(value)):
                        numeric[name] = None
                quoted = {'last_price': price, 'bid': float(b.get('price') or 0), 'bid_qty': float(b.get('quantity') or 0), 'ask': float(a.get('price') or 0), 'ask_qty': float(a.get('quantity') or 0)}
                if any((not isfinite(x) or x < 0 for x in quoted.values())):
                    continue
                out[key] = {**quoted, 'timestamp': stamp, **numeric}
            except (TypeError, ValueError):
                continue
        return out

    def nearest_nifty_future(self, now: datetime, cache: Path) -> dict:
        """Resolve from the provider's daily instrument master, never stale-cache fallback."""
        day = now.astimezone(IST).date().isoformat()
        try:
            if cache.exists():
                saved = json.loads(cache.read_text(encoding='utf-8'))
                if saved.get('day') == day and saved.get('instruments'):
                    instruments = saved['instruments']
                else:
                    instruments = []
            else:
                instruments = []
            if not instruments:
                req = Request('https://assets.upstox.com/market-quote/instruments/exchange/NSE.json.gz', headers={'User-Agent': 'nifty-scanner/116'})
                with urlopen(req, timeout=20) as response:
                    raw = response.read(40000001)
                if len(raw) > 40000000:
                    raise ProviderError('Instrument master too large')
                master = json.loads(gzip.decompress(raw))
                instruments = [x for x in master if x.get('segment') == 'NSE_FO' and x.get('instrument_type') == 'FUT' and (x.get('underlying_key') == INDEX) and (x.get('underlying_symbol') == 'NIFTY')]
                if not instruments:
                    raise ProviderError('No NIFTY futures in instrument master')
                cache.parent.mkdir(parents=True, exist_ok=True)
                tmp = cache.with_suffix('.tmp')
                tmp.write_text(json.dumps({'day': day, 'instruments': instruments}), encoding='utf-8')
                os.replace(tmp, cache)
            found = []
            for item in instruments:
                exp = datetime.fromtimestamp(float(item['expiry']) / 1000, timezone.utc).astimezone(IST).date()
                if exp >= now.astimezone(IST).date():
                    found.append((exp, item))
            if not found:
                raise ProviderError('No unexpired NIFTY future')
            exp, item = min(found, key=lambda t: t[0])
            return {'instrument_key': item['instrument_key'], 'expiry': exp.isoformat(), 'trading_symbol': item.get('trading_symbol')}
        except (OSError, ValueError, TypeError, KeyError, URLError, json.JSONDecodeError) as e:
            raise ProviderError('NIFTY futures master unavailable') from None

def parse_feed_timestamp(value):
    """Accept documented Upstox exchange timestamps (ISO or epoch milliseconds)."""
    if isinstance(value,bool) or value is None:
        raise ValueError('Missing provider timestamp')
    if isinstance(value,(int,float)) or (isinstance(value,str) and value.strip().isdigit()):
        number=float(value)
        if not isfinite(number):raise ValueError('Non-finite quote timestamp')
        seconds=number/1000 if abs(number)>1e11 else number
        return datetime.fromtimestamp(seconds,timezone.utc).astimezone(IST)
    t=datetime.fromisoformat(str(value).replace('Z','+00:00'))
    if t.tzinfo is None:raise ValueError('Unzoned quote timestamp')
    return t.astimezone(IST)

def checked_spot(quote_data: dict, now: datetime, max_age: float) -> float:
    try:
        timestamp = parse_feed_timestamp(quote_data['timestamp'])
        if timestamp.tzinfo is None:
            raise ValueError()
        age = (now - timestamp).total_seconds()
        spot = float(quote_data['last_price'])
        if age < -2 or age > max_age or (not isfinite(spot)) or (spot <= 0):
            raise ValueError()
        return spot
    except (TypeError, ValueError, KeyError):
        raise DataError('SPOT_QUOTE_STALE_OR_INVALID') from None


# scanner/state.py
import fcntl
import hashlib
import json
import os
import tempfile
import copy
from contextlib import contextmanager
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any

class StateError(RuntimeError):
    pass

def validate_position(position):
    """Reject ambiguous state instead of silently discarding an open lock."""
    from math import isfinite
    from datetime import date
    p = position
    try:
        if p.get('status') != 'OPEN' or p['direction'] not in ('BULLISH', 'BEARISH'):
            raise ValueError()
        side = 'CE' if p['direction'] == 'BULLISH' else 'PE'
        if p.get('side', side) != side or not isinstance(p['instrument_key'], str) or (not p['instrument_key'].strip()) or any((c in p['instrument_key'] for c in '\r\n')):
            raise ValueError()
        for key in ('entry_spot', 'entry_ask', 'stop', 't1', 't2', 'best_spot'):
            if isinstance(p[key], bool) or not isinstance(p[key], (int, float)) or (not isfinite(p[key])) or (p[key] <= 0):
                raise ValueError()
        sign = 1 if p['direction'] == 'BULLISH' else -1
        if sign * (p['t1'] - p['entry_spot']) <= 0 or sign * (p['t2'] - p['t1']) <= 0:
            raise ValueError()
        if sign * (p['t2'] - p['stop']) <= 0 or not 0 < float(p.get('remaining_pct', 100)) <= 100:
            raise ValueError()
        opened = datetime.fromisoformat(p['opened_at'])
        checkpoint = datetime.fromisoformat(p['last_candle'])
        if opened.tzinfo is None or checkpoint.tzinfo is None or checkpoint.second or checkpoint.microsecond:
            raise ValueError()
        if not p.get('id') or date.fromisoformat(p['expiry']) < opened.date():
            raise ValueError()
        if (p.get('plan') or {}).get('t1_underlying', p['t1']) != p['t1'] or (p.get('plan') or {}).get('t2_underlying', p['t2']) != p['t2']:
            raise ValueError()
    except (ValueError, TypeError, KeyError, AttributeError):
        raise StateError('Invalid open position; lock requires reconciliation') from None

def migrate_state(source, destination, now):
    """Import an existing alert state once, without changing its source bytes.

    Operational records are translated. No previous strategy implementation,
    old setup watch or old directional thesis becomes a v116 trading rule.
    """
    from math import isfinite
    if destination.exists():
        raise StateError('Destination state already exists; refusing to overwrite')
    try:
        raw = source.read_bytes()

        def bad_number(value):
            raise ValueError('Non-finite legacy state')
        legacy = json.loads(raw, parse_constant=bad_number, parse_float=finite_json_float)
        if not isinstance(legacy, dict):
            raise ValueError()
    except (ValueError, OSError):
        raise StateError('Migration source is unreadable') from None
    if legacy.get('schema') in (1, 2, 3, 4):
        state = load(source, allow_legacy=True)
        state.update(schema=4, engine_version='116.0.0', thesis=None, setup_watches=[], oi_snapshot=None, oi_history=[], futures_snapshot=None)
    elif legacy.get('schema_version') in (107, 109):
        if legacy.get('position_reconciliation_required'):
            raise StateError('Legacy state requires reconciliation; it cannot be migrated as flat')
        state = {'schema': 4, 'engine_version': '116.0.0', 'initialized_at': now.isoformat(), 'session_date': legacy.get('session_date'), 'thesis': None, 'position': None, 'history': [], 'outbox': [], 'last_exit': None, 'oi_snapshot': None, 'oi_history': [], 'setup_watches': [], 'thesis_history': []}
        original = legacy.get('active_position')
        if original is not None:
            if not isinstance(original, dict) or original.get('status') != 'OPEN':
                raise StateError('Ambiguous legacy active position; reconcile before migrating')

            def required(name):
                value = original.get(name)
                if value is None:
                    raise StateError('Legacy active position lacks ' + name)
                return value
            p = {'id': required('position_id'), 'status': 'OPEN', 'direction': required('direction'), 'instrument_key': required('instrument_key'), 'expiry': required('expiry'), 'side': required('side'), 'strike': required('strike'), 'session_date': required('session_date'), 'opened_at': required('opened_at'), 'last_candle': required('last_monitored_candle'), 'entry_spot': required('entry_spot'), 'entry_ask': required('entry_premium_ask'), 'stop': required('stop_underlying'), 't1': required('t1_underlying'), 't2': required('t2_underlying'), 'best_spot': required('favourable_spot_extreme'), 't1_hit': bool(original.get('t1_hit')), 'remaining_pct': required('remaining_pct'), 'contract': original.get('selected_contract') or {}, 'plan': {'t1_underlying': required('t1_underlying'), 't2_underlying': required('t2_underlying')}, 'last_progress_at': original.get('last_checked_at') or required('opened_at'), 'migrated_legacy_position': True}
            if p['t1_hit']:
                at = original.get('post_t1_started_at') or original.get('t1_hit_at')
                if not at:
                    raise StateError('Legacy T1 runner has no T1 time; reconcile before migrating')
                p.update(t1_at=at, runner_started_at=at, runner_last_progress_at=original.get('post_t1_last_progress_at') or at, runner_progress_anchor=original.get('post_t1_anchor_spot') or p['t1'], runner_peak_spot=original.get('post_t1_peak_spot') or p['t1'], runner_peak_bid=original.get('post_t1_peak_premium_bid'))
            validate_position(p)
            state['position'] = p
        prior_exit = legacy.get('last_position_exit') or {}
        if prior_exit.get('closed_at'):
            closed_at = datetime.fromisoformat(prior_exit['closed_at'])
            origin = closed_at.replace(hour=9, minute=15, second=0, microsecond=0)
            elapsed = int((closed_at - origin).total_seconds() // 180)
            last_completed = origin + timedelta(minutes=3 * (elapsed - 1))
            state['last_exit'] = {'at': prior_exit['closed_at'], 'direction': prior_exit.get('direction'), 'three': last_completed.isoformat()}
        state['legacy_position_history'] = legacy.get('position_history') or []
        state['legacy_notification_history'] = legacy.get('notification_history') or []
        for item in legacy.get('pending_notifications') or []:
            details = {'legacy_notification': item, 'source_version': legacy.get('scanner_version'), 'historical': True}
            event = queue(state, 'LEGACY_NOTIFICATION_REVIEW_REQUIRED', details, now)
            entry = next((e for e in state['outbox'] if e['id'] == event))
            entry.update(status='DELIVERY_UNCERTAIN', delayed_delivery=True)
    else:
        raise StateError('Unsupported migration schema; no state was created')
    digest = hashlib.sha256(raw).hexdigest()
    archive = destination.parent / 'archives_v116' / (source.name + '.' + digest[:16] + '.json')
    if not archive.exists():
        archive.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp = tempfile.mkstemp(dir=archive.parent, prefix='.migration-')
        try:
            with os.fdopen(fd, 'wb') as stream:
                stream.write(raw)
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(tmp, archive)
        finally:
            if os.path.exists(tmp):
                os.unlink(tmp)
    state['migration'] = {'source_file': source.name, 'source_sha256': digest, 'archive': str(archive), 'at': now.isoformat()}
    save(destination, state)
    load(destination)
    return state

@contextmanager
def lock(path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(str(path) + '.lock', 'a+') as f:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise StateError('Another local scan is running') from None
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)

def save(path: Path, state: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix='.' + path.name + '.', dir=path.parent)
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as f:
            json.dump(state, f, sort_keys=True, separators=(',', ':'), allow_nan=False)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
        directory = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)

def load(path: Path, allow_legacy=False):
    if not path.exists():
        raise StateError('STATE_NOT_INITIALIZED: reconcile prior scanner and initialize the new state')
    try:

        def invalid_number(value):
            raise ValueError('Non-finite number in state')
        with path.open(encoding='utf-8') as f:
            s = json.load(f, parse_constant=invalid_number, parse_float=finite_json_float)
    except (OSError, ValueError) as e:
        raise StateError('State is unreadable; reconcile before continuing') from e
    if not isinstance(s, dict) or s.get('schema') not in ((1, 2, 3, 4) if allow_legacy else (4,)) or (not isinstance(s.get('outbox'), list)) or ('position' not in s) or (not isinstance(s.get('history'), list)):
        raise StateError('Unsupported or invalid state; reconcile before continuing')
    if s['position'] is not None:
        p = s['position']
        if not isinstance(p, dict) or p.get('status') != 'OPEN' or p.get('direction') not in ('BULLISH', 'BEARISH') or (not all((k in p for k in ('id', 'instrument_key', 'expiry', 'entry_spot', 'entry_ask', 'stop', 't1', 't2', 'opened_at', 'last_candle')))):
            raise StateError('Invalid open position; lock requires reconciliation')
    seen = set()
    for e in s['outbox']:
        if not isinstance(e, dict) or not all((k in e for k in ('id', 'kind', 'details', 'created_at', 'status'))) or e['id'] in seen or (e['status'] not in ('PENDING', 'CLAIMED', 'SENT', 'DELIVERY_UNCERTAIN')):
            raise StateError('Invalid notification outbox')
        seen.add(e['id'])
    if s['position'] is not None:
        validate_position(s['position'])
    for field in ('setup_watches', 'thesis_history'):
        if field in s and (not isinstance(s[field], list)):
            raise StateError('Invalid state collection: ' + field)
    if s.get('schema') != 4:
        s['migrated_from_schema'] = s['schema']
        s['thesis'] = None
        s['setup_watches'] = []
        s['oi_snapshot'] = None
    s['schema'] = 4
    s['engine_version'] = '116.0.0'
    s.setdefault('oi_history', [])
    s.setdefault('setup_watches', [])
    s.setdefault('thesis_history', [])
    return s

def initialize(path: Path, now: datetime):
    if path.exists():
        raise StateError('State already exists; refusing to overwrite')
    save(path, {'schema': 4, 'engine_version': '116.0.0', 'initialized_at': now.isoformat(), 'initialized_flat': True, 'session_date': None, 'thesis': None, 'position': None, 'history': [], 'outbox': [], 'last_exit': None, 'oi_snapshot': None, 'oi_history': [], 'setup_watches': [], 'thesis_history': []})

def queue(state: dict, kind: str, details: dict, when: datetime):
    raw = json.dumps([kind, details], sort_keys=True, separators=(',', ':'), allow_nan=False)
    event_id = hashlib.sha256(raw.encode()).hexdigest()[:24]
    if not any((x['id'] == event_id for x in state['outbox'])):
        state['outbox'].append({'id': event_id, 'kind': kind, 'created_at': when.isoformat(), 'details': copy.deepcopy(details), 'status': 'PENDING', 'claim': None})
    return event_id

def claim(state: dict, token: str, now=None):
    if not token or len(token) > 160:
        raise StateError('Notification claim token required')
    for event in state['outbox']:
        if event['status'] == 'PENDING':
            if now and (now - datetime.fromisoformat(event['created_at'])).total_seconds() > 8 * 60:
                event['delayed_delivery'] = True
            event.update(status='CLAIMED', claim=token)
    sent = [e for e in state['outbox'] if e['status'] == 'SENT']
    if len(sent) > 1000:
        keep = {e['id'] for e in sent[-1000:]}
        state['outbox'] = [e for e in state['outbox'] if e['status'] != 'SENT' or e['id'] in keep]

def append_audit(path: Path, event: dict):
    path.parent.mkdir(parents=True, exist_ok=True)
    line = json.dumps(event, sort_keys=True, separators=(',', ':'), allow_nan=False) + '\n'
    with path.open('a', encoding='utf-8') as f:
        f.write(line)
        f.flush()
        os.fsync(f.fileno())

def capture_inputs(directory: Path, identifier: str, data: dict) -> dict:
    """Write reproducible market inputs without credentials or inferred candle prices."""
    import gzip
    directory.mkdir(parents=True, exist_ok=True)
    raw = json.dumps(data, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()
    content = gzip.compress(raw, mtime=0)
    path = directory / (identifier + '.json.gz')
    if path.exists():
        identifier = identifier + '-' + hashlib.sha256(content).hexdigest()[:12]
        path = directory / (identifier + '.json.gz')
    fd, tmp = tempfile.mkstemp(dir=directory, prefix='.inputs-')
    try:
        with os.fdopen(fd, 'wb') as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)
    return {'path': str(path), 'sha256': hashlib.sha256(content).hexdigest(), 'format': 'RECORDED_INPUTS_V1'}

def wire(value):
    from datetime import date
    if isinstance(value, datetime):
        return {'__datetime__': value.isoformat()}
    if isinstance(value, date):
        return {'__date__': value.isoformat()}
    if isinstance(value, Path):
        return {'__path__': str(value)}
    if isinstance(value, tuple):
        return {'__tuple__': [wire(x) for x in value]}
    if isinstance(value, list):
        return [wire(x) for x in value]
    if isinstance(value, dict):
        return {k: wire(v) for k, v in value.items()}
    return value

def unwire(value):
    from datetime import date
    if isinstance(value, list):
        return [unwire(x) for x in value]
    if isinstance(value, dict):
        if set(value) == {'__datetime__'}:
            return datetime.fromisoformat(value['__datetime__'])
        if set(value) == {'__date__'}:
            return date.fromisoformat(value['__date__'])
        if set(value) == {'__path__'}:
            return Path(value['__path__'])
        if set(value) == {'__tuple__'}:
            return tuple((unwire(x) for x in value['__tuple__']))
        return {k: unwire(v) for k, v in value.items()}
    return value

class RecordingAPI:
    """Record public market-data method results only, never headers or tokens."""
    methods = {'session', 'candles', 'contracts', 'chain', 'quotes', 'nearest_nifty_future', 'previous_session'}

    def __init__(self, api, events):
        self.api = api
        self.events = events

    def __getattr__(self, name):
        target = getattr(self.api, name, None)
        if name == 'previous_session' and target is None:
            def target(*args, **kwargs):
                raise ProviderError('Previous day enrichment not implemented by adapter')
        elif target is None:
            raise AttributeError(name)
        if name not in self.methods or not callable(target):
            return target

        def call(*args, **kwargs):
            row = {'method': name, 'args': wire(args), 'kwargs': wire(kwargs)}
            self.events.append(row)
            try:
                result = target(*args, **kwargs)
                row['result'] = wire(result)
                return result
            except Exception as exc:
                row['error_type'] = type(exc).__name__
                row['error_message'] = str(exc) if type(exc).__name__ in ('ProviderError', 'DataError') else 'Market adapter failed'
                raise
        return call


# scanner/forecasting.py
from datetime import datetime, timedelta
import hashlib

def forecast_report(records):
    """Report directional outcomes, not simulated option fills or trade P&L."""
    settled = [r for r in records if r.get('status') == 'ASSESSED']
    correct = sum((r['directional_correct_at_horizon'] for r in settled))
    by_scenario = {}
    for row in settled:
        name = row['primary_scenario']
        result = by_scenario.setdefault(name, {'assessed': 0, 'directionally_correct': 0})
        result['assessed'] += 1
        result['directionally_correct'] += int(row['directional_correct_at_horizon'])
    return {'scope': 'FORWARD_UNDERLYING_DIRECTION_ONLY_NOT_OPTION_TRADE_PERFORMANCE', 'recorded': len(records), 'assessed': len(settled), 'directionally_correct': correct, 'directional_accuracy': correct / len(settled) if settled else None, 'pending': sum((r.get('status') == 'PENDING' for r in records)), 'unscorable': sum((r.get('status') == 'UNSCORABLE' for r in records)), 'by_scenario': by_scenario, 'probability_calibration_established': False}

def record_and_assess(state, bars, now, forecast, horizon_minutes=15):
    """Freeze today's outlook before observing its later, completed candles.

    The minute containing the creation quote is excluded from excursions
    because its extremes could precede the observation. Every subsequent
    required minute must be present. Missing values are never interpolated.
    """
    records = state.setdefault('forecast_records', [])
    by_time = {c.start: c for c in bars}
    for record in records:
        if record.get('status') != 'PENDING':
            continue
        made = datetime.fromisoformat(record['created_at'])
        due = made + timedelta(minutes=record['horizon_minutes'])
        end = due.replace(second=0, microsecond=0)
        if due > end:
            end += timedelta(minutes=1)
        if now < end:
            continue
        first = made.replace(second=0, microsecond=0)
        if made > first:
            first += timedelta(minutes=1)
        times = []
        cursor = first
        while cursor < end:
            times.append(cursor)
            cursor += timedelta(minutes=1)
        if not times or any((t not in by_time for t in times)):
            record.update(status='UNSCORABLE', reason='INCOMPLETE_FORWARD_MINUTE_PATH', assessed_at=now.isoformat())
            continue
        path = [by_time[t] for t in times]
        sign = 1 if record['direction'] == 'BULLISH' else -1
        baseline = record['spot_at_creation']
        move = sign * (path[-1].close - baseline)
        favorable = max((sign * ((c.high if sign == 1 else c.low) - baseline) for c in path))
        adverse = max((-sign * ((c.low if sign == 1 else c.high) - baseline) for c in path))
        record.update(status='ASSESSED', assessed_at=now.isoformat(), endpoint_at=end.isoformat(), endpoint_spot=path[-1].close, signed_change_underlying=move, favorable_excursion_points=max(0.0, favorable), adverse_excursion_points=max(0.0, adverse), directional_correct_at_horizon=move > 0)
    direction = forecast.get('directional_thesis')
    ready = forecast.get('entry_readiness', 'ASSESS_TRIGGER') == 'ASSESS_TRIGGER'
    if direction in ('BULLISH', 'BEARISH') and ready and (not forecast.get('primary_scenario', '').startswith('STRUCTURAL_BREAK_')):
        slot = forecast['as_of']
        identifier = hashlib.sha256((now.date().isoformat() + '|' + slot + '|' + direction).encode()).hexdigest()[:24]
        if not any((r['id'] == identifier for r in records)):
            records.append({'id': identifier, 'created_at': now.isoformat(), 'forecast_bar_end': slot, 'horizon_minutes': horizon_minutes, 'direction': direction, 'spot_at_creation': forecast['spot'], 'primary_scenario': forecast['primary_scenario'], 'protected_boundary': forecast.get('protected_boundary'), 'status': 'PENDING'})
    pending = [r for r in records if r['status'] == 'PENDING']
    settled = [r for r in records if r['status'] != 'PENDING'][-500:]
    state['forecast_records'] = settled + pending
    return forecast_report(state['forecast_records'])


# scanner/position.py
from datetime import datetime, timedelta
from math import isfinite

# v116.1 independent, completed-candle chronological position management.
from datetime import datetime, timedelta
from math import isfinite

def manage(position, bars, spot, quote, now, market_close, config, structure=None, oi=None):
    """Manage the *alert reference*, not a broker-confirmed position or fill.

    No assumption about the ordering of extremes inside a minute: when a stop
    and target are both touched, prefer the adverse stop. Missing intervals
    raise DataError; the orchestration retains the original contract lock.
    """
    p=copy.deepcopy(position)
    plan_check=p.get('plan') or {}
    if any(plan_check.get(field) is not None and float(plan_check[field]) != float(p[target]) for field,target in [('t1_underlying','t1'),('t2_underlying','t2')]):
        raise DataError('FIXED_TARGETS_CHANGED')
    validate_position(p)
    events=[]; oi=oi or {}
    direction=p['direction']; sign=1 if direction=='BULLISH' else -1
    opened=datetime.fromisoformat(p['opened_at'])
    checkpoint=datetime.fromisoformat(p['last_candle'])
    if opened>now or checkpoint>now.replace(second=0,microsecond=0):
        raise DataError('POSITION_CLOCK_NOT_MONOTONIC')
    ordered=sorted(bars,key=lambda b:b.start)
    new=[c for c in ordered if c.start>checkpoint]
    if new and new[0].start!=checkpoint+timedelta(minutes=1):
        raise DataError('POSITION_MONITORING_CANDLE_GAP')
    if any(b.start-a.start!=timedelta(minutes=1) for a,b in zip(new,new[1:])):
        raise DataError('POSITION_MONITORING_CANDLE_GAP')
    if any(c.start+timedelta(minutes=1)>now for c in new):
        raise DataError('UNCOMPLETED_POSITION_CANDLE')
    # The entry checkpoint is initialized to the minute containing the alert.
    # Review that completed candle once, separately from the later candles.
    # Its OHLC cannot establish whether a touch preceded or followed entry.
    entry_start = opened.replace(second=0, microsecond=0)
    if not p.get('entry_minute_reviewed') and now >= entry_start + timedelta(minutes=1):
        entry_bars = [c for c in ordered if c.start == entry_start]
        if not entry_bars:
            events.append({'kind':'MONITORING_DEGRADED', 'position_id':p['id'],
                           'at':now.isoformat(), 'reason':'ENTRY_MINUTE_HISTORY_UNAVAILABLE',
                           'fill_confirmed':False})
        else:
            entry_bar = entry_bars[0]
            adverse = entry_bar.low if sign == 1 else entry_bar.high
            favourable = entry_bar.high if sign == 1 else entry_bar.low
            # A migrated position may already have a ratcheted stop. Prefer
            # the original plan rather than projecting a later stop backward.
            initial_stop = (p.get('plan') or {}).get('stop_underlying')
            initial_stop = float(initial_stop) if initial_stop is not None else float(p['stop'])
            touched = []
            if sign*(adverse-initial_stop) <= 0:
                touched.append('STOP')
            if sign*(favourable-p['t1']) >= 0:
                touched.append('T1')
            if touched:
                events.append({'kind':'MONITORING_DEGRADED', 'position_id':p['id'],
                               'at':(entry_start+timedelta(minutes=1)).isoformat(),
                               'reason':'ENTRY_MINUTE_TOUCH_ORDER_UNKNOWN',
                               'possible_touches':touched, 'stop_reference':initial_stop,
                               'stop_reference_source':'INITIAL_PLAN' if (p.get('plan') or {}).get('stop_underlying') is not None else 'CURRENT_STOP_LEGACY',
                               'fill_confirmed':False})
        p['entry_minute_reviewed'] = True
    quote_bid=None
    if quote:
        try:
            stamped=parse_feed_timestamp(quote['timestamp'])
            age=(now-stamped).total_seconds()
            bid=float(quote['bid'])
            if stamped.tzinfo and -2<=age<=config.max_quote_age and isfinite(bid) and bid>0:
                quote_bid=bid
                p['last_bid']=bid
                p['last_bid_at']=stamped.isoformat()
        except (KeyError,ValueError,TypeError):pass
    volatility=max(atr(ordered),1)
    progress_increment=max(2,config.runner_progress_atr*volatility)

    def update_stop(new_stop,why,at):
        if not isfinite(new_stop):return
        if sign*(new_stop-p['stop'])<=0:return
        if sign*(p['best_spot']-new_stop)<=0:return
        former=p['stop']
        p['stop']=round(new_stop,5)
        events.append({'kind':'STOP_RATCHET','position_id':p['id'],'at':at.isoformat(),
                       'old_stop':former,'new_stop':p['stop'],'source':why,
                       'broker_order_amended':False})

    def finish(reason,at,reference,origin):
        p.update(status='CLOSED',closed_at=at.isoformat(),exit_reason=reason,
                 exit_reference_spot=reference,exit_source=origin,remaining_pct=0,
                 fill_confirmed=False)
        return None, events+[{'kind':'EXIT','position':copy.deepcopy(p),
                               'reason':reason,'detected_at':now.isoformat(),
                               'event_time':at.isoformat(),'reference_spot':reference,
                               'source':origin,'reference_bid_at_detection':quote_bid,
                               'fill_confirmed':False}],p

    def target1(at,origin):
        if p.get('t1_hit'):return
        p.update(t1_hit=True,t1_at=at.isoformat(),runner_started_at=at.isoformat(),
                 runner_last_progress_at=at.isoformat(),runner_progress_anchor=p['t1'],
                 runner_peak_spot=p['t1'],runner_peak_bid=None,
                 runner_grace_used=False,management_state='RUNNER',remaining_pct=50)
        # A protected stop moves to break even. The ratio is a modelled slice,
        # never evidence that a broker executed a partial exit.
        p['stop']=max(float(p['stop']),float(p['entry_spot'])) if sign==1 else min(float(p['stop']),float(p['entry_spot']))
        events.append({'kind':'TARGET_1','position_id':p['id'],'at':at.isoformat(),
                       'reference_spot':p['t1'],'new_stop':p['stop'],
                       'remaining_pct':50,'source':origin,'broker_fill_confirmed':False})

    def progress(price,at):
        if sign*(price-p['best_spot'])>0:p['best_spot']=price
        anchor=float(p.get('progress_anchor',p['entry_spot']))
        if sign*(price-anchor)>=progress_increment:
            p.update(progress_anchor=price,last_progress_at=at.isoformat())
        if p.get('t1_hit'):
            if sign*(price-float(p.get('runner_peak_spot',p['t1'])))>0:
                p['runner_peak_spot']=price
            anchor=float(p.get('runner_progress_anchor',p['t1']))
            if sign*(price-anchor)>=progress_increment:
                p.update(runner_progress_anchor=price,runner_last_progress_at=at.isoformat())

    # Walk all unseen *completed* candles chronologically.
    for i,c in enumerate(new):
        if c.start<=opened.replace(second=0,microsecond=0):
            p['last_candle']=c.start.isoformat(); continue
        event_at=c.start+timedelta(minutes=1)
        adverse=c.low if sign==1 else c.high
        favourable=c.high if sign==1 else c.low
        if sign*(adverse-p['stop'])<=0:
            return finish('STOP_TOUCHED',event_at,p['stop'],'COMPLETED_1M_STOP_FIRST_IF_AMBIGUOUS')
        if not p.get('t1_hit') and sign*(favourable-p['t1'])>=0:
            target1(event_at,'COMPLETED_1M_EXTREME')
            # OHLC does not reveal whether the new breakeven stop was crossed
            # before or after T1. Use the conservative outcome, not a fill claim.
            if sign*(adverse-p['stop'])<=0:
                return finish('POST_T1_STOP_POSSIBLE_SAME_CANDLE',event_at,p['stop'],'AMBIGUOUS_1M_ADVERSE_ASSUMPTION')
        if p.get('t1_hit') and sign*(favourable-p['t2'])>=0:
            return finish('TARGET_2_TOUCHED',event_at,p['t2'],'COMPLETED_1M_EXTREME')
        progress(favourable,event_at)
        p['last_candle']=c.start.isoformat()
    # Live spot protects a position even if the option bid is missing.
    if sign*(spot-p['stop'])<=0:
        return finish('STOP_TOUCHED',now,spot,'FRESH_LIVE_INDEX_QUOTE')
    if not p.get('t1_hit') and sign*(spot-p['t1'])>=0:target1(now,'FRESH_LIVE_INDEX_QUOTE')
    if p.get('t1_hit') and sign*(spot-p['t2'])>=0:
        return finish('TARGET_2_TOUCHED',now,spot,'FRESH_LIVE_INDEX_QUOTE')
    progress(spot,now)
    # A genuine accepted structural reversal invalidates the previous trade.
    if structure and structure.get('boundary_trusted',True) and not structure.get('pending_break') and structure.get('direction') in ('BULLISH','BEARISH') and structure['direction']!=direction:
        rev=structure.get('last_reversal') or {}
        if rev.get('direction')==structure['direction'] and rev.get('confirmed_at'):
            if datetime.fromisoformat(rev['confirmed_at'])>=opened:
                return finish('OPPOSITE_STRUCTURE_CONFIRMED',now,spot,'TWO_CLOSED_3M_ACCEPTANCES')
    # Structural trailing uses fully confirmed three-minute pivots, and before
    # T1 additionally requires a fresh, matched positive OI change.
    completed_threes=aggregate(ordered,3)
    low,high=pivots(completed_threes)
    candidate_pivots=low if sign==1 else high
    eligible=[(t,v) for t,v in candidate_pivots if t>=opened]
    if eligible:
        _,pivot=eligible[-1]
        candidate=pivot-sign*max(config.stop_buffer,0.1*volatility)
        if p.get('t1_hit'):
            update_stop(candidate,'CONFIRMED_3M_RUNNER_STRUCTURE',now)
        else:
            wall=oi.get('put_support' if sign==1 else 'call_resistance') or {}
            supportive=(oi.get('fresh_snapshot') and wall.get('oi_change') is not None and
                        float(wall['oi_change'])>0 and wall.get('strike') is not None and
                        abs(float(wall['strike'])-pivot)<=config.strike_step)
            if supportive and sign*(spot-p['entry_spot'])>=progress_increment:
                update_stop(candidate,'CONFIRMED_3M_PIVOT_AND_MATCHED_OI',now)
    if quote_bid is not None:
        if quote_bid<=float(p['entry_ask'])*(1-config.premium_hard_loss_pct/100):
            return finish('PREMIUM_LOSS_GUARD',now,spot,'FRESH_LIVE_OPTION_BID')
        if p.get('t1_hit'):
            # On the T1 detection scan no historical bid is invented; only
            # subsequent *observations* count for drawdown.
            start=datetime.fromisoformat(p['runner_started_at'])
            if now>start:
                peak=max(float(p.get('runner_peak_bid') or 0),quote_bid)
                p['runner_peak_bid']=peak
                days_left=(market_close-now).total_seconds()/60
                same_day=p.get('expiry')==now.date().isoformat()
                cap=config.premium_runner_drawdown_pct if not same_day else max(8.0,min(config.premium_runner_drawdown_pct,8+days_left/120*10))
                p['runner_bid_drawdown_pct']=100*(peak-quote_bid)/peak
                p['runner_drawdown_limit_pct']=cap
                if p['runner_bid_drawdown_pct']>=cap:
                    return finish('RUNNER_PREMIUM_DRAWDOWN',now,spot,'FRESH_LIVE_OPTION_BID')
    if p.get('t1_hit'):
        t1time=datetime.fromisoformat(p.get('runner_started_at') or p['t1_at'])
        last=datetime.fromisoformat(p.get('runner_last_progress_at') or p['t1_at'])
        idle=max(0.0,(now-last).total_seconds()/60)
        elapsed=max(0.0,(now-t1time).total_seconds()/60)
        theta=(p.get('contract') or {}).get('theta')
        decay=abs(float(theta))*elapsed/(1440*float(p['entry_ask'])) if theta is not None and isfinite(float(theta)) else None
        p.update(runner_idle_minutes=idle,estimated_runner_theta_fraction=decay,
                 runner_no_progress_3m_bars=int(idle//3))
        stalled=idle>=config.no_progress_minutes
        theta_stalled=decay is not None and idle>=6 and decay>=0.005
        if stalled or theta_stalled:
            grace_until=p.get('runner_grace_until')
            if grace_until and now<datetime.fromisoformat(grace_until):
                pass
            elif grace_until:
                return finish('RUNNER_THETA_NO_PROGRESS' if theta_stalled else 'RUNNER_NO_PROGRESS',now,spot,'POST_T1_PROGRESS')
            else:
                wall=oi.get('put_support' if sign==1 else 'call_resistance') or {}
                supportive=oi.get('fresh_snapshot') and float(wall.get('oi_change') or 0)>0
                if supportive and not p.get('runner_grace_used'):
                    p.update(runner_grace_used=True,runner_grace_until=(now+timedelta(minutes=3)).isoformat())
                else:
                    return finish('RUNNER_THETA_NO_PROGRESS' if theta_stalled else 'RUNNER_NO_PROGRESS',now,spot,'POST_T1_PROGRESS')
    elif (now-opened).total_seconds()/60>=config.no_progress_minutes and sign*(p['best_spot']-p['entry_spot'])<.3*volatility:
        return finish('ENTRY_NO_PROGRESS',now,spot,'PRE_T1_NO_PROGRESS')
    if (market_close-now).total_seconds()<=60*config.session_exit_lead_minutes:
        return finish('SESSION_EXIT_WINDOW',now,spot,'SESSION_TIMINGS')
    if p.get('expiry')==now.date().isoformat() and (market_close-now).total_seconds()<=25*60 and p.get('t1_hit'):
        return finish('EXPIRY_RUNNER_PROTECTION',now,spot,'EXPIRY_TIME_WINDOW')
    p['management_state']='RUNNER' if p.get('t1_hit') else 'INITIAL'
    p['last_checked_at']=now.isoformat()
    return p,events,None


def clock():
    return datetime.now(IST)

def release_fingerprint():
    """Bind replay evidence to these exact executable source bytes."""
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

def fresh_candles(api: Upstox, config: Config, raw=None, clock_fn=None):
    """Bounded retry for publication lag; never reuse an incomplete last minute."""
    for attempt in range(3):
        if raw is None:
            raw = api.candles()
        now = (clock_fn or clock)()
        bars, discarded = contiguous_tail(normalize_candles(raw, now))
        try:
            if not bars:
                raise DataError('LATEST_COMPLETED_CANDLE_MISSING')
            validate_latest_start(bars[-1].start, now)
            validate_candles(bars, now, config.min_bars)
            return (bars, discarded, now, attempt)
        except DataError as exc:
            if str(exc) != 'LATEST_COMPLETED_CANDLE_MISSING' or attempt == 2:
                raise
            if not getattr(api, 'replay_mode', False):
                time.sleep(2)
            raw = None
    raise DataError('LATEST_COMPLETED_CANDLE_MISSING')

def oi_comparison(previous: dict | None, chain: list[dict], expiry: str, now: datetime,
                  spot: float | None=None, history: list[dict] | None=None):
    """Identity-matched OI changes against last valid and longer-horizon receipts.

    Unlike prev_oi (previous SESSION reference), delta here compares same-session
    recordings. Equal exchange freshness is not guaranteed by fetch timestamps.
    """
    result={'status':'BASELINE_ONLY','flows':[], 'nearby_changes':[], 'horizons':[],
            'quality':'RECEIPT_TIME_NOT_EXCHANGE_SNAPSHOT_TIME'}
    sources=[]
    if previous:
        sources.append(('LAST_SUCCESSFUL',previous))
    for old in history or []:
        if isinstance(old,dict) and old.get('fetched_at') != (previous or {}).get('fetched_at'):
            sources.append(('SESSION_HISTORY',old))
    usable=[]
    for label, snap in sources:
        try:
            if snap.get('expiry')!=expiry or snap.get('session_date')!=now.astimezone(IST).date().isoformat():
                continue
            age=(now-datetime.fromisoformat(snap['fetched_at'])).total_seconds()
            if not 30<=age<=3600:
                continue
            old={r['instrument_key']:r for r in snap['rows']}
            changes=[]; flows=[]; matched=0
            for r in chain:
                p=old.get(r['instrument_key'])
                if not p or any(p.get(k)!=r.get(k) for k in ('expiry','side','strike')):
                    continue
                matched+=1
                old_oi=float(p['oi']); new_oi=float(r['oi'])
                flow=classify_flow(old_oi,new_oi,float(p['ltp']),float(r['ltp']),r['side'])
                if spot is None or abs(float(r['strike'])-spot)<=400:
                    changes.append({'instrument_key':r['instrument_key'],'strike':r['strike'],
                                    'side':r['side'],'previous_oi':old_oi,'current_oi':new_oi,
                                    'oi_change':new_oi-old_oi,'option_price_change':float(r['ltp'])-float(p['ltp']),
                                    'classification':flow,'interval_seconds':age})
                if flow not in ('UNAVAILABLE','UNCHANGED_OR_NOISY'):
                    flows.append({'side':r['side'],'strike':r['strike'],'classification':flow})
            if matched:
                usable.append({'label':label,'interval_seconds':age,'nearby_changes':changes,
                               'flows':flows,'matched':matched,
                               'aggregate_ce_oi_change':sum(x['oi_change'] for x in changes if x['side']=='CE'),
                               'aggregate_pe_oi_change':sum(x['oi_change'] for x in changes if x['side']=='PE')})
        except (TypeError,KeyError,ValueError,OverflowError,ZeroDivisionError):
            continue
    if not usable:
        result['status']='BASELINE_GAP' if previous else 'BASELINE_ONLY'
        return result
    usable.sort(key=lambda x:x['interval_seconds'])
    recent=usable[0]
    result.update(status='COMPARABLE_RECEIPT_TIMES_ONLY',flows=recent['flows'],
                  nearby_changes=recent['nearby_changes'],interval_seconds=recent['interval_seconds'],
                  matched_contracts=recent['matched'],
                  horizons=[{k:v for k,v in h.items() if k not in ('nearby_changes','flows')} for h in usable],
                  session_baseline_oi_changes=usable[-1]['nearby_changes'])
    return result


def snapshot_compact(chain, expiry, timestamp, spot):
    """Bound storage, keep exact expiry/contract identity and no fabricated OI."""
    rows=[{k:r.get(k) for k in ('instrument_key','expiry','side','strike','oi','ltp')}
          for r in chain if abs(float(r['strike'])-spot)<=650]
    return {'session_date':timestamp.astimezone(IST).date().isoformat(),
            'expiry':expiry,'fetched_at':timestamp.isoformat(),'rows':rows}


def advance_oi_history(state, chain, expiry, timestamp, spot):
    """Append successful receipt snapshots; preserve first snapshot of session."""
    new=snapshot_compact(chain,expiry,timestamp,spot)
    older=state.get('oi_history') or []
    older=[x for x in older if x.get('expiry')==expiry and x.get('session_date')==new['session_date']]
    if not older or (timestamp-datetime.fromisoformat(older[-1]['fetched_at'])).total_seconds()>=30:
        older.append(new)
    # Retain first snapshot as session anchor and up to 20 most recent snapshots.
    state['oi_history']=[older[0]]+older[-20:] if len(older)>21 else older
    state['oi_snapshot']=new
    return new


def scan(state: dict[str, Any], api: Upstox, config: Config, audit_dir: Path, time_source=None) -> dict:
    samples = []

    def tick():
        t = (time_source or clock)()
        samples.append(t.isoformat())
        return t
    started = tick()
    day = started.date().isoformat()
    result = {'timestamp': started.isoformat(), 'version': __version__, 'session_date': day, 'decision': 'NO_TRADE', 'reason': 'UNSET'}
    evidence = {'version': __version__, 'started_at': started.isoformat(), 'state_before': copy.deepcopy(state)}
    evidence.update(clock_samples=samples, api_events=[], config=asdict(config))
    evidence['release_sha256'] = release_fingerprint()
    api = RecordingAPI(api, evidence['api_events'])

    def remember_structure(value, at):
        state['thesis'] = value
        history = state.setdefault('thesis_history', [])
        fields = ('direction', 'state', 'support', 'resistance', 'pending_break', 'last_reversal')
        if not history or any((history[-1].get(k) != value.get(k) for k in fields)):
            history.append(dict(value, at=at.isoformat()))
            state['thesis_history'] = history[-200:]
    try:
        if state.get('session_date') and state['session_date'] != day and state.get('position'):
            result['reason'] = 'PRIOR_SESSION_POSITION_REQUIRES_RECONCILIATION'
            return result
        if state.get('session_date') != day:
            state.update(session_date=day, thesis=None, oi_snapshot=None, oi_history=[], previous_session=None, futures_snapshot=None, last_exit=None, last_processed_candle=None, setup_watches=[])
        session = api.session(started)
        if session is None:
            if state.get('position'):
                result.update(decision='POSITION_MONITORING_UNAVAILABLE', reason='MARKET_CLOSED_POSITION_LOCK_RETAINED')
                queue(state, 'MONITORING_UNAVAILABLE', {'position_id': state['position'].get('id'), 'session_date': day, 'cause': 'MARKET_CLOSED'}, tick())
            else:
                result['reason'] = 'MARKET_CLOSED_OR_TIMINGS_UNAVAILABLE'
            return result
        session_start, session_end = session
        evidence['session'] = [session_start.isoformat(), session_end.isoformat()]
        if not state.get('position') and started < session_start + timedelta(minutes=config.min_bars):
            result['reason'] = 'OPENING_CANDLE_WARMUP'
            return result
        raw = api.candles()
        open_position = state.get('position')
        keys = [INDEX] + ([open_position['instrument_key']] if open_position else [])
        previous_future = state.get('futures_snapshot') or {}
        if open_position and previous_future.get('instrument_key'):
            keys.append(previous_future['instrument_key'])
        quotes = api.quotes(keys)
        bars, discarded, now, retries = fresh_candles(api, config, raw, clock_fn=tick)
        result['candle_refresh_retries'] = retries
        evidence.update(candles=[[c.start.isoformat(), c.open, c.high, c.low, c.close, c.volume] for c in bars], quotes=quotes, evaluated_at=now.isoformat())
        spot = checked_spot(quotes.get(INDEX, {}), now, config.max_quote_age)
        complete_history = bars[0].start == session_start.replace(second=0, microsecond=0)
        if not complete_history:
            result['structure_data_quality'] = 'SESSION_OPENING_HISTORY_MISSING'
            if not open_position:
                result['reason'] = 'SESSION_STRUCTURE_HISTORY_INCOMPLETE'
                return result
        result.update(spot=spot, spot_quote_timestamp=quotes[INDEX]['timestamp'], last_complete_1m=bars[-1].start.isoformat(), discarded_pre_gap_candles=discarded)
        last_processed = state.get('last_processed_candle')
        if discarded and (not last_processed or datetime.fromisoformat(last_processed) < bars[0].start):
            state['thesis'] = None
            result['structure_reset_reason'] = 'UNSEEN_CANDLE_GAP'
        thesis = update_structure(bars, state.get('thesis'))
        thesis['boundary_trusted'] = complete_history
        remember_structure(thesis, now)
        state['last_processed_candle'] = bars[-1].start.isoformat()
        result['structure'] = thesis
        result['forecast'] = forecast_market(bars, thesis, spot, {})
        if open_position:
            active_oi = {}
            active_chain = []
            try:
                active_exp, active_contracts = api.contracts(now.date())
                if active_exp != open_position['expiry']:
                    raise ProviderError('ACTIVE_EXPIRY_OI_UNAVAILABLE')
                active_chain = api.chain(active_exp, active_contracts)
                oi_at = tick()
                comparison = oi_comparison(state.get('oi_snapshot'), active_chain, active_exp, oi_at, spot, state.get('oi_history'))
                active_oi = enrich_oi_context(oi_context(active_chain, spot, config), comparison, bars, spot, config=config)
                advance_oi_history(state,active_chain,active_exp,oi_at,spot)
                evidence.update(chain=active_chain, chain_received_at=oi_at.isoformat(), contracts=active_contracts)
                result.update(oi_levels=active_oi, oi_flow_context=comparison)
            except (ProviderError, DataError, ValueError, TypeError, KeyError):
                result['oi_monitoring'] = 'UNAVAILABLE_SPOT_PROTECTION_CONTINUES'
            quotes = api.quotes(keys)
            bars, _, now, _ = fresh_candles(api, config, clock_fn=tick)
            spot = checked_spot(quotes.get(INDEX, {}), now, config.max_quote_age)
            thesis = update_structure(bars, thesis)
            thesis['boundary_trusted'] = bars[0].start == session_start.replace(second=0, microsecond=0)
            remember_structure(thesis, now)
            if active_chain:
                active_oi = enrich_oi_context(oi_context(active_chain, spot, config), comparison, bars, spot, fresh=(now - oi_at).total_seconds() <= config.max_quote_age, config=config)
                result['oi_levels'] = active_oi
            state['last_processed_candle'] = bars[-1].start.isoformat()
            evidence.update(candles=[[c.start.isoformat(), c.open, c.high, c.low, c.close, c.volume] for c in bars], quotes=quotes, evaluated_at=now.isoformat())
            result.update(spot=spot, structure=thesis, last_complete_1m=bars[-1].start.isoformat())
            result['forecast'] = forecast_market(bars, thesis, spot, active_oi)
            future_quote = quotes.get(previous_future.get('instrument_key'))
            if future_quote:
                try:
                    future_price = checked_spot(future_quote, now, config.max_quote_age)
                    result['futures'] = {'instrument_key': previous_future['instrument_key'], 'price': future_price, 'provider_average_price': future_quote.get('average_price'), 'quote_timestamp': future_quote['timestamp'], 'role': 'CONTEXT_ONLY'}
                except DataError:
                    result['futures'] = {'status': 'STALE', 'role': 'CONTEXT_ONLY'}
            option_quote = quotes.get(open_position['instrument_key'])
            valid_option_quote = False
            try:
                qt = parse_feed_timestamp(option_quote['timestamp'])
                age = (now - qt).total_seconds()
                valid_option_quote = qt.tzinfo is not None and -2 <= age <= config.max_quote_age and (float(option_quote['bid']) > 0)
            except (TypeError, KeyError, ValueError):
                pass
            if not valid_option_quote:
                result['premium_monitoring'] = 'OPTION_QUOTE_UNAVAILABLE_OR_STALE'
                queue(state, 'MONITORING_DEGRADED', {'position_id': open_position['id'], 'session_date': day, 'cause': 'OPTION_QUOTE_UNAVAILABLE_OR_STALE'}, now)
            managed, events, closed = manage(open_position, bars, spot, option_quote, now, session_end, config, thesis, active_oi)
            state['position'] = managed
            for event in events:
                event.update(contract={k: open_position.get(k) for k in ('side', 'strike', 'expiry', 'direction')}, structure=thesis, oi_levels=active_oi)
                context_position = managed or closed or open_position
                event['position_context'] = {k: context_position.get(k) for k in ('side', 'strike', 'expiry', 'direction', 'entry_spot', 'entry_ask', 'stop', 't1', 't2', 'remaining_pct', 'management_state')}
                if event.get('remaining_pct') is not None:
                    event['position_context']['remaining_pct'] = event['remaining_pct']
                if event.get('new_stop') is not None:
                    event['position_context']['stop'] = event['new_stop']
                queue(state, event['kind'], event, now)
            reversal_exit = None
            if closed:
                state['history'].append(closed)
                state['history'] = state['history'][-200:]
                state['last_exit'] = {'at': closed['closed_at'], 'direction': closed['direction'], 'three': thesis.get('last_3m')}
                result.update(decision='POSITION_CLOSED', reason=closed['exit_reason'], position=closed)
                result['position_exit'] = closed
                if closed['exit_reason'] == 'OPPOSITE_STRUCTURE_CONFIRMED':
                    reversal_exit = closed
            else:
                result.update(decision='POSITION_OPEN', reason='POSITION_LOCKED', position=managed)
            if reversal_exit is None:
                return result
        try:
            future = api.nearest_nifty_future(now, Path('.cache/nifty_futures_v116.json'))
            fq = api.quotes([future['instrument_key']]).get(future['instrument_key'], {})
            ft = tick()
            fp = checked_spot(fq, ft, config.max_quote_age)
            current = {**future, 'price': fp, 'oi': fq.get('oi'), 'at': ft.isoformat()}
            prior = state.get('futures_snapshot')
            pattern = 'UNAVAILABLE'
            if prior and prior.get('instrument_key') == current['instrument_key']:
                try:
                    gap = (ft - datetime.fromisoformat(prior['at'])).total_seconds()
                    if 30 <= gap <= 900:
                        pattern = classify_flow(float(prior['oi']), float(current['oi']), float(prior['price']), fp, 'CE')
                except (ValueError, TypeError, KeyError):
                    pass
            state['futures_snapshot'] = current
            result['futures'] = {**future, 'price': fp, 'average_price': fq.get('average_price'), 'price_oi_pattern': pattern, 'role': 'CONTEXT_ONLY'}
            try:
                future_bars = normalize_candles(api.candles(future['instrument_key']), tick())
                validate_candles(future_bars, tick(), 1)
                volume = sum((c.volume for c in future_bars))
                if volume > 0:
                    result['futures']['candle_vwap_estimate'] = sum(((c.high + c.low + c.close) / 3 * c.volume for c in future_bars)) / volume
                    result['futures']['vwap_method'] = 'COMPLETED_CANDLE_TYPICAL_PRICE_ESTIMATE'
                else:
                    result['futures']['vwap_status'] = 'NO_POSITIVE_VOLUME'
            except (ProviderError, DataError, TypeError):
                result['futures']['vwap_status'] = 'UNAVAILABLE'
            if prior and prior.get('instrument_key') == current['instrument_key'] and (30 <= (ft - datetime.fromisoformat(prior['at'])).total_seconds() <= 900):
                delta = fp - float(prior['price'])
                old_oi = prior.get('oi')
                new_oi = current.get('oi')
                if old_oi and new_oi and (abs(delta) >= max(1.0, 0.1 * float(thesis.get('atr_1m') or 1))) and (abs(float(new_oi) - float(old_oi)) / float(old_oi) >= 0.0005):
                    result['futures']['price_oi_pattern'] = {(True, True): 'LONG_BUILDUP_HYPOTHESIS', (True, False): 'SHORT_COVERING_HYPOTHESIS', (False, True): 'SHORT_BUILDUP_HYPOTHESIS', (False, False): 'LONG_UNWINDING_HYPOTHESIS'}[delta > 0, float(new_oi) > float(old_oi)]
        except (ProviderError, ValueError, TypeError, KeyError):
            result['futures'] = {'status': 'UNAVAILABLE', 'role': 'CONTEXT_ONLY'}
        except DataError:
            result['futures'] = {'status': 'STALE', 'role': 'CONTEXT_ONLY'}
        # Yesterday's completed daily OHLC is immutable for this session; use
        # a verified session-scoped cache to avoid repeat API calls and delays.
        prior_cached=state.get('previous_session') or {}
        previous_day=None
        if prior_cached.get('validated_for_session')==day and prior_cached.get('date') and prior_cached['date']<day:
            previous_day=prior_cached
        else:
            try:
                previous_day=api.previous_session(now.date())
                if previous_day.get('date') and previous_day['date']<day:
                    previous_day=dict(previous_day,validated_for_session=day)
                    state['previous_session']=previous_day
                else:
                    previous_day=None
            except (ProviderError, DataError, ValueError, TypeError, AttributeError):
                result['previous_session_levels']={'status':'UNAVAILABLE','reason':'NONFATAL_ENRICHMENT'}
        if previous_day:
            result['previous_session_levels']=previous_day
        expiry, contracts = api.contracts(tick().date())
        chain = api.chain(expiry, contracts)
        chain_at = tick()
        result['chain_received_at'] = chain_at.isoformat()
        result['chain_timestamp_quality'] = 'FETCH_TIME_ONLY'
        context = oi_context(chain, spot, config)
        result['oi_levels'] = context
        result['oi_flow_context'] = oi_comparison(state.get('oi_snapshot'), chain, expiry, chain_at, spot, state.get('oi_history'))
        advance_oi_history(state,chain,expiry,chain_at,spot)
        evidence.update(chain=chain, chain_received_at=chain_at.isoformat(), contracts=contracts, futures=result.get('futures'))
        strikes = sorted({r['strike'] for r in chain})
        if len(strikes) < 3:
            raise DataError('INSUFFICIENT_STRIKE_GRID')
        actual_steps = sorted(set((round(b - a, 6) for a, b in zip(strikes, strikes[1:]) if b > a)))
        if not actual_steps or abs(actual_steps[0] - config.strike_step) > 1e-06:
            raise DataError('STRIKE_GRID_CHANGED')
        atm = min(strikes, key=lambda x: (abs(x - spot), x))
        targets = {atm + i * config.strike_step for i in range(-3, 4)}
        keys = [INDEX] + [r['instrument_key'] for r in chain if r['strike'] in targets]
        full = api.quotes(keys)
        now = tick()
        try:
            validate_candles(bars, now, config.min_bars)
        except DataError as exc:
            if str(exc) != 'LATEST_COMPLETED_CANDLE_MISSING':
                raise
            bars, discarded, now, retries = fresh_candles(api, config, clock_fn=tick)
            if discarded and datetime.fromisoformat(state['last_processed_candle']) < bars[0].start:
                thesis = None
            thesis = update_structure(bars, thesis)
            thesis['boundary_trusted'] = bars[0].start == session_start.replace(second=0, microsecond=0)
            remember_structure(thesis, now)
            state['last_processed_candle'] = bars[-1].start.isoformat()
            result.update(structure=thesis, last_complete_1m=bars[-1].start.isoformat(), post_chain_candle_refresh=True, post_chain_candle_refresh_retries=retries)
        if (now - chain_at).total_seconds() > config.max_quote_age:
            raise DataError('CHAIN_TOO_OLD')
        if bars[0].start != session_start.replace(second=0, microsecond=0):
            result['reason'] = 'SESSION_STRUCTURE_HISTORY_INCOMPLETE'
            return result
        if (now - started).total_seconds() > 120:
            raise DataError('SCAN_BUDGET_EXCEEDED')
        spot = checked_spot(full.get(INDEX, {}), now, config.max_quote_age)
        context = enrich_oi_context(oi_context(chain, spot, config), result['oi_flow_context'], bars, spot, config=config)
        supports = [float(x) for x in (thesis.get('confirmed_pivot_low'), thesis.get('confirmed_15m_pivot_low')) if x is not None and float(x) < spot]
        resistances = [float(x) for x in (thesis.get('confirmed_pivot_high'), thesis.get('confirmed_15m_pivot_high')) if x is not None and float(x) > spot]
        context.update(price_support=thesis.get('confirmed_15m_pivot_low'), price_resistance=thesis.get('confirmed_15m_pivot_high'), minor_support=max(supports) if supports else None, minor_resistance=min(resistances) if resistances else None)
        context.update(build_level_book(bars, thesis, context, spot, previous_day, result.get('futures')))
        result['futures_alignment']=contextual_futures_alignment(result.get('futures'),thesis,spot)
        context['price_oi_interpretation']=price_oi_evidence(context,result['oi_flow_context'],thesis,spot)
        result['price_oi_interpretation']=context['price_oi_interpretation']
        result['level_inventory']=context['levels']
        result.update(spot=spot, spot_quote_timestamp=full[INDEX]['timestamp'], oi_levels=context)
        result['forecast'] = forecast_market(bars, thesis, spot, context, result.get('futures'))
        evidence.update(candles=[[c.start.isoformat(), c.open, c.high, c.low, c.close, c.volume] for c in bars], quotes=full, evaluated_at=now.isoformat())
        fresh_setups = make_setups(bars, thesis, bars[-1].close, config, context)
        last_bar = bars[-1]
        result['entry_price_diagnostics'] = {'latest_1m': {'start': last_bar.start.isoformat(), 'open': last_bar.open, 'high': last_bar.high, 'low': last_bar.low, 'close': last_bar.close}, 'recent_3m': thesis.get('recent_3m'), 'thesis': thesis.get('direction'), 'fresh_candidates': len(fresh_setups), 'retained_watch_count': len(state.get('setup_watches') or [])}
        setups, watches, watch_diagnostics = refresh_setup_watches(bars, thesis, spot, now, state.get('setup_watches'), config, context, fresh_setups)
        if open_position and result.get('position_exit'):
            setups = [s for s in setups if s['direction'] != open_position['direction'] and s['kind'] == 'CONFIRMED_REVERSAL']
        state['setup_watches'] = watches
        result['setup_watch_diagnostics'] = watch_diagnostics
        if not setups:
            result['reason'] = 'WAIT_FOR_ALIGNED_PRICE_SETUP'
            return result
        if (session_end - now).total_seconds() <= config.entry_cutoff_lead_minutes * 60:
            result['reason'] = 'ENTRY_TOO_CLOSE_TO_SESSION_END'
            return result
        last = state.get('last_exit') or {}
        evaluations = []
        passing = []
        for candidate in setups:
            row = {'setup': candidate}
            allowed, reason = gate_candidate(candidate, thesis)
            if allowed and last.get('at'):
                immediate_reversal = bool(result.get('position_exit') and candidate['direction'] != last.get('direction') and (candidate['kind'] == 'CONFIRMED_REVERSAL'))
                if not immediate_reversal and datetime.fromisoformat(candidate['confirmed_at']) <= datetime.fromisoformat(last['at']):
                    allowed = False
                    reason = 'WAIT_FOR_FRESH_SETUP_AFTER_EXIT'
                elif last.get('direction') == candidate['direction'] and (not thesis.get('last_3m') or thesis['last_3m'] <= str(last.get('three') or '')):
                    allowed = False
                    reason = 'WAIT_FOR_NEW_3M_AFTER_SAME_DIRECTION_EXIT'
            plan = None
            contract = None
            if allowed:
                plan, reason = risk_plan(candidate, spot, context, config)
            if plan:
                scenario = 'RANGE' if candidate['kind'].startswith('RANGE_') else 'REVERSAL' if candidate['kind'] == 'CONFIRMED_REVERSAL' else 'TREND'
                contract, rejected = select_contract(chain, full, candidate['direction'], scenario, spot, now, expiry, config)
                row['rejected_contracts'] = rejected
                if not contract:
                    reason = 'NO_FRESH_LIQUID_CONTRACT'
            if contract:
                contract['plan_sensitivity'] = contract_sensitivity(contract, plan)
                event_key = '|'.join([day, expiry, candidate['direction'], contract['instrument_key'], candidate['confirmed_at'], candidate['kind']])
                ident = hashlib.sha256(event_key.encode()).hexdigest()[:24]
                if any((p.get('id') == ident for p in state['history'])):
                    reason = 'DUPLICATE_SUPPRESSED'
                else:
                    reason = 'QUALIFIED'
                    passing.append((candidate, plan, contract, ident))
            row.update(reason=reason, risk_plan=plan, selected_contract=contract)
            evaluations.append(row)
        result['candidate_evaluations'] = evaluations
        if not passing:
            result['reason'] = evaluations[0]['reason']
            return result
        def opportunity_quality(candidate,plan,contract):
            # Higher-quality opportunities may win over the first encountered
            # setup; each watch was independently evaluated before ranking.
            score=float(contract['execution_score'])
            if candidate['kind'].startswith('FALSE_BREAK'):score+=.045
            if candidate['kind']=='CONFIRMED_REVERSAL':score+=.05
            if thesis.get('context_15m')==candidate['direction']:score+=.04
            alignment=result.get('futures_alignment',{}).get('alignment')
            if alignment=='SUPPORTIVE_HYPOTHESIS':score+=.03
            if alignment=='CONFLICTING_HYPOTHESIS':score-=.025
            oi_bias=result.get('price_oi_interpretation',{}).get('bias')
            if (oi_bias=='BULLISH_SUPPORT_HYPOTHESIS' and candidate['direction']=='BULLISH') or (oi_bias=='BEARISH_RESISTANCE_HYPOTHESIS' and candidate['direction']=='BEARISH'):
                score+=.02
            elif (oi_bias=='BEARISH_RESISTANCE_HYPOTHESIS' and candidate['direction']=='BULLISH') or (oi_bias=='BULLISH_SUPPORT_HYPOTHESIS' and candidate['direction']=='BEARISH'):
                score-=.02
            if plan.get('target_quality')=='OBSERVED_OBSTRUCTION':score+=.02
            score+=.005*min(plan['underlying_rr'],3)
            return score
        passing.sort(key=lambda x:(-opportunity_quality(x[0],x[1],x[2]),x[0]['confirmed_at'],x[3]))
        result['qualified_opportunity_rankings']=[{'kind':x[0]['kind'],'direction':x[0]['direction'],
            'strike':x[2]['strike'],'score':round(opportunity_quality(x[0],x[1],x[2]),5),
            'score_is_probability':False} for x in passing]
        setup, plan, contract, ident = passing[0]
        result.update(setup=setup, risk_plan=plan)
        position = {'id': ident, 'status': 'OPEN', 'session_date': day, 'opened_at': now.isoformat(), 'direction': setup['direction'], 'kind': setup['kind'], 'instrument_key': contract['instrument_key'], 'expiry': expiry, 'strike': contract['strike'], 'side': contract['side'], 'entry_spot': spot, 'entry_ask': contract['ask'], 'stop': plan['stop_underlying'], 't1': plan['t1_underlying'], 't2': plan['t2_underlying'], 't1_hit': False, 'remaining_pct': 100, 'last_candle': now.replace(second=0, microsecond=0).isoformat(), 'last_progress_at': now.isoformat(), 'best_spot': spot, 'entry_minute_ohlc_ignored': True, 'plan': plan, 'contract': contract}
        state['position'] = position
        queue(state, 'ENTRY', {'position': position, 'structure': thesis, 'oi_levels': context, 'forecast': result['forecast']}, now)
        result.update(decision='QUALIFIED', reason='QUALIFIED_' + contract['side'], position=position)
        return result
    except (DataError, ProviderError, ValueError, KeyError, TypeError) as exc:
        result.update(decision='NO_TRADE', reason='DATA_OR_INTEGRATION_ERROR', message=str(exc))
        if state.get('position'):
            result.update(decision='POSITION_MONITORING_UNAVAILABLE', reason='POSITION_LOCK_RETAINED')
            queue(state, 'MONITORING_UNAVAILABLE', {'position_id': state['position'].get('id'), 'session_date': day, 'cause': str(exc)}, tick())
        return result
    except Exception as exc:
        result.update(decision='NO_TRADE', reason='UNEXPECTED_INTERNAL_ERROR', error_type=type(exc).__name__, message='Unexpected scan failure; no new entry is approved')
        if state.get('position'):
            result.update(decision='POSITION_MONITORING_UNAVAILABLE', reason='POSITION_LOCK_RETAINED')
            queue(state, 'MONITORING_UNAVAILABLE', {'position_id': state['position'].get('id'), 'session_date': day, 'cause': type(exc).__name__}, tick())
        return result
    finally:
        result['finished_at'] = tick().isoformat()
        if result.get('forecast') and result.get('spot') and ('bars' in locals()):
            try:
                result['forecast_statistics'] = record_and_assess(state, bars, datetime.fromisoformat(result['finished_at']), result['forecast'], config.forecast_horizon_minutes)
            except Exception as exc:
                result['forecast_assessment_error'] = type(exc).__name__
        evidence['expected_result'] = copy.deepcopy(result)
        evidence['expected_state_after'] = copy.deepcopy(state)
        identifier = started.strftime('%H%M%S%f')
        # Audit/input write failures are operational errors, but never discard
        # a qualified reference position or its durable outbox lock. main()
        # still commits state and exits nonzero so the workflow reports failure.
        try:
            result['input_capture'] = capture_inputs(audit_dir / 'inputs_v116' / day, identifier, evidence)
        except (OSError,ValueError,TypeError) as exc:
            result['persistence_error']='INPUT_CAPTURE_FAILED_'+type(exc).__name__
        try:
            append_audit(audit_dir / ('market_scan_v116_' + day + '.jsonl'), result)
        except (OSError,ValueError,TypeError) as exc:
            result['persistence_error']='AUDIT_WRITE_FAILED_'+type(exc).__name__

# market_scanner.py
import argparse
import json
import os
import smtplib
import ssl
import sys
from datetime import datetime
from email.message import EmailMessage
from pathlib import Path

def paths():
    return (Path(os.environ.get('STATE_FILE', 'state/market_state_v116.json')), Path(os.environ.get('AUDIT_DIR', 'audit')))

def alert_text(event):
    d = event['details']
    p = d.get('position') or d.get('position_context') or {}
    contract = d.get('contract') or p
    lines = ['NIFTY ' + event['kind'].replace('_', ' '), 'Original observation: ' + event['created_at']]
    if contract.get('side'):
        lines.append(f"Contract: {contract.get('strike')} {contract['side']} | Expiry {contract.get('expiry')}")
    for field, label in [('entry_spot', 'NIFTY entry reference'), ('entry_ask', 'Option ask reference'), ('stop', 'NIFTY stop'), ('t1', 'NIFTY target 1'), ('t2', 'NIFTY target 2'), ('remaining_pct', 'Remaining position %')]:
        if p.get(field) is not None:
            lines.append(f'{label}: {p[field]}')
    if d.get('new_stop') is not None:
        lines.append('Updated NIFTY stop: ' + str(d['new_stop']))
    reason = d.get('reason') or d.get('cause')
    if reason:
        lines.append('Reason: ' + str(reason).replace('_', ' '))
    structure = d.get('structure') or {}
    oi = d.get('oi_levels') or {}
    if structure:
        lines.append(f"Market structure: {structure.get('state')} | Support {structure.get('support')} | Resistance {structure.get('resistance')} | 15m context {structure.get('context_15m')}")
    for key, label in [('put_support', 'Put OI support'), ('call_resistance', 'Call OI resistance')]:
        wall = oi.get(key)
        if wall:
            lines.append(f"{label}: {wall['strike']} | OI change {wall.get('oi_change')} | Pattern {wall.get('pattern', 'unavailable')}")
    if p.get('plan'):
        lines.append('Underlying reward/risk: ' + str(p['plan'].get('underlying_rr')))
    if p.get('management_state'):
        lines.append('Management: ' + p['management_state'])
    forecast = d.get('forecast') or {}
    if forecast:
        lines.append('Primary scenario: ' + forecast['primary_scenario'])
        lines.append('Scenario invalidation boundary: ' + str(forecast.get('protected_boundary')))
        lines.append('Evidence: ' + ', '.join(forecast.get('supporting_evidence') or []))
        if forecast.get('cautions'):
            lines.append('Cautions: ' + ', '.join(forecast['cautions']))
    sensitivity = (p.get('contract') or {}).get('plan_sensitivity') or {}
    if sensitivity.get('status') == 'LOCAL_SENSITIVITY_ESTIMATE':
        lines.append('Modelled option bid at underlying T1: ' + str(round(sensitivity['estimated_bid_at_underlying_t1'], 2)) + ' (unchanged-IV/Greeks approximation)')
    if d.get('reference_spot') is not None:
        lines.append('NIFTY at detection/interval reference: ' + str(d['reference_spot']))
    if d.get('detected_at'):
        lines.append('Detected at: ' + d['detected_at'])
    if d.get('event_time') or d.get('at'):
        lines.append('Event time / candle interval end: ' + str(d.get('event_time') or d['at']))
    if d.get('source'):
        lines.append('Observation source: ' + d['source'])
    if d.get('reference_bid_at_detection') is not None:
        lines.append('Option bid at detection: ' + str(d['reference_bid_at_detection']))
    lines.append('This is an analytical alert, not a submitted order or confirmed fill. Stops require management at the broker.')
    if event.get('manually_requeued_at') or event.get('delayed_delivery'):
        lines.append('Historical/delayed observation; this message is not a fresh entry instruction.')
    return '\n'.join(lines)

def deliver(s: dict, path: Path, token: str):
    sender = os.environ.get('EMAIL_SENDER', '')
    receiver = os.environ.get('EMAIL_RECEIVER', '')
    username = os.environ.get('EMAIL_USERNAME') or sender
    password = os.environ.get('EMAIL_PASSWORD', '')
    host = os.environ.get('SMTP_HOST', 'smtp.gmail.com')
    port = int(os.environ.get('SMTP_PORT', '465'))
    if not token:
        raise StateError('Notification claim token missing')
    if not any((e.get('status') == 'CLAIMED' and e.get('claim') == token for e in s['outbox'])):
        return 0
    if not all((sender, receiver, username, password, token)):
        raise StateError('Email credentials or claim token missing')
    uncertain = False
    for event in s['outbox']:
        if event.get('status') != 'CLAIMED' or event.get('claim') != token:
            continue
        label = 'HISTORICAL ' if event.get('delayed_delivery') else 'RETRIED ' if event.get('manually_requeued_at') else ''
        msg = EmailMessage()
        msg['Subject'] = 'NIFTY scanner: ' + label + event['kind']
        msg['From'] = sender
        msg['To'] = receiver
        msg['Message-ID'] = '<' + event['id'] + '@nifty-scanner.local>'
        msg.set_content(alert_text(event))
        try:
            event['delivery_stage'] = 'CONNECT'
            with smtplib.SMTP_SSL(host, port, timeout=20, context=ssl.create_default_context()) as smtp:
                event['delivery_stage'] = 'AUTHENTICATE'
                smtp.login(username, password)
                event['delivery_stage'] = 'SEND'
                smtp.send_message(msg)
            event['status'] = 'SENT'
            event['sent_at'] = datetime.now(IST).isoformat()
        except (OSError, smtplib.SMTPException) as exc:
            event['status'] = 'DELIVERY_UNCERTAIN'
            event['attempted_at'] = datetime.now(IST).isoformat()
            uncertain = True
            event['error_type'] = type(exc).__name__
        save(path, s)
    return 1 if uncertain else 0

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--version', action='store_true')
    mode.add_argument('--initialize-flat', action='store_true', help='Initialize only after manually reconciling prior scanner and broker positions')
    mode.add_argument('--scan-and-claim', action='store_true')
    mode.add_argument('--deliver-claimed', action='store_true')
    mode.add_argument('--reconcile-flat', metavar='POSITION_ID', help='After manual verification, close the matching alert lock without inventing a fill')
    mode.add_argument('--requeue-alert', metavar='ALERT_ID', help='After verifying non-delivery, explicitly requeue an uncertain alert')
    mode.add_argument('--migrate-state', metavar='SOURCE', help='Migrate a recognized existing state once; preserves its source and active lock')
    mode.add_argument('--forecast-report', action='store_true', help='Summarize recorded forward-underlying outcomes, without calling the API')
    args = parser.parse_args()
    if args.version:
        print(__version__)
        return 0
    state_path, audit_dir = paths()
    try:
        with lock(state_path):
            if args.migrate_state:
                migrated = migrate_state(Path(args.migrate_state), state_path, datetime.now(IST))
                print(json.dumps({'status': 'MIGRATED', 'schema': migrated['schema'], 'position_locked': bool(migrated.get('position'))}))
                return 0
            if args.initialize_flat:
                initialize(state_path, datetime.now(IST))
                print('Initialized flat state after operator reconciliation.')
                return 0
            state = load(state_path)
            if args.forecast_report:
                print(json.dumps(forecast_report(state.get('forecast_records') or []), sort_keys=True))
                return 0
            if args.reconcile_flat:
                position = state.get('position')
                if not isinstance(position, dict) or position.get('id') != args.reconcile_flat:
                    raise StateError('Position ID does not match the current open lock')
                now = datetime.now(IST).isoformat()
                closed = dict(position, status='CLOSED', closed_at=now, exit_reason='MANUAL_RECONCILIATION_NO_FILL')
                state['history'].append(closed)
                state['position'] = None
                state['last_exit'] = {'at': now, 'direction': closed.get('direction'), 'three': (state.get('thesis') or {}).get('last_3m')}
                save(state_path, state)
                append_audit(audit_dir / ('market_scan_v116_' + datetime.now(IST).date().isoformat() + '.jsonl'), {'operation': 'MANUAL_RECONCILIATION', 'position_id': args.reconcile_flat, 'at': now, 'fill': 'UNKNOWN'})
                print(json.dumps({'status': 'RECONCILED_FLAT', 'position_id': args.reconcile_flat, 'at': now}))
                return 0
            if args.requeue_alert:
                event = next((x for x in state['outbox'] if x.get('id') == args.requeue_alert), None)
                if not event or event.get('status') not in {'CLAIMED', 'DELIVERY_UNCERTAIN'}:
                    raise StateError('Alert ID is not an uncertain or previously claimed alert')
                event.update(status='PENDING', claim=None, manually_requeued_at=datetime.now(IST).isoformat())
                save(state_path, state)
                append_audit(audit_dir / ('market_scan_v116_' + datetime.now(IST).date().isoformat() + '.jsonl'), {'operation': 'MANUAL_ALERT_REQUEUE', 'alert_id': args.requeue_alert, 'at': datetime.now(IST).isoformat()})
                print(json.dumps({'status': 'REQUEUED', 'alert_id': args.requeue_alert}))
                return 0
            token = os.environ.get('NOTIFICATION_CLAIM_TOKEN', '')
            if args.deliver_claimed:
                return deliver(state, state_path, token)
            if not token:
                raise StateError('NOTIFICATION_CLAIM_TOKEN is required')
            try:
                api = Upstox(os.environ.get('UPSTOX_ANALYTICS_TOKEN', ''))
            except ProviderError as exc:
                if state.get('position'):
                    now = datetime.now(IST)
                    queue(state, 'MONITORING_UNAVAILABLE', {'position_id': state['position'].get('id'), 'session_date': now.date().isoformat(), 'cause': 'TOKEN_UNAVAILABLE'}, now)
                    claim(state, token, datetime.now(IST))
                    save(state_path, state)
                print(json.dumps({'decision': 'ERROR', 'message': str(exc)}), file=sys.stderr)
                return 1
            values = json.loads(os.environ.get('NIFTY_SCANNER_CONFIG', '{}'))
            if not isinstance(values, dict):
                raise StateError('NIFTY_SCANNER_CONFIG must be a JSON object')
            try:
                config = Config(**values)
            except TypeError:
                raise StateError('Unknown or invalid strategy configuration field') from None
            result = scan(state, api, config, audit_dir)
            claim(state, token, datetime.now(IST))
            save(state_path, state)
            print(json.dumps(result, sort_keys=True, allow_nan=False))
            return 1 if result['decision'] == 'POSITION_MONITORING_UNAVAILABLE' or bool(result.get('persistence_error')) or result['reason'] in {'DATA_OR_INTEGRATION_ERROR', 'UNEXPECTED_INTERNAL_ERROR', 'PRIOR_SESSION_POSITION_REQUIRES_RECONCILIATION'} else 0
    except (StateError, OSError, ValueError) as exc:
        print(json.dumps({'decision': 'ERROR', 'message': str(exc)}, allow_nan=False), file=sys.stderr)
        return 1
if __name__ == '__main__':
    sys.exit(main())
