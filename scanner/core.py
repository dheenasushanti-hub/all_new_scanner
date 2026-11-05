"""Independent NIFTY market-structure engine. Pure functions and no network I/O."""
from __future__ import annotations

from dataclasses import dataclass, asdict
from datetime import datetime, timedelta, timezone
from math import isfinite
from statistics import median
from typing import Any

IST = timezone(timedelta(hours=5, minutes=30))

class DataError(ValueError):
    pass

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
            raise DataError("Candle timestamps must be timezone-aware minute starts")
        vals = (self.open, self.high, self.low, self.close, self.volume)
        if not all(isfinite(v) for v in vals) or min(self.open,self.high,self.low,self.close) <= 0:
            raise DataError("Invalid candle prices")
        if self.high < max(self.open,self.close,self.low) or self.low > min(self.open,self.close,self.high) or self.volume < 0:
            raise DataError("Invalid candle OHLC or volume")

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

    def __post_init__(self):
        for field in (self.max_risk,self.min_rr,self.max_quote_age,self.max_spread_pct,self.max_entry_extension_atr,self.min_wall_fraction,self.strike_step,self.stop_buffer,self.premium_hard_loss_pct,self.premium_runner_drawdown_pct):
            if not isfinite(field) or field <= 0:
                raise DataError("Invalid strategy configuration")
        if self.min_wall_fraction > 1 or self.min_bars < 6 or self.no_progress_minutes < 1:
            raise DataError("Invalid strategy configuration")


def normalize_candles(raw: list[list[Any]], now: datetime) -> list[Candle]:
    if now.tzinfo is None:
        raise DataError("naive evaluation time")
    today = now.astimezone(IST).date()
    by_time: dict[datetime,Candle] = {}
    for row in raw:
        if len(row) < 5:
            raise DataError("Malformed candle")
        t = datetime.fromisoformat(str(row[0]).replace("Z","+00:00"))
        if t.tzinfo is None:
            raise DataError("Candle timestamp has no timezone")
        t = t.astimezone(IST)
        if t.date() != today or t + timedelta(minutes=1) > now.astimezone(IST):
            continue
        c = Candle(t, *(float(v) for v in row[1:5]), float(row[5] or 0) if len(row)>5 else 0.)
        if t in by_time and by_time[t] != c:
            raise DataError("Conflicting duplicate candles")
        by_time[t] = c
    return [by_time[t] for t in sorted(by_time)]


def validate_candles(bars: list[Candle], now: datetime, minimum: int = 9) -> None:
    if len(bars) < minimum:
        raise DataError("INSUFFICIENT_CANDLES")
    latest = now.astimezone(IST).replace(second=0,microsecond=0) - timedelta(minutes=1)
    if bars[-1].start != latest:
        raise DataError("LATEST_COMPLETED_CANDLE_MISSING")
    # Check entire available session from first observed bar; do not infer nonexistent opening bars.
    for a,b in zip(bars,bars[1:]):
        if b.start-a.start != timedelta(minutes=1):
            raise DataError("CANDLE_GAP")


def contiguous_tail(bars: list[Candle]) -> tuple[list[Candle],int]:
    """Discard pre-gap history; management separately checks its full open interval."""
    cut=0
    for i in range(1,len(bars)):
        if bars[i].start-bars[i-1].start!=timedelta(minutes=1): cut=i
    return bars[cut:],cut


def aggregate(bars: list[Candle], n: int) -> list[Candle]:
    groups: dict[datetime,list[Candle]] = {}
    for b in bars:
        start = b.start.replace(hour=9,minute=15,second=0,microsecond=0)
        elapsed = int((b.start-start).total_seconds()//60)
        if elapsed < 0:
            continue
        slot=start+timedelta(minutes=(elapsed//n)*n)
        groups.setdefault(slot,[]).append(b)
    result=[]
    for t, g in sorted(groups.items()):
        if len(g)==n and all(c.start==t+timedelta(minutes=i) for i,c in enumerate(g)):
            result.append(Candle(t,g[0].open,max(x.high for x in g),min(x.low for x in g),g[-1].close,sum(x.volume for x in g)))
    return result


def atr(bars: list[Candle], n: int=14) -> float:
    ranges=[]
    for i,c in enumerate(bars):
        prev=bars[i-1].close if i else c.open
        ranges.append(max(c.high-c.low,abs(c.high-prev),abs(c.low-prev)))
    return sum(ranges[-n:])/len(ranges[-n:]) if ranges else 0.0


def pivots(bars: list[Candle]) -> tuple[list[tuple[datetime,float]],list[tuple[datetime,float]]]:
    """Confirmed with one complete right-hand bar, so never see the future."""
    lows=[]; highs=[]
    for i in range(2,len(bars)-1):
        x=bars[i]
        if x.low < min(bars[i-2].low,bars[i-1].low) and x.low <= bars[i+1].low:
            lows.append((x.start,x.low))
        if x.high > max(bars[i-2].high,bars[i-1].high) and x.high >= bars[i+1].high:
            highs.append((x.start,x.high))
    return lows,highs


def update_structure(bars: list[Candle], old: dict[str,Any] | None) -> dict[str,Any]:
    three=aggregate(bars,3); fifteen=aggregate(bars,15)
    if len(three)<2:
        return {"direction":"RANGE","state":"WARMUP","support":None,"resistance":None,"last_3m":None,"context_15m":"UNAVAILABLE"}
    a=max(atr(three),1.0); one_a=max(atr(bars),1.0)
    close=three[-1].close; previous=three[-2].close
    # Momentum is descriptive. A durable directional thesis survives ordinary pullbacks.
    impulse=close-three[-3 if len(three)>=3 else -2].close
    recent_dir="BULLISH" if impulse>0.18*a and close>previous else "BEARISH" if impulse< -0.18*a and close<previous else "MIXED"
    lows, highs=pivots(three)
    old=old or {}; direction=old.get("direction","RANGE")
    if direction not in {"BULLISH","BEARISH","RANGE"}: raise DataError("INVALID_THESIS")
    support=old.get("support"); resistance=old.get("resistance")
    change="PERSISTENT"
    buffer=max(2.0,0.12*one_a)
    established=old.get("established_at")
    # Confirm break on a completed 3m close AND current completed 1m close.
    # A retest/rejection of a nearby wall alone does not invert the trend.
    if direction=="BULLISH" and support is not None and close<float(support)-buffer and bars[-1].close<float(support)-buffer:
        direction="BEARISH"; resistance=float(support); support=min(x.low for x in three[-3:]); change="SUPPORT_BREAK_CONFIRMED"; established=three[-1].start.isoformat()
    elif direction=="BEARISH" and resistance is not None and close>float(resistance)+buffer and bars[-1].close>float(resistance)+buffer:
        direction="BULLISH"; support=float(resistance); resistance=max(x.high for x in three[-3:]); change="RESISTANCE_BREAK_CONFIRMED"; established=three[-1].start.isoformat()
    elif direction=="RANGE" and recent_dir in {"BULLISH","BEARISH"}:
        direction=recent_dir; change="STRUCTURE_ESTABLISHED"; established=three[-1].start.isoformat()
        support=(lows[-1][1] if lows else min(x.low for x in three[-3:]))
        resistance=(highs[-1][1] if highs else max(x.high for x in three[-3:]))
    # Only completed pivots made after the trend was established can advance a stop boundary.
    since=datetime.fromisoformat(established) if established else three[0].start
    if direction=="BULLISH":
        usable=[v for t,v in lows if t>=since and v<close]
        if usable: support=max(float(support) if support is not None else usable[-1], usable[-1])
        state="BULL_TREND" if recent_dir=="BULLISH" else "BULL_PULLBACK"
    elif direction=="BEARISH":
        usable=[v for t,v in highs if t>=since and v>close]
        if usable: resistance=min(float(resistance) if resistance is not None else usable[-1], usable[-1])
        state="BEAR_TREND" if recent_dir=="BEARISH" else "BEAR_PULLBACK"
    else: state="RANGE"
    context_lows,context_highs=pivots(fifteen)
    if len(fifteen)>=2:
        context="BULLISH" if fifteen[-1].close>fifteen[-2].close else "BEARISH" if fifteen[-1].close<fifteen[-2].close else "SIDEWAYS"
    else: context="DEVELOPING"
    return {"direction":direction,"state":state,"support":support,"resistance":resistance,"confirmed_pivot_low":lows[-1][1] if lows else None,"confirmed_pivot_high":highs[-1][1] if highs else None,"confirmed_15m_pivot_low":context_lows[-1][1] if context_lows else None,"confirmed_15m_pivot_high":context_highs[-1][1] if context_highs else None,"reason":change,"established_at":established,"recent_3m":recent_dir,"atr_1m":one_a,"atr_3m":a,"last_3m":three[-1].start.isoformat(),"last_3m_close":close,"context_15m":context,"buffer":buffer}


def classify_flow(old_oi: float, new_oi: float, old_price: float, new_price: float, side: str) -> str:
    """Price/OI pattern only; it does not identify initiators or participant positions."""
    if side not in {"CE","PE"} or min(old_oi,new_oi,old_price,new_price)<=0:
        return "UNAVAILABLE"
    dp=(new_price-old_price)/old_price; doi=(new_oi-old_oi)/old_oi
    if abs(dp)<0.005 or abs(doi)<0.005: return "UNCHANGED_OR_NOISY"
    return { (True,True):"LONG_BUILDUP_HYPOTHESIS",(True,False):"SHORT_COVERING_HYPOTHESIS",(False,True):"SHORT_BUILDUP_HYPOTHESIS",(False,False):"LONG_UNWINDING_HYPOTHESIS"}[(dp>0,doi>0)]


def oi_context(chain: list[dict[str,Any]], spot: float, config: Config) -> dict[str,Any]:
    """OI identifies potential walls; it is not an order-flow or reversal detector."""
    near=[r for r in chain if abs(float(r["strike"])-spot)<=400]
    def wall(side: str, eligible):
        rows=[r for r in near if r["side"]==side and float(r.get("oi") or 0)>0 and eligible(float(r["strike"]))]
        if not rows: return None
        high=max(float(r["oi"]) for r in rows)
        strong=[r for r in rows if float(r["oi"])>=high*config.min_wall_fraction]
        v=min(strong,key=lambda r:abs(float(r["strike"])-spot))
        return {"strike":float(v["strike"]),"oi":float(v["oi"]),"relative_to_side_max":float(v["oi"])/high}
    return {"put_support":wall("PE",lambda p:p<=spot),"call_resistance":wall("CE",lambda p:p>=spot),"meaning":"potential levels; OI is not evidence of trade initiator"}


def make_setup(bars: list[Candle], structure: dict[str,Any], spot: float, config: Config, context: dict[str,Any] | None = None) -> dict[str,Any] | None:
    if len(bars)<config.min_bars:
        return None
    d=structure["direction"]; curr=bars[-1]; prev=bars[-2]; a=max(atr(bars),1.)
    context=context or {}
    kind="TREND_CONTINUATION"
    if d=="RANGE" and structure.get("state")!="WARMUP":
        put=context.get("put_support"); call=context.get("call_resistance")
        band=max(2.0,0.3*a)
        if put and any(c.low<=put["strike"]+band for c in bars[-4:-1]) and curr.close>prev.high and curr.close>put["strike"]+band and structure.get("recent_3m")!="BEARISH":
            d="BULLISH"; kind="RANGE_SUPPORT_RECLAIM"
        elif call and any(c.high>=call["strike"]-band for c in bars[-4:-1]) and curr.close<prev.low and curr.close<call["strike"]-band and structure.get("recent_3m")!="BULLISH":
            d="BEARISH"; kind="RANGE_RESISTANCE_REJECTION"
        else:
            return None
    elif d not in {"BULLISH","BEARISH"}:
        return None
    # Latest completed 3m must resume or sustain the structural direction.
    if structure["direction"]!="RANGE" and structure["recent_3m"] != d: return None
    if d=="BULLISH":
        if curr.close<=curr.open or curr.close<=prev.close or spot<curr.close: return None
        invalid=min(b.low for b in bars[-4:])-config.stop_buffer
        if structure.get("support") is not None and spot<=float(structure["support"]): return None
    else:
        if curr.close>=curr.open or curr.close>=prev.close or spot>curr.close: return None
        invalid=max(b.high for b in bars[-4:])+config.stop_buffer
        if structure.get("resistance") is not None and spot>=float(structure["resistance"]): return None
    if abs(spot-curr.close)>config.max_entry_extension_atr*a:
        return None
    if structure.get("reason") in {"SUPPORT_BREAK_CONFIRMED","RESISTANCE_BREAK_CONFIRMED"}:
        kind="CONFIRMED_REVERSAL"
    elif kind=="TREND_CONTINUATION":
        if d=="BULLISH" and curr.close>max(c.high for c in bars[-6:-1]): kind="TREND_BREAKOUT"
        elif d=="BEARISH" and curr.close<min(c.low for c in bars[-6:-1]): kind="TREND_BREAKDOWN"
        elif d=="BULLISH" and context.get("put_support") and min(c.low for c in bars[-4:-1])<=context["put_support"]["strike"]+max(2,0.3*a): kind="TREND_SUPPORT_RECLAIM"
        elif d=="BEARISH" and context.get("call_resistance") and max(c.high for c in bars[-4:-1])>=context["call_resistance"]["strike"]-max(2,0.3*a): kind="TREND_RESISTANCE_REJECTION"
    return {"direction":d,"kind":kind,"trigger":curr.close,"confirmed_at":(curr.start+timedelta(minutes=1)).isoformat(),"invalidation":invalid}


def make_setups(bars: list[Candle], structure: dict[str,Any], spot: float, config: Config, context: dict[str,Any]) -> list[dict[str,Any]]:
    """Reconsider up to three recently closed 1m triggers, independently.

    This permits a 3-minute polling cadence without treating an invalidated or
    chased trigger as fresh. Structural context is strictly current at scan time.
    """
    out=[]
    for back in range(min(3,len(bars)-config.min_bars+1)):
        prefix=bars[:len(bars)-back] if back else bars
        c=make_setup(prefix,structure,spot,config,context)
        if c is None: continue
        intervening=bars[len(prefix):]
        if c["direction"]=="BULLISH" and any(x.low<=c["invalidation"] for x in intervening): continue
        if c["direction"]=="BEARISH" and any(x.high>=c["invalidation"] for x in intervening): continue
        # A confirmed reversal only exists after the three-minute break completed.
        if c["kind"]=="CONFIRMED_REVERSAL" and structure.get("last_3m"):
            confirmation=datetime.fromisoformat(structure["last_3m"])+timedelta(minutes=3)
            if datetime.fromisoformat(c["confirmed_at"])<confirmation: continue
        out.append(c)
    return out


def gate_candidate(setup: dict[str,Any], structure: dict[str,Any]) -> tuple[bool,str]:
    d=setup.get("direction"); thesis=structure.get("direction")
    if d not in {"BULLISH","BEARISH"}: return False,"INVALID_DIRECTION"
    if thesis=="RANGE" and str(setup.get("kind","" )).startswith("RANGE_"): return True,"RANGE_LEVEL_RECLAIM"
    if thesis!=d: return False,"THESIS_OPPOSES_OR_UNCONFIRMED"
    return True,"ALIGNED"


def risk_plan(setup: dict[str,Any], spot: float, context: dict[str,Any], config: Config) -> tuple[dict[str,Any]|None,str]:
    d=setup["direction"]; sign=1 if d=="BULLISH" else -1
    stop=float(setup["invalidation"]); risk=sign*(spot-stop)
    if not isfinite(risk) or risk<=0: return None,"INVALID_STOP"
    if risk>config.max_risk: return None,"STOP_TOO_WIDE"
    step=config.strike_step
    # Round strikes are reference targets, not automatically impassable barriers.
    # Choose the first grid meeting minimum R:R, then respect real opposing levels.
    import math
    required=config.min_rr*risk
    if sign==1:
        target1=max((math.floor(spot/step)+1)*step,math.ceil((spot+required)/step)*step)
    else:
        target1=min((math.ceil(spot/step)-1)*step,math.floor((spot-required)/step)*step)
    target_source="GRID_MEETING_MINIMUM_RR"
    wall=context.get("call_resistance" if sign==1 else "put_support")
    if wall:
        w=float(wall["strike"])
        if sign*(w-spot)>0 and sign*(w-target1)<0:
            target1=w;target_source="OPPOSING_OI_WALL"
    structural=context.get("price_resistance" if sign==1 else "price_support")
    if structural is not None:
        level=float(structural)
        if sign*(level-spot)>0 and sign*(level-target1)<0:
            target1=level;target_source="OPPOSING_CONFIRMED_STRUCTURE"
    dist=sign*(target1-spot)
    if dist/risk<config.min_rr: return None,"TARGET_ROOM_INSUFFICIENT"
    target2=(math.floor(target1/step)+1)*step if sign==1 else (math.ceil(target1/step)-1)*step
    return {"entry_underlying":spot,"stop_underlying":stop,"risk_points":risk,"t1_underlying":target1,"t2_underlying":target2,"underlying_rr":dist/risk,"target_source":target_source,"fixed_targets":True},"OK"


def select_contract(chain: list[dict[str,Any]], quotes: dict[str,dict[str,Any]], direction: str, scenario: str, spot: float, now: datetime, expiry: str, config: Config) -> tuple[dict[str,Any]|None,list[dict[str,Any]]]:
    side="CE" if direction=="BULLISH" else "PE"
    strikes=sorted({float(r["strike"]) for r in chain if r["side"]==side})
    if not strikes: return None,[{"reason":"NO_LISTED_STRIKES"}]
    atm=min(strikes,key=lambda s:(abs(s-spot),s))
    offsets=([-1,-2] if side=="CE" else [1,2]) if scenario in {"RANGE","REVERSAL"} else ([0,-1] if side=="CE" else [0,1])
    allowed=[atm+o*config.strike_step for o in offsets]
    scored=[]; rejected=[]
    for r in chain:
        strike=float(r["strike"])
        if r["side"]!=side or strike not in allowed or str(r["expiry"])!=expiry: continue
        volume=float(r.get("volume") or 0)
        if not isfinite(volume) or volume<=0:
            rejected.append({"strike":strike,"reason":"NO_RECORDED_VOLUME"});continue
        q=quotes.get(r["instrument_key"])
        if not q:
            rejected.append({"strike":strike,"reason":"MISSING_FULL_QUOTE"});continue
        try:
            ts=datetime.fromisoformat(str(q["timestamp"]).replace("Z","+00:00"))
            if ts.tzinfo is None: raise ValueError()
            age=(now-ts).total_seconds(); bid=float(q["bid"]); ask=float(q["ask"]); bq=float(q["bid_qty"]); aq=float(q["ask_qty"])
            if not all(isfinite(x) for x in (age,bid,ask,bq,aq)) or age < -2 or age>config.max_quote_age or bid<=0 or ask<bid or bq<=0 or aq<=0: raise ValueError()
            spread=100*(ask-bid)/((ask+bid)/2)
            if spread>config.max_spread_pct: raise ValueError()
        except (ValueError,TypeError,KeyError):
            rejected.append({"strike":strike,"reason":"STALE_OR_ILLQUID_QUOTE"});continue
        delta=r.get("delta"); delta_score=0.0
        if delta is not None:
            delta=float(delta)
            if not isfinite(delta) or not 0<abs(delta)<=1 or (side=="CE" and delta<0) or (side=="PE" and delta>0):
                rejected.append({"strike":strike,"reason":"INVALID_DELTA"}); continue
            delta_score=1-abs(abs(delta)-0.55)
        # OI is intentionally absent from contract ranking; use executable quote quality.
        import math
        score=delta_score - spread/100 + min(bq,aq)/max(bq,aq)*0.05 + min(math.log10(1+volume)/200,0.04) - allowed.index(strike)*0.01
        scored.append((score,{"instrument_key":r["instrument_key"],"expiry":expiry,"strike":strike,"side":side,"bid":bid,"ask":ask,"bid_qty":bq,"ask_qty":aq,"quote_timestamp":ts.isoformat(),"delta":delta,"volume":volume,"gamma":r.get("gamma"),"theta":r.get("theta"),"spread_pct":spread,"atm":atm,"offset":int(round((strike-atm)/config.strike_step)),"selection_score":score,"scenario":scenario}))
    if not scored: return None,rejected or [{"reason":"NO_CONTRACT_IN_ALLOWED_OFFSETS"}]
    scored.sort(key=lambda x:(-x[0],x[1]["strike"]))
    return scored[0][1],rejected
