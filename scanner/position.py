"""Alert-based position tracking. No broker orders or assumed executable fills."""
from __future__ import annotations
from datetime import datetime, timedelta
from typing import Any
from .core import Candle, Config, DataError, atr, aggregate, pivots


def manage(position: dict[str,Any], bars: list[Candle], spot: float, quote: dict|None, now: datetime, market_close: datetime, config: Config, structure: dict|None = None):
    p=dict(position); direction=p["direction"]; sign=1 if direction=="BULLISH" else -1
    opened=datetime.fromisoformat(p["opened_at"]); checkpoint=datetime.fromisoformat(p["last_candle"])
    new=[c for c in bars if c.start>checkpoint]
    if new and new[0].start != checkpoint+timedelta(minutes=1):
        raise DataError("POSITION_MONITORING_CANDLE_GAP")
    events=[]
    def close(reason, at, level, source):
        p.update(status="CLOSED",closed_at=at.isoformat(),exit_reason=reason,exit_reference_spot=level,exit_source=source)
        return None,events+[{"kind":"EXIT","position":p,"reason":reason,"detected_at":now.isoformat(),"event_time":at.isoformat(),"reference_spot":level,"source":source}],p
    for c in new:
        # The entry minute may contain pre-entry extremes and must not be replayed.
        if c.start<=opened.replace(second=0,microsecond=0):
            p["last_candle"]=c.start.isoformat(); continue
        sl=float(p["stop"]); t1=float(p["t1"]); t2=float(p["t2"])
        hit_stop=c.low<=sl if sign==1 else c.high>=sl
        hit_t1=c.high>=t1 if sign==1 else c.low<=t1
        hit_t2=c.high>=t2 if sign==1 else c.low<=t2
        # Without intrabar ordering, stop wins if multiple levels touch in one candle.
        if hit_stop: return close("STOP_TOUCHED",c.start+timedelta(minutes=1),sl,"COMPLETED_CANDLE_INTERVAL")
        if not p.get("t1_hit") and hit_t1:
            p["t1_hit"]=True; p["t1_at"]=(c.start+timedelta(minutes=1)).isoformat(); p["remaining_pct"]=50
            p["stop"]=max(sl,p["entry_spot"]) if sign==1 else min(sl,p["entry_spot"])
            p["runner_peak_bid"]=None
            events.append({"kind":"TARGET_1","position_id":p["id"],"at":p["t1_at"],"reference_spot":t1,"remaining_pct":50,"new_stop":p["stop"],"source":"COMPLETED_CANDLE_INTERVAL"})
        if p.get("t1_hit") and hit_t2: return close("TARGET_2_TOUCHED",c.start+timedelta(minutes=1),t2,"COMPLETED_CANDLE_INTERVAL")
        p["last_candle"]=c.start.isoformat()
        favorable=c.high if sign==1 else c.low
        if sign*(favorable-float(p["best_spot"]))>0:
            p["best_spot"]=favorable; p["last_progress_at"]=(c.start+timedelta(minutes=1)).isoformat()
    # Live spot is a detection-time quote, not an execution.
    sl=float(p["stop"]); t1=float(p["t1"]); t2=float(p["t2"])
    if sign*(spot-sl)<=0: return close("STOP_TOUCHED",now,spot,"LIVE_SPOT")
    if not p.get("t1_hit") and sign*(spot-t1)>=0:
        p.update(t1_hit=True,t1_at=now.isoformat(),remaining_pct=50,runner_peak_bid=None)
        p["stop"]=max(sl,p["entry_spot"]) if sign==1 else min(sl,p["entry_spot"])
        events.append({"kind":"TARGET_1","position_id":p["id"],"at":now.isoformat(),"reference_spot":spot,"remaining_pct":50,"new_stop":p["stop"],"source":"LIVE_SPOT"})
    if p.get("t1_hit") and sign*(spot-t2)>=0: return close("TARGET_2_TOUCHED",now,spot,"LIVE_SPOT")
    if structure and structure.get("direction") in {"BULLISH","BEARISH"} and structure.get("direction")!=direction and structure.get("reason") in {"SUPPORT_BREAK_CONFIRMED","RESISTANCE_BREAK_CONFIRMED"}:
        return close("OPPOSITE_STRUCTURE_CONFIRMED",now,spot,"COMPLETED_3M_STRUCTURE")
    # Ratchet after completed bars; only pivots formed after entry may tighten
    # the stop, and they cannot retroactively alter any earlier candle.
    previous_stop=p["stop"]
    three=aggregate(bars,3); lows,highs=pivots(three)
    lows=[(t,x) for t,x in lows if t>=opened]
    highs=[(t,x) for t,x in highs if t>=opened]
    if sign==1 and lows:
        candidate=lows[-1][1]-config.stop_buffer
        if p["stop"]<candidate<spot: p["stop"]=candidate
    elif sign==-1 and highs:
        candidate=highs[-1][1]+config.stop_buffer
        if spot<candidate<p["stop"]: p["stop"]=candidate
    if p["stop"]!=previous_stop:
        events.append({"kind":"STOP_RATCHET","position_id":p["id"],"at":now.isoformat(),"old_stop":previous_stop,"new_stop":p["stop"],"source":"CONFIRMED_3M_PIVOT"})
    if quote:
        try:
            qt=datetime.fromisoformat(str(quote["timestamp"]).replace("Z","+00:00")); age=(now-qt).total_seconds(); bid=float(quote["bid"])
            if qt.tzinfo is None or age < -2 or age>config.max_quote_age or bid<=0: raise ValueError()
            p["last_bid"]=bid; p["last_bid_at"]=qt.isoformat()
            if bid<=float(p["entry_ask"])*(1-config.premium_hard_loss_pct/100): return close("PREMIUM_LOSS_GUARD",now,spot,"LIVE_BID")
            if p.get("t1_hit"):
                peak=max(float(p.get("runner_peak_bid") or 0),bid); p["runner_peak_bid"]=peak
                if bid<=peak*(1-config.premium_runner_drawdown_pct/100): return close("RUNNER_PREMIUM_DRAWDOWN",now,spot,"LIVE_BID")
        except (KeyError,TypeError,ValueError): pass
    progress=datetime.fromisoformat(p["last_progress_at"])
    if p.get("t1_hit") and (now-progress).total_seconds()>=config.no_progress_minutes*60:
        return close("RUNNER_NO_PROGRESS",now,spot,"TIME_AND_CANDLES")
    if not p.get("t1_hit") and (now-opened).total_seconds()>=config.no_progress_minutes*60 and (now-progress).total_seconds()>=config.no_progress_minutes*60 and sign*(float(p["best_spot"])-float(p["entry_spot"]))<0.3*max(atr(bars),1):
        return close("ENTRY_NO_PROGRESS",now,spot,"TIME_AND_CANDLES")
    if (market_close-now).total_seconds()<=10*60:
        return close("SESSION_END_ALERT",now,spot,"SESSION_TIME")
    return p,events,None
