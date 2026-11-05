"""Scan orchestration: validate, evaluate, persist, and claim alerts."""
from __future__ import annotations
import hashlib
import json
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any
from .core import Config,DataError,IST,normalize_candles,validate_candles,contiguous_tail,update_structure,oi_context,make_setups,gate_candidate,risk_plan,select_contract,classify_flow
from .provider import INDEX, Upstox, ProviderError, checked_spot
from .position import manage
from .state import append_audit,queue


def clock(): return datetime.now(IST)


def oi_comparison(previous: dict|None, chain: list[dict], expiry: str, now: datetime, spot: float|None=None):
    output={"status":"BASELINE_ONLY","flows":[]}
    if not previous or previous.get("expiry")!=expiry or previous.get("session_date")!=now.date().isoformat(): return output
    try:
        age=(now-datetime.fromisoformat(previous["fetched_at"])).total_seconds()
        if age<30 or age>900: return {"status":"BASELINE_GAP","flows":[]}
        old={r["instrument_key"]:r for r in previous["rows"]}
        flows=[]; changes=[]
        for r in chain:
            p=old.get(r["instrument_key"])
            if p and p["expiry"]==r["expiry"] and p["side"]==r["side"] and p["strike"]==r["strike"]:
                flow=classify_flow(float(p["oi"]),float(r["oi"]),float(p["ltp"]),float(r["ltp"]),r["side"])
                if spot is None or abs(float(r["strike"])-spot)<=250:
                    changes.append({"strike":r["strike"],"side":r["side"],"previous_oi":p["oi"],"current_oi":r["oi"],"oi_change":r["oi"]-p["oi"],"option_price_change":r["ltp"]-p["ltp"],"classification":flow})
                if flow not in {"UNAVAILABLE","UNCHANGED_OR_NOISY"}: flows.append({"strike":r["strike"],"side":r["side"],"classification":flow})
        return {"status":"COMPARABLE_RECEIPT_TIMES_ONLY","interval_seconds":age,"nearby_changes":changes,"flows":flows}
    except (KeyError,ValueError,TypeError): return {"status":"INVALID_BASELINE","flows":[]}


def scan(state: dict[str,Any], api: Upstox, config: Config, audit_dir: Path) -> dict:
    started=clock(); day=started.date().isoformat()
    result={"timestamp":started.isoformat(),"version":"113.0.0","session_date":day,"decision":"NO_TRADE","reason":"UNSET"}
    try:
        # Do not pretend an old open alert position was closed at a session rollover.
        if state.get("session_date") and state["session_date"]!=day and state.get("position"):
            result["reason"]="PRIOR_SESSION_POSITION_REQUIRES_RECONCILIATION"
            return result
        if state.get("session_date")!=day:
            state.update(session_date=day,thesis=None,oi_snapshot=None,futures_snapshot=None,last_exit=None,last_processed_candle=None)
        session=api.session(started)
        if session is None:
            if state.get("position"):
                result.update(decision="POSITION_MONITORING_UNAVAILABLE",reason="MARKET_CLOSED_POSITION_LOCK_RETAINED")
                queue(state,"MONITORING_UNAVAILABLE",{"position_id":state["position"].get("id"),"session_date":day,"cause":"MARKET_CLOSED"},clock())
            else: result["reason"]="MARKET_CLOSED_OR_TIMINGS_UNAVAILABLE"
            return result
        _,session_end=session
        raw=api.candles(); open_position=state.get("position")
        keys=[INDEX]+([open_position["instrument_key"]] if open_position else [])
        quotes=api.quotes(keys); now=clock(); bars,discarded=contiguous_tail(normalize_candles(raw,now))
        validate_candles(bars,now,config.min_bars)
        spot=checked_spot(quotes.get(INDEX,{}) ,now,config.max_quote_age)
        result.update(spot=spot,spot_quote_timestamp=quotes[INDEX]["timestamp"],last_complete_1m=bars[-1].start.isoformat(),discarded_pre_gap_candles=discarded)
        last_processed=state.get("last_processed_candle")
        if discarded and (not last_processed or datetime.fromisoformat(last_processed)<bars[0].start):
            state["thesis"]=None
            result["structure_reset_reason"]="UNSEEN_CANDLE_GAP"
        thesis=update_structure(bars,state.get("thesis")); state["thesis"]=thesis
        state["last_processed_candle"]=bars[-1].start.isoformat()
        result["structure"]=thesis
        if open_position:
            option_quote=quotes.get(open_position["instrument_key"])
            valid_option_quote=False
            try:
                qt=datetime.fromisoformat(str(option_quote["timestamp"]).replace("Z","+00:00"))
                age=(now-qt).total_seconds()
                valid_option_quote=qt.tzinfo is not None and -2<=age<=config.max_quote_age and float(option_quote["bid"])>0
            except (TypeError,KeyError,ValueError): pass
            if not valid_option_quote:
                result["premium_monitoring"]="OPTION_QUOTE_UNAVAILABLE_OR_STALE"
                queue(state,"MONITORING_DEGRADED",{"position_id":open_position["id"],"session_date":day,"cause":"OPTION_QUOTE_UNAVAILABLE_OR_STALE"},now)
            managed, events, closed=manage(open_position,bars,spot,option_quote,now,session_end,config,thesis)
            state["position"]=managed
            for event in events: queue(state,event["kind"],event,now)
            if closed:
                state["history"].append(closed); state["history"]=state["history"][-200:]
                state["last_exit"]={"at":closed["closed_at"],"direction":closed["direction"],"three":thesis.get("last_3m")}
                result.update(decision="POSITION_CLOSED",reason=closed["exit_reason"],position=closed)
            else: result.update(decision="POSITION_OPEN",reason="POSITION_LOCKED",position=managed)
            return result
        # Futures are contextual; an unavailable or tiny change never blocks entry.
        try:
            future=api.nearest_nifty_future(now,Path(".cache/nifty_futures_v113.json"))
            fq=api.quotes([future["instrument_key"]]).get(future["instrument_key"],{})
            ft=clock(); fp=checked_spot(fq,ft,config.max_quote_age)
            current={"instrument_key":future["instrument_key"],"price":fp,"oi":fq.get("oi"),"at":ft.isoformat()}
            prior=state.get("futures_snapshot")
            pattern="UNAVAILABLE"
            if prior and prior.get("instrument_key")==current["instrument_key"]:
                try:
                    gap=(ft-datetime.fromisoformat(prior["at"])).total_seconds()
                    if 30<=gap<=900:
                        pattern=classify_flow(float(prior["oi"]),float(current["oi"]),float(prior["price"]),fp,"CE")
                except (ValueError,TypeError,KeyError): pass
            state["futures_snapshot"]=current
            result["futures"]={**future,"price":fp,"average_price":fq.get("average_price"),"price_oi_pattern":pattern,"role":"CONTEXT_ONLY"}
        except ProviderError:
            result["futures"]={"status":"UNAVAILABLE","role":"CONTEXT_ONLY"}
        except DataError:
            result["futures"]={"status":"STALE","role":"CONTEXT_ONLY"}
        expiry,contracts=api.contracts(clock().date())
        chain=api.chain(expiry,contracts); chain_at=clock()
        result["chain_received_at"]=chain_at.isoformat(); result["chain_timestamp_quality"]="FETCH_TIME_ONLY"
        context=oi_context(chain,spot,config); result["oi_levels"]=context
        result["oi_flow_context"]=oi_comparison(state.get("oi_snapshot"),chain,expiry,chain_at,spot)
        state["oi_snapshot"]={"session_date":day,"expiry":expiry,"fetched_at":chain_at.isoformat(),"rows":chain}
        # Refresh spot and the allowed strikes immediately before the signal.
        strikes=sorted({r["strike"] for r in chain})
        if len(strikes)<3: raise DataError("INSUFFICIENT_STRIKE_GRID")
        actual_steps=sorted(set(round(b-a,6) for a,b in zip(strikes,strikes[1:]) if b>a))
        if not actual_steps or abs(actual_steps[0]-config.strike_step)>1e-6: raise DataError("STRIKE_GRID_CHANGED")
        atm=min(strikes,key=lambda x:(abs(x-spot),x))
        targets={atm+i*config.strike_step for i in range(-3,4)}
        keys=[INDEX]+[r["instrument_key"] for r in chain if r["strike"] in targets]
        full=api.quotes(keys); now=clock()
        validate_candles(bars,now,config.min_bars)
        if (now-chain_at).total_seconds()>config.max_quote_age: raise DataError("CHAIN_TOO_OLD")
        spot=checked_spot(full.get(INDEX,{}),now,config.max_quote_age)
        context=oi_context(chain,spot,config)
        supports=[float(x) for x in (thesis.get("confirmed_pivot_low"),thesis.get("confirmed_15m_pivot_low")) if x is not None and float(x)<spot]
        resistances=[float(x) for x in (thesis.get("confirmed_pivot_high"),thesis.get("confirmed_15m_pivot_high")) if x is not None and float(x)>spot]
        context.update(price_support=max(supports) if supports else None,price_resistance=min(resistances) if resistances else None)
        result.update(spot=spot,spot_quote_timestamp=full[INDEX]["timestamp"],oi_levels=context)
        setups=make_setups(bars,thesis,spot,config,context)
        if not setups:
            result["reason"]="WAIT_FOR_ALIGNED_PRICE_SETUP"; return result
        if (session_end-now).total_seconds()<=20*60:
            result["reason"]="ENTRY_TOO_CLOSE_TO_SESSION_END"; return result
        last=state.get("last_exit") or {}; evaluations=[]; passing=[]
        for candidate in setups:
            row={"setup":candidate}; allowed,reason=gate_candidate(candidate,thesis)
            if allowed and last.get("at"):
                if datetime.fromisoformat(candidate["confirmed_at"])<=datetime.fromisoformat(last["at"]):
                    allowed=False;reason="WAIT_FOR_FRESH_SETUP_AFTER_EXIT"
                elif last.get("direction")==candidate["direction"] and (not thesis.get("last_3m") or thesis["last_3m"]<=str(last.get("three") or "")):
                    allowed=False;reason="WAIT_FOR_NEW_3M_AFTER_SAME_DIRECTION_EXIT"
            plan=None;contract=None
            if allowed: plan,reason=risk_plan(candidate,spot,context,config)
            if plan:
                scenario="RANGE" if candidate["kind"].startswith("RANGE_") else "REVERSAL" if candidate["kind"]=="CONFIRMED_REVERSAL" else "TREND"
                contract,rejected=select_contract(chain,full,candidate["direction"],scenario,spot,now,expiry,config)
                row["rejected_contracts"]=rejected
                if not contract: reason="NO_FRESH_LIQUID_CONTRACT"
            if contract:
                event_key="|".join([day,expiry,candidate["direction"],contract["instrument_key"],candidate["confirmed_at"],candidate["kind"]])
                ident=hashlib.sha256(event_key.encode()).hexdigest()[:24]
                if any(p.get("id")==ident for p in state["history"]): reason="DUPLICATE_SUPPRESSED"
                else:
                    reason="QUALIFIED";passing.append((candidate,plan,contract,ident))
            row.update(reason=reason,risk_plan=plan,selected_contract=contract);evaluations.append(row)
        result["candidate_evaluations"]=evaluations
        if not passing:
            result["reason"]=evaluations[0]["reason"];return result
        # Newest valid trigger wins; a rejected candidate never hides another.
        setup,plan,contract,ident=passing[0]
        result.update(setup=setup,risk_plan=plan)
        position={"id":ident,"status":"OPEN","session_date":day,"opened_at":now.isoformat(),"direction":setup["direction"],"kind":setup["kind"],"instrument_key":contract["instrument_key"],"expiry":expiry,"strike":contract["strike"],"side":contract["side"],"entry_spot":spot,"entry_ask":contract["ask"],"stop":plan["stop_underlying"],"t1":plan["t1_underlying"],"t2":plan["t2_underlying"],"t1_hit":False,"remaining_pct":100,"last_candle":now.replace(second=0,microsecond=0).isoformat(),"last_progress_at":now.isoformat(),"best_spot":spot,"entry_minute_ohlc_ignored":True,"plan":plan,"contract":contract}
        state["position"]=position
        queue(state,"ENTRY",{"position":position,"structure":thesis,"oi_levels":context},now)
        result.update(decision="QUALIFIED",reason="QUALIFIED_"+contract["side"],position=position)
        return result
    except (DataError,ProviderError,ValueError,KeyError,TypeError) as exc:
        result.update(decision="NO_TRADE",reason="DATA_OR_INTEGRATION_ERROR",message=str(exc))
        if state.get("position"):
            result.update(decision="POSITION_MONITORING_UNAVAILABLE",reason="POSITION_LOCK_RETAINED")
            queue(state,"MONITORING_UNAVAILABLE",{"position_id":state["position"].get("id"),"session_date":day,"cause":str(exc)},clock())
        return result
    finally:
        result["finished_at"]=clock().isoformat()
        append_audit(audit_dir/("market_scan_v113_"+day+".jsonl"),result)
