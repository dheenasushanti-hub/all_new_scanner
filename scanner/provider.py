"""Upstox REST adapter; read-only, no order placement."""
from __future__ import annotations
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
from .core import DataError, IST

INDEX="NSE_INDEX|Nifty 50"

class ProviderError(RuntimeError):
    pass

class Upstox:
    def __init__(self, token: str):
        if not token or any(c in token for c in "\r\n"):
            raise ProviderError("UPSTOX_ANALYTICS_TOKEN missing or invalid")
        self._token=token

    def get(self,path: str,params: dict|None=None):
        url="https://api.upstox.com"+path+("?"+urlencode(params) if params else "")
        req=Request(url,headers={"Authorization":"Bearer "+self._token,"Accept":"application/json","User-Agent":"nifty-scanner/113"})
        for attempt in range(3):
            try:
                with urlopen(req,timeout=12) as r:
                    obj=json.load(r)
                if not isinstance(obj,dict) or obj.get("status")!="success" or "data" not in obj:
                    raise ProviderError("Upstox returned an unsuccessful or invalid response")
                return obj["data"]
            except HTTPError as e:
                if e.code in (429,500,502,503,504) and attempt<2:
                    time.sleep(1+attempt); continue
                raise ProviderError(f"Upstox request failed HTTP {e.code}") from None
            except (URLError, TimeoutError, OSError, json.JSONDecodeError) as e:
                if attempt<2: time.sleep(1+attempt); continue
                raise ProviderError("Upstox request failed or returned invalid JSON") from None
        raise ProviderError("Upstox request failed")

    def session(self, now: datetime):
        data=self.get("/v2/market/timings/"+now.astimezone(IST).date().isoformat())
        matches=[x for x in data if x.get("exchange")=="NFO"] if isinstance(data,list) else []
        if not matches: return None
        sessions=[]
        for row in matches:
            start=datetime.fromtimestamp(float(row["start_time"])/1000,timezone.utc).astimezone(IST)
            end=datetime.fromtimestamp(float(row["end_time"])/1000,timezone.utc).astimezone(IST)
            if start.date()==now.astimezone(IST).date() and start<end: sessions.append((start,end))
        return next(((a,b) for a,b in sessions if a<=now.astimezone(IST)<b),None)

    def candles(self,key=INDEX):
        data=self.get("/v3/historical-candle/intraday/"+quote(key,safe="")+"/minutes/1")
        if not isinstance(data,dict) or not isinstance(data.get("candles"),list): raise ProviderError("Invalid candle response")
        return data["candles"]

    def contracts(self, today: date):
        data=self.get("/v2/option/contract",{"instrument_key":INDEX})
        if not isinstance(data,list): raise ProviderError("Invalid option contract response")
        rows=[]
        for r in data:
            if r.get("underlying_key")!=INDEX or r.get("instrument_type") not in ("CE","PE"): continue
            try: exp=date.fromisoformat(str(r["expiry"]))
            except (ValueError,KeyError): continue
            if exp>=today: rows.append(r)
        if not rows: raise ProviderError("No unexpired NIFTY option contracts")
        expiry=min(date.fromisoformat(r["expiry"]) for r in rows).isoformat()
        return expiry,[r for r in rows if r["expiry"]==expiry]

    def chain(self,expiry: str, contracts: list[dict]):
        data=self.get("/v2/option/chain",{"instrument_key":INDEX,"expiry_date":expiry})
        if not isinstance(data,list) or not data: raise ProviderError("Empty option chain")
        valid={r["instrument_key"]:(float(r["strike_price"]),r["instrument_type"]) for r in contracts if r.get("instrument_key") and r.get("strike_price") is not None}
        result=[]; seen=set()
        for row in data:
            if row.get("underlying_key")!=INDEX or row.get("expiry")!=expiry: raise ProviderError("Chain underlying or expiry mismatch")
            try: strike=float(row["strike_price"])
            except (TypeError,ValueError,KeyError): raise ProviderError("Invalid strike") from None
            for side,field in (("CE","call_options"),("PE","put_options")):
                option=row.get(field) or {}; key=option.get("instrument_key")
                if not key: continue
                if valid.get(key)!=(strike,side) or key in seen: raise ProviderError("Contract identity mismatch")
                seen.add(key); market=option.get("market_data") or {}; greeks=option.get("option_greeks") or {}
                try:
                    oi=float(market.get("oi") or 0); ltp=float(market.get("ltp") or 0); volume=float(market.get("volume") or 0)
                    delta=float(greeks["delta"]) if greeks.get("delta") is not None else None
                    gamma=float(greeks["gamma"]) if greeks.get("gamma") is not None else None
                    theta=float(greeks["theta"]) if greeks.get("theta") is not None else None
                except (ValueError,TypeError): raise ProviderError("Invalid OI/greek data") from None
                if not all(isfinite(x) and x>=0 for x in (oi,ltp,volume)): raise ProviderError("Invalid option chain values")
                if any(x is not None and not isfinite(x) for x in (delta,gamma,theta)): raise ProviderError("Invalid option greek data")
                result.append({"instrument_key":key,"expiry":expiry,"strike":strike,"side":side,"oi":oi,"ltp":ltp,"volume":volume,"delta":delta,"gamma":gamma,"theta":theta})
        if len(result)<4 or not {"CE","PE"}.issubset({r["side"] for r in result}): raise ProviderError("Incomplete option chain")
        return result

    def quotes(self,keys: list[str]):
        if not keys: return {}
        data=self.get("/v2/market-quote/quotes",{"instrument_key":",".join(dict.fromkeys(keys))})
        if not isinstance(data,dict): raise ProviderError("Invalid quote response")
        out={}
        for q in data.values():
            key=q.get("instrument_token"); stamp=q.get("timestamp")
            if key not in keys or not stamp: continue
            try:
                price=float(q.get("last_price") or 0)
                buys=(q.get("depth") or {}).get("buy") or []
                sells=(q.get("depth") or {}).get("sell") or []
                b=buys[0] if buys else {}; a=sells[0] if sells else {}
                numeric={name:float(q[name]) if q.get(name) is not None else None for name in ("oi","average_price")}
                for name,value in numeric.items():
                    if value is not None and not isfinite(value): numeric[name]=None
                quoted={"last_price":price,"bid":float(b.get("price") or 0),"bid_qty":float(b.get("quantity") or 0),"ask":float(a.get("price") or 0),"ask_qty":float(a.get("quantity") or 0)}
                if any(not isfinite(x) or x<0 for x in quoted.values()): continue
                out[key]={**quoted,"timestamp":stamp,**numeric}
            except (TypeError,ValueError): continue
        return out

    def nearest_nifty_future(self, now: datetime, cache: Path) -> dict:
        """Resolve from the provider's daily instrument master, never stale-cache fallback."""
        day=now.astimezone(IST).date().isoformat()
        try:
            if cache.exists():
                saved=json.loads(cache.read_text(encoding="utf-8"))
                if saved.get("day")==day and saved.get("instruments"):
                    instruments=saved["instruments"]
                else: instruments=[]
            else: instruments=[]
            if not instruments:
                req=Request("https://assets.upstox.com/market-quote/instruments/exchange/NSE.json.gz",headers={"User-Agent":"nifty-scanner/113"})
                with urlopen(req,timeout=20) as response:
                    raw=response.read(40_000_001)
                if len(raw)>40_000_000: raise ProviderError("Instrument master too large")
                master=json.loads(gzip.decompress(raw))
                instruments=[x for x in master if x.get("segment")=="NSE_FO" and x.get("instrument_type")=="FUT" and x.get("underlying_key")==INDEX and x.get("underlying_symbol")=="NIFTY"]
                if not instruments: raise ProviderError("No NIFTY futures in instrument master")
                cache.parent.mkdir(parents=True,exist_ok=True)
                tmp=cache.with_suffix(".tmp")
                tmp.write_text(json.dumps({"day":day,"instruments":instruments}),encoding="utf-8")
                os.replace(tmp,cache)
            found=[]
            for item in instruments:
                exp=datetime.fromtimestamp(float(item["expiry"])/1000,timezone.utc).astimezone(IST).date()
                if exp>=now.astimezone(IST).date(): found.append((exp,item))
            if not found: raise ProviderError("No unexpired NIFTY future")
            exp,item=min(found,key=lambda t:t[0])
            return {"instrument_key":item["instrument_key"],"expiry":exp.isoformat(),"trading_symbol":item.get("trading_symbol")}
        except (OSError,ValueError,TypeError,KeyError,URLError,json.JSONDecodeError) as e:
            raise ProviderError("NIFTY futures master unavailable") from None


def checked_spot(quote_data: dict, now: datetime, max_age: float) -> float:
    try:
        timestamp=datetime.fromisoformat(str(quote_data["timestamp"]).replace("Z","+00:00"))
        if timestamp.tzinfo is None: raise ValueError()
        age=(now-timestamp).total_seconds(); spot=float(quote_data["last_price"])
        if age< -2 or age>max_age or not isfinite(spot) or spot<=0: raise ValueError()
        return spot
    except (TypeError,ValueError,KeyError):
        raise DataError("SPOT_QUOTE_STALE_OR_INVALID") from None
