/* ProEdge Scanner: runs on GitHub Actions and sends BUY/SELL alerts to Telegram.
   The signal engine below is identical to ProEdge_v2.html, so the app and the scanner always agree. */

/* ======== SIGNAL ENGINE (same as ProEdge_v2.html) ======== */
const TF = {
  '5m':  {ms:300000,   htf:'15m'},
  '15m': {ms:900000,   htf:'1h'},
  '1h':  {ms:3600000,  htf:'4h'},
  '4h':  {ms:14400000, htf:'1d'},
  '1d':  {ms:86400000, htf:null}
};
const isNum = v => typeof v === 'number' && isFinite(v);
const last = a => a[a.length-1];
const clamp = (v,a,b) => Math.max(a, Math.min(b, v));
function dec(p){ const a=Math.abs(p); return a>=1000?2:a>=100?3:a>=10?4:a>=1?5:6; }
function fmt(p){ return isNum(p) ? p.toFixed(dec(p)) : '—'; }

/* ---------- data parsers ---------- */
function parseBinance(j){
  if(!Array.isArray(j)) throw new Error('bad Binance reply');
  return j.map(k=>({t:+k[0],o:+k[1],h:+k[2],l:+k[3],c:+k[4],v:+k[5]}));
}
function parseBybit(j){
  if(!j || j.retCode!==0 || !j.result || !Array.isArray(j.result.list)) throw new Error('bad Bybit reply');
  return j.result.list.map(k=>({t:+k[0],o:+k[1],h:+k[2],l:+k[3],c:+k[4],v:+k[5]})).reverse();
}
function parseOKX(j){
  if(!j || j.code!=='0' || !Array.isArray(j.data)) throw new Error('bad OKX reply');
  return j.data.map(k=>({t:+k[0],o:+k[1],h:+k[2],l:+k[3],c:+k[4],v:+k[5]})).reverse();
}
function parseYahoo(j){
  const r = j && j.chart && j.chart.result && j.chart.result[0];
  if(!r || !r.timestamp || !r.indicators || !r.indicators.quote || !r.indicators.quote[0]) throw new Error('bad Yahoo reply');
  const q = r.indicators.quote[0], out=[];
  for(let i=0;i<r.timestamp.length;i++){
    if(isNum(q.open[i]) && isNum(q.high[i]) && isNum(q.low[i]) && isNum(q.close[i]))
      out.push({t:r.timestamp[i]*1000,o:q.open[i],h:q.high[i],l:q.low[i],c:q.close[i],v:q.volume&&isNum(q.volume[i])?q.volume[i]:0});
  }
  return out;
}
function parseDeriv(j){
  if(!j || !Array.isArray(j.candles)) throw new Error('bad Deriv reply');
  return j.candles.map(k=>({t:+k.epoch*1000,o:+k.open,h:+k.high,l:+k.low,c:+k.close,v:0}));
}
function parseTD(j){
  if(!j || j.status==='error') throw new Error((j&&j.message)||'bad Twelve Data reply');
  if(!Array.isArray(j.values)) throw new Error('bad Twelve Data reply');
  return j.values.map(k=>({t:Date.parse(String(k.datetime).replace(' ','T')+(String(k.datetime).length>10?'Z':'T00:00:00Z')),o:+k.open,h:+k.high,l:+k.low,c:+k.close,v:+(k.volume||0)}));
}
function clean(cs){
  const m = new Map();
  for(const k of cs){
    if(isNum(k.t)&&isNum(k.o)&&isNum(k.h)&&isNum(k.l)&&isNum(k.c)&&k.h>=k.l&&k.h>=Math.max(k.o,k.c)-1e-12&&k.l<=Math.min(k.o,k.c)+1e-12) m.set(k.t,k);
  }
  return [...m.values()].sort((a,b)=>a.t-b.t);
}
function resample(cs, ms){
  const out=[]; let cur=null;
  for(const k of cs){
    const b=Math.floor(k.t/ms)*ms;
    if(!cur || cur.t!==b){ if(cur) out.push(cur); cur={t:b,o:k.o,h:k.h,l:k.l,c:k.c,v:k.v}; }
    else { cur.h=Math.max(cur.h,k.h); cur.l=Math.min(cur.l,k.l); cur.c=k.c; cur.v+=k.v; }
  }
  if(cur) out.push(cur);
  return out;
}

/* ---------- indicators ---------- */
function emaNaN(v,n){
  const out=new Array(v.length).fill(NaN);
  let s=-1; for(let i=0;i<v.length;i++){ if(isNum(v[i])){ s=i; break; } }
  if(s<0 || v.length-s<n) return out;
  let sum=0; for(let i=s;i<s+n;i++) sum+=v[i];
  let prev=sum/n; out[s+n-1]=prev;
  const k=2/(n+1);
  for(let i=s+n;i<v.length;i++){ prev=v[i]*k+prev*(1-k); out[i]=prev; }
  return out;
}
function rsiCalc(c,n=14){
  const out=new Array(c.length).fill(NaN);
  if(c.length<=n) return out;
  let g=0,l=0;
  for(let i=1;i<=n;i++){ const d=c[i]-c[i-1]; if(d>0) g+=d; else l-=d; }
  let ag=g/n, al=l/n;
  const f=()=> (ag===0&&al===0)?50:(al===0?100:100-100/(1+ag/al));
  out[n]=f();
  for(let i=n+1;i<c.length;i++){
    const d=c[i]-c[i-1];
    ag=(ag*(n-1)+(d>0?d:0))/n;
    al=(al*(n-1)+(d<0?-d:0))/n;
    out[i]=f();
  }
  return out;
}
function trCalc(h,l,c){
  const t=[h[0]-l[0]];
  for(let i=1;i<c.length;i++) t.push(Math.max(h[i]-l[i],Math.abs(h[i]-c[i-1]),Math.abs(l[i]-c[i-1])));
  return t;
}
function atrCalc(h,l,c,n=14){
  const tr=trCalc(h,l,c), out=new Array(c.length).fill(NaN);
  if(tr.length<n) return out;
  let s=0; for(let i=0;i<n;i++) s+=tr[i];
  let a=s/n; out[n-1]=a;
  for(let i=n;i<tr.length;i++){ a=(a*(n-1)+tr[i])/n; out[i]=a; }
  return out;
}
function adxCalc(h,l,c,n=14){
  const N=c.length;
  const pdi=new Array(N).fill(NaN), mdi=new Array(N).fill(NaN), adx=new Array(N).fill(NaN);
  if(N<2*n+1) return {pdi,mdi,adx};
  const tr=[0],pdm=[0],mdm=[0];
  for(let i=1;i<N;i++){
    const up=h[i]-h[i-1], dn=l[i-1]-l[i];
    pdm.push(up>dn&&up>0?up:0);
    mdm.push(dn>up&&dn>0?dn:0);
    tr.push(Math.max(h[i]-l[i],Math.abs(h[i]-c[i-1]),Math.abs(l[i]-c[i-1])));
  }
  let trS=0,pS=0,mS=0;
  for(let i=1;i<=n;i++){ trS+=tr[i]; pS+=pdm[i]; mS+=mdm[i]; }
  const dx=new Array(N).fill(NaN);
  const setDI=i=>{
    pdi[i]=trS?100*pS/trS:0; mdi[i]=trS?100*mS/trS:0;
    const s=pdi[i]+mdi[i]; dx[i]=s?100*Math.abs(pdi[i]-mdi[i])/s:0;
  };
  setDI(n);
  for(let i=n+1;i<N;i++){ trS=trS-trS/n+tr[i]; pS=pS-pS/n+pdm[i]; mS=mS-mS/n+mdm[i]; setDI(i); }
  let s=0; for(let i=n;i<=2*n-1;i++) s+=dx[i];
  let a=s/n; adx[2*n-1]=a;
  for(let i=2*n;i<N;i++){ a=(a*(n-1)+dx[i])/n; adx[i]=a; }
  return {pdi,mdi,adx};
}
function macdCalc(c,f=12,s=26,sg=9){
  const ef=emaNaN(c,f), es=emaNaN(c,s);
  const line=c.map((_,i)=>isNum(ef[i])&&isNum(es[i])?ef[i]-es[i]:NaN);
  const sig=emaNaN(line,sg);
  const hist=line.map((v,i)=>isNum(v)&&isNum(sig[i])?v-sig[i]:NaN);
  return {line,sig,hist};
}
function swingPoints(h,l,L=3,R=3){
  const highs=[],lows=[];
  for(let i=L;i<h.length-R;i++){
    let isH=true,isL=true;
    for(let k=1;k<=L;k++){ if(h[i-k]>=h[i]) isH=false; if(l[i-k]<=l[i]) isL=false; }
    for(let k=1;k<=R;k++){ if(h[i+k]>h[i]) isH=false; if(l[i+k]<l[i]) isL=false; }
    if(isH) highs.push({i,p:h[i]});
    if(isL) lows.push({i,p:l[i]});
  }
  return {highs,lows};
}

/* ---------- fair value gaps (unfilled only) ---------- */
function findFVGs(o,h,l,c,atr,lookback=100){
  const N=h.length, start=Math.max(2,N-lookback), res=[];
  for(let i=start;i<N;i++){
    const a=atr[i]; if(!isNum(a)) continue;
    const minGap=a*0.15;
    let z=null;
    if(l[i]-h[i-2]>=minGap && c[i-1]>o[i-1]) z={type:'bull',top:l[i],bottom:h[i-2],i};
    else if(l[i-2]-h[i]>=minGap && c[i-1]<o[i-1]) z={type:'bear',top:l[i-2],bottom:h[i],i};
    if(!z) continue;
    let filled=false;
    for(let j=i+1;j<N;j++){
      if(z.type==='bull' && l[j]<=z.bottom){ filled=true; break; }
      if(z.type==='bear' && h[j]>=z.top){ filled=true; break; }
    }
    if(!filled) res.push(z);
  }
  return res;
}

/* ---------- candlestick patterns on candle i ---------- */
function detectPatterns(o,h,l,c,i,atrv,ema21){
  const out=[];
  if(i<6) return out;
  const body=k=>Math.abs(c[k]-o[k]), rng=k=>h[k]-l[k];
  const up=k=>h[k]-Math.max(o[k],c[k]), lo=k=>Math.min(o[k],c[k])-l[k];
  const bull=k=>c[k]>o[k], bear=k=>c[k]<o[k];
  const R=rng(i), B=body(i);
  if(!(R>0)) return out;
  const downCtx = c[i-1]<c[i-6] && (!isNum(ema21[i-1]) || c[i-1]<ema21[i-1]);
  const upCtx   = c[i-1]>c[i-6] && (!isNum(ema21[i-1]) || c[i-1]>ema21[i-1]);
  if(B<=0.1*R) out.push({name:'Doji (indecision)',dir:0,w:0});
  if(B<=0.4*R && lo(i)>=2*B && lo(i)>=0.6*R && up(i)<=0.25*R)
    out.push(downCtx?{name:'Hammer',dir:1,w:8}:{name:'Bullish pin bar',dir:1,w:5});
  if(B<=0.4*R && up(i)>=2*B && up(i)>=0.6*R && lo(i)<=0.25*R)
    out.push(upCtx?{name:'Shooting star',dir:-1,w:8}:{name:'Bearish pin bar',dir:-1,w:5});
  if(bull(i)&&bear(i-1)&&c[i]>=o[i-1]&&o[i]<=c[i-1]&&B>body(i-1)&&B>=0.5*atrv)
    out.push({name:'Bullish engulfing',dir:1,w:downCtx?10:7});
  if(bear(i)&&bull(i-1)&&c[i]<=o[i-1]&&o[i]>=c[i-1]&&B>body(i-1)&&B>=0.5*atrv)
    out.push({name:'Bearish engulfing',dir:-1,w:upCtx?10:7});
  if(i>=2){
    if(bear(i-2)&&body(i-2)>=0.6*rng(i-2)&&body(i-1)<=0.35*body(i-2)&&bull(i)&&c[i]>(o[i-2]+c[i-2])/2)
      out.push({name:'Morning star',dir:1,w:12});
    if(bull(i-2)&&body(i-2)>=0.6*rng(i-2)&&body(i-1)<=0.35*body(i-2)&&bear(i)&&c[i]<(o[i-2]+c[i-2])/2)
      out.push({name:'Evening star',dir:-1,w:12});
    if(bull(i)&&bull(i-1)&&bull(i-2)&&c[i]>c[i-1]&&c[i-1]>c[i-2]&&o[i]>o[i-1]&&o[i-1]>o[i-2]&&body(i)>=0.5*R&&body(i-1)>=0.5*rng(i-1)&&body(i-2)>=0.5*rng(i-2))
      out.push({name:'Three white soldiers',dir:1,w:9});
    if(bear(i)&&bear(i-1)&&bear(i-2)&&c[i]<c[i-1]&&c[i-1]<c[i-2]&&o[i]<o[i-1]&&o[i-1]<o[i-2]&&body(i)>=0.5*R&&body(i-1)>=0.5*rng(i-1)&&body(i-2)>=0.5*rng(i-2))
      out.push({name:'Three black crows',dir:-1,w:9});
  }
  if(B>=0.85*R && B>=0.8*atrv) out.push(bull(i)?{name:'Bullish marubozu',dir:1,w:5}:{name:'Bearish marubozu',dir:-1,w:5});
  return out;
}

/* ---------- higher timeframe bias ---------- */
function htfBias(cs){
  if(!cs || cs.length<60) return null;
  const cl=cs.map(k=>k.c), e21=emaNaN(cl,21), e50=emaNaN(cl,50), i=cl.length-1;
  if(!isNum(e50[i])) return null;
  const p=cl[i], a=e21[i], b=e50[i];
  if(p>b && a>b) return {score:13,label:'Bullish'};
  if(p<b && a<b) return {score:-13,label:'Bearish'};
  if(p>b) return {score:5,label:'Mild bullish'};
  if(p<b) return {score:-5,label:'Mild bearish'};
  return {score:0,label:'Neutral'};
}

/* ---------- main analysis (closed candles only) ---------- */
function analyze(p){
  const cs=p.candles, N=cs.length;
  if(N<60) return {error:'Not enough candles ('+N+'). Need at least 60.'};
  const o=cs.map(k=>k.o), h=cs.map(k=>k.h), l=cs.map(k=>k.l), c=cs.map(k=>k.c), t=cs.map(k=>k.t);
  const e9=emaNaN(c,9), e21=emaNaN(c,21), e50=emaNaN(c,50), e200=emaNaN(c,200);
  const rsiA=rsiCalc(c,14), atrA=atrCalc(h,l,c,14), adxO=adxCalc(h,l,c,14), mac=macdCalc(c);
  const i=N-1;
  const price=isNum(p.live)?p.live:c[i];
  const atrV=atrA[i], rsiV=rsiA[i], adxV=adxO.adx[i], pdi=adxO.pdi[i], mdi=adxO.mdi[i];
  if(!(atrV>0)) return {error:'Price data looks flat (ATR is zero). Market may be closed.'};
  if(![e21[i],e50[i],rsiV,adxV,mac.hist[i],mac.hist[i-1]].every(isNum)) return {error:'Not enough history to compute all indicators.'};
  const has200=isNum(e200[i]);

  const comps=[];
  // 1) trend
  let sT=0;
  sT += c[i]>e50[i]?10:-10;
  sT += e21[i]>e50[i]?8:-8;
  if(has200) sT += e50[i]>e200[i]?7:-7;
  comps.push({name:'Trend (EMAs)',score:sT,max:25,
    note:'Close '+(c[i]>e50[i]?'above':'below')+' EMA50, EMA21 '+(e21[i]>e50[i]?'above':'below')+' EMA50'+(has200?', EMA50 '+(e50[i]>e200[i]?'above':'below')+' EMA200':', EMA200 n/a (short history)')});
  // 2) MACD
  const h0=mac.hist[i], h1=mac.hist[i-1];
  const sM=(h0>0?8:-8)+(h0>h1?4:-4)+(mac.line[i]>0?3:-3);
  comps.push({name:'Momentum (MACD)',score:sM,max:15,
    note:'Histogram '+(h0>0?'positive':'negative')+' and '+(h0>h1?'rising':'falling')+', line '+(mac.line[i]>0?'above':'below')+' zero'});
  // 3) RSI
  let sR;
  if(rsiV>=75) sR=-6; else if(rsiV>=60) sR=8; else if(rsiV>=50) sR=4;
  else if(rsiV>=40) sR=-4; else if(rsiV>25) sR=-8; else sR=6;
  comps.push({name:'RSI zone',score:sR,max:10,
    note:'RSI '+rsiV.toFixed(1)+(rsiV>=75?' (overbought, bullish bias weakened)':rsiV<=25?' (oversold, bounce risk)':rsiV>=50?' (bullish zone)':' (bearish zone)')});
  // 4) ADX / DI
  const dir0=pdi>mdi?1:-1;
  const base=adxV>=25?15:adxV>=20?10:4;
  comps.push({name:'Trend strength (ADX)',score:dir0*base,max:15,
    note:'ADX '+adxV.toFixed(1)+', +DI '+pdi.toFixed(1)+' vs -DI '+mdi.toFixed(1)+(adxV<20?' (weak / ranging)':adxV>=25?' (strong trend)':' (developing trend)')});
  // 5) candle patterns
  const pats=detectPatterns(o,h,l,c,i,atrV,e21);
  const mb=Math.max(0,...pats.filter(x=>x.dir>0).map(x=>x.w)), ms=Math.max(0,...pats.filter(x=>x.dir<0).map(x=>x.w));
  const sP=clamp(mb-ms,-12,12);
  comps.push({name:'Candle pattern',score:sP,max:12,
    note:pats.length?pats.map(x=>x.name).join(', '):'No significant pattern on the last closed candle'});
  // 6) FVG
  const zonesAll=findFVGs(o,h,l,c,atrA,100);
  const dist=z=> price>z.top ? price-z.top : (price<z.bottom ? z.bottom-price : 0);
  let sup=0,res=0;
  for(const z of zonesAll){
    const d=dist(z), w=d<=0.5*atrV?10:d<=atrV?6:0;
    if(z.type==='bull') sup=Math.max(sup,w); else res=Math.max(res,w);
  }
  const sF=clamp(sup-res,-10,10);
  const near=zonesAll.map(z=>({...z,d:dist(z)})).sort((a,b)=>a.d-b.d).slice(0,4);
  comps.push({name:'Fair value gap',score:sF,max:10,
    note:sF>0?'Open bullish FVG acting as support nearby':sF<0?'Open bearish FVG acting as resistance nearby':(sup||res)?'Bullish and bearish FVGs both nearby (cancel out)':'No open FVG close to price'});
  // 7) higher timeframe
  const hb=htfBias(p.htf);
  comps.push({name:'Higher timeframe'+(p.htfTf?' ('+p.htfTf+')':''),score:hb?hb.score:0,max:13,
    note:hb?hb.label+' trend on '+p.htfTf:(p.htfTf?'Higher-timeframe data unavailable (counted as neutral)':'No higher timeframe for this chart')});

  const score=comps.reduce((a,x)=>a+x.score,0);
  const direction=score>0?1:score<0?-1:0;

  // freshness
  const ageMs=p.now-(t[i]+p.ms);
  const stale=ageMs>3*p.ms;

  // gates
  const gates=[];
  if(stale) gates.push('Data looks stale (last closed candle is '+Math.round(ageMs/60000)+' min old). Market may be closed.');
  if(adxV<20) gates.push('ADX is '+adxV.toFixed(1)+' (below 20): market is ranging, trend signals are unreliable.');
  if(Math.abs(score)<50) gates.push('Combined score '+(score>0?'+':'')+score+' is below the ±50 threshold.');
  if(direction>0 && rsiV>=78) gates.push('RSI '+rsiV.toFixed(1)+' is extremely overbought; buying here is chasing.');
  if(direction<0 && rsiV<=22) gates.push('RSI '+rsiV.toFixed(1)+' is extremely oversold; selling here is chasing.');
  if(hb && direction!==0 && hb.score*direction<=-13) gates.push('Higher-timeframe trend ('+hb.label+') is against this direction.');
  const signal=gates.length===0&&direction!==0?(direction>0?'BUY':'SELL'):'NO TRADE';
  const conf=Math.min(100,Math.abs(score));
  const grade=conf>=70?'Strong':conf>=50?'Moderate':'Weak';

  // swing levels
  const sw=swingPoints(h,l,3,3), win=N-100;
  const supL=sw.lows.filter(s=>s.i>=win&&s.p<price).map(s=>s.p).sort((a,b)=>b-a)[0];
  const resL=sw.highs.filter(s=>s.i>=win&&s.p>price).map(s=>s.p).sort((a,b)=>a-b)[0];

  // trade plan
  let plan=null;
  if(signal!=='NO TRADE'){
    const dir=direction; let slDist=1.5*atrV;
    if(dir>0 && isNum(supL)){ const d=price-(supL-0.25*atrV); if(d>=atrV&&d<=2.5*atrV) slDist=d; }
    if(dir<0 && isNum(resL)){ const d=(resL+0.25*atrV)-price; if(d>=atrV&&d<=2.5*atrV) slDist=d; }
    plan={entry:price,sl:price-dir*slDist,tp1:price+dir*slDist*1.5,tp2:price+dir*slDist*2.5,risk:slDist,slPct:slDist/price*100};
  }

  // chart window
  const W=70, s0=Math.max(0,N-W);
  const chart={o:o.slice(s0),h:h.slice(s0),l:l.slice(s0),c:c.slice(s0),e21:e21.slice(s0),e50:e50.slice(s0),
    zones:zonesAll.filter(z=>z.i>=s0-30).map(z=>({type:z.type,top:z.top,bottom:z.bottom,i:z.i-s0}))};

  return {symbol:p.symbol,tf:p.tf,market:p.market,price,lastT:t[i],ageMs,stale,
    ind:{ema9:e9[i],ema21:e21[i],ema50:e50[i],ema200:has200?e200[i]:NaN,rsi:rsiV,macd:mac.line[i],macdSig:mac.sig[i],hist:h0,adx:adxV,pdi,mdi,atr:atrV,atrPct:atrV/price*100},
    comps,score,direction,gates,signal,grade,conf,htf:hb?{...hb,tf:p.htfTf}:null,plan,
    fvgNear:near,patterns:pats,support:supL,resist:resL,chart};
}

/* ================================================================
   Scanner part: data loading, Telegram alerts, de-duplication
   ================================================================ */
import fs from 'node:fs';

const TOKEN = process.env.TELEGRAM_BOT_TOKEN || '';
const CHAT = process.env.TELEGRAM_CHAT_ID || '';
const TDKEY = process.env.TWELVEDATA_KEY || '';
const TEST_MODE = String(process.env.TEST_MODE || '') === 'true';
const TIMEFRAMES = (process.env.TIMEFRAMES || '15m,1h,4h').split(',').map(s => s.trim()).filter(x => TF[x]);
const MARKETS = (process.env.MARKETS || 'crypto,forex,synth').split(',').map(s => s.trim());
const STATE_FILE = 'state.json';
const SETTLE_MS = 20000;      // wait after a candle closes before reading it
const REPEAT_CANDLES = 8;     // never repeat the same signal within this many candles
const RETRY_MS = 15 * 60000;  // after a data failure, wait before retrying that pair

const CRYPTO = ['BTCUSDT','ETHUSDT','SOLUSDT','BNBUSDT','XRPUSDT','ADAUSDT','DOGEUSDT','LINKUSDT','AVAXUSDT','TONUSDT'];
const FOREX = [
  {s:'EURUSD',y:['EURUSD=X'],td:'EUR/USD',bn:'EURUSDT'},
  {s:'GBPUSD',y:['GBPUSD=X'],td:'GBP/USD',bn:'GBPUSDT'},
  {s:'USDJPY',y:['JPY=X'],td:'USD/JPY'},
  {s:'AUDUSD',y:['AUDUSD=X'],td:'AUD/USD',bn:'AUDUSDT'},
  {s:'USDCAD',y:['CAD=X'],td:'USD/CAD'},
  {s:'USDCHF',y:['CHF=X'],td:'USD/CHF'},
  {s:'NZDUSD',y:['NZDUSD=X'],td:'NZD/USD'},
  {s:'EURJPY',y:['EURJPY=X'],td:'EUR/JPY'},
  {s:'GBPJPY',y:['GBPJPY=X'],td:'GBP/JPY'},
  {s:'XAUUSD',y:['XAUUSD=X','GC=F'],td:'XAU/USD',bn:'PAXGUSDT'}
];
const SYNTH = [
  {s:'R_10',n:'Volatility 10'},{s:'R_25',n:'Volatility 25'},{s:'R_75',n:'Volatility 75'},
  {s:'R_100',n:'Volatility 100'},{s:'stpRNG',n:'Step Index'}
];
const BYBIT = {'5m':'5','15m':'15','1h':'60','4h':'240','1d':'D'};
const OKX = {'5m':'5m','15m':'15m','1h':'1H','4h':'4H','1d':'1D'};
const TDI = {'5m':'5min','15m':'15min','1h':'1h','4h':'4h','1d':'1day'};
const YAHOO = {
  '5m':{iv:'5m',range:'5d'}, '15m':{iv:'15m',range:'10d'}, '1h':{iv:'60m',range:'1mo'},
  '4h':{iv:'60m',range:'3mo',rs:14400000}, '1d':{iv:'1d',range:'2y'}
};
const DERIV_GRAN = {'5m':300,'15m':900,'1h':3600,'4h':14400,'1d':86400};
const UA = 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36';

const labelOf = (mk, s) => mk === 'crypto' ? s.replace('USDT', '/USDT')
  : mk === 'forex' ? s.slice(0, 3) + '/' + s.slice(3)
  : (SYNTH.find(x => x.s === s) || {n: s}).n;

/* ---------- network helpers ---------- */
async function getJSON(url, ms = 10000, headers = {}) {
  const r = await fetch(url, {signal: AbortSignal.timeout(ms), headers});
  if (!r.ok) throw new Error('HTTP ' + r.status);
  return r.json();
}

function derivCandles(symbol, tf) {
  return new Promise((resolve, reject) => {
    let ws = null, done = false, timer = null;
    const fin = (fn, v) => { if (done) return; done = true; clearTimeout(timer); try { ws && ws.close(); } catch (e) {} fn(v); };
    timer = setTimeout(() => fin(reject, new Error('Deriv timeout')), 12000);
    try { ws = new WebSocket('wss://ws.derivws.com/websockets/v3?app_id=1089'); } catch (e) { return fin(reject, e); }
    ws.addEventListener('open', () => ws.send(JSON.stringify({
      ticks_history: symbol, adjust_start_time: 1, count: 500, end: 'latest', style: 'candles', granularity: DERIV_GRAN[tf]
    })));
    ws.addEventListener('message', ev => {
      let j; try { j = JSON.parse(ev.data); } catch (e) { return; }
      if (j.error) return fin(reject, new Error(j.error.message || 'Deriv error'));
      if (j.candles) { try { fin(resolve, clean(parseDeriv(j))); } catch (e) { fin(reject, e); } }
    });
    ws.addEventListener('error', () => fin(reject, new Error('Deriv connection failed')));
    ws.addEventListener('close', () => fin(reject, new Error('Deriv connection closed')));
  });
}

async function getCandles(market, symbol, tf) {
  const errs = [];
  if (market === 'synth') {
    const cs = await derivCandles(symbol, tf);
    if (cs.length < 60) throw new Error('Deriv returned too few candles');
    return {candles: cs, source: 'Deriv'};
  }
  if (market === 'crypto') {
    // GitHub's servers are in the US, where binance.com is blocked, so the mirror and OKX come first.
    const q = base => `${base}?symbol=${symbol}&interval=${tf}&limit=500`;
    const ex = [
      ['Binance mirror', q('https://data-api.binance.vision/api/v3/klines'), parseBinance],
      ['OKX', `https://www.okx.com/api/v5/market/candles?instId=${symbol.replace('USDT', '-USDT')}&bar=${OKX[tf]}&limit=300`, parseOKX],
      ['Bybit', `https://api.bybit.com/v5/market/kline?category=spot&symbol=${symbol}&interval=${BYBIT[tf]}&limit=500`, parseBybit],
      ['Binance', q('https://api.binance.com/api/v3/klines'), parseBinance]
    ];
    for (const [name, url, parse] of ex) {
      try {
        const cs = clean(parse(await getJSON(url, 9000, {'User-Agent': UA})));
        if (cs.length >= 60) return {candles: cs, source: name};
        errs.push(name + ': too few candles');
      } catch (e) { errs.push(name + ': ' + e.message); }
    }
    throw new Error(errs.join(' | '));
  }
  // forex & gold
  const f = FOREX.find(x => x.s === symbol);
  if (TDKEY) {
    try {
      const u = `https://api.twelvedata.com/time_series?symbol=${encodeURIComponent(f.td)}&interval=${TDI[tf]}&outputsize=500&order=asc&timezone=UTC&apikey=${encodeURIComponent(TDKEY)}`;
      const cs = clean(parseTD(await getJSON(u, 10000)));
      if (cs.length >= 60) return {candles: cs, source: 'Twelve Data'};
      errs.push('TwelveData: too few candles');
    } catch (e) { errs.push('TwelveData: ' + e.message); }
  }
  const y = YAHOO[tf];
  for (const tk of f.y) {
    for (const host of ['query1', 'query2']) {
      try {
        const u = `https://${host}.finance.yahoo.com/v8/finance/chart/${encodeURIComponent(tk)}?interval=${y.iv}&range=${y.range}&includePrePost=false`;
        let cs = clean(parseYahoo(await getJSON(u, 10000, {'User-Agent': UA, 'Accept': 'application/json'})));
        if (y.rs) cs = resample(cs, y.rs);
        if (cs.length >= 60) return {candles: cs, source: 'Yahoo ' + tk};
        errs.push('Yahoo ' + tk + ': too few candles');
      } catch (e) { errs.push('Yahoo ' + tk + ' ' + host + ': ' + e.message); }
    }
  }
  if (f.bn) {
    try {
      const url = `https://data-api.binance.vision/api/v3/klines?symbol=${f.bn}&interval=${tf}&limit=500`;
      const cs = clean(parseBinance(await getJSON(url, 9000)));
      if (cs.length >= 60) return {candles: cs, source: 'Binance ' + f.bn + ' (USDT proxy)'};
    } catch (e) { errs.push('Binance proxy: ' + e.message); }
  }
  throw new Error(errs.join(' | '));
}

async function analyzeJob(j) {
  const tfo = TF[j.tf];
  const [main, htf] = await Promise.all([
    getCandles(j.mk, j.symbol, j.tf),
    tfo.htf ? getCandles(j.mk, j.symbol, tfo.htf).catch(() => null) : Promise.resolve(null)
  ]);
  const now = Date.now();
  const closed = main.candles.filter(k => k.t + tfo.ms <= now);
  const live = main.candles.length ? last(main.candles).c : null;
  let htfClosed = null;
  if (htf) { const hm = TF[tfo.htf].ms; htfClosed = htf.candles.filter(k => k.t + hm <= now); }
  const r = analyze({candles: closed, live, htf: htfClosed, htfTf: tfo.htf, ms: tfo.ms, now, market: j.mk, symbol: j.symbol, tf: j.tf});
  if (!r.error) r.source = main.source;
  return r;
}

/* ---------- state ---------- */
function loadState() {
  try {
    const s = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
    return {done: s.done || {}, alerts: s.alerts || {}, retry: s.retry || {}};
  } catch (e) { return {done: {}, alerts: {}, retry: {}}; }
}
function saveState(s) { fs.writeFileSync(STATE_FILE, JSON.stringify(s, null, 1)); }

/* ---------- Telegram ---------- */
async function tg(text) {
  if (!TOKEN || !CHAT) { console.log('[no Telegram secrets, printing instead]\n' + text + '\n'); return false; }
  try {
    const r = await fetch(`https://api.telegram.org/bot${TOKEN}/sendMessage`, {
      method: 'POST', headers: {'content-type': 'application/json'},
      body: JSON.stringify({chat_id: CHAT, text, disable_web_page_preview: true}),
      signal: AbortSignal.timeout(15000)
    });
    if (!r.ok) { console.log('Telegram error', r.status, await r.text()); return false; }
    return true;
  } catch (e) { console.log('Telegram error', e.message); return false; }
}

const wat = t => new Date(t).toLocaleString('en-GB', {timeZone: 'Africa/Lagos', day: '2-digit', month: 'short', hour: '2-digit', minute: '2-digit', hour12: false}) + ' WAT';

function buildMessage(j, r) {
  const d = r.direction, p = r.plan;
  const why = r.comps.filter(c => c.score * d > 0 && Math.abs(c.score) >= 0.4 * c.max)
    .sort((a, b) => b.score * d - a.score * d).slice(0, 4).map(c => c.name).join(', ');
  const sgn = r.score > 0 ? '+' + r.score : String(r.score);
  const lines = [
    (r.signal === 'BUY' ? '🟢 BUY' : '🔴 SELL') + '  ' + labelOf(j.mk, j.symbol) + ' · ' + j.tf,
    'Strength: ' + r.grade + ' (score ' + sgn + '/100)',
    '',
    'Entry: ' + fmt(p.entry),
    'Stop loss: ' + fmt(p.sl) + ' (' + p.slPct.toFixed(2) + '%)',
    'TP1: ' + fmt(p.tp1) + ' (1.5R)',
    'TP2: ' + fmt(p.tp2) + ' (2.5R)',
    '',
    'Why: ' + (why || 'multiple indicators agree'),
    r.htf ? 'Higher TF (' + r.htf.tf + '): ' + r.htf.label : 'Higher TF: n/a',
    'RSI ' + r.ind.rsi.toFixed(0) + ' · ADX ' + r.ind.adx.toFixed(0) + ' · ATR ' + fmt(r.ind.atr),
    'Candle closed: ' + wat(r.lastT + TF[j.tf].ms),
    '',
    'Not financial advice. Risk 1% or less per trade, always use the stop loss.'
  ];
  return lines.join('\n');
}

const maxAgeMs = tf => Math.min(TF[tf].ms * 0.9, 25 * 60000);
const forexClosed = now => { const d = new Date(now), day = d.getUTCDay(), h = d.getUTCHours(); return day === 6 || (day === 5 && h >= 22) || (day === 0 && h < 22); };

/* ---------- main ---------- */
async function main() {
  if (TEST_MODE) {
    const ok = await tg('✅ ProEdge scanner is connected.\nYou will get a message here when a BUY or SELL setup appears.');
    console.log(ok ? 'Test message sent.' : 'Test message NOT sent. Check the TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID secrets.');
    return;
  }
  const state = loadState();
  const now = Date.now();
  const jobs = [];
  for (const mk of MARKETS) {
    if (mk === 'forex' && forexClosed(now)) { console.log('Forex market closed, skipping forex.'); continue; }
    const list = mk === 'crypto' ? CRYPTO : mk === 'forex' ? FOREX.map(f => f.s) : mk === 'synth' ? SYNTH.map(x => x.s) : [];
    for (const symbol of list) for (const tf of TIMEFRAMES) {
      const ms = TF[tf].ms, boundary = Math.floor(now / ms) * ms, key = mk + '|' + symbol + '|' + tf;
      if (state.done[key] === boundary) continue;      // already analysed this candle
      if (now - boundary < SETTLE_MS) continue;        // candle only just closed, wait a moment
      if (state.retry[key] && now < state.retry[key]) continue;
      jobs.push({mk, symbol, tf, key, boundary});
    }
  }
  console.log('Pairs to analyse this run: ' + jobs.length);
  let i = 0, sent = 0, errors = 0, signals = 0;
  const worker = async () => {
    while (i < jobs.length) {
      const j = jobs[i++];
      try {
        const r = await analyzeJob(j);
        delete state.retry[j.key];
        state.done[j.key] = j.boundary;
        if (r.error) { console.log('· ' + j.key + ': ' + r.error); continue; }
        if (r.signal === 'NO TRADE') continue;
        signals++;
        if (r.ageMs > maxAgeMs(j.tf)) { console.log('· ' + j.key + ': ' + r.signal + ' but candle is old, skipped'); continue; }
        const prev = state.alerts[j.key];
        if (prev && prev.signal === r.signal && (r.lastT - prev.t) <= REPEAT_CANDLES * TF[j.tf].ms) continue;
        if (await tg(buildMessage(j, r))) { state.alerts[j.key] = {signal: r.signal, t: r.lastT}; sent++; console.log('✓ alert sent: ' + j.key + ' ' + r.signal); }
      } catch (e) {
        errors++; state.retry[j.key] = Date.now() + RETRY_MS;
        console.log('✗ ' + j.key + ': ' + String(e.message).slice(0, 300));
      }
    }
  };
  await Promise.all(Array.from({length: 4}, worker));
  saveState(state);
  console.log(`Done. analysed=${jobs.length} signals=${signals} alerts_sent=${sent} errors=${errors}`);
}

export const done = main().catch(e => { console.error(e); process.exitCode = 1; });
