/* Shared by the offline explorer and its dependency-free numerical tests. */
(function(root){
'use strict';
const rows=[[-1,0,0],[0,-1,0],[1,0,16],[0,1,16],[1,1,24]];
const dot=(a,p)=>a[0]*p[0]+a[1]*p[1];
const slack=(a,p)=>a[2]+.5-dot(a,p);
function clip(poly,a,b){const out=[];for(let i=0;i<poly.length;i++){const p=poly[i],q=poly[(i+1)%poly.length],s=b-dot(a,p),t=b-dot(a,q);if(s>=-1e-10)out.push(p);if((s<0&&t>0)||(s>0&&t<0)){const r=s/(s-t);out.push([p[0]+r*(q[0]-p[0]),p[1]+r*(q[1]-p[1])]);}}return out;}
function region(offset){return rows.reduce((p,a)=>clip(p,a,a[2]+offset),[[-40,-40],[40,-40],[40,40],[-40,40]]);}
const P=region(0),Q=region(.25),shifted=region(.5);
function thresholds(ell){const a=[];for(let k=-2;k<5;k++)for(let j=0;j<ell;j++)a.push(2**k*(1+j/ell));a.push(32);return a;}
// A common infinitesimal direction assigns boundary lattice points to a full
// chamber. It does not alter their coordinates or feasibility.
function bands(p,ell){const ts=thresholds(ell),v=[1,Math.SQRT2];return rows.map(a=>{let s=slack(a,p),idx=ts.findIndex(t=>t>s+1e-9)-1;if(idx<0)idx=ts.length-2;const hit=ts.findIndex(t=>Math.abs(s-t)<1e-9);if(hit>=0)idx=hit-(dot(a,v)>0?1:0);return Math.max(0,Math.min(ts.length-2,idx));});}
function cell(p,ell){const ts=thresholds(ell),bs=bands(p,ell);let poly=Q;rows.forEach((a,i)=>{poly=clip(poly,a,a[2]+.5-ts[bs[i]]);poly=clip(poly,[-a[0],-a[1]],ts[bs[i]+1]-a[2]-.5);});return {poly,bands:bs,intervals:bs.map(i=>[ts[i],ts[i+1]])};}
const points=[];for(let x=0;x<=16;x++)for(let y=0;y<=16;y++)if(x+y<=24)points.push([x,y]);
const objectives={
 bowl:{name:'Quadratic bowl',degree:2,formula:'f(x,y) = (x − 10)² + 2(y − 7)²',f:([x,y])=>(x-10)**2+2*(y-7)**2},
 cubic:{name:'Nonconvex cubic',degree:3,formula:'f(x,y) = (x − 8)³/30 + (y − 6)² − 3x',f:([x,y])=>(x-8)**3/30+(y-6)**2-3*x},
 wells:{name:'Quartic with two wells',degree:4,formula:'f(x,y) = (x − 5)²(x − 12)²/40 + (y − 8)²/2 + (x − 8)(y − 8)/3',f:([x,y])=>(x-5)**2*(x-12)**2/40+(y-8)**2/2+(x-8)*(y-8)/3}
};
function solve(ell,key){const o=objectives[key],groups=new Map();for(const p of points){const k=bands(p,ell).join(',');if(!groups.has(k))groups.set(k,[]);groups.get(k).push(p);}const reps=[...groups.values()].map(g=>g[0]);const best=ps=>ps.reduce((a,b)=>o.f(a)<=o.f(b)?a:b);const min=best(points),chosen=best(reps),lo=o.f(min),hi=Math.max(...points.map(o.f));return {groups,reps,min,chosen,lo,hi,value:o.f(chosen),error:hi===lo?0:(o.f(chosen)-lo)/(hi-lo)};}
const api={rows,dot,slack,clip,P,Q,shifted,thresholds,bands,cell,points,objectives,solve};
if(typeof module!=='undefined')module.exports=api;root.CellGeometry=api;
})(typeof globalThis!=='undefined'?globalThis:this);
