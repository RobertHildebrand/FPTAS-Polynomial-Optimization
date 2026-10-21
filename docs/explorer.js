'use strict';
const G=CellGeometry,$=id=>document.getElementById(id),ns='http://www.w3.org/2000/svg';
function el(tag,attrs={},text){const n=document.createElementNS(ns,tag);for(const[k,v]of Object.entries(attrs))n.setAttribute(k,v);if(text!==undefined)n.textContent=text;return n;}
function add(svg,tag,attrs,text){const n=el(tag,attrs,text);svg.appendChild(n);return n;}
const fmt=x=>Number(x.toFixed(4)).toString(),pair=p=>`(${p.map(fmt).join(', ')})`;
const scale=464/G.extent,ox=55,oy=540,X=x=>ox+scale*x,Y=y=>oy-scale*y;
const path=p=>p.map((v,i)=>`${i?'L':'M'}${X(v[0])},${Y(v[1])}`).join(' ')+'Z';
let selected=[40,20];
for(const p of G.points){const o=document.createElement('option');o.value=p.join(',');o.textContent=pair(p);$('pick').appendChild(o);}$('pick').value='40,20';
function color(t){const a=[33,107,136],b=[221,144,87];return `rgb(${a.map((v,i)=>Math.round(v+(b[i]-v)*Math.max(0,Math.min(1,t)))).join(',')})`;}
function render(){const ell=+$('ell').value,key=$('objective').value,o=G.objectives[key],result=G.solve(ell,key),c=G.cell(selected,ell),s=$('cells'),eps=+$('eps').value;
 s.replaceChildren(el('title',{},'Refined slack cells of a pentagon'),el('desc',{},'Solid boundary: P. Highlight: selected closed cell. Rings: representatives.'));
 const defs=add(s,'defs'),cp=add(defs,'clipPath',{id:'qclip'});add(cp,'path',{d:path(G.Q)});
 add(s,'path',{d:path(G.Q),fill:'#eef2ec'});
 const lines=add(s,'g',{'clip-path':'url(#qclip)',stroke:'#9cafaa','stroke-width':ell>8?.35:.65,opacity:ell>16?.55:.85});
 for(const a of G.rows)for(const t of G.thresholds(ell)){const b=a[2]+.5-t;let p,q;if(a[1]===0){p=[b/a[0],-2];q=[b/a[0],G.extent+4];}else{p=[-2,(b+2*a[0])/a[1]];q=[G.extent+4,(b-(G.extent+4)*a[0])/a[1]];}add(lines,'line',{x1:X(p[0]),y1:Y(p[1]),x2:X(q[0]),y2:Y(q[1])});}
 add(s,'path',{d:path(c.poly),fill:'#e8a879','fill-opacity':.5,stroke:'#bc4e26','stroke-width':2});
 add(s,'path',{d:path(G.P),fill:'none',stroke:'#172f37','stroke-width':2.1});
 const reps=new Set(result.reps.map(p=>p.join(',')));
 for(const p of G.points){const value=o.f(p);const n=add(s,'circle',{cx:X(p[0]),cy:Y(p[1]),r:reps.has(p.join(','))?1.8:1.1,fill:$('heat').checked?color((value-result.lo)/(result.hi-result.lo)):'#216b88',stroke:reps.has(p.join(','))?'#172f37':'none','stroke-width':.65});n.appendChild(el('title',{},`${pair(p)} · f = ${fmt(value)}${reps.has(p.join(','))?' · representative':''}`));}
 add(s,'circle',{cx:X(result.chosen[0]),cy:Y(result.chosen[1]),r:8,fill:'none',stroke:'#bc4e26','stroke-width':2});
 for(let v=0;v<=G.extent;v+=G.extent/4){add(s,'text',{x:X(v),y:570,'text-anchor':'middle',fill:'#52646a','font-size':13},v);add(s,'text',{x:32,y:Y(v)+4,'text-anchor':'end',fill:'#52646a','font-size':13},v);}add(s,'text',{x:555,y:570,'font-size':14,fill:'#172f37'},'x');add(s,'text',{x:25,y:45,'font-size':14,fill:'#172f37'},'y');
 $('ell-value').textContent=ell;$('objective-formula').textContent=o.formula;$('point-count').textContent=G.points.length;$('group-count').textContent=result.groups.size;$('error').textContent=(100*result.error).toFixed(3)+'% of range';$('best').textContent=`${pair(result.chosen)} · ${fmt(result.value)}`;$('optimum').textContent=`${pair(result.min)} · ${fmt(result.lo)}`;
 const target=Math.max(o.degree**2,Math.ceil(o.degree/Math.sqrt(eps))),valid=ell>=target;$('guarantee').classList.toggle('certified',valid);$('guarantee').textContent=valid?`Theorem conditions met: ℓ ≥ D² and D²/ℓ² ≤ ε. Guaranteed range-relative error ≤ ${fmt(o.degree**2/ell**2)} for this representative cover.`:`Exploratory refinement. The theorem requires ℓ ≥ ${target} for D = ${o.degree} and ε = ${eps}. An observed small error alone does not give a guarantee.`;
 const labels=['x + ½','y + ½','64½ − x','64½ − y','96½ − x − y'];$('slacks').replaceChildren();c.intervals.forEach(([a,b],i)=>{const tr=document.createElement('tr');for(const t of [labels[i],fmt(a),fmt(b),fmt((b-a)/a)]){const td=document.createElement('td');td.textContent=t;tr.appendChild(td);}$('slacks').appendChild(tr);});
 const members=G.points.filter(p=>c.intervals.every(([a,b],i)=>G.slack(G.rows[i],p)>=a-1e-8&&G.slack(G.rows[i],p)<=b+1e-8));$('selection').textContent=`Inspecting near ${pair(selected)}. This closed cell contains ${members.length} feasible integer point${members.length===1?'':'s'}; boundary points may also lie in adjacent cells. Orange ring: best representative globally.`;
}
$('cells').addEventListener('click',e=>{const pt=$('cells').createSVGPoint();pt.x=e.clientX;pt.y=e.clientY;const v=pt.matrixTransform($('cells').getScreenCTM().inverse());const p=[(v.x-ox)/scale,(oy-v.y)/scale];if(G.rows.every(a=>G.slack(a,p)>=.25&&G.slack(a,p)<=2**G.Phi)){selected=p;render();}});
for(const id of ['ell','objective','heat','eps'])$(id).addEventListener('input',render);
$('pick').addEventListener('change',()=>{selected=$('pick').value.split(',').map(Number);render();});$('reset').addEventListener('click',()=>{selected=[40,20];$('pick').value='40,20';render();});
$('certify').addEventListener('click',()=>{const D=G.objectives[$('objective').value].degree,n=Math.max(D*D,Math.ceil(D/Math.sqrt(+$('eps').value)));$('ell').value=n;render();});
function curve(){const l=+$('length').value,c=+$('odd').value,s=$('curve'),f=t=>(t/l)**2+c*(t/l)**3,e=t=>(t/l)**2;const cx=t=>55+(t/l+1)*275,cy=y=>315-y*145;s.replaceChildren();add(s,'title',{},'Symmetrization cancels the odd part of the cubic');for(const y of [0,.5,1,1.5]){add(s,'line',{x1:55,x2:605,y1:cy(y),y2:cy(y),stroke:'#c3d0c7','stroke-width':1});add(s,'text',{x:42,y:cy(y)+4,'text-anchor':'end','font-size':12,fill:'#52646a'},y);}for(const t of [-l,0,l])add(s,'text',{x:cx(t),y:340,'text-anchor':'middle','font-size':12,fill:'#52646a'},t);add(s,'text',{x:625,y:340,'font-size':14,fill:'#172f37'},'t');
 for(const [fn,col]of [[f,'#216b88'],[e,'#bc4e26']]){const d=Array.from({length:241},(_,i)=>{const t=-l+2*l*i/240;return `${i?'L':'M'}${cx(t)},${cy(fn(t))}`;}).join(' ');add(s,'path',{d,fill:'none',stroke:col,'stroke-width':2.5});}for(let k=-l;k<=l;k++)add(s,'circle',{cx:cx(k),cy:cy(f(k)),r:2.7,fill:'#216b88'});$('odd-value').textContent=fmt(c);$('length-value').textContent=l;$('curve-detail').textContent=`p(1) − p(0) = ${fmt(f(1))}. Sample range = ${fmt(1+Math.abs(c))}. For D = 3, the sharper symmetric bound is 4(b−a)/ℓ² = ${fmt(4*(1+Math.abs(c))/l**2)}.`;}
$('odd').addEventListener('input',curve);$('length').addEventListener('input',curve);render();curve();
