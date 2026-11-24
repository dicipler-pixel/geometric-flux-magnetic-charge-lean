/* ===== v2 additions (Jeromie Beasley, 23 Nov 2026): what bends. Six eyes. Numbers from PRIME-COVARIANCE-01, WHAT-BENDS-01, WHAT-BENDS-01b, SHAPE-AUDIT-01 ===== */
const BD=__DATA__;
const BND=new T.Group();BND.visible=false;world.add(BND);NG.push(BND);
let bndKey='',bndT=0;const BU={};
function bndOn(treeOp){hideNew();BND.visible=true;buildTree(5);moveTree(0,0);TR.visible=treeOp>0;TR.material.opacity=treeOp;PA.visible=false;CHN.visible=false;SWG.visible=false;for(const c of SH.children)if(c.isSprite)c.visible=false;}
const LS=()=>Math.min(1,SS3/2.6);
function bTube(pts,col,rad){return new T.Mesh(new T.TubeGeometry(new T.CatmullRomCurve3(pts),Math.max(8,pts.length*3),rad,6,false),new T.MeshBasicMaterial({color:col}));}
function bLine(pts,col,op){return new T.Line(new T.BufferGeometry().setFromPoints(pts),new T.LineBasicMaterial({color:col,transparent:true,opacity:op==null?1:op}));}
function bBall(p,r,col){const m=new T.Mesh(new T.SphereGeometry(r,14,10),new T.MeshBasicMaterial({color:col}));m.position.copy(p);return m;}
function bLab(t,p,c,s){const l=label(t,c||'#dfe7ef',(s||.2)*LS());l.position.copy(p);return l;}
function rng32(a){return function(){a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};}
function shuf(n,rnd){const p=Array.from({length:n},(_,i)=>i);for(let i=n-1;i>0;i--){const j=Math.floor(rnd()*(i+1)),t=p[i];p[i]=p[j];p[j]=t;}return p;}
const pct=x=>(100*x).toFixed(1)+'%';
/* ---- eye: pairs at a gap ---- */
function ssr(h){let r=1,m=h;while(m%2===0)m/=2;for(let p=3;p*p<=m;p+=2){if(m%p===0){r*=(p-1)/(p-2);while(m%p===0)m/=p;}}if(m>1)r*=(m-1)/(m-2);return r;}
const COV=BD.cov.filter(c=>c[0]<=60);
function covScene(u,dt){bndOn(.06);bndT+=dt;const n=COV.length,z0=-.36,hs=.2,R0=.56,at=(k,z)=>{const th=2*PI*k/n;return DSP([R0*Math.cos(th),R0*Math.sin(th),z]);};
 if(bndKey!=='cov'+CUR_S.name){bndKey='cov'+CUR_S.name;clearG(BND);
  const ring=z=>{const p=[];for(let i=0;i<=120;i++){const th=2*PI*i/120;p.push(DSP([R0*Math.cos(th),R0*Math.sin(th),z]));}return p;};
  BND.add(bLine(ring(z0),0x55657a,.7));BND.add(bLine(ring(z0+hs),0xdfe7ef,.55));
  COV.forEach(([h,m],k)=>{BND.add(bTube([at(k,z0),at(k,z0+hs*m)],m>1.05?0x63d3ff:0x8fa3b8,.022*LS()+.006));BND.add(bBall(at(k,z0+hs*ssr(h)),.05*LS()+.01,GOLD));
   if(h<=12||h===30||h===42||h===60)BND.add(bLab(String(h),at(k,z0-.09),'#a4b1bf',.17));});
  BND.add(bLab('twin level',DSP([0,0,z0+hs+.05]),'#dfe7ef',.16));
  BU.mk=bBall(at(0,z0),.075*LS()+.01,0xffffff);BND.add(BU.mk);}
 const k=scr?Math.min(n-1,Math.floor(u*n)):Math.floor(bndT/1.4)%n,[h,m]=COV[k];BU.mk.position.copy(at(k,z0+hs*m+.06));
 const big=BD.cov.filter(c=>c[0]>60).map(c=>'gap '+c[0]+': '+c[1].toFixed(3)+' (predicted '+ssr(c[0]).toFixed(3)+')').join(' · ');
 let worst=0;for(const [g,v] of BD.cov)worst=Math.max(worst,Math.abs(v/ssr(g)-1));
 return [['counted','prime pairs (p, p + gap) below '+BD.N.toLocaleString()],['bar','count at that gap ÷ twin count'],['gold bead','predicted: product of (p−1)/(p−2) over odd primes p dividing the gap'],['gap shown (white bead)',String(h)],['measured',m.toFixed(4)],['predicted',ssr(h).toFixed(4)],['flat would mean','every bar at the twin level'],['range over all gaps','1 to '+Math.max(...BD.cov.map(c=>c[1])).toFixed(2)+' times the twin count'],['larger gaps',big],['worst mismatch with the prediction',pct(worst)],['status','measured · the prediction is the Hardy–Littlewood conjecture, not a theorem']];}
/* ---- eye: end digits ---- */
const DGN=[1,7,9];
const DGL=(()=>{const ix={1:0,7:1,9:2},M=[[0,0,0],[0,0,0],[0,0,0]];for(let j=0;j+1<TW.length;j++)M[ix[TW[j]%10]][ix[TW[j+1]%10]]++;const rs=M.map(r=>r[0]+r[1]+r[2]),cs=[0,1,2].map(c=>M[0][c]+M[1][c]+M[2][c]),tot=rs[0]+rs[1]+rs[2];return {R:M.map((r,i)=>r.map((x,j)=>x/(rs[i]*cs[j]/tot))),n:tot};})();
function digScene(u,dt){bndOn(.05);bndT+=dt;const tip=a=>{const p=[0,0,0];p[a]=.62;return p;},R=BD.dig;
 const path=(a,b)=>{const pa=tip(a),pb=tip(b),f=((b-a+3)%3===1)?1.42:.5,o=[];for(let i=0;i<=24;i++){const t=i/24,w=4*t*(1-t),q=pa.map((x,j)=>(1-t)*x+t*pb[j]),mid=pa.map((x,j)=>(x+pb[j])/2*f);o.push(DSP(q.map((x,j)=>x*(1-w)+mid[j]*w+0*j)));}return o;};
 if(bndKey!=='dig'+CUR_S.name){bndKey='dig'+CUR_S.name;clearG(BND);BU.beads=[];
  for(let a=0;a<3;a++){BND.add(bBall(DSP(tip(a)),.11*LS()+.02,AXC[a]));BND.add(bLab('ends in '+DGN[a],DSP(tip(a).map(x=>x*1.42)),'#dfe7ef',.2));BND.add(bLine([DSP([0,0,0]),DSP(tip(a))],AXC[a],.35));
   const r=R[a][a],tor=new T.Mesh(new T.TorusGeometry((.2*LS()+.05),.012+.25*Math.abs(r-1),8,40),new T.MeshBasicMaterial({color:0xe8553f}));tor.position.copy(DSP(tip(a)));tor.lookAt(DSP(tip(a).map(x=>x*3)));BND.add(tor);
   BND.add(bLab(r.toFixed(3),DSP(tip(a).map(x=>x*1.18)),'#e8553f',.17));
   for(let b=0;b<3;b++){if(a===b)continue;const v=R[a][b],P=path(a,b),col=v>1.01?GOLD:(v<.99?0xe8553f:0x8fa3b8);BND.add(bTube(P,col,.01+.25*Math.abs(v-1)));BND.add(bLab(v.toFixed(3),P[12].clone().multiplyScalar(1.06),v>1.01?'#f2c14e':'#a4b1bf',.16));
    const bd=bBall(P[0],.05*LS()+.012,0xffffff);BND.add(bd);BU.beads.push({bd,P,v});}}}
 for(const {bd,P,v} of BU.beads){const t=(bndT*.35*v)%1;bd.position.copy(P[Math.min(24,Math.floor(t*25))]);}
 const rows=[['counted',BD.twins.toLocaleString()+' twin pairs below '+BD.N.toLocaleString()],['each number','times that step happens ÷ times it would if end digits were drawn on their own'],['flat would mean','all nine read 1.000']];
 for(let a=0;a<3;a++)rows.push(['from '+DGN[a]+' → 1, 7, 9',R[a].map(x=>x.toFixed(4)).join(' · ')]);
 rows.push(['same digit twice in a row','8 to 9% rarer (coral rings)'],['next arm round, 1 → 7 → 9 → 1','about 9% more common (gold)'],['counting noise','about 0.6%'],['this page’s own chain ('+DGL.n.toLocaleString()+' pairs), same digit twice',[0,1,2].map(a=>DGL.R[a][a].toFixed(3)).join(' · ')],['status','measured · the covariance is in the turns between arms']);return rows;}
/* ---- eye: the zeros push ---- */
const ZF=(()=>{const r=rng32(77),o=[0];for(let i=1;i<BD.zer.length;i++)o.push(o[i-1]-Math.log(1-r()));const sc=BD.zer[BD.zer.length-1]/o[o.length-1];return o.map(x=>x*sc);})();
const zsmall=a=>{let c=0;for(let i=0;i+1<a.length;i++)if(a[i+1]-a[i]<.3)c++;return c/(a.length-1);};
function zerScene(u,dt){bndOn(.05);bndT+=dt;const WN=26,span=.82;
 if(bndKey!=='zer'+CUR_S.name){bndKey='zer'+CUR_S.name;clearG(BND);BU.z=[];
  for(const [row,zz,col] of [[.14,BD.zer,0x63d3ff],[-.14,ZF,0x8fa3b8]]){BND.add(bLine([DSP([-span,0,row]),DSP([span,0,row])],0x55657a,.6));const balls=[];for(let i=0;i<WN+6;i++){const b=bBall(DSP([0,0,row]),.05*LS()+.012,col);BND.add(b);balls.push(b);}BU.z.push({row,zz,col,balls});}
  BND.add(bLab('the zeros',DSP([-span,0,.27]),'#63d3ff',.18));BND.add(bLab('free points, same average spacing',DSP([-span+.25,0,-.28]),'#a4b1bf',.16));}
 const s0=scr?u*(BD.zer.length-WN-2):(bndT*1.3)%(BD.zer.length-WN-2);
 for(const {row,zz,col,balls} of BU.z){let bi=0;for(let i=0;i<zz.length&&bi<balls.length;i++){const x=(zz[i]-s0)/WN*2-1;if(x<-1||x>1)continue;const b=balls[bi++];b.visible=true;b.position.copy(DSP([x*span,0,row]));const close=(i+1<zz.length&&zz[i+1]-zz[i]<.3)||(i>0&&zz[i]-zz[i-1]<.3);b.material.color.setHex(close?0xe8553f:col);}for(;bi<balls.length;bi++)balls[bi].visible=false;}
 return [['top row','the first '+BD.zer.length+' zeros, spaced so the average gap is 1'],['bottom row','points dropped freely with the same average gap'],['coral','a neighbour closer than 0.3 of the average gap'],['share of small gaps: zeros',pct(zsmall(BD.zer))],['share of small gaps: free points (this row)',pct(zsmall(ZF))],['expected if free','25.9%'],['expected if they push each other apart','about 3%'],['reading','free = steps that commute; pushing = steps that do not'],['status','measured on 400 zeros · the general law is Montgomery’s conjecture']];}
/* ---- eyes: the ball as reader of the order, and the flat reader ---- */
function chainSteps(){const n=CH.n,ax=[],r=[];for(let j=0;j<n;j++){ax.push(axOf(TW[j+1]));r.push(Math.log(TW[j+1]/TW[j]));}return {n,ax,r};}
function ballWalk(ax,r,keep){let G=[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]];const pts=[];for(let j=0;j<ax.length;j++){if(keep)pts.push(W([G[0][0],G[1][0],G[2][0],G[3][0]]));const a=ax[j],c=Math.cosh(r[j]),s=Math.sinh(r[j]);for(let i=0;i<4;i++){const g0=G[i][0],ga=G[i][a+1];G[i][0]=c*g0+s*ga;G[i][a+1]=s*g0+c*ga;}}if(keep)pts.push(W([G[0][0],G[1][0],G[2][0],G[3][0]]));return {d:Math.acosh(Math.max(1,G[0][0])),pts};}
let shMode='arms';
function shfScene(u,dt){bndOn(.07);
 if(bndKey!=='shf'+CUR_S.name+shMode){bndKey='shf'+CUR_S.name+shMode;clearG(BND);const {n,ax,r}=chainSteps(),rnd=rng32(2311),ends=[];
  for(let k=0;k<80;k++){const p=shuf(n,rnd),a2=p.map(i=>ax[i]),r2=shMode==='arms'?r:p.map(i=>r[i]),w=ballWalk(a2,r2,k<14);ends.push(w.d);if(k<14){BND.add(bLine(w.pts,0x9fb3c8,.6));BND.add(bBall(w.pts[w.pts.length-1],.045*LS()+.01,0x7f93aa));}}
  const real=ballWalk(ax,r,true);BND.add(bLine(real.pts,GOLD,1));BND.add(bBall(real.pts[real.pts.length-1],.085*LS()+.015,GOLD));ends.sort((a,b)=>a-b);
  BU.sh={real:real.d,lo:ends[2],hi:ends[77],len:r.reduce((a,b)=>a+b,0),n};}
 const S=BU.sh,inside=S.real>=S.lo&&S.real<=S.hi;
 return [['gold','the real chain: '+S.n+' twin pairs, each step the ratio of one twin start to the next, along the arm of its end digit'],['grey','the same steps walked in shuffled order (14 drawn, 80 counted)'],['what is shuffled',shMode==='arms'?'the arms only; step sizes stay in their real order':'whole steps: arm and size together'],['path length',S.len.toFixed(3)],['end distance from the centre: real order',S.real.toFixed(4)],['end distance: middle 95% of shuffles',S.lo.toFixed(4)+' to '+S.hi.toFixed(4)],['real order is',inside?'inside the shuffled range':'outside the shuffled range'],['recorded run, arms only (600 / 2400 / 9600 pairs)','inside every time'],['recorded run, whole steps','at or just below the low edge: the big early steps come first'],['reading','this readout does not show the end-digit covariance: failed this way. It does show the thinning.'],['untried','how much the chain turns; the loop gaps along it'],['status','computed live in this page · record WHAT-BENDS-01, 01b']];}
function fltScene(u,dt){bndOn(.05);
 if(bndKey!=='flt'+CUR_S.name){bndKey='flt'+CUR_S.name;clearG(BND);const {n,ax,r}=chainSteps(),rnd=rng32(911);
  const walk=(a2,r2)=>{const p=[0,0,0],o=[[0,0,0]];for(let j=0;j<a2.length;j++){p[a2[j]]+=r2[j];if(j%4===3||j===a2.length-1)o.push(p.slice());}return {o,e:p.slice()};};
  const real=walk(ax,r),L=Math.hypot(...real.e),sc=.72/L,D=q=>DSP(q.map(x=>x*sc));let spread=0;
  for(let k=0;k<12;k++){const p=shuf(n,rnd),w=walk(p.map(i=>ax[i]),p.map(i=>r[i]));BND.add(bLine(w.o.map(D),0x7f93aa,.4));spread=Math.max(spread,Math.hypot(...w.e.map((x,i)=>x-real.e[i])));}
  BND.add(bLine(real.o.map(D),GOLD,1));BND.add(bBall(D(real.e),.09*LS()+.015,GOLD));
  for(let a=0;a<3;a++){const e=[0,0,0];e[a]=real.e[a];BND.add(bLine([DSP([0,0,0]),D(e)],AXC[a],.6));}
  const q=Math.log(5),lp=[[0,0,0],[q,0,0],[q,q,0],[0,q,0],[0,0,0]].map(D);BND.add(bTube(lp,0xb48cff,.014));BND.add(bBall(lp[0],.05*LS()+.01,0xb48cff));BND.add(bLab('loop closes',lp[2].clone().multiplyScalar(1.5),'#b48cff',.15));
  BU.fl={L,spread,ball:ballWalk(ax,r,false).d,n};}
 const F=BU.fl;
 return [['the flat reader','one book per arm; a step multiplies that book, so steps on one arm just add'],['its own home','the tetrahedron (and the triangle): the only shapes that read the same from every point'],['gold','the real chain; grey: 12 shuffled orders'],['where every order ends','the same point'],['largest difference between orders',F.spread.toExponential(1)],['end distance, flat reader',F.L.toFixed(4)+' ('+F.n+' pairs)'],['end distance, ball, real order',F.ball.toFixed(4)],['violet','the loop A B A⁻¹ B⁻¹ at z = 5: closes exactly here'],['same loop in the ball','misses home by 3.4487 at z = 5, by 4.1894 at the wall'],['places reached in four steps','189 here (a grid) · 937 in the ball (a tree)'],['reading','this reader keeps totals and cannot see order; the wall belongs to the ball'],['status','derived, and run in SHAPE-AUDIT-01 (A3, A5): loop gap 5e−13 at z = 2, 3, 5, the wall, 7, 50']];}
function brdScene(u,dt){bndOn(.45);CHN.visible=true;CH.line.geometry.setDrawRange(0,CH.n);CH.pts.geometry.setDrawRange(0,CH.n);if(bndKey!=='brd'){bndKey='brd';clearG(BND);}
 return [['1 · adding against multiplying (pairs at a gap)','measured: not flat, 1 to 3.55 times the twin count'],['2 · the end-digit record (the arms)','measured: not flat, same digit twice 8 to 9% rarer'],['3 · the zeros pushing apart','measured: 1.0% small gaps against 26% if free'],['4 · the order of the end digits, read by the ball','failed this way: inside the shuffled range'],['5 · the thinning (steps shrink along the chain)','measured: small, real'],['6 · the flat reader','derived: cannot bend, order never shows'],['7 · the two books on the primes (connection energy and its opposite)','in the connection-energy paper; not rerun here'],['8 · curvature on the projector bundle from a prime operator','untested: no operator fixed yet'],['9 · nothing bends, it is all the instrument','ruled out by 1 to 3, which use no ball'],['eyes','7 to 11 show options 1 to 6']];}
E.bCov={view:[.6,.5,10.5],step(dt,P,t,u){return covScene(u,dt);}};
E.bDig={view:[2.356,.615,10.5],step(dt,P,t,u){return digScene(u,dt);}};
E.bZer={view:[.05,.25,10.5],step(dt,P,t,u){return zerScene(u,dt);}};
E.bShf={view:[.75,.5,9.6],step(dt,P,t,u){return shfScene(u,dt);},controls(el){el.append(sel('What is shuffled',[['arms','the arms only'],['steps','whole steps']],shMode,v=>{shMode=v;}));}};
E.bFlt={view:[.75,.5,10.5],step(dt,P,t,u){return fltScene(u,dt);}};
E.bBrd={view:[.75,.42,9.6],step(dt,P,t,u){return brdScene(u,dt);}};
