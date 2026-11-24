/* ===== v2 additions (Jeromie Beasley, 23 Nov 2026): the wall line, the tree in other solids, a Smith chart on every face ===== */
const NG=[];const SOL=new T.Group(),WAL=new T.Group(),FAC=new T.Group();[SOL,WAL,FAC].forEach(g=>{g.visible=false;world.add(g);NG.push(g);});
function hideNew(){NG.forEach(g=>g.visible=false);if(TR)TR.visible=true;SH.visible=true;}
function clearG(G){while(G.children.length){const c=G.children[0];G.remove(c);if(c.geometry)c.geometry.dispose();if(c.material){if(c.material.map)c.material.map.dispose();c.material.dispose();}}}
const PHI=(1+Math.sqrt(5))/2,WALLZ=3+2*Math.sqrt(2);
const nrm=v=>{const l=Math.hypot(...v);return v.map(x=>x/l);},dot=(a,b)=>a[0]*b[0]+a[1]*b[1]+a[2]*b[2];
const crs=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];
function sgn(v){const o=[];const s=[-1,1];for(const a of s)for(const b of s)for(const c of s){const w=[v[0]*a,v[1]*b,v[2]*c];if(!o.some(u=>u.every((x,i)=>Math.abs(x-w[i])<1e-9)))o.push(w);}return o;}
const cyc=v=>[v,[v[1],v[2],v[0]],[v[2],v[0],v[1]]];
const TET=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],CUB=sgn([1,1,1]),OCT=[[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1]];
const ICO=[].concat(...sgn([0,1,PHI]).map(cyc)),DOD=CUB.concat([].concat(...sgn([0,1/PHI,PHI]).map(cyc)));
function solid(name,V,Ndir,dual){const N=Ndir.map(nrm);let inr=-1e9;for(const n of N)for(const v of V)inr=Math.max(inr,dot(n,v));const Vs=V.map(v=>v.map(x=>x/inr));
 const faces=N.map(n=>{const f=Vs.filter(v=>Math.abs(dot(n,v)-1)<1e-6);const c=f.reduce((a,v)=>a.map((x,i)=>x+v[i]/f.length),[0,0,0]);const e1=nrm(f[0].map((x,i)=>x-c[i])),e2=crs(n,e1);f.sort((a,b)=>Math.atan2(dot(a.map((x,i)=>x-c[i]),e2),dot(a.map((x,i)=>x-c[i]),e1))-Math.atan2(dot(b.map((x,i)=>x-c[i]),e2),dot(b.map((x,i)=>x-c[i]),e1)));const e1b=nrm(f[0].map((x,i)=>x-c[i]));return {n,c,v:f,e1:e1b,e2:crs(n,e1b),k:f.length,cr:Math.hypot(...f[0].map((x,i)=>x-c[i]))};});
 return {name,V:Vs,N,faces,dual,circ:Math.max(...Vs.map(v=>Math.hypot(...v)))};}
const ICO_N=CUB.concat([].concat(...sgn([0,PHI,1/PHI]).map(cyc))),DOD_N=[].concat(...sgn([0,PHI,1]).map(cyc));
/* each solid's partner (alternate reader) has its corners along the solid's face directions and its faces along the solid's corners */
function withDual(name,V,N,dname){const S=solid(name,V,N,dname);S.dualS=solid(dname,N,V,name);return S;}
const SOLIDS={tetrahedron:withDual('tetrahedron',TET,TET.map(v=>v.map(x=>-x)),'flipped tetrahedron'),cube:withDual('cube',CUB,OCT,'octahedron'),octahedron:withDual('octahedron',OCT,CUB,'cube'),dodecahedron:withDual('dodecahedron',DOD,DOD_N,'icosahedron'),icosahedron:withDual('icosahedron',ICO,ICO_N,'dodecahedron')};
const AGREE={tetrahedron:'octahedron',cube:'cuboctahedron',octahedron:'cuboctahedron',dodecahedron:'icosidodecahedron',icosahedron:'icosidodecahedron'};
let SS3=RB*.62;const DSP=p=>V(p[0]*SS3,p[2]*SS3,-p[1]*SS3);
function gaugeR(S,u){let m=-1e9;for(const n of S.N)m=Math.max(m,dot(n,u));return 1/m;}
function poinToKlein(P){const s=[P.x/RB,-P.z/RB,P.y/RB],q=s[0]*s[0]+s[1]*s[1]+s[2]*s[2];return s.map(x=>2*x/(1+q));}
function kleinToSolid(S,k){const r=Math.hypot(...k);if(r<1e-12)return [0,0,0];const u=k.map(x=>x/r);return u.map(x=>x*r*gaugeR(S,u));}
function solidDist(S,x){/* the solid's own distance from the centre, along the ray: 1/2 ln((T+ + |x|)/(T+ - |x|) * ...) */const r=Math.hypot(...x);if(r<1e-12)return 0;const u=x.map(v=>v/r),tp=gaugeR(S,u),tn=gaugeR(S,u.map(v=>-v));return .5*Math.log((tp*(r+tn))/((tp-r)*tn));}
function edges(S,col,op){const pts=[];for(const f of S.faces)for(let i=0;i<f.k;i++){pts.push(DSP(f.v[i]),DSP(f.v[(i+1)%f.k]));}const g=new T.BufferGeometry().setFromPoints(pts);return new T.LineSegments(g,new T.LineBasicMaterial({color:col,transparent:true,opacity:op}));}
/* ---- eye: the tree in other solids ---- */
let solKey='',solName='cube',solAlt=true,solShowChain=true;
function solScene(u,dt){hideNew();SOL.visible=true;buildTree(5);moveTree(0,0);TR.visible=false;SH.visible=false;PA.visible=false;CHN.visible=false;
 const S=SOLIDS[solName];
 if(solKey!==solName+'/'+solAlt+'/'+solShowChain){solKey=solName+'/'+solAlt+'/'+solShowChain;clearG(SOL);
  SOL.add(edges(S,0xdfe7ef,.85));if(solAlt)SOL.add(edges(S.dualS,0xb48cff,.55));
  const P=TR.geometry.attributes.position.array,C=TR.geometry.attributes.color.array,pts=new Float32Array(P.length);
  for(let i=0;i<P.length/3;i++){const k=poinToKlein({x:P[i*3],y:P[i*3+1],z:P[i*3+2]}),x=kleinToSolid(S,k),d=DSP(x);pts[i*3]=d.x;pts[i*3+1]=d.y;pts[i*3+2]=d.z;}
  const g=new T.BufferGeometry();g.setAttribute('position',new T.BufferAttribute(pts,3));g.setAttribute('color',new T.BufferAttribute(new Float32Array(C),3));
  const L=new T.LineSegments(g,new T.LineBasicMaterial({vertexColors:true,transparent:true,opacity:.7}));L.frustumCulled=false;SOL.add(L);
  /* the wall: the ball's sphere at the wall rapidity ln(3+2 sqrt2), carried into the solid */
  const wr=Math.tanh(Math.log(WALLZ)),wl=[];for(let a=0;a<12;a++)for(let b=0;b<48;b++){const th=PI*(a+.5)/12,ph=2*PI*b/48,ph2=2*PI*(b+1)/48;
   const p1=[Math.sin(th)*Math.cos(ph),Math.sin(th)*Math.sin(ph),Math.cos(th)].map(x=>x*wr),p2=[Math.sin(th)*Math.cos(ph2),Math.sin(th)*Math.sin(ph2),Math.cos(th)].map(x=>x*wr);wl.push(DSP(kleinToSolid(S,p1)),DSP(kleinToSolid(S,p2)));}
  SOL.add(new T.LineSegments(new T.BufferGeometry().setFromPoints(wl),new T.LineBasicMaterial({color:0xe8553f,transparent:true,opacity:.35})));
  if(solShowChain){const n=CH.n,cp=new Float32Array(n*3);for(let j=0;j<n;j++){const k=poinToKlein({x:CH.P[j*3],y:CH.P[j*3+1],z:CH.P[j*3+2]}),d=DSP(kleinToSolid(S,k));cp[j*3]=d.x;cp[j*3+1]=d.y;cp[j*3+2]=d.z;}
   const cg=new T.BufferGeometry();cg.setAttribute('position',new T.BufferAttribute(cp,3));const cc=CH.line.geometry.attributes.color.array;cg.setAttribute('color',new T.BufferAttribute(new Float32Array(cc),3));const cl_=new T.Line(cg,new T.LineBasicMaterial({vertexColors:true}));cl_.frustumCulled=false;SOL.add(cl_);SOL.userData.cg=cg;}
 }
 const n=Math.max(2,Math.floor(2+Math.pow(u,1.6)*(CH.n-2)));if(SOL.userData.cg)SOL.userData.cg.setDrawRange(0,n);
 const kk=poinToKlein({x:CH.P[(n-1)*3],y:CH.P[(n-1)*3+1],z:CH.P[(n-1)*3+2]}),xs=kleinToSolid(S,kk),dBall=CH.d[n-1],dSol=solidDist(S,xs);
 return [['solid',S.name+' · '+S.faces.length+' faces of '+S.faces[0].k+' sides'],['carried from the ball','same ray, stretched so the rim lands on the faces'],['alternate reader',solAlt?S.dualS.name+' (violet)':'off'],['where the two readers agree',AGREE[S.name]],['twin pairs drawn',n],['latest pair',TW[n-1]+', '+(TW[n-1]+2)],['distance from centre: ball',dBall.toFixed(4)],['distance from centre: this solid',dSol.toFixed(4)],['wall (red)','the ball’s wall sphere, carried in'],['grade','placement: a choice; distances: computed']];}
/* ---- eye: the wall line (Two Trees v3) ---- */
function boost4(ax,r){const M=[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],c=Math.cosh(r),s=Math.sinh(r);M[0][0]=M[ax][ax]=c;M[0][ax]=M[ax][0]=s;return M;}
const mm=(A,B)=>A.map((r,i)=>B[0].map((_,j)=>r.reduce((s,x,k)=>s+x*B[k][j],0))),mv=(A,v)=>A.map(r=>r.reduce((s,x,k)=>s+x*v[k],0));
let walKey='',walZ=5;
function walScene(u,dt){hideNew();WAL.visible=true;buildTree(5);moveTree(0,0);TR.visible=true;TR.material.opacity=.12;PA.visible=false;CHN.visible=false;SH.visible=true;
 const z=walZ,r=Math.log(z),A=boost4(1,r),B=boost4(2,r),Ai=boost4(1,-r),Bi=boost4(2,-r);
 const steps=[A,mm(A,B),mm(mm(A,B),Ai),mm(mm(mm(A,B),Ai),Bi)];const K=steps[3];
 if(walKey!==String(z)){walKey=String(z);clearG(WAL);
  const pts=[O].concat(steps.map(M=>mv(M,O)));
  const cols=[AXC[0],AXC[1],AXC[0],AXC[1]];
  for(let i=0;i<4;i++){const g=geoS(pts[i],pts[i+1],40).map(W);const tg=new T.TubeGeometry(new T.CatmullRomCurve3(g),60,.025,6,false);WAL.add(new T.Mesh(tg,new T.MeshBasicMaterial({color:cols[i]})));}
  const gap=geoS(pts[4],O,40).map(W);WAL.add(new T.Mesh(new T.TubeGeometry(new T.CatmullRomCurve3(gap),40,.018,6,false),new T.MeshBasicMaterial({color:0xe8553f})));
  pts.forEach((p,i)=>{const b=new T.Mesh(new T.SphereGeometry(i?.07:.1,16,12),new T.MeshStandardMaterial({color:i?0xdfe7ef:0xf2c14e,emissive:i?0x111111:0x6a5210}));b.position.copy(W(p));WAL.add(b);});
  /* fixed point of the loop (when it is a turn): solve the spatial rows of (K - I)(1,x,y,0) = 0 */
  const a11=K[1][1]-1,a12=K[1][2],a21=K[2][1],a22=K[2][2]-1,det=a11*a22-a12*a21;
  if(Math.abs(det)>1e-12){const x=(-K[1][0]*a22+K[2][0]*a12)/det,y=(-a11*K[2][0]+a21*K[1][0])/det;if(x*x+y*y<1){const t=1/Math.sqrt(1-x*x-y*y);const fp=[t,t*x,t*y,0];const b=new T.Mesh(new T.SphereGeometry(.11,18,12),new T.MeshStandardMaterial({color:0xb48cff,emissive:0x3a1d6a}));b.position.copy(W(fp));WAL.add(b);WAL.userData.fp=[1,x,y];}else WAL.userData.fp=null;}else WAL.userData.fp=null;
 }
 const tr4=K[0][0]+K[1][1]+K[2][2]+K[3][3],t2=2-4*Math.pow(Math.sinh(r/2),4),cs=(tr4-2)/2,G_=(z-1)/(z+1);
 const kind=Math.abs(z-WALLZ)<1e-3?'parabolic: exactly on the wall':(z<WALLZ?'a turn (rotation): the loop closes as a pure turn':'hyperbolic: the loop slides, no fixed point inside');
 const fp=WAL.userData.fp;
 return [['peel ratio z',z.toFixed(4)+(Math.abs(z-WALLZ)<1e-3?' = 3 + 2√2':'')],['edge rapidity ln z',r.toFixed(4)],['peel step Γ, Γ²',G_.toFixed(4)+', '+(G_*G_).toFixed(4)],['trace of the loop, 2 − 4 sinh⁴(r/2)',t2.toFixed(6)],['check: 4×4 trace = (that)²',tr4.toFixed(6)+' vs '+(t2*t2).toFixed(6)],['what the loop is',kind],['turn of the loop',cs<=1&&cs>=-1?(Math.acos(cs)*180/PI).toFixed(3)+'° (cos = '+cs.toFixed(6)+')':'none'],['at z = 5','cos = −527/625 = −0.8432, fixed point (3, 2, 2, 0)'],['fixed point (violet)',fp?'(1, '+fp[1].toFixed(4)+', '+fp[2].toFixed(4)+') · scaled':'none inside'],['red','the gap: where the loop fails to close']];}
/* ---- eye: a Smith chart on every face ---- */
function lgam(x){const g=7,c=[0.99999999999980993,676.5203681218851,-1259.1392167224028,771.32342877765313,-176.61502916214059,12.507343278686905,-0.13857109526572012,9.9843695780195716e-6,1.5056327351493116e-7];if(x<.5)return Math.log(PI/Math.sin(PI*x))-lgam(1-x);x-=1;let a=c[0];const t=x+g+.5;for(let i=1;i<9;i++)a+=c[i]/(x+i);return .5*Math.log(2*PI)+(x+.5)*Math.log(t)-t+Math.log(a);}
function hyp(a,b,c,zr,zi){let sr=1,si=0,tr=1,ti=0;for(let k=0;k<900;k++){const f=(a+k)*(b+k)/((c+k)*(k+1)),nr=(tr*zr-ti*zi)*f,ni=(tr*zi+ti*zr)*f;tr=nr;ti=ni;sr+=tr;si+=ti;if(Math.abs(tr)+Math.abs(ti)<1e-12)break;}return [sr,si];}
function scMap(n,gr,gi){/* disk -> regular n-gon, inner radius 1, a corner at angle 0 */let m=Math.hypot(gr,gi);if(m>.985){gr*=.985/m;gi*=.985/m;}
 const a=1/n,b=2/n,c=1+1/n;let pr=1,pi=0;for(let k=0;k<n;k++){const t=pr*gr-pi*gi;pi=pr*gi+pi*gr;pr=t;}const F=hyp(a,b,c,pr,pi);
 const F1=Math.exp(lgam(c)+lgam(c-a-b)-lgam(c-a)-lgam(c-b)),inr=F1*Math.cos(PI/n);return [(gr*F[0]-gi*F[1])/inr,(gr*F[1]+gi*F[0])/inr];}
function stMap(n,gr,gi){/* stretch: Klein point carried along its ray to the n-gon's faces */const q=gr*gr+gi*gi,kr=2*gr/(1+q),ki=2*gi/(1+q),r=Math.hypot(kr,ki);if(r<1e-12)return [0,0];const ux=kr/r,uy=ki/r;let mx=-1e9;for(let j=0;j<n;j++){const th=PI/n+2*PI*j/n;mx=Math.max(mx,ux*Math.cos(th)+uy*Math.sin(th));}return [ux*r/mx,uy*r/mx];}
function smithLines(){const L=[];const circ=(cx,cy,R,keep)=>{const o=[];for(let i=0;i<=160;i++){const t=2*PI*i/160,x=cx+R*Math.cos(t),y=cy+R*Math.sin(t);if(x*x+y*y<=1.0000001)o.push([x,y]);else if(o.length){L.push({p:o.slice(),t:keep});o.length=0;}}if(o.length)L.push({p:o,t:keep});};
 for(const r of [0.2,0.5,1,2,5])circ(r/(1+r),0,1/(1+r),'r');for(const x of [0.2,0.5,1,2,5])for(const s of [1,-1])circ(1,s/x,1/x,'x');
 L.push({p:[[-1,0],[1,0]],t:'x'});circ(0,0,Math.SQRT1_2,'w');return L;}
const SMITH=smithLines();
let facKey='',facName='icosahedron',facType='angles',facReader='both';
function facScene(u,dt){hideNew();FAC.visible=true;TR.visible=false;SH.visible=false;PA.visible=false;CHN.visible=false;
 const S=SOLIDS[facName];
 if(facKey!==facName+facType+facReader){facKey=facName+facType+facReader;clearG(FAC);FAC.add(edges(S,0xdfe7ef,.9));
  const readers=facReader==='both'?[1,-1]:(facReader==='impedance'?[1]:[-1]);
  for(const f of S.faces){const n=f.k,inr3=f.cr*Math.cos(PI/n),emb=p=>DSP(f.c.map((x,i)=>x+inr3*(p[0]*f.e1[i]+p[1]*f.e2[i]))),map=facType==='angles'?scMap:stMap;
   for(const sg of readers){for(const line of SMITH){const pts=line.p.map(([x,y])=>emb(map(n,sg*x,sg*y)));if(pts.length<2)continue;const col=line.t==='w'?0xe8553f:(sg>0?(line.t==='r'?0x63d3ff:0x3fbf80):(line.t==='r'?0xf2c14e:0xb48cff));
     FAC.add(new T.Line(new T.BufferGeometry().setFromPoints(pts),new T.LineBasicMaterial({color:col,transparent:true,opacity:line.t==='w'?.9:.55})));}
    const op=emb(map(n,sg*.999,0)),b=new T.Mesh(new T.SphereGeometry(.045,10,8),new T.MeshBasicMaterial({color:sg>0?0xf2c14e:0xb48cff}));b.position.copy(op);FAC.add(b);}
   const ctr=new T.Mesh(new T.SphereGeometry(.035,10,8),new T.MeshBasicMaterial({color:0xffffff}));ctr.position.copy(emb([0,0]));FAC.add(ctr);}
 }
 const k=S.faces[0].k,shape={3:'triangle',4:'square',5:'pentagon'}[k];
 const uni={3:'yes: the triangle reads the same from every point (2.000000 at 40 points)',4:'no: the square changes from point to point (1.09 to 1.50)',5:'untested'}[k];
 const mir={3:'no on its own (0.88 vs 1.49); the flipped reader undoes it',4:'yes',5:'untested'}[k];
 return [['solid',S.name+' · '+S.faces.length+' '+shape+' faces'],['chart on each face',facType==='angles'?'keeps angles (Schwarz–Christoffel)':'stretched to the faces'],['reader',{both:'impedance (blue/green) + admittance flip (gold/violet)',impedance:'impedance',admittance:'admittance (−Γ)'}[facReader]],['one universal sheet per face?',uni],['open/short mirror on a face?',mir],['red ring','the wall, |Γ| = 1/√2'],['dots','white = matched, gold = open (impedance), violet = open (admittance)'],['faces meet at','each chart’s lossless rim: a face hop is a turn, not a slide'],['source','SHAPE-SMITH-01 (2D tests); pentagon faces untested']];}
function sel(label,opts,val,on){const c=document.createElement('label');c.textContent=label;const s=document.createElement('select');for(const [k,v] of opts)s.add(new Option(v,k));s.value=val;s.onchange=()=>on(s.value);c.append(s);return c;}
E.solids={view:[.6,.45,12.5],step(dt,P,t,u){return solScene(u,dt);},controls(el){el.append(sel('Solid',Object.keys(SOLIDS).map(k=>[k,k]),solName,v=>{solName=v;}));el.append(sel('Alternate reader',[['on','on: draw its partner'],['off','off']],solAlt?'on':'off',v=>{solAlt=v==='on';}));}};
E.wall={view:[.6,.55,10.5],step(dt,P,t,u){return walScene(u,dt);},controls(el){const c=document.createElement('label');c.innerHTML='Peel ratio z <output id="o_wz">'+walZ.toFixed(3)+'</output><input id="p_wz" type="range" min="2" max="8" step="0.001" value="'+walZ+'">';el.append(c);c.querySelector('input').oninput=e=>{walZ=+e.target.value;if(Math.abs(walZ-WALLZ)<.02)walZ=WALLZ;c.querySelector('output').textContent=walZ.toFixed(3);};
 const r=document.createElement('div');r.className='row';for(const [t,z] of [['z = 5',5],['the wall 3 + 2√2',WALLZ],['z = 3',3],['z = 7',7]]){const b=document.createElement('button');b.textContent=t;b.onclick=()=>{walZ=z;c.querySelector('input').value=z;c.querySelector('output').textContent=z.toFixed(3);};r.append(b);}el.append(r);}};
E.faces={view:[.6,.45,10.5],step(dt,P,t,u){return facScene(u,dt);},controls(el){el.append(sel('Solid',Object.keys(SOLIDS).map(k=>[k,k]),facName,v=>{facName=v;}));el.append(sel('Chart on each face',[['angles','keeps angles'],['stretch','stretched to the faces']],facType,v=>{facType=v;}));el.append(sel('Reader',[['both','both, laid together'],['impedance','impedance'],['admittance','admittance (flip)']],facReader,v=>{facReader=v;}));}};
