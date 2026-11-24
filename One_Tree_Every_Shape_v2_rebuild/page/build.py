# SCRIPT: OTES-BUILD-01  builds "One Tree, Every Shape" v1 from One Tree, One Ball (Seiberg-Witten 4): same eyes, no ball.
import re, json
src = open('/mnt/user-data/attachments/502f5ad8-acd9-59a2-b5cf-d48e7967cc3a/ebbf321c-One_Tree_One_Ball_Seiberg_Witten__4_.html').read()
def rep(old, new, count=1):
    global src
    n = src.count(old); assert n == count, (old[:80], n); src = src.replace(old, new)
new = open('new_eyes.js').read()
# keep only the shared helpers, the wall eye and the faces eye from new_eyes.js (the separate 'solids' eye is dropped: every eye is in a solid now)
new = new.replace("E.solids={", "/*E.solids dropped*/const _unusedSolids={")
# ---- 1. the map: every hyperboloid point goes into the chosen solid (Klein point stretched along its ray to the faces) ----
rep("const W=v=>{const k=RB/(1+v[0]);return V(v[1]*k,v[3]*k,-v[2]*k);};",
    "let CUR_S=null,RLIM=RB;const W=v=>{const x=kleinToSolid(CUR_S,[v[1]/v[0],v[2]/v[0],v[3]/v[0]]);return DSP(x);};")
rep("const k=RB/(1+t2);P[i*3]=v[0]*k;P[i*3+1]=v[2]*k;P[i*3+2]=-v[1]*k;",
    "const x=kleinToSolid(CUR_S,[v[0]/t2,v[1]/t2,v[2]/t2]);P[i*3]=x[0]*SS3;P[i*3+1]=x[2]*SS3;P[i*3+2]=-x[1]*SS3;")
src = src.replace("(RB*RB)", "(RLIM*RLIM)")
# ---- 2. the level shells become the solid's own level surfaces, plus the solid's edges ----
old_sh = src[src.index("function shells(z){"):src.index("/* the tree, as seen from any one of its balls */")]
rep(old_sh, """function shells(z){while(SH.children.length){const c=SH.children[0];SH.remove(c);if(c.geometry)c.geometry.dispose();}SH.add(edges(CUR_S,0xdfe7ef,.8));if(SHOWDUAL)SH.add(edges(CUR_S.dualS,0xb48cff,.5));
 for(let Lv=1;Lv<=3;Lv++){const kr=Math.tanh(Lv*Math.log(z)),pts=[];for(let a=0;a<8;a++)for(let b=0;b<40;b++){const th=PI*(a+.5)/8,p1=2*PI*b/40,p2=2*PI*(b+1)/40,s=(th,ph)=>[Math.sin(th)*Math.cos(ph)*kr,Math.sin(th)*Math.sin(ph)*kr,Math.cos(th)*kr];pts.push(DSP(kleinToSolid(CUR_S,s(th,p1))),DSP(kleinToSolid(CUR_S,s(th,p2))));}
  SH.add(new T.LineSegments(new T.BufferGeometry().setFromPoints(pts),new T.LineBasicMaterial({color:GOLD,transparent:true,opacity:.06})));const l=label('level '+Lv+': '+Lv+'\\u00b7ln '+z,'#f2c14e',.16);const la=[Math.sin(Lv*.7)*kr,-Math.cos(Lv*.7)*kr*.3,-Math.cos(Lv*.7)*kr];l.position.copy(DSP(kleinToSolid(CUR_S,la)));SH.add(l);}
 if(FACECH!=='off')SH.add(faceCharts(CUR_S,FACECH,FACERD,.22));}
""")
# move the shared helper block (solids, maps, charts) to the top of the closure, right after 'const RB=3.4,O=[1,0,0,0];'
helpers_end = new.index("/* ---- eye: the tree in other solids ---- */")
helpers = new[:helpers_end].replace("g.visible=false;world.add(g);NG.push(g);","g.visible=false;NG.push(g);")
rest = new[helpers_end:]
rep("const RB=3.4,O=[1,0,0,0];", "const RB=3.4,O=[1,0,0,0];\n" + helpers + "\nlet SHOWDUAL=false,FACECH='angles',FACERD='impedance';")
rep("const world=new T.Group();", "const world=new T.Group();NG.forEach(g=>world.add(g));")
# ---- 3. the whole chain is rebuilt when the shape changes ----
i0 = src.index("const CHN=new T.Group();world.add(CHN);const CH={n:2400,d:[],len:[]};(()=>{")
rep("const CHN=new T.Group();world.add(CHN);const CH={n:2400,d:[],len:[]};(()=>{", "const CHN=new T.Group();world.add(CHN);const CH={n:2400,d:[],len:[]};function buildCH(){while(CHN.children.length){const c=CHN.children[0];CHN.remove(c);if(c.geometry)c.geometry.dispose();}CH.d=[];CH.len=[];(()=>{")
rep("CHN.add(CH.mk);CH.P=P;})();", "CHN.add(CH.mk);CH.P=P;})();}")
# ---- 4. the Seiberg-Witten rim becomes the solid's slice through the same plane ----
rep("""const swRim=[];
for(let i=0;i<=120;i++)swRim.push(V(RB*Math.cos(i*PI/60),0,RB*Math.sin(i*PI/60)));
const swCircle=new T.Line(new T.BufferGeometry().setFromPoints(swRim),
 new T.LineBasicMaterial({color:0x5797b9,transparent:true,opacity:.4}));
SWG.add(swCircle);""", """let swCircle=null;function swRimBuild(){if(swCircle){SWG.remove(swCircle);swCircle.geometry.dispose();}const rim=[];for(let i=0;i<=240;i++){const th=i*PI/120,u=[Math.cos(th),Math.sin(th),0];rim.push(DSP(u.map(x=>x*gaugeR(CUR_S,u)*.9999)));}
 swCircle=new T.Line(new T.BufferGeometry().setFromPoints(rim),new T.LineBasicMaterial({color:0x5797b9,transparent:true,opacity:.6}));SWG.add(swCircle);}""")
# ---- 5. face charts helper (used as the shape's skin) ----
faces_fn = """
function faceCharts(S,type,reader,op){const G=new T.Group();const readers=reader==='both'?[1,-1]:(reader==='impedance'?[1]:[-1]);
 for(const f of S.faces){const n=f.k,inr3=f.cr*Math.cos(PI/n),emb=p=>DSP(f.c.map((x,i)=>x+inr3*(p[0]*f.e1[i]+p[1]*f.e2[i]))),map=type==='angles'?scMap:stMap;
  for(const sg of readers)for(const line of SMITH){const pts=line.p.map(([x,y])=>emb(map(n,sg*x,sg*y)));if(pts.length<2)continue;const col=line.t==='w'?0xe8553f:(sg>0?(line.t==='r'?0x63d3ff:0x3fbf80):(line.t==='r'?0xf2c14e:0xb48cff));
   G.add(new T.Line(new T.BufferGeometry().setFromPoints(pts),new T.LineBasicMaterial({color:col,transparent:true,opacity:line.t==='w'?Math.min(1,op*2.5):op})));}}
 return G;}
"""
rest = rest.replace("/* ---- eye: the wall line (Two Trees v3) ---- */", faces_fn + "/* ---- eye: the wall line (Two Trees v3) ---- */")
# faces eye: reuse faceCharts at full strength
rest = rest.replace("""  for(const f of S.faces){const n=f.k,inr3=f.cr*Math.cos(PI/n),emb=p=>DSP(f.c.map((x,i)=>x+inr3*(p[0]*f.e1[i]+p[1]*f.e2[i]))),map=facType==='angles'?scMap:stMap;""",
 """  FAC.add(faceCharts(S,facType,facReader,.6));
  for(const f of S.faces){const n=f.k,inr3=f.cr*Math.cos(PI/n),emb=p=>DSP(f.c.map((x,i)=>x+inr3*(p[0]*f.e1[i]+p[1]*f.e2[i]))),map=facType==='angles'?scMap:stMap;""")
rest = rest.replace("""   for(const sg of readers){for(const line of SMITH){const pts=line.p.map(([x,y])=>emb(map(n,sg*x,sg*y)));if(pts.length<2)continue;const col=line.t==='w'?0xe8553f:(sg>0?(line.t==='r'?0x63d3ff:0x3fbf80):(line.t==='r'?0xf2c14e:0xb48cff));
     FAC.add(new T.Line(new T.BufferGeometry().setFromPoints(pts),new T.LineBasicMaterial({color:col,transparent:true,opacity:line.t==='w'?.9:.55})));}
    const op""", """   for(const sg of readers){
    const op""")
# faces eye uses the global shape
rest = rest.replace("const S=SOLIDS[facName];", "const S=CUR_S;").replace("if(facKey!==facName+facType+facReader){facKey=facName+facType+facReader;", "if(facKey!==CUR_S.name+facType+facReader){facKey=CUR_S.name+facType+facReader;")
rest = rest.replace("el.append(sel('Solid',Object.keys(SOLIDS).map(k=>[k,k]),facName,v=>{facName=v;}));el.append(sel('Chart on each face'", "el.append(sel('Chart on each face'")
# wall eye: its key must include the shape
rest = rest.replace("if(walKey!==String(z)){walKey=String(z);", "if(walKey!==String(z)+CUR_S.name){walKey=String(z)+CUR_S.name;")
rep("/* stage */", rest + "\n/* stage */")
# ---- 6. scenes: retitle and add the two new eyes ----
scenes = json.loads(src[src.index("window.SCENES=") + len("window.SCENES="):src.index(";</script>", src.index("window.SCENES="))])
scenes.append({"id": "wall", "title": "The wall line for the loop.", "grade": "Exact (Two Trees v3, Lean); trace checked on 4×4 boosts",
  "eq": "loop = A B A⁻¹ B⁻¹, two equal perpendicular steps of ln z\ntr = 2 − 4 sinh⁴(r/2)\na pure turn exactly for z < 3 + 2√2",
  "sub": "Two steps at right angles and back again. Below the wall the loop closes as a pure turn about a fixed point (violet); on the wall z = 3 + 2√2 it is parabolic; above it the loop slides and never closes. At z = 5 the turn has cos = −527/625, no rational part of a full turn, with fixed point (3, 2, 2, 0).",
  "note": "The red piece is the gap: how far the loop misses home. The tree is free for every peel ratio z ≥ 2 that is not a power of 2 (Two Trees v3, Lean), yet at ln 5 this turn makes the placement non-discrete.",
  "lean": "Lean: PeelTrees3 comm5_fixes_p, comm5_trace, comm7_trace · PeelTrees2 free_general, free_not_pow_two · BallJoins J4"})
scenes.append({"id": "faces", "title": "A Smith chart on every face.", "grade": "Charts exact by construction; per-face claims from SHAPE-SMITH-01",
  "eq": "Γ = (z − 1)/(z + 1) on every face\nkeeps angles: w ↦ w · ₂F₁(1/n, 2/n; 1 + 1/n; wⁿ)\nflip (admittance): Γ ↦ −Γ",
  "sub": "Each face carries its own Smith chart: resistance circles, reactance arcs, the wall ring |Γ| = 1/√2 in red, matched at the centre and the open point on a corner. Choose the chart that keeps angles or the one stretched to the faces, and the impedance reader, its flip, or both laid together.",
  "note": "Triangle faces (tetrahedron, octahedron, icosahedron) carry one universal sheet each: the triangle reads the same from every point. Square faces (cube) change from point to point. Pentagon faces (dodecahedron) are untested. Neighbouring faces meet on each chart's lossless rim, so moving to the next face is a turn, not a slide.",
  "lean": "Scripts: SHAPE-SMITH-01 (T1–T8), SHAPE-DEVICES-01, BALL-TO-SHAPES-01 · on claude/moving-matrix-of-balls"})
for sc in scenes:
    for k in ('sub','note','eq'):
        for o,n in [('fills the ball','fills the shape'),('inside the same ball','inside the same shape'),('toward the rim','toward the faces'),('slice of the same ball','slice of the same shape'),('the ball','the shape')]:
            sc[k]=sc[k].replace(o,n)
a = src.index("window.SCENES=") + len("window.SCENES="); b = src.index(";</script>", a)
src = src[:a] + json.dumps(scenes, ensure_ascii=False) + src[b:]
# ---- 7. panel: title, shape picker and face-chart controls (global) ----
rep("<title>One Tree, One Ball</title>", "<title>One Tree, Every Shape</title>")
rep("<h1>One Tree, One Ball</h1><div class=\"by\">The twin-prime chain as a path in the tree of peel steps<br>",
    "<h1>One Tree, Every Shape</h1><div class=\"by\">The twin-prime chain as a path in the tree of peel steps, carried into each solid<br>")
rep("<div class=\"ey\" id=\"ey\"></div>", "<div class=\"ctl\" id=\"gctl\"></div><div class=\"ey\" id=\"ey\"></div>")
rep("function show(id){", "function show(id){hideNew();")
rep("$('twin-key').hidden=id.startsWith('sw');", "$('twin-key').hidden=!(id==='ride'||id==='whole');")
rep("Vw.yaw=cur.view[0];Vw.y0=cur.view[0];", "if(cur.controls)cur.controls($('ctl'));Vw.yaw=cur.view[0];Vw.y0=cur.view[0];")
# global shape setter, placed before the first show()
rep("size();show(SC[0].id);requestAnimationFrame(loop);", """function setShape(name){CUR_S=SOLIDS[name];SS3=RB*1.12/CUR_S.circ;RLIM=SS3*CUR_S.circ;const z=TZ||5;TZ=0;buildTree(z);buildCH();swRimBuild();swKey='';walKey='';facKey='';}
setShape('icosahedron');
$('gctl').append(sel('Shape (every eye)',Object.keys(SOLIDS).map(k=>[k,k]),'icosahedron',v=>{setShape(v);}));
$('gctl').append(sel('Partner shape (alternate reader)',[['off','off'],['on','on']],'off',v=>{SHOWDUAL=v==='on';const z=TZ;TZ=0;buildTree(z);}));
$('gctl').append(sel('Face charts on the shape',[['angles','keep angles'],['stretch','stretched to the faces'],['off','off']],'angles',v=>{FACECH=v;const z=TZ;TZ=0;buildTree(z);}));
size();show(SC[0].id);requestAnimationFrame(loop);""")
# buildTree draws shells from CUR_S; the CH IIFE is now a function and needs CUR_S set first: drop the immediate call order issue
rep("CHN.add(CH.mk);CH.P=P;})();}", "CHN.add(CH.mk);CH.P=P;})();}\n")
src = src.replace("/* SCRIPT: one_tree_one_ball_mixer_v1.", "/* SCRIPT: one_tree_every_shape_v1 (built from one_tree_one_ball_mixer_v1).", 1)
src = src.replace("['orbit in the ball',","['orbit in the shape',")
rep("['distance from the centre ball',d.toFixed(4)],", "['distance from the centre (tree)',d.toFixed(4)],['same point, this shape\u2019s own reading',solidDist(CUR_S,[CH.P[(n-1)*3]/SS3,-CH.P[(n-1)*3+2]/SS3,CH.P[(n-1)*3+1]/SS3]).toFixed(4)],")
open('One_Tree_Every_Shape_v1.html', 'w').write(src)
print('written', len(src))
