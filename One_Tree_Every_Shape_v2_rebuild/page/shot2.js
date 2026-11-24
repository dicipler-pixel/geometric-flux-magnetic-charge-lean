// SCRIPT: OTES-SHOT-02  render check for One Tree, Every Shape v2: every eye in three shapes, no page errors
const {chromium}=require('playwright');(async()=>{let b;try{b=await chromium.launch({args:['--use-gl=swiftshader','--enable-unsafe-swiftshader','--no-sandbox']});}catch(e){b=await chromium.launch({executablePath:'/usr/bin/google-chrome',args:['--use-gl=swiftshader','--enable-unsafe-swiftshader','--no-sandbox']});}
const p=await b.newPage({viewport:{width:1280,height:800}});const errs=[];p.on('pageerror',e=>errs.push(e.message));p.on('console',m=>{if(m.type()==='error')errs.push(m.text());});
await p.goto('file://'+process.cwd()+'/One_Tree_Every_Shape_v2.html');await p.waitForTimeout(1500);
const ids=['ride','whole','swCharges','swCusp','wall','faces','bCov','bDig','bZer','bShf','bFlt','bBrd'];
for(const sh of ['icosahedron','cube','tetrahedron']){await p.selectOption('#gctl select >> nth=0',sh);
 for(const id of ids){const rows=await p.evaluate(([id])=>{let r;for(let i=0;i<25;i++)r=window.API.frame(0.05,id,null);return r;},[id]);await p.waitForTimeout(200);
  if(sh==='icosahedron'||id.startsWith('b'))await p.screenshot({path:'s_'+sh.slice(0,3)+'_'+id+'.jpg',type:'jpeg',quality:70});
  if(sh==='icosahedron'&&id.startsWith('b'))console.log(id,JSON.stringify(rows).slice(0,1500));}}
await p.evaluate(()=>{document.querySelector('#ctl select')&&0;});
console.log('byline',await p.evaluate(()=>document.querySelector('.by').textContent));console.log('errors',JSON.stringify(errs));await b.close();})();
