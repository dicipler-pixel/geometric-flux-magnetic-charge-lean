const {chromium}=require('playwright');(async()=>{const b=await chromium.launch({args:['--use-gl=swiftshader','--enable-unsafe-swiftshader']});const p=await b.newPage({viewport:{width:1280,height:800}});
const errs=[];p.on('pageerror',e=>errs.push(e.message));p.on('console',m=>{if(m.type()==='error')errs.push(m.text());});
await p.goto('file://'+process.cwd()+'/One_Tree_Every_Shape_v1.html');await p.waitForTimeout(1500);
const ids=['ride','whole','swCharges','swCusp','wall','faces'];
for(const id of ids){const rows=await p.evaluate(([id])=>{let r;for(let i=0;i<20;i++)r=window.API.frame(0.05,id,0.4);return r;},[id]);await p.waitForTimeout(300);await p.screenshot({path:'s_'+id+'.jpg',type:'jpeg',quality:80});console.log(id,JSON.stringify(rows).slice(0,500));}
// switch shape and recheck two eyes
await p.selectOption('#gctl select >> nth=0','cube');for(const id of ['ride','wall']){await p.evaluate(([id])=>{for(let i=0;i<20;i++)window.API.frame(0.05,id,0.4);},[id]);await p.screenshot({path:'s_cube_'+id+'.jpg',type:'jpeg',quality:80});}
await p.selectOption('#gctl select >> nth=0','tetrahedron');await p.evaluate(()=>{for(let i=0;i<20;i++)window.API.frame(0.05,'faces',0.4);});await p.screenshot({path:'s_tet_faces.jpg',type:'jpeg',quality:80});
console.log('errors',errs);await b.close();})();
