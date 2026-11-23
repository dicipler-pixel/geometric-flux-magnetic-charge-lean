from pathlib import Path
import re,json,hashlib
import sympy as s
import fitz
from lxml import html
root=Path(__file__).resolve().parent
t,p,c=s.symbols('theta phi cut',real=True);I=s.I
sig=[s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-I],[I,0]]),s.Matrix([[1,0],[0,-1]])]
n=s.Matrix([s.sin(t)*s.cos(p),s.sin(t)*s.sin(p),s.cos(t)])
H=sum((n[i]*sig[i] for i in range(3)),s.zeros(2));P=(s.eye(2)-H)/2;Q=s.eye(2)-P
reduce=lambda a:a.applyfunc(lambda e:s.simplify(s.trigsimp(s.expand_complex(e)))) if isinstance(a,s.MatrixBase) else s.simplify(s.trigsimp(s.expand_complex(a)))
checks={}
checks['unit_direction']=reduce(n.dot(n)-1)==0
checks['projector_idempotence']=reduce(P*P-P)==s.zeros(2)
curv=lambda A:reduce(I*s.trace(A*(A.diff(t)*A.diff(p)-A.diff(p)*A.diff(t))))
checks['lower_actual_derivative_curvature']=reduce(curv(P)-s.sin(t)/2)==0
checks['upper_actual_derivative_curvature']=reduce(curv(Q)+s.sin(t)/2)==0
uN=s.Matrix([-s.exp(-I*p)*s.sin(t/2),s.cos(t/2)])
uS=s.Matrix([-s.sin(t/2),s.exp(I*p)*s.cos(t/2)])
checks['north_lower_eigenvector']=reduce(H*uN+uN)==s.zeros(2,1)
checks['south_transition_phase']=reduce(uS-s.exp(I*p)*uN)==s.zeros(2,1)
checks['north_connection']=reduce(I*(uN.conjugate().T*uN.diff(p))[0]-(1-s.cos(t))/2)==0
checks['south_connection']=reduce(I*(uS.conjugate().T*uS.diff(p))[0]+(1+s.cos(t))/2)==0
w=s.sin(t)/2;N=(1-s.cos(t))/2;S=-(1+s.cos(t))/2
checks['pole_endpoint_difference']=s.simplify(N.subs(t,s.pi)-N.subs(t,0))==1
checks['fixed_coefficient_jump']=s.simplify(N-S)==1
checks['latitude_split_integral']=s.simplify(s.integrate(w,(t,0,c))+s.integrate(w,(t,c,s.pi)))==1
checks['lower_normalized_flux']=s.simplify(s.integrate(curv(P),(t,0,s.pi)))==1
checks['upper_normalized_flux']=s.simplify(s.integrate(curv(Q),(t,0,s.pi)))==-1
checks['derived_band_flux_cancellation']=s.simplify(s.integrate(curv(P)+curv(Q),(t,0,s.pi)))==0
checks['curvature_flux_2pi']=s.simplify(s.integrate(w,(t,0,s.pi))*2*s.pi)==2*s.pi
config=json.loads((root.parent/'scripts/config.json').read_text());inventory={};names=[]
for mod in config['modules']:
 src=(root.parent/mod['path']).read_text()
 src=re.sub(r'/\-.*?\-/','',src,flags=re.S)
 found=re.findall(r'^theorem\s+([^\s:(]+)',src,re.M)
 inventory[mod['module']]=len(found);names+=found
controls=sorted(f.name for f in (root.parent/'FalseControls').glob('*.lean'))
checks['source_inventory_56']=len(names)==config['expected_theorems']==56
checks['source_controls_11']=len(controls)==config['expected_false_controls']==11
stem='Geometric_Flux_and_Magnetic_Charge_v5'
D=html.fromstring((root/(stem+'.html')).read_text());visible=D.text_content()
ids=set(D.xpath('//@id'));bad=[a.get('href') for a in D.xpath('//a[starts-with(@href,"#")]') if a.get('href')[1:] not in ids]
checks['html_internal_links_resolved']=not bad
pdf=fitz.open(root/(stem+'.pdf'));text='\n'.join(page.get_text() for page in pdf)
display=lambda name:name.replace('θ','theta').replace('φ','phi')
checks['all_56_theorem_names_in_HTML']=all(display(name) in visible for name in names)
checks['all_56_theorem_names_in_PDF']=all(display(name) in text for name in names)
checks['all_three_in_HTML_byline']=all(name in D.xpath('//header')[0].text_content() for name in ['Jeromie Beasley','GPT (OpenAI)','Claude (Anthropic)'])
checks['all_three_in_PDF_byline']=all(name in pdf[0].get_text() for name in ['Jeromie Beasley','GPT (OpenAI)','Claude (Anthropic)'])
checks['HTML_assistance_before_abstract']=visible.index('AI assistance')<visible.index('Abstract')
checks['PDF_assistance_before_abstract']=text.index('AI assistance')<text.index('Abstract')
checks['embedded_figure']=len(D.xpath('//img[starts-with(@src,"data:image/")]'))==1
checks['PDF_references_resolved']='??' not in text
checks['PDF_page_count_reasonable']=10<=len(pdf)<=18
checks['no_Type3_fonts']=all(font[2]!='Type3' for page in pdf for font in page.get_fonts())
log=(root/(stem+'.log')).read_text()
checks['no_overfull_boxes']='Overfull' not in log
checks['no_unresolved_LaTeX_references']='undefined' not in log.lower()
checks['no_draft_placeholders']=not any(v in (root/(stem+'.tex')).read_text() for v in ['PROOF_COMMIT','PROOF_SHORT','CI_URL'])
checks['remaining_boundaries_named']=all(v in ' '.join(text.split()) for v in ['Chern class','gauge changes','degree formula','physical field identification'])
result={'checks':checks,'failed_internal_links':bad,'pdf_pages':len(pdf),'module_theorem_inventory':inventory,'total_theorems':len(names),'false_controls':controls,'validation_scope':'Exact symbolic checks and document checks supplement Lean CI; this script does not run Lean.','proof_commit':'d02b612e508e083e94baaf7d781ef15b76953f68','proof_CI':'https://github.com/dicipler-pixel/geometric-flux-magnetic-charge-lean/actions/runs/42027723304','source_sha256':{m['path']:hashlib.sha256((root.parent/m['path']).read_bytes()).hexdigest() for m in config['modules']}}
(root/'paper_validation_v5.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(result,indent=2,ensure_ascii=False));assert all(checks.values()),[k for k,v in checks.items() if not v]
