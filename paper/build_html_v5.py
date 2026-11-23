from pathlib import Path
import re,subprocess
from lxml import html,etree
root=Path(__file__).resolve().parent
s=(root/'Geometric_Flux_and_Magnetic_Charge_v5.tex').read_text()
aux=(root/'Geometric_Flux_and_Magnetic_Charge_v5.aux').read_text()
labels=dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}',aux))
s=re.sub(r'\\newcommand\{\\leanname\}[^\n]*\n','',s)
s=re.sub(r'\\leanname\{([^}]+)\}',lambda m:r'\texttt{'+m[1].replace('_',r'\_')+'}',s)
s=s.replace('figures/curvature_and_gauges_v5.pdf','figures/curvature_and_gauges_v5.png')
# Resolve all labelled references against the authoritative LaTeX .aux numbers.
s=re.sub(r'\\eqref\{([^}]+)\}',lambda m:r'\hyperref['+m[1]+']{('+labels[m[1]]+')}',s)
s=re.sub(r'\\ref\{([^}]+)\}',lambda m:r'\hyperref['+m[1]+']{'+labels[m[1]]+'}',s)
anchors={}
def equation(m):
 body=m[1];lab=re.search(r'\\label\{([^}]+)\}',body)
 if not lab:return m[0]
 key=lab[1];anchors[key]=labels[key]
 body=re.sub(r'\\label\{[^}]+\}','',body)
 return r'\hypertarget{'+key+r'}{}'+ '\n'+r'\begin{equation}'+body+r'\end{equation}'
s=re.sub(r'\\begin\{equation\}(.*?)\\end\{equation\}',equation,s,flags=re.S)
(root/'html_source.tex').write_text(s)
subprocess.run(['pandoc','html_source.tex','--from=latex','--to=html5','--standalone','--mathml','--toc','--toc-depth=2','--css=paper.css','--embed-resources','--metadata','title=From Geometric Flux to Magnetic Charge','--output=Geometric_Flux_and_Magnetic_Charge_v5.html'],cwd=root,check=True)
p=root/'Geometric_Flux_and_Magnetic_Charge_v5.html'
doc=html.fromstring(p.read_text())
# Pandoc treats the abstract as title metadata; restore the disclosure before it.
disclosure=doc.xpath('//body/p[strong[contains(.,"AI assistance")]]')
abstract=doc.xpath('//header/div[@class="abstract"]')
assert len(disclosure)==len(abstract)==1
disclosure[0].getparent().remove(disclosure[0])
abstract[0].addprevious(disclosure[0])
# Keep theorem numbering synchronized with the PDF's section-numbered theorem counter.
for node in doc.xpath('//div[@id]'):
 key=node.get('id')
 if key in labels and any(c in node.get('class','').split() for c in ('proposition','theorem','definition','corollary')):
  for el in node.xpath('.//strong')[:1]:
   text=''.join(el.itertext())
   text=re.sub(r'^(Proposition|Theorem|Definition|Corollary)\s+\d+',lambda m:m[1]+' '+labels[key],text)
   for child in list(el):el.remove(child)
   el.text=text
# Add the same equation number as the PDF next to each labelled display.
for key,num in anchors.items():
 found=doc.xpath('//*[@id=$k]',k=key)
 if not found:raise RuntimeError('Missing equation anchor '+key)
 a=found[0]; container=a.getparent()
 if container is None:continue
 candidates=container.xpath('.//math[@display="block"]')
 if not candidates:
  for nxt in container.itersiblings():
   candidates=nxt.xpath('.//math[@display="block"]')
   if candidates:break
 if candidates:
  math=candidates[0]; wrap=math.getparent()
  sp=etree.Element('span',{'class':'eqnumber'});sp.text='('+num+')';wrap.insert(0,sp)
p.write_text('<!DOCTYPE html>\n'+etree.tostring(doc,method='html',encoding='unicode'))
visible=doc.text_content()
for required in ['lowerProjector_hermitian','no_continuous_Pauli_axis_extension','formal_stance','bridge_transfers_charge','matrix_to_integer']:
 assert required in visible, required
assert '[eq:' not in visible
assert len(doc.xpath('//img'))==1
print('HTML verified:',len(anchors),'labelled equations;',len(doc.xpath('//math')),'MathML nodes; embedded figure; Lean names present.')

