#!/usr/bin/env python3
"""Build proofs, audit every theorem, and require six false controls to fail."""
from pathlib import Path
import re, subprocess, sys, json
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification'
OUT.mkdir(exist_ok=True)

def run(args, log):
    p = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=300)
    (OUT / log).write_text(p.stdout)
    return p

p = run(['lake', 'build'], 'build.log')
if p.returncode:
    print(p.stdout); sys.exit(p.returncode)
names = []
for path in sorted((ROOT/'MonopoleStance').glob('*.lean')):
    src = path.read_text()
    # No holes or newly declared axioms; #print axioms supplies the dependency check.
    if re.search(r'^\s*(axiom|sorry|admit)\b|\b(?:by\s+sorry|native_decide)\b', src, re.M):
        raise RuntimeError('Forbidden declaration/proof placeholder in '+str(path))
    names += re.findall(r'^theorem\s+(\w+)', src, re.M)
audit = 'import MonopoleStance\n\n' + ''.join(
    '#print axioms MonopoleStance.'+name+'\n' for name in names)
(ROOT/'AxiomAudit.lean').write_text(audit)
p = run(['lake','env','lean','AxiomAudit.lean'], 'axioms.log')
if p.returncode:
    print(p.stdout); sys.exit(p.returncode)
entries = re.findall(r"'MonopoleStance\.([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", p.stdout)
assert len(entries) == len(names), (len(entries), len(names), p.stdout)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, text in entries:
    actual = set(filter(None, (v.strip() for v in text.split(','))))
    assert actual <= allowed, (name, actual)
controls=[]
for path in sorted((ROOT/'negative_controls').glob('*.lean')):
    p=run(['lake','env','lean',str(path.relative_to(ROOT))], path.stem+'.log')
    assert p.returncode != 0 and 'error:' in p.stdout, 'False control accepted: '+path.name
    assert not any(s in p.stdout for s in ['unknown module prefix','object file','unknown identifier','failed to locate']), p.stdout
    controls.append({'file':path.name,'rejected':True})
assert len(controls)==6
version=run(['lean','--version'],'lean-version.log').stdout.strip()
report={'lean':version,'theorems':names,'theorem_count':len(names),
        'allowed_axioms':sorted(allowed),'all_axiom_dependencies_within_allowed':True,
        'negative_controls':controls,'new_axiom_declarations':0,'proof_holes':0,
        'scope':'Concrete matrix/integral/axis-obstruction proofs plus conditional record-language independence; no EM existence theorem.'}
(OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(f'PASS: {len(names)} theorems, all dependency audits, {len(controls)} rejected false controls.')
