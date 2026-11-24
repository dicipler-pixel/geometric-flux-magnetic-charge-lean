# SCRIPT: OTES-BUILD-02  builds One Tree, Every Shape v2 from v1 (v1 kept unchanged): six "what bends" eyes, the audit's pentagon and loop results, byline
import json, sys
v1, eyes, data, out = sys.argv[1:5]
src = open(v1).read()
def rep(old, new, count=1):
    global src
    n = src.count(old); assert n == count, (old[:90], n); src = src.replace(old, new)
D = json.load(open(data))
new = open(eyes).read().replace('__DATA__', json.dumps(D, separators=(',', ':')))
rep("/* stage */", new + "\n/* stage */")
# byline and wording
rep("Jeromie Beasley · prime chain with Elizabeth Johnson · 3D mixer", "Jeromie Beasley · 3D mixer · v2")
rep("Elizabeth’s wheel uses its own gap colors", "The end-digit wheel uses its own gap colors")
rep("// Elizabeth's wheel supplies the digit transition.", "// The end-digit wheel supplies the digit transition.")
rep("name:'Elizabeth’s wheel → charges'", "name:'End-digit wheel → charges'")
rep("/* SCRIPT: one_tree_every_shape_v1 ", "/* SCRIPT: one_tree_every_shape_v2 ")
# audit results into the two v1 shape eyes
rep("5:'untested'}[k];\n const mir", "5:'no: the pentagon changes from point to point (8.75 to 9.51 on the stretch-proof measure)'}[k];\n const mir")
rep("['source','SHAPE-SMITH-01 (2D tests); pentagon faces untested']", "['source','SHAPE-SMITH-01 (2D tests); pentagon and the five solids: SHAPE-AUDIT-01 A3']")
rep("['red','the gap: where the loop fails to close']", "['red','the gap: where the loop fails to close'],['same loop in the flat reader (tetrahedron’s own moves)','always closes, at every z (eye 11)']")
a = src.index("window.SCENES=") + len("window.SCENES="); b = src.index(";</script>", a)
sc = json.loads(src[a:b])
for s in sc:
    if s['id'] == 'faces':
        s['note'] = s['note'].replace("Pentagon faces (dodecahedron) are untested.", "Pentagon faces (dodecahedron) change from point to point as well. Among the solids themselves only the tetrahedron reads the same from every point.")
        s['lean'] = "Scripts: SHAPE-SMITH-01 (T1–T8), SHAPE-DEVICES-01, BALL-TO-SHAPES-01, SHAPE-AUDIT-01 · on claude/moving-matrix-of-balls"
src_rec = "Scripts: PRIME-COVARIANCE-01, WHAT-BENDS-01, WHAT-BENDS-01b · research/what-bends on claude/moving-matrix-of-balls"
sc += [
 {"id": "bCov", "title": "What bends 1 · pairs at a gap.", "grade": "Measured below 50,000,000; prediction is a conjecture",
  "eq": "count of (p, p + gap) ÷ count of twins\npredicted = ∏ (p − 1)/(p − 2) over odd primes p dividing the gap",
  "sub": "Multiplying alone is flat: every whole number is a list of prime powers, one book per prime, and multiplying adds the books in any order. Adding a gap does not respect those books. Each bar is how often two primes sit that gap apart, against how often they sit 2 apart.",
  "note": "If the primes carried no covariance every bar would stand at the twin level. They stand anywhere from 1 to 3.55 times it, and the height is set by which primes divide the gap: an infinite product, one factor per prime. Gold beads are the predicted heights.", "lean": src_rec},
 {"id": "bDig", "title": "What bends 2 · the end-digit record.", "grade": "Measured on 239,099 twin pairs",
  "eq": "twin start ends in 1, 7, 9  →  arm i, j, k\ncell = observed steps ÷ steps if the digits were independent",
  "sub": "The chain of eye 1 changes arm with the end digit of each twin start. Here are the nine ways one end digit can follow another. Thick gold: happens more than chance. Coral ring at an arm: staying on the same arm, which happens less than chance.",
  "note": "The same end digit twice in a row is 8 to 9% rarer than independent draws; stepping round 1 → 7 → 9 → 1 is about 9% more common. Counting noise is about 0.6%. The white beads run faster on the commoner steps.", "lean": src_rec},
 {"id": "bZer", "title": "What bends 3 · the zeros push apart.", "grade": "Measured on the first 400 zeros",
  "eq": "gaps between neighbouring zeros, average set to 1\nsmall gap: less than 0.3", "sub": "Top row: the zeros of the zeta function, the other face of the same covariance. Bottom row: points dropped freely at the same average spacing. Free points often land close together; the zeros almost never do.",
  "note": "Points that sit freely are what steps that commute give. Points that hold each other apart are what steps that do not commute give. The zeros hold each other apart: 1.0% small gaps against 26% for free points.", "lean": src_rec},
 {"id": "bShf", "title": "What bends 4, 5 · does the ball read the order?", "grade": "Computed live; recorded in WHAT-BENDS-01, 01b",
  "eq": "real chain against the same steps in shuffled order\nend distance from the centre, in the ball's reading", "sub": "Gold is the real chain of eye 2. Grey chains use exactly the same steps in a shuffled order. If the order of the primes bent the path, gold would end outside the grey spread.",
  "note": "With only the arms shuffled, gold ends inside the spread: this readout does not show the end-digit covariance. With whole steps shuffled, gold ends at the low edge, because in the real chain the big steps come first: that is the thinning. Turning and loop gaps along the chain are untried readouts.", "lean": src_rec},
 {"id": "bFlt", "title": "What bends 6 · the flat reader.", "grade": "Derived; run in SHAPE-AUDIT-01",
  "eq": "one book per arm; a step multiplies its book\nlength of a step by ratio z = ½ ln z, lengths add\nA B A⁻¹ B⁻¹ = home, at every z", "sub": "The tetrahedron's own moves are peel steps on its face books, and they commute. Walk the same chain in that reading and every order ends at the same point; the loop of two steps out and back always closes.",
  "note": "So this reader keeps totals and cannot see order, and it has no wall. The ball reads order, and the wall at 3 + 2√2 is where its loop stops closing as a turn. Drawn here in the flat reader's own coordinates inside the chosen shape; it is native to the tetrahedron.", "lean": "Scripts: SHAPE-AUDIT-01 (A3, A5), SHAPE-DEVICES-01 (H2, H3) · research/poincare-diamond on claude/moving-matrix-of-balls"},
 {"id": "bBrd", "title": "What bends · every option.", "grade": "Board: measured, derived, failed this way, untested",
  "eq": "is it the infinite covariance of the primes that bends?", "sub": "All nine options for what could be bending, with where each one stands tonight.",
  "note": "The covariance is real and shows three ways (1, 2, 3). The ball's end-of-chain distance does not register it (4). Whether it is a bend in the projector-bundle sense rests on options 7 and 8.", "lean": src_rec + " · SHAPE-AUDIT-01"},
]
src = src[:a] + json.dumps(sc, ensure_ascii=False) + src[b:]
open(out, 'w').write(src); print('wrote', out, len(src))
