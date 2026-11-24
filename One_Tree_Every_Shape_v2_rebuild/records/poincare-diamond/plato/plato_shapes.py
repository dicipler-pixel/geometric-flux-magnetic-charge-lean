# SCRIPT: PLATO-SHAPES-01  Plato's elements and heavens laid on the shape devices, and the real nested bubbles
# Jeromie Beasley, 22 Nov 2026, AI-assisted.  Sources: Timaeus (Jowett), Republic X, Phaedo; bubble sizes as cited in the report.
# Peel step G(z) = (z-1)/(z+1); peel addition a (+) b = (a+b)/(1+ab).  Every test states its kill condition first.
from fractions import Fraction as F
import numpy as np
G = lambda z: (z - 1) / (z + 1)
op = lambda a, b: (a + b) / (1 + a * b)

print("Q1  Plato's elements as books of triangles (Timaeus)")
# Timaeus: 6 half-equilateral triangles make one equilateral face; 4 right-isosceles make one square face.
# fire = 4 faces, air = 8, water = 20 (all equilateral), earth = cube, 6 square faces.
# Why this tests the 'books close' reading: if every change Plato allows keeps the triangle count, the triangles are a
# conserved book, and the three triangle-faced elements share ONE book while earth keeps its own.
# Kill: any allowed change that does not conserve triangles, or any way to build earth's triangle from fire's.
tri = {'fire': 4 * 6, 'air': 8 * 6, 'water': 20 * 6}; earth = 6 * 4
print("   triangles: fire %d, air %d, water %d ; earth %d (a different triangle)" % (tri['fire'], tri['air'], tri['water'], earth))
rules = [("1 water -> 1 fire + 2 air", tri['water'], tri['fire'] + 2 * tri['air']),
         ("1 air -> 2 fire", tri['air'], 2 * tri['fire']),
         ("2 fire -> 1 air", 2 * tri['fire'], tri['air']),
         ("2.5 air -> 1 water", 2.5 * tri['air'], tri['water'])]
for name, a, b in rules: print("   %-26s %6.1f -> %6.1f   %s" % (name, a, b, 'conserved' if a == b else 'BROKEN'))
print("   earth's triangle has angles 45-45-90, fire's 30-60-90: no whole number of one tiles the other's angles -> earth's book is separate")

print("\nQ2  Plato's bond: fire : air = air : water = water : earth  (two means for solids)")
# Why: a continued proportion puts the four elements at equal steps of the log of their books, i.e. on ONE straight
# line of the flat (triangle/tetrahedron) device, the geometric mean being its midpoint (SHAPE-DEVICES-01 H2).
# Plato's further claim: planes need one mean, solids need two.  Check on whole numbers: between a^2 and b^2 the one
# mean ab is a whole product; between a^3 and b^3 the two means a^2 b and a b^2 are, while a single mean (ab)^1.5 is not.
# Kill: steps unequal, or the one/two-mean claim failing on whole numbers.
bad = 0
for a in range(1, 30):
    for b in range(a + 1, 30):
        s = np.diff(np.log([a**3, a*a*b, a*b*b, b**3]))
        if np.ptp(s) > 1e-12: bad += 1
        m = (a * b) ** 1.5
        if abs(m - round(m)) < 1e-9 and round((a*b) ** .5) ** 2 != a * b: bad += 1
print("   equal log steps for every a<b<30 with the two means; single-mean whole only when ab is a square: failures = %d" % bad)

print("\nQ3  The world soul is a peel ladder")
# Timaeus: portions 1,2,3,4,9,8,27; intervals 3/2, 4/3, 9/8; leftover 256/243.  Claim: peel steps of these are
# G(2) = 1/3, G(3/2) = 1/5, G(4/3) = 1/7, G(9/8) = 1/17, every (n+1)/n goes to 1/(2n+1), and Plato's interval
# sums are exact peel additions.  Kill: any identity not exact in whole fractions.
for z in [F(2), F(3, 2), F(4, 3), F(9, 8), F(256, 243)]: print("   peel of %-7s = %s" % (z, G(z)))
chk = [("fifth (+) fourth = octave", op(G(F(3, 2)), G(F(4, 3))), G(F(2))),
       ("tone (+) tone (+) leimma = fourth", op(op(G(F(9, 8)), G(F(9, 8))), G(F(256, 243))), G(F(4, 3))),
       ("fourth (+) tone = fifth", op(G(F(4, 3)), G(F(9, 8))), G(F(3, 2)))]
for n, a, b in chk: print("   %-34s %s = %s  %s" % (n, a, b, 'exact' if a == b else 'BROKEN'))
print("   (n+1)/n -> 1/(2n+1) for n = 1..50:", all(G(F(n + 1, n)) == F(1, 2 * n + 1) for n in range(1, 51)))

print("\nQ4  Plato's Lambda (1,2,4,8 and 1,3,9,27) is a two-book diamond")
# Every portion is 2^a 3^b: one book counts doublings, one counts triplings.  Claim: each interval is a short step on
# that two-axis grid (fifth = (-1,1), fourth = (2,-1), tone = (-3,2)), and reading in peel steps is the same as adding
# grid steps (peel addition of the two axes' parts).  Kill: any interval not a 2^a 3^b step, or peel reading not matching.
for name, (a, b) in [('fifth 3/2', (-1, 1)), ('fourth 4/3', (2, -1)), ('tone 9/8', (-3, 2)), ('leimma 256/243', (8, -5))]:
    z = F(2) ** a * F(3) ** b; t2 = G(F(2) ** a) if a >= 0 else -G(F(2) ** -a); t3 = G(F(3) ** b) if b >= 0 else -G(F(3) ** -b)
    print("   %-15s = 2^%d 3^%d = %s ; peel(2-book) (+) peel(3-book) = %s  %s" % (name, a, b, z, op(t2, t3), 'match' if op(t2, t3) == G(z) else 'BROKEN'))

print("\nQ5  The real nested bubbles, earth outward (radii, standard values; see report for sources)")
# Claim to TRY TO KILL: 'each bubble is the last scaled by one fixed factor' (a constant step), or 'by Plato's ratios'.
# Kill for constant step: spread of the log steps larger than half their mean.
LY = 9.4607e15; AU = 1.496e11; PC = 3.0857e16
B = [('Earth', 6.371e6), ('magnetosphere (day side)', 10 * 6.371e6), ("Earth's Hill sphere", 1.5e9),
     ('heliosphere (heliopause)', 121 * AU), ('Oort cloud outer edge', 1e5 * AU), ('Local Bubble', 500 * LY),
     ('Milky Way disc', 5e4 * LY), ('Milky Way halo (virial)', 2.5e5 * PC * 1.0), ('Local Group', 1.5e6 * PC),
     ('Laniakea', 8e7 * PC)]
steps = []
for (n0, r0), (n1, r1) in zip(B, B[1:]):
    s = np.log10(r1 / r0); steps.append(s); print("   %-26s -> %-26s x %.3g  (%.2f decades)" % (n0, n1, r1 / r0, s))
steps = np.array(steps)
print("   mean step %.2f decades, spread %.2f -> constant step %s" % (steps.mean(), steps.std(), 'KILLED' if steps.std() > steps.mean() / 2 else 'survives'))
print("   peel of each step ratio sits at", ', '.join('%.4f' % G(10 ** s) for s in steps), "(the halo-to-Local-Group step lands near the wall 0.7071 only because the halo radius is uncertain, 200-300 kpc: not a finding)")

print("\nQ6  The largest scale is a foam of many-faced bubbles: mean faces of a random cell")
# The cosmic web is modelled as a Voronoi foam (voids = cells, walls = faces).  Known value for random seeds:
# mean faces per cell 15.535 (Meijering 1953).  Kill: our count off by more than 0.2.
from scipy.spatial import Voronoi
rng = np.random.default_rng(3); P = rng.uniform(0, 1, (6000, 3)); V = Voronoi(P)
faces = np.zeros(len(P), int)
for (i, j) in V.ridge_points: faces[i] += 1; faces[j] += 1
inner = np.all((P > .2) & (P < .8), axis=1)
print("   interior cells %d: mean faces %.3f (dodecahedron 12, Kelvin cell 14, icosahedron 20)" % (inner.sum(), faces[inner].mean()))
