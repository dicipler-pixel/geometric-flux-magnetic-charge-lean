# SCRIPT: PARTICLE-SHAPES-01  the shape tools on the particles: generations, bosons, neutrinos
# Jeromie Beasley, 23 Nov 2026, AI-assisted.  Data: PDG 2026 summary tables (leptons, quarks, gauge/Higgs); NuFIT 6.0 (IC19, normal ordering).
# Kill conditions are written above each test BEFORE it runs.  'special values' are the ones from this session:
#   wall z = 3+2sqrt2 (peel 1/sqrt2), wall squared (3+2sqrt2)^2 (physical-map reading 2sqrt2/3), 3, 2, 3/2, 2/3.
import numpy as np, itertools
rng = np.random.default_rng(26)
G = lambda z: (z - 1) / (z + 1); W = 3 + 2 * np.sqrt(2)
m = {'e': (0.51099895069, 1.6e-10), 'mu': (105.6583755, 2.3e-6), 'tau': (1776.93, 0.09),
     'u': (2.16, 0.07), 'd': (4.70, 0.07), 's': (92.9, 0.7), 'c': (1272.9, 4.5), 'b': (4186., 6.), 't': (172600., 270.),
     'W': (80362.5, 7.7), 'Z': (91187.9, 2.0), 'H': (125130., 110.)}          # MeV
fam = {'charged leptons': ('e', 'mu', 'tau'), 'up quarks': ('u', 'c', 't'), 'down quarks': ('d', 's', 'b')}

print("A1  Triangle device on each family: Koide's ratio Q = sum m / (sum sqrt m)^2  (2/3 means the sqrt-mass point sits at 45 deg)")
# Kill for 'every family sits on 2/3': any family off by more than 3 standard errors.  (Koide 1981 is prior art for leptons.)
for f, ks in fam.items():
    def Q(v): return v.sum() / np.sqrt(v).sum() ** 2
    v = np.array([m[k][0] for k in ks]); s = np.array([m[k][1] for k in ks])
    draws = [Q(np.abs(v + s * rng.normal(size=3))) for _ in range(20000)]
    print("   %-16s Q = %.6f +- %.6f   (2/3 = 0.666667)  off by %.1f sigma" % (f, Q(v), np.std(draws), abs(Q(v) - 2 / 3) / np.std(draws)))

print("\nA2  Where the middle generation sits on the straight line of the flat triangle: f = ln(m2/m1) / ln(m3/m1)")
# f = 1/2 is Plato's mean (geometric mean).  Kill for 'one shared position': spread of f across families above 0.05.
fs = []
for f, ks in fam.items():
    a, b, c = (m[k][0] for k in ks); x = np.log(b / a) / np.log(c / a); fs.append(x); print("   %-16s f = %.4f" % (f, x))
print("   spread %.3f -> shared position %s" % (np.ptp(fs), 'KILLED' if np.ptp(fs) > .05 else 'survives'))

print("\nB  Peel ladder between generations (which steps pass the wall z = 5.83)")
for f, ks in fam.items():
    a, b, c = (m[k][0] for k in ks)
    print("   %-16s steps %8.2f, %8.2f   peels %.4f, %.4f   past the wall: %s" % (f, b / a, c / b, G(b / a), G(c / b), [b / a > W, c / b > W]))

print("\nC  Bosons.  Derived identity first: peel of mZ/mW = (1 - cos thW)/(1 + cos thW) = tan^2(thW/2) (on-shell cos thW = mW/mZ)")
r = m['Z'][0] / m['W'][0]; c = 1 / r; th = np.arccos(c)
print("   mZ/mW = %.6f  peel %.6f  tan^2(thW/2) = %.6f  (thW = %.3f deg, sin^2 = %.5f)" % (r, G(r), np.tan(th / 2) ** 2, np.degrees(th), 1 - c * c))
print("C2  Higgs as the straight midpoint (geometric mean) of Z and top: kill if off by more than 3 sigma")
gm = np.sqrt(m['Z'][0] * m['t'][0]); sg = .5 * gm * np.hypot(m['t'][1] / m['t'][0], m['Z'][1] / m['Z'][0]); sH = np.hypot(m['H'][1], sg)
print("   sqrt(mZ mt) = %.2f MeV vs mH = %.0f MeV: off %.3f%% = %.1f sigma -> %s" % (gm, m['H'][0], 100 * (gm / m['H'][0] - 1), (gm - m['H'][0]) / sH,
      'KILLED' if abs(gm - m['H'][0]) / sH > 3 else 'survives'))
# look-elsewhere: in the 12 masses, how many triples have one mass within 0.3% of the geometric mean of two others?
names = list(m); vals = np.array([m[k][0] for k in names])
def gm_hits(v, tol=.003):
    h = 0
    for i, j in itertools.combinations(range(len(v)), 2):
        g_ = np.sqrt(v[i] * v[j])
        for k in range(len(v)):
            if k not in (i, j) and abs(g_ / v[k] - 1) < tol: h += 1
    return h
real = gm_hits(vals); sims = [gm_hits(np.exp(rng.uniform(np.log(vals.min()), np.log(vals.max()), len(vals)))) for _ in range(2000)]
print("   look-elsewhere: real triples within 0.3%%: %d ; random masses over the same span give >= that %.1f%% of the time" % (real, 100 * np.mean(np.array(sims) >= real)))

print("\nD  Neutrinos.  Splitting ratio Delta m^2_31 / Delta m^2_21 against the wall squared (3+2sqrt2)^2 = %.3f" % W ** 2)
# Kill: off by more than 2 sigma.  Then the look-elsewhere control: how often do random ratios land within their error of ANY special value?
d21, s21, d31, s31 = 7.49e-5, .19e-5, 2.534e-3, .024e-3
R = d31 / d21; sR = R * np.hypot(s21 / d21, s31 / d31)
print("   ratio %.2f +- %.2f ; wall^2 %.2f : off %.2f sigma -> %s ; peel of the ratio %.5f vs the wall's physical-map value 2sqrt2/3 = %.5f" %
      (R, sR, W ** 2, (R - W ** 2) / sR, 'KILLED' if abs(R - W ** 2) / sR > 2 else 'survives', G(R), 2 * np.sqrt(2) / 3))
special = np.array([W, W ** 2, 3, 2, 1.5, 2 / 3])
ratios = {'d31/d21': (R, sR)}
for f, ks in fam.items():
    a, b, c_ = (m[k] for k in ks); ratios[f + ' 2/1'] = (b[0] / a[0], b[0] / a[0] * np.hypot(a[1] / a[0], b[1] / b[0])); ratios[f + ' 3/2'] = (c_[0] / b[0], c_[0] / b[0] * np.hypot(b[1] / b[0], c_[1] / c_[0]))
ratios['Z/W'] = (r, r * 1e-4); ratios['H/Z'] = (m['H'][0] / m['Z'][0], m['H'][0] / m['Z'][0] * 1e-3); ratios['t/H'] = (m['t'][0] / m['H'][0], m['t'][0] / m['H'][0] * 2e-3)
hits = [k for k, (v, s) in ratios.items() if np.any(np.abs(v - special) < 2 * s)]
print("   ratios tested %d; within 2 sigma of a special value: %s" % (len(ratios), hits))
# chance: for each ratio, the probability that a log-uniform value over 1..300 lands within 2 sigma of some special value
p = []
for k, (v, s) in ratios.items():
    x = np.exp(rng.uniform(0, np.log(300), 20000)); sx = x * s / v
    p.append(np.mean(np.any(np.abs(x[:, None] - special[None]) < 2 * sx[:, None], 1)))
p = np.array(p); sims = rng.random((20000, len(p))) < p
print("   expected hits by chance %.2f ; chance of >= %d hits %.1f%%" % (p.sum(), len(hits), 100 * np.mean(sims.sum(1) >= len(hits))))

print("\nD2  Same test with JUNO's first results (207.2 days, normal ordering): Delta m^2_21 = 7.388e-5 (7.310-7.466), Delta m^2_31 = 2.509e-3 (2.484-2.536)")
# Reading in peel terms: x = sqrt(Delta31/Delta21) (ratio of the square-root splittings); claim Gamma(x) = 1/sqrt2, i.e. x = 3+2sqrt2 = the wall.
# PRIOR ART: arXiv 2610.06738 proposes (sqrt D31 + sqrt D21)/(sqrt D31 - sqrt D21) = sqrt2, which is the same relation.  Kill: > 2 sigma.
d21, s21, d31, s31 = 7.388e-5, .078e-5, 2.509e-3, .026e-3
x = np.sqrt(d31 / d21); sx = .5 * x * np.hypot(s21 / d21, s31 / d31)
print("   x = %.4f +- %.4f vs wall %.4f : %.2f sigma -> %s ; peel of x = %.5f (1/sqrt2 = %.5f) ; ratio %.2f vs (3+2sqrt2)^2 = %.2f" %
      (x, sx, W, (x - W) / sx, 'KILLED' if abs(x - W) / sx > 2 else 'survives', G(x), 2 ** -.5, d31 / d21, W ** 2))
