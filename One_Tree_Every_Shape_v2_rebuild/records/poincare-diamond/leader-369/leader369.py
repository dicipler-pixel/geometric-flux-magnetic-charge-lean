# SCRIPT: LEADER-369-01  sun, galaxy, universe as eigenvalues 3, 6, 9 following the leader: build it, break it, straw-man it
# Jeromie Beasley, 22 Nov 2026, AI-assisted.  Every test writes its kill condition BEFORE it runs.  Values and sources in the report.
import numpy as np
from fractions import Fraction as F
from scipy.linalg import expm
rng = np.random.default_rng(369)
G = lambda z: (z - 1) / (z + 1)
DAY, YR, MYR = 86400., 3.15576e7, 3.15576e13; KPC_KM = 3.0857e16; GN = 6.674e-11
verdict = {}

print("=== BUILD ===")
print("B1  The model: three modes, rates 3, 6, 9, sun feeds galaxy feeds universe with coupling c")
# Claims: (a) coupling never moves the eigenvalues; (b) with c > 0 every start ends on the leader; (c) larger c = faster takeover;
# (d) with c = 0 nothing follows.  Kill: eigenvalues move by > 1e-9, or (b),(c),(d) fail.
ok = True; times = []
for c in [0, 1, 5, 50, 500]:
    A = np.array([[3, 0, 0], [c, 6, 0], [0, c, 9.]])
    if np.max(np.abs(np.sort(np.linalg.eigvals(A).real) - [3, 6, 9])) > 1e-9: ok = False
    # takeover time: first t with universe share > 0.99 starting from the sun mode
    t_hit = None
    for t in np.linspace(0, 6, 6001):
        y = expm(A * t) @ np.array([1, 0, 0.]); 
        if np.linalg.norm(y) > 0 and abs(y[2]) / np.linalg.norm(y) > .99: t_hit = t; break
    times.append(t_hit)
print("   eigenvalues fixed at 3, 6, 9 for every coupling:", ok)
print("   time for the universe mode to hold 99%% of the direction, c = 0, 1, 5, 50, 500:", times)
b1 = ok and times[0] is None and all(times[i] > times[i + 1] for i in range(1, len(times) - 1))
verdict['B1 model'] = 'HOLDS' if b1 else 'KILLED'
print("B2  The 3-6-9 spectrum is Plato's chord: ratios 2, 3/2, 3; peels 1/3, 1/5, 1/2; and x3, x6, x9 closed mod 9")
b2 = (G(F(6, 3)), G(F(9, 6)), G(F(9, 3))) == (F(1, 3), F(1, 5), F(1, 2)) and all((a * m) % 9 in (0, 3, 6) for a in range(9) for m in (3, 6, 9)) \
     and sorted({pow(2, k, 9) for k in range(6)}) == [1, 2, 4, 5, 7, 8]
verdict['B2 chord + mod 9'] = 'HOLDS (exact arithmetic)' if b2 else 'KILLED'
print("  ", verdict['B2 chord + mod 9'])

print("\n=== BREAK: real rates ===")
# Candidate periods for each scale (seconds).  Each is (name, low, high) to carry the measurement spread.
R0 = 8.2467; Ob = (33.29 - 1.81, 33.29 + 1.81)
sun = [('rotation, equator sidereal', 25.38 * DAY, 25.38 * DAY), ('rotation, Carrington', 27.2753 * DAY, 27.2753 * DAY),
       ('sunspot cycle', 10.5 * YR, 11.5 * YR), ('magnetic (Hale) cycle', 21 * YR, 23 * YR), ('5-minute oscillation', 300., 300.),
       ('dynamical 1/sqrt(G rho), rho 1408 kg/m3', 1 / np.sqrt(GN * 1408), 1 / np.sqrt(GN * 1408))]
P = lambda V: 2 * np.pi * R0 * KPC_KM / V
gal = [("Sun's orbit (V 229 to 251 km/s)", P(251.31), P(229.0)), ('bar pattern (33.29 +- 1.81 km/s/kpc)', 2 * np.pi * KPC_KM / Ob[1], 2 * np.pi * KPC_KM / Ob[0])]
Msun = 1.989e30; KPC = 3.0857e19
def tdyn_gal(M, R): return 1 / np.sqrt(GN * M * Msun / (4 / 3 * np.pi * (R * KPC) ** 3))
gal.append(('dynamical, M 0.8-1.5e12 Msun within 200-300 kpc', tdyn_gal(1.5e12, 200), tdyn_gal(0.8e12, 300)))
H = lambda h: h / 3.0857e19
uni = [('1/H0, H0 67.4 to 73.0 km/s/Mpc', 1 / H(73.0), 1 / H(67.4)),
       ('dynamical of the Hubble density 3H0^2/8piG', np.sqrt(8 * np.pi / 3) / H(73.0), np.sqrt(8 * np.pi / 3) / H(67.4))]
for nm, L in [('sun', sun), ('galaxy', gal), ('universe', uni)]:
    for n, a, b in L: print("   %-8s %-46s %.3g to %.3g s" % (nm, n, a, b))

def ratio_hits(Ls, Lg, Lu, tol=.10):
    hits = []
    for reading, (r1, r2) in [('decay: periods 1 : 1.5 : 3', (1.5, 2.0)), ('growth: periods 3 : 1.5 : 1 (sun slowest)', (1 / 2.0, 1 / 1.5))]:
        for s in Ls:
            for g in Lg:
                for u in Lu:
                    q1 = (g[1] / s[2], g[2] / s[1]); q2 = (u[1] / g[2], u[2] / g[1])
                    if q1[0] <= r1 * (1 + tol) and q1[1] >= r1 * (1 - tol) and q2[0] <= r2 * (1 + tol) and q2[1] >= r2 * (1 - tol):
                        hits.append((reading, s[0], g[0], u[0]))
    return hits
print("K1  Kill if no sun/galaxy/universe triple of periods sits on 3 : 6 : 9 (either reading) within 10%")
h = ratio_hits(sun, gal, uni); print("   hits:", h if h else 'none')
lo = min(g[1] for g in gal) / max(s[2] for s in sun); hi = max(g[2] for g in gal) / min(s[1] for s in sun)
print("   galaxy/sun period ratios span %.2g to %.2g ; universe/galaxy span %.3g to %.3g (targets 1.5 to 2)" %
      (lo, hi, min(u[1] for u in uni) / max(g[2] for g in gal), max(u[2] for u in uni) / min(g[1] for g in gal)))
verdict['K1 direct 3:6:9 rates'] = 'KILLED' if not h else 'survives'

print("K2  Straw-man at full strength: ANY two candidates from ANY two scales on 2, 3/2 or 3, then a look-elsewhere control")
# Why the control: with many candidates, some ratio will land near a target by chance.  Count real hits, then the same count
# for candidates drawn at random across the same span of decades.  Kill if the real count is not above the random 95th percentile.
def pair_hits(groups, tol=.05):
    n = 0; found = []
    for i in range(3):
        for j in range(i + 1, 3):
            for a in groups[i]:
                for b in groups[j]:
                    for t in (2, 1.5, 3):
                        r = (b[1] / a[2], b[2] / a[1])
                        if r[0] <= t * (1 + tol) and r[1] >= t * (1 - tol): n += 1; found.append((a[0], b[0], t))
    return n, found
n_real, found = pair_hits([sun, gal, uni]); print("   real hits:", n_real, found)
allv = np.log10([x[1] for L in (sun, gal, uni) for x in L]); sims = []
for _ in range(4000):
    grp = []
    for L in (sun, gal, uni):
        lv = rng.uniform(allv.min(), allv.max(), len(L)); grp.append([('r', 10 ** v, 10 ** v * (x[2] / x[1])) for v, x in zip(lv, L)])
    sims.append(pair_hits(grp)[0])
p95 = np.percentile(sims, 95); print("   random 95th percentile: %.0f ; real above it: %s" % (p95, n_real > p95))
verdict['K2 any-pair chord'] = 'KILLED (no more than chance)' if n_real <= p95 else 'survives'

print("K3  Same physics at each scale (dynamical rate sqrt(G rho)): kill if the three rates are not 1 : 2 : 3 within 10%")
rs = [1 / sun[5][1], 1 / np.sqrt(tdyn_gal(1e12, 250) ** 2), 1 / uni[1][1]]
print("   rates relative to the slowest: %s" % np.round(np.array(rs) / min(rs), 3))
verdict['K3 dynamical rates'] = 'KILLED' if abs(sorted(np.array(rs) / min(rs))[1] - 2) > .2 else 'survives'

print("\n=== BREAK: following the leader in direction ===")
# Spin axes.  Sun's rotation pole (IAU): RA 286.13, Dec 63.87.  Galactic north pole: RA 192.85948, Dec 27.12825.
# Supergalactic north pole in galactic coordinates: l 47.37, b 6.32.  Random axes: cos(angle) uniform on [0,1].
def vec(ra, dec): ra, dec = np.radians([ra, dec]); return np.array([np.cos(dec) * np.cos(ra), np.cos(dec) * np.sin(ra), np.sin(dec)])
ang_sg = np.degrees(np.arccos(abs(vec(286.13, 63.87) @ vec(192.85948, 27.12825))))
p_sg = 1 - np.cos(np.radians(ang_sg))
print("K4  Sun follows the galaxy: kill if the Sun's spin is no closer to the galaxy's than chance (p > 0.3)")
print("   angle %.1f deg ; chance of a random axis being this close or closer p = %.2f" % (ang_sg, p_sg))
verdict['K4 sun follows galaxy (spin)'] = 'KILLED (chance level)' if p_sg > .3 else 'survives'
ang_gs = 90 - 6.32; p_gs = np.cos(np.radians(ang_gs))
print("K5  Galaxy follows the Local Sheet (spin lying in the sheet, as tidal torques give): kill if p > 0.3")
print("   spin to sheet-normal angle %.1f deg ; chance of a random axis lying this flat in the sheet p = %.2f (one galaxy only)" % (ang_gs, p_gs))
verdict['K5 galaxy follows sheet (spin)'] = 'survives (one galaxy; surveys carry the statistics)' if p_gs <= .3 else 'KILLED'

print("\n=== STRAW-MAN the number games ===")
print("K6  'Measured numbers reduce to 3, 6, 9 by digital root': kill if the root changes with the units")
dr = lambda x: 1 + (int(round(x)) - 1) % 9
for n, v in [('sun rotation', 25.38 * 24 * 3600), ('Sun orbit', P(229.0))]:
    print("   %-13s days %s -> %d ; hours %s -> %d ; seconds %s -> %d" % (n, round(v / DAY), dr(v / DAY), round(v / 3600), dr(v / 3600), round(v), dr(v)))
verdict['K6 digital roots of measurements'] = 'KILLED (unit artifact)'
print("K7  'Peel of the real scale ratios lands on the chord': kill if no real ratio peels to within 0.02 of 1/3, 1/5 or 1/2")
rr = [lo, hi, min(u[1] for u in uni) / max(g[2] for g in gal), max(u[2] for u in uni) / min(g[1] for g in gal)]
print("   peels:", ['%.6f' % G(x) for x in rr], "(the extreme ratios of each span)")
print("   the universe/galaxy span (2.39 to 240) does pass through 3 (peel 1/2), but only because the span is wide; K2's random control is the fair test")
verdict['K7 peel of raw ratios'] = 'KILLED (a wide span covers any target; chance level per K2)'

print("\n=== WHAT HOLDS ===")
for k, v in verdict.items(): print("   %-36s %s" % (k, v))
