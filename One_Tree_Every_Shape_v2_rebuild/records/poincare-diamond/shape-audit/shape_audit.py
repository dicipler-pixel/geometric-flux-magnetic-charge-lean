# SCRIPT: SHAPE-AUDIT-01  audit of the Poincare shape system: what holds, what was over its own kill line, what each shape does natively
# Jeromie Beasley, 23 Nov 2026, AI-assisted.  Kill conditions are written above each test, before the run.
import numpy as np, itertools, mpmath as mp
from scipy.spatial import ConvexHull
rng = np.random.default_rng(23)
phi = (1 + 5 ** .5) / 2
def nr(A): A = np.array(A, float); return A / np.linalg.norm(A, axis=1, keepdims=True)
def signs(v):
    out = []
    for s in itertools.product([1, -1], repeat=len(v)):
        w = np.array(v, float) * np.array(s)
        if not any(np.allclose(w, o) for o in out): out.append(w)
    return out
cyc = lambda v: [v, v[[1, 2, 0]], v[[2, 0, 1]]]
def poly2(n, rot=0): return np.array([[np.cos(2 * np.pi * k / n + rot), np.sin(2 * np.pi * k / n + rot)] for k in range(n)])
TET = nr([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]])
SOL = {'tetrahedron': TET, 'cube': np.vstack([np.eye(3), -np.eye(3)]), 'octahedron': nr(signs(np.ones(3))),
       'dodecahedron': nr([w for v in signs(np.array([0, 1, phi])) for w in cyc(v)]),
       'icosahedron': nr(signs(np.ones(3)) + [w for v in signs(np.array([0, 1 / phi, phi])) for w in cyc(v)])}
def d_own(A, x, y):                       # the shape's own distance: one book per face, half (largest - smallest) log ratio
    r = np.log(1 - A @ y) - np.log(1 - A @ x); return .5 * (r.max() - r.min())
def fwd(A, x, y): r = np.log(1 - A @ x) - np.log(1 - A @ y); return r.max()      # forward book (one-way distance x -> y)

print("A1  The angle-keeping face chart ON the rim itself (the earlier test stood 1e-6 inside the rim, where corners cannot be reached).")
print("    Kill: any rim point, more than 1e-6 of a turn away from a corner, lands off the polygon's edge by more than 1e-10")
mp.mp.dps = 30
for n in (3, 4, 5, 6):
    a, b, c = mp.mpf(1) / n, mp.mpf(2) / n, 1 + mp.mpf(1) / n
    F1 = mp.gamma(c) * mp.gamma(c - a - b) / (mp.gamma(c - a) * mp.gamma(c - b)); inr = F1 * mp.cos(mp.pi / n)
    worst = 0
    for j in range(240):
        th = 2 * mp.pi * (j + mp.mpf('0.37')) / 240
        w = mp.expjpi(th / mp.pi); p = w * mp.hyp2f1(a, b, c, w ** n) / inr
        # edge normals sit at angles pi/n + 2 pi k/n ; inner radius 1
        m = max(mp.re(p * mp.expjpi(-(mp.mpf(1) / n + mp.mpf(2) * k / n))) for k in range(n))
        worst = max(worst, abs(m - 1))
    print("   %d-gon  rim to edge worst %.1e   %s" % (n, float(worst), 'pass' if worst < 1e-10 else 'KILLED'))

print("\nA2  The angle-keeping chart keeps angles (the earlier test used a one-sided step of 1e-6 and read 2.5e-6, over its own 1e-6 line).")
print("    Kill: angle between the images of two right-angle steps off 90 degrees by more than 1e-10 rad, 200 points each")
for n in (3, 4, 5, 6):
    a, b, c = mp.mpf(1) / n, mp.mpf(2) / n, 1 + mp.mpf(1) / n
    f = lambda w: w * mp.hyp2f1(a, b, c, w ** n); worst = 0; h = mp.mpf('1e-10')
    for _ in range(200):
        g = mp.mpf(.9 * np.sqrt(rng.uniform())) * mp.expjpi(2 * rng.uniform())
        da = (f(g + h) - f(g - h)); db = (f(g + 1j * h) - f(g - 1j * h))
        worst = max(worst, abs(abs(mp.arg(db / da)) - mp.pi / 2))
    print("   %d-gon  worst angle error %.1e rad   %s" % (n, float(worst), 'pass' if worst < 1e-10 else 'KILLED'))

print("\nA3  Same from every point?  Pentagon faces (untested until now) and the five solids, by a measure no stretch or shear can change")
print("    (volume of the local yardstick times volume of its dual).  Prediction written first: constant ONLY for triangle and tetrahedron.")
print("    Kill: triangle or tetrahedron not constant to 1e-9 ; or any other shape constant to 1e-6")
def mahler(A, x):
    l = 1 - A @ x; P = A / l[:, None]                                   # local yardstick F(u) = 1/2 [h_P(u) + h_P(-u)]
    Q = np.array([.5 * (p - q) for p in P for q in P])                  # = support function of Q = (P - P)/2
    H = ConvexHull(Q); eq = H.equations                                 # facets n.x + off <= 0
    polar = np.array([e[:-1] / (-e[-1]) for e in eq]); polar = np.unique(np.round(polar, 12), axis=0)
    return H.volume * ConvexHull(polar).volume
tests = [('triangle', poly2(3)), ('square', poly2(4)), ('pentagon', poly2(5)), ('hexagon', poly2(6))] + list(SOL.items())
for nm, A in tests:
    v = []
    for _ in range(60):
        while True:
            x = rng.uniform(-1.4, 1.4, A.shape[1])
            if np.all(1 - A @ x > .06): break
        v.append(mahler(A, x))
    v = np.array(v); const = np.ptp(v) < 1e-9 * v.mean(); want = nm in ('triangle', 'tetrahedron')
    print("   %-13s measure %.6f to %.6f   %-22s %s" % (nm, v.min(), v.max(), 'same from every point' if const else 'changes with the point',
          'pass' if (const == want and (want or np.ptp(v) > 1e-6)) else 'KILLED'))

print("\nA4  One Tree, Every Shape: the tree is carried in along rays (rim onto faces).  Measured in each solid's OWN reading:")
print("    every edge is ln 5 = 1.6094 in the ball.  Is it still one step length in the solid?  Are the carried edges straight in the solid?")
print("    Not a kill test: a measurement of how much of the ball's tree survives the carry.")
def bv(v, ax, r):
    c, s = np.cosh(r), np.sinh(r); o = v.copy(); o[0] = c * v[0] + s * v[ax + 1]; o[ax + 1] = s * v[0] + c * v[ax + 1]; return o
def tree(z, D):
    rap = np.log(z); O = np.array([1., 0, 0, 0]); E = []
    def pt(w):
        v = O
        for k in reversed(w): v = bv(v, k >> 1, (-1 if k & 1 else 1) * rap)
        return v
    def walk(w):
        if len(w) == D: return
        p = pt(w)
        for k in range(6):
            if w and (k ^ 1) == w[-1]: continue
            E.append((p, pt(w + [k]), len(w))); walk(w + [k])
    walk([]); return E
def carry(A, k):
    r = np.linalg.norm(k)
    if r < 1e-14: return k
    u = k / r; return u * r / np.max(A @ u)
def geo(p, q, t):
    ip = -p[0] * q[0] + p[1:] @ q[1:]; d = np.arccosh(max(1., -ip)); return (np.sinh((1 - t) * d) * p + np.sinh(t * d) * q) / np.sinh(d)
E3 = tree(5, 3)
print("   %-13s own length of an edge: level-1 edges      level-2 edges      level-3 edges      worst sideways bend / chord" % 'solid')
for nm, A in SOL.items():
    L = {0: [], 1: [], 2: []}; bend = 0
    for p, q, lv in E3:
        x, y = carry(A, p[1:] / p[0]), carry(A, q[1:] / q[0]); L[lv].append(d_own(A, x, y))
        ch = y - x; Lc = np.linalg.norm(ch)
        for t in (.25, .5, .75):
            m = geo(p, q, t); xm = carry(A, m[1:] / m[0]); off = xm - x; perp = off - (off @ ch) / Lc ** 2 * ch; bend = max(bend, np.linalg.norm(perp) / Lc)
    print("   %-13s %27s %18s %18s      %.3f" % (nm, *['%.3f to %.3f' % (min(L[i]), max(L[i])) for i in range(3)], bend))

print("\nA5  The tetrahedron's own moves.  A peel step by ratio z on one face book: multiply that book by z, keep the point in the solid.")
print("    Kill (a): the step changes any own distance by more than 1e-11 (then it is not the solid's own motion)")
print("    Kill (b): step length is not 1/2 ln z, or two steps on one book do not add, to 1e-11")
print("    Kill (c): the loop A B A^-1 B^-1 on two different books fails to close by more than 1e-11 at any z (then the tetrahedron HAS a wall)")
V = np.array([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]], float) * 3 / np.sqrt(3) * -1    # corners opposite each face, inner radius 1
bary = lambda x: (1 - TET @ x) / 4.                                    # four books, they add to 1
def step(x, i, z):
    l = bary(x).copy(); l[i] *= z; l /= l.sum()
    return np.linalg.lstsq(np.vstack([TET, np.ones(3) * 0]), np.append(1 - 4 * l, 0), rcond=None)[0]
def rpt():
    while True:
        x = rng.uniform(-1.5, 1.5, 3)
        if np.all(1 - TET @ x > .05): return x
wa = wb = wc = 0; W = 3 + 2 * np.sqrt(2)
for z in (2, 3, 5, W, 7, 50):
    for _ in range(200):
        x, y = rpt(), rpt(); i, j = rng.choice(4, 2, replace=False)
        wa = max(wa, abs(d_own(TET, step(x, i, z), step(y, i, z)) - d_own(TET, x, y)))
        wb = max(wb, abs(d_own(TET, x, step(x, i, z)) - .5 * np.log(z)), abs(d_own(TET, x, step(step(x, i, z), i, z)) - np.log(z)))
        loop = step(step(step(step(x, i, z), j, z), i, 1 / z), j, 1 / z); wc = max(wc, d_own(TET, x, loop))
print("   (a) worst change of a distance under a step %.1e   %s" % (wa, 'pass' if wa < 1e-11 else 'KILLED'))
print("   (b) worst step-length / adding error        %.1e   %s" % (wb, 'pass' if wb < 1e-11 else 'KILLED'))
print("   (c) worst loop gap, z = 2, 3, 5, wall, 7, 50  %.1e   %s  -> the loop always closes: no wall in the tetrahedron" % (wc, 'pass' if wc < 1e-11 else 'KILLED'))
# the same loop in the ball
def loopgap_ball(z):
    r = np.log(z); v = np.array([1., 0, 0, 0])
    for ax, s in ((1, -1), (0, -1), (1, 1), (0, 1)): v = bv(v, ax, s * r)
    return np.arccosh(v[0])
print("       same loop in the ball: gap %.4f at z = 3, %.4f at z = 5, %.4f at the wall, %.4f at z = 7" % tuple(loopgap_ball(z) for z in (3, 5, W, 7)))
# how many different places words of length <= L reach: tree (ball) vs tetrahedron
def reach_tet(L):
    seen = {(0, 0, 0, 0)}; fr = [(0, 0, 0, 0)]; out = [1]
    for _ in range(L):
        nx = []
        for e in fr:
            for i in range(4):
                for s in (1, -1):
                    f = list(e); f[i] += s; m = min(f); f = tuple(v - m for v in f)       # multiplying all four books together changes nothing
                    if f not in seen: seen.add(f); nx.append(f)
        fr = nx; out.append(len(seen))
    return out
def reach_ball(L, gens):
    out = [1]; n = 1; fr = 1
    for k in range(L): fr = fr * (gens if k == 0 else gens - 1); n += fr; out.append(n)
    return out
print("   places reached by 0..4 steps:  ball tree, three arms %s   tetrahedron, four books %s" % (reach_ball(4, 6), reach_tet(4)))

print("\nA6  Two books in every shape: the own reading is the average of a forward and a backward one-way reading.")
print("    Kill: average differs from the own reading by more than 1e-12.  Also reported: where forward and backward disagree.")
for nm, A in SOL.items():
    w = 0; asym = 0
    for _ in range(300):
        while True:
            x, y = rng.uniform(-1.2, 1.2, 3), rng.uniform(-1.2, 1.2, 3)
            if np.all(1 - A @ x > .05) and np.all(1 - A @ y > .05): break
        w = max(w, abs(.5 * (fwd(A, x, y) + fwd(A, y, x)) - d_own(A, x, y)))
    c = np.zeros(3); u = A[0]; p = .6 * u / np.max(A @ u)
    print("   %-13s worst %.1e  %s ; from the centre toward a face: out %.4f, back %.4f" % (nm, w, 'pass' if w < 1e-12 else 'KILLED', fwd(A, c, p), fwd(A, p, c)))
