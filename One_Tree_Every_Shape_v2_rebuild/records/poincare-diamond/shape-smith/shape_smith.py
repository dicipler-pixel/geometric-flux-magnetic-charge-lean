# SCRIPT: SHAPE-SMITH-01  a Smith chart for each shape: testing every idea, and how the shapes act inside and against each other
# Jeromie Beasley, 23 Nov 2026, AI-assisted.  Shapes (2D): triangle, square (faces across the axes), diamond (corners on the axes),
# hexagon, and the disk.  Each shape has inner radius 1.  Smith point G = (z-1)/(z+1); open circuit G = +1, short G = -1.
# THREE VERSIONS of a shape's chart (built side by side):
#   V1 keep angles  : Schwarz-Christoffel map of the disk onto the regular n-gon, f(w) = w 2F1(1/n, 2/n; 1+1/n; w^n), scaled.
#   V2 keep lines   : Klein point k = 2G/(1+|G|^2), stretched out along its own ray so the disk's rim lands on the shape's boundary.
#   V3 face+position: each face its own ordinary chart (exact on every face by construction; a full turn crosses n faces).
# The shape's own distance (Hilbert): d(x,y) = 1/2 ln of the cross-ratio with the two boundary hits.  Kill conditions above each test.
import numpy as np
from scipy.special import hyp2f1
rng = np.random.default_rng(11)
G = lambda z: (z - 1) / (z + 1); op = lambda a, b: (a + b) / (1 + a * b)
def poly(n, rot): return np.array([[np.cos(2 * np.pi * k / n + rot), np.sin(2 * np.pi * k / n + rot)] for k in range(n)])
# rot chosen so that the open-circuit direction (+x) points at a CORNER for triangle and diamond, at a FACE MIDDLE for square and hexagon
SH = {'triangle': (3, poly(3, np.pi / 3)), 'square': (4, poly(4, 0)), 'diamond': (4, poly(4, np.pi / 4)), 'hexagon': (6, poly(6, 0))}
def tmax_poly(A):
    def f(x, u):
        au = A @ u; gap = 1 - A @ x; m = au > 1e-14; return np.min(gap[m] / au[m])
    return f
def tmax_disk(x, u):
    b = x @ u; c = x @ x - 1; return -b + np.sqrt(b * b - c)
def tmax_lp(p):
    def f(x, u):
        lo, hi = 0., 3.
        for _ in range(80):
            m = (lo + hi) / 2
            if np.sum(np.abs(x + m * u) ** p) ** (1 / p) < 1: lo = m
            else: hi = m
        return lo
    return f
def dist(tm, x, y):
    if np.allclose(x, y): return 0.
    u = (y - x) / np.linalg.norm(y - x); s = np.linalg.norm(y - x); tp = tm(x, u); tn = tm(x, -u)
    return .5 * np.log((tp * (s + tn)) / ((tp - s) * tn))
def finsler(tm, x, u): return .5 * (1 / tm(x, u) + 1 / tm(x, -u))
# --- the three versions --------------------------------------------------------------------------------------------------
def v1_map(n, alpha):
    # F(w) = w 2F1(1/n, 2/n; 1+1/n; w^n) maps the disk onto a regular n-gon with corners at angles 2 pi k/n;
    # turned by alpha so its corners sit on the shape's own corners.  (First run turned it wrongly: rim missed the boundary by up to 0.41.)
    inr = abs(hyp2f1(1 / n, 2 / n, 1 + 1 / n, 1.0 + 0j)) * np.cos(np.pi / n)
    def f(g):
        w = g * np.exp(-1j * alpha)
        if abs(w) >= 1: w = w / abs(w) * (1 - 1e-12)
        return np.exp(1j * alpha) * w * hyp2f1(1 / n, 2 / n, 1 + 1 / n, w ** n) / inr
    return f
def v2_map(tm):
    def f(g):
        k = 2 * g / (1 + abs(g) ** 2); r = abs(k)
        if r < 1e-15: return 0j
        u = np.array([k.real, k.imag]) / r; R = tm(np.zeros(2), u); return complex(*(r * R * u))
    return f
C = lambda z: np.array([z.real, z.imag])

print("T0  Smith's own lines are the three motions.  Kill: any check off by more than 1e-12")
w0 = 0
for r in np.linspace(.1, 5, 30):                        # constant resistance circle: centre r/(1+r), radius 1/(1+r): touches rim at +1 (horocycle)
    w0 = max(w0, abs(r / (1 + r) + 1 / (1 + r) - 1))
for x in np.linspace(.2, 5, 30):                        # constant reactance circle: centre 1 + i/x, radius 1/x: square-on to the rim (geodesic)
    w0 = max(w0, abs(abs(1 + 1j / x) ** 2 - 1 - 1 / x ** 2))
pts = [G(1.7 + 1j * x) for x in np.linspace(-9, 9, 50)]; cen = 1.7 / 2.7
w0 = max(w0, max(abs(abs(p - cen) - 1 / 2.7) for p in pts))
print("   resistance circles touch the rim at the open point, reactance arcs meet the rim square-on: worst %.1e" % w0)

print("\nT1  Matched -> centre, lossless rim -> the shape's boundary, in V1 and V2.  Kill: any boundary point off by more than 1e-6")
for nm, (n, A) in SH.items():
    rot = np.arctan2(A[0, 1], A[0, 0]) + np.pi / n            # a corner direction of this shape
    tm = tmax_poly(A); f1, f2 = v1_map(n, rot), v2_map(tm); worst = [0, 0]
    for th in np.linspace(0, 2 * np.pi, 721)[:-1]:
        g = .999999 * np.exp(1j * th)
        for i, f in enumerate((f1, f2)):
            p = C(f(g)); worst[i] = max(worst[i], abs(1 - np.max(A @ p)))
    print("   %-9s centre V1 %.1e V2 %.1e ; rim to boundary worst V1 %.1e V2 %.1e" % (nm, abs(f1(0j)), abs(f2(0j)), worst[0], worst[1]))
    SH[nm] = (n, A, rot)

print("\nT2  V1 keeps angles, V2 does not.  Kill: V1 angle error > 1e-6 rad, or V2 angle error < 1e-3 rad (then V2 would also be conformal)")
for nm, (n, A, rot) in SH.items():
    f1, f2 = v1_map(n, rot), v2_map(tmax_poly(A)); e = [0, 0]
    for _ in range(300):
        g = .9 * np.sqrt(rng.uniform()) * np.exp(2j * np.pi * rng.uniform()); h = 1e-6
        for i, f in enumerate((f1, f2)):
            a = f(g + h) - f(g); b = f(g + 1j * h) - f(g)              # images of two right-angle steps
            e[i] = max(e[i], abs(abs(np.angle(b / a)) - np.pi / 2))
    print("   %-9s worst angle error: V1 %.1e rad, V2 %.3f rad" % (nm, e[0], e[1]))

print("\nT3  The turn (moving along a lossless line, |G| fixed): does it stay at one distance from the centre in the shape's own reading?")
# Idea under test: 'the standing-wave circles become the shape's own rings'.  Kill for V2 on shapes with a centre of symmetry:
# spread of distance > 1e-9 (V2 should keep it exactly there); for the triangle the spread should be > 0 (no centre of symmetry).
for nm, (n, A, rot) in SH.items():
    tm = tmax_poly(A); f1, f2 = v1_map(n, rot), v2_map(tm)
    for gm in (.5, 2 ** -.5):
        d = [[dist(tm, np.zeros(2), C(f(gm * np.exp(1j * th)))) for th in np.linspace(0, 2 * np.pi, 361)[:-1]] for f in (f1, f2)]
        print("   %-9s |G| = %.4f  distance from centre: V1 %.4f to %.4f   V2 %.6f to %.6f (disk value %.4f)" %
              (nm, gm, min(d[0]), max(d[0]), min(d[1]), max(d[1]), np.arctanh(2 * gm / (1 + gm ** 2))))

print("\nT4  The slide (a junction, r -> r (+) g): straight in the shape?  Measured as the largest sideways bend / chord length")
# Idea under test: 'junction slides become straight in straight-sided shapes'.  Run on the axis (r0 = 0) and off it (r0 = 0.3i).
# Kill: off-axis bend in V2 not smaller than the disk's own (Klein) bend -> the slide is NOT straightened by the shape.
def bend(path):
    a, b = path[0], path[-1]; ch = b - a; L = abs(ch); nrm = 1j * ch / L
    return max(abs(((p - a) * nrm.conjugate()).real) for p in path) / L
for nm, (n, A, rot) in list(SH.items()) + [('disk', (None, None, None))]:
    for r0 in (0j, .3j):
        path = [op(r0, g) for g in np.linspace(-.8, .8, 161)]
        if nm == 'disk':
            K = [2 * p / (1 + abs(p) ** 2) for p in path]; print("   %-9s start %-5s Smith/Poincare disk bend %.4f   Klein disk bend %.4f" % (nm, r0, bend(path), bend(K)))
        else:
            f1, f2 = v1_map(n, rot), v2_map(tmax_poly(A))
            print("   %-9s start %-5s V1 bend %.4f   V2 bend %.4f" % (nm, r0, bend([f1(p) for p in path]), bend([f2(p) for p in path])))

print("\nT5  Open and short: mirror images in every shape?  Distance from the centre of G = +0.9 (toward open) and -0.9 (toward short)")
# Idea under test: odd shapes break the open/short mirror.  Kill: triangle's two distances equal to 1e-9.
for nm, (n, A, rot) in SH.items():
    tm = tmax_poly(A)
    for i, f in enumerate((v1_map(n, rot), v2_map(tm))):
        do, ds = dist(tm, np.zeros(2), C(f(.9 + 0j))), dist(tm, np.zeros(2), C(f(-.9 + 0j)))
        print("   %-9s V%d  open side %.4f  short side %.4f  %s" % (nm, i + 1, do, ds, 'mirror' if abs(do - ds) < 1e-9 else 'NOT a mirror'))

print("\nT6  Same from every point?  The local yardstick's SHAPE, by a measure that ignores stretching and shearing")
# First run counted the yardstick's corners (6 triangle, 8 square and diamond, 12 hexagon) at every point: that count cannot tell
# a changing octagon from a fixed one, so it was too weak.  Now: the yardstick polygon's area over the area of the polygon made by
# every other corner (unchanged by any stretch or shear).  Kill: triangle value not constant to 1e-6; or square/diamond/hexagon constant.
def yardstick(A, x):
    l = 1 - A @ x; ph = np.linspace(0, 2 * np.pi, 20001)[:-1]
    U = np.c_[np.cos(ph), np.sin(ph)]; S = (U @ A.T) / l
    key = np.c_[np.argmax(S, 1), np.argmax(-S, 1)]; F = .5 * (S.max(1) + (-S).max(1))
    P = U / F[:, None]; idx = [i for i in range(len(ph)) if (key[i] != key[i - 1]).any()]
    V = P[idx]; ang = np.arctan2(V[:, 1], V[:, 0]); V = V[np.argsort(ang)]
    area = lambda Q: .5 * abs(np.dot(Q[:, 0], np.roll(Q[:, 1], -1)) - np.dot(Q[:, 1], np.roll(Q[:, 0], -1)))
    return area(V) / area(V[::2]), len(V)
for nm, (n, A, rot) in SH.items():
    vals = []
    for _ in range(40):
        while True:
            x = rng.uniform(-1.5, 1.5, 2)
            if np.all(1 - A @ x > .05): break
        vals.append(yardstick(A, x))
    r = np.array([v[0] for v in vals]); k = sorted(set(v[1] for v in vals))
    print("   %-9s corners %s ; shape measure %.6f to %.6f -> %s" % (nm, k, r.min(), r.max(), 'same from every point' if np.ptp(r) < 1e-6 else 'changes with the point'))

print("\nT7  Shapes inside each other: a bigger shape always reads shorter distances (inner circle <= shape <= outer circle)")
# Kill: any pair where the bigger domain reads a LONGER distance than the smaller one.
bad = 0; rat = {}
for nm, (n, A, rot) in SH.items():
    Rc = 1 / np.cos(np.pi / n); tm = tmax_poly(A); r = []
    for _ in range(300):
        x, y = [rng.uniform(-.7, .7, 2) for _ in range(2)]
        if np.linalg.norm(x) > .95 or np.linalg.norm(y) > .95: continue
        din = dist(tmax_disk, x, y); dsh = dist(tm, x, y); dout = dist(tmax_disk, x / Rc, y / Rc)
        if not (dout <= dsh + 1e-12 and dsh <= din + 1e-12): bad += 1
        r.append(dsh / din)
    rat[nm] = (min(r), max(r))
print("   violations %d ; shape / inner-circle distance ratio: %s" % (bad, ', '.join('%s %.2f-%.2f' % (k, *v) for k, v in rat.items())))

print("\nT8  Surgery: cut the diamond (p=1) through the disk (p=2) to the square (p=infinity) with |x|^p + |y|^p <= 1")
# Measured at 30 points: how far the local yardstick is from an ellipse (0 = Riemannian, like the ball), and whether the wall
# (distance ln(3+2 sqrt2) from the centre) is a round ring.  Kill: p = 2 not Riemannian to 1e-6, or any other p Riemannian.
def nonriem(tm, x):
    ph = np.linspace(0, np.pi, 90, endpoint=False); U = np.c_[np.cos(ph), np.sin(ph)]
    F2 = np.array([finsler(tm, x, u) ** 2 for u in U]); M = np.c_[U[:, 0] ** 2, 2 * U[:, 0] * U[:, 1], U[:, 1] ** 2]
    c, *_ = np.linalg.lstsq(M, F2, rcond=None); return np.max(np.abs(M @ c - F2)) / np.max(F2)
for p in (1, 1.5, 2, 3, 8):
    tm = tmax_lp(p); nr = []
    for _ in range(30):
        while True:
            x = rng.uniform(-1, 1, 2)
            if np.sum(np.abs(x) ** p) < .6: break
        nr.append(nonriem(tm, x))
    W = np.log(3 + 2 * np.sqrt(2)); ring = []
    for th in np.linspace(0, np.pi / 2, 19):
        u = np.array([np.cos(th), np.sin(th)]); R = tm(np.zeros(2), u); t = np.tanh(W) * R
        ring.append(np.linalg.norm(t * u))
    print("   p = %-4s off-ellipse %.1e to %.1e ; wall ring radius %.3f to %.3f (round only if equal)" % (p, min(nr), max(nr), min(ring), max(ring)))
