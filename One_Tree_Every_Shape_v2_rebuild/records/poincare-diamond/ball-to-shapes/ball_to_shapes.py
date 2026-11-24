# SCRIPT: BALL-TO-SHAPES-01  the Standard Model as placed in the Poincare ball, measured again in every other shape
# Jeromie Beasley, 23 Nov 2026, AI-assisted.
# BALL PLACEMENT (as in SM_in_the_Ball_Mixer_v1, reading A): one common energy E; rapidity eta = arccosh(E/m); Poincare radius tanh(eta/2).
#   Directions: generation 1 on arm 1, generation 2 on arm 2, generation 3 on arm 3 (leptons and quarks of a generation share the arm);
#   W, Z, H on the diagonal (1,1,1).  Massless (photon, gluon) sit on the rim: infinitely far, listed but left out of distances.
#   3D: arms are the x, y, z axes.  2D (ASSIGNMENT, flagged): arms at 0, 120, 240 degrees, bosons at 60 degrees.
# CARRYING A POINT INTO ANOTHER SHAPE (a fork, both built):
#   (a) same spot: the ball's Klein point (radius tanh eta, same direction) placed as-is inside the shape (each shape has inner radius 1,
#       so it contains the ball) and read with that shape's own distance.
#   (b) same distance from the centre: the point on the same direction whose distance from the centre IN THAT SHAPE is eta.
# MEASURED in every shape: (1) distance from centre; (2) inside or outside the wall (distance < ln(3+2 sqrt2) = 1.7627);
#   (3) all pairwise distances vs the ball's (rank agreement); (4) each particle's nearest neighbour vs the ball's;
#   (5) the e-mu-tau path defect d(e,mu) + d(mu,tau) - d(e,tau) (zero would mean the three sit on one straight line).
import numpy as np
from scipy.stats import spearmanr
E = 200e3                                                  # MeV, above the top so every massive particle is inside
mass = {'e': .51099895, 'mu': 105.6583755, 'tau': 1776.93, 'u': 2.16, 'c': 1272.9, 't': 172600., 'd': 4.70, 's': 92.9, 'b': 4186.,
        'W': 80362.5, 'Z': 91187.9, 'H': 125130.}
gen = {'e': 0, 'u': 0, 'd': 0, 'mu': 1, 'c': 1, 's': 1, 'tau': 2, 't': 2, 'b': 2}
names = list(mass); eta = {k: np.arccosh(E / v) for k, v in mass.items()}
WALL = np.log(3 + 2 * np.sqrt(2))
phi = (1 + 5 ** .5) / 2
def nr(A): A = np.array(A, float); return A / np.linalg.norm(A, axis=1, keepdims=True)
def poly2(n, rot=0): return np.array([[np.cos(2 * np.pi * k / n + rot), np.sin(2 * np.pi * k / n + rot)] for k in range(n)])
def signs(v):
    out = []
    for s in np.array(np.meshgrid(*[[1, -1]] * len(v))).T.reshape(-1, len(v)):
        w = v * s
        if not any(np.allclose(w, o) for o in out): out.append(w)
    return out
cyc = lambda v: [v, v[[1, 2, 0]], v[[2, 0, 1]]]
SH2 = {'triangle': poly2(3, np.pi / 2), 'square': poly2(4), 'diamond': poly2(4, np.pi / 4), 'hexagon': poly2(6)}
SH3 = {'tetrahedron': nr([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]]), 'cube': np.vstack([np.eye(3), -np.eye(3)]),
       'octahedron': nr(signs(np.ones(3))), 'dodecahedron': nr([w for v in signs(np.array([0, 1, phi])) for w in cyc(v)]),
       'icosahedron': nr(signs(np.ones(3)) + [w for v in signs(np.array([0, 1 / phi, phi])) for w in cyc(v)])}
def dirs(dim):
    if dim == 3: arms = np.eye(3); diag = np.ones(3) / np.sqrt(3)
    else: arms = np.array([[np.cos(a), np.sin(a)] for a in np.radians([0, 120, 240])]); diag = np.array([np.cos(np.pi / 3), np.sin(np.pi / 3)])
    return {k: (arms[gen[k]] if k in gen else diag) for k in names}
def d_ball(x, y):   # Klein-model distance
    return np.arccosh(max(1., (1 - x @ y) / np.sqrt((1 - x @ x) * (1 - y @ y))))
def d_poly(A, x, y):
    lx, ly = 1 - A @ x, 1 - A @ y; r = np.log(ly) - np.log(lx); return .5 * (r.max() - r.min())
def same_distance_point(A, u, target):
    lo, hi = 0., 1.
    au = A @ u; tmax = np.min(1 / au[au > 1e-12])
    lo, hi = 0., tmax * (1 - 1e-15)
    for _ in range(200):
        mid = (lo + hi) / 2
        if d_poly(A, np.zeros_like(u), mid * u) < target: lo = mid
        else: hi = mid
    return lo * u
def measure(dist, P):
    n = len(names); M = np.zeros((n, n))
    for i in range(n):
        for j in range(n): M[i, j] = dist(P[names[i]], P[names[j]]) if i != j else 0
    return M
def report(tag, dim, shapes):
    U = dirs(dim)
    Pb = {k: np.tanh(eta[k]) * U[k] for k in names}
    Mb = measure(d_ball, Pb); iu = np.triu_indices(len(names), 1)
    nb = [names[np.argmin(np.where(np.eye(len(names)) > 0, np.inf, Mb)[i])] for i in range(len(names))]
    ie, im, it = names.index('e'), names.index('mu'), names.index('tau')
    rows = [('ball (now)', [Mb[i, :][i] for i in range(0)], Mb, {k: eta[k] for k in names})]
    print("\n== %s (%dD) ==" % (tag, dim))
    print("   %-14s %-7s %-34s %-9s %-9s %s" % ('shape', 'carry', 'outside the wall (of 12)', 'rank agr', 'same NN', 'e-mu-tau defect'))
    print("   %-14s %-7s %-34s %-9s %-9s %.3f" % ('ball (now)', '-', str(sum(eta[k] > WALL for k in names)) + ': ' + ' '.join(k for k in names if eta[k] > WALL), '1.000', '12/12', Mb[ie, im] + Mb[im, it] - Mb[ie, it]))
    out = {}
    for nm, A in shapes.items():
        for carry in ('a', 'b'):
            if carry == 'a': P = {k: np.tanh(eta[k]) * U[k] for k in names}
            else: P = {k: same_distance_point(A, U[k], eta[k]) for k in names}
            dist = lambda x, y, A=A: d_poly(A, x, y); M = measure(dist, P)
            r0 = {k: d_poly(A, np.zeros(dim), P[k]) for k in names}
            outside = [k for k in names if r0[k] > WALL]
            rho = spearmanr(Mb[iu], M[iu]).correlation
            nn = [names[np.argmin(np.where(np.eye(len(names)) > 0, np.inf, M)[i])] for i in range(len(names))]
            same = sum(a == b for a, b in zip(nb, nn))
            dfx = M[ie, im] + M[im, it] - M[ie, it]
            out[(nm, carry)] = (r0, M)
            print("   %-14s %-7s %-34s %-9.3f %-9s %.3f" % (nm, 'spot' if carry == 'a' else 'dist', str(len(outside)) + ': ' + ' '.join(outside), rho, '%d/12' % same, dfx))
    return out, Mb
print("Common energy E = 200 GeV.  Rapidity from the centre (ball):", ', '.join('%s %.2f' % (k, eta[k]) for k in names))
print("Wall: distance ln(3+2 sqrt2) = %.4f from the centre.  Massless photon and gluon: on the rim in every shape (infinitely far)." % WALL)
o2, _ = report('2D shapes', 2, SH2)
o3, _ = report('3D solids', 3, SH3)
print("\nDistance from the centre under 'same spot' (a), per particle and shape (ball value first):")
for k in names:
    print("   %-4s ball %.2f | " % (k, eta[k]) + ' '.join('%s %.2f' % (nm[:4], o3[(nm, 'a')][0][k]) for nm in SH3) + ' | ' + ' '.join('%s %.2f' % (nm[:4], o2[(nm, 'a')][0][k]) for nm in SH2))
