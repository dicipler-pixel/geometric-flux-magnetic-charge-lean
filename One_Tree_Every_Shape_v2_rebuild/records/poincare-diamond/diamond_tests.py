# SCRIPT: POINCARE-DIAMOND-01  the Poincare diamond as a measuring device: what it straightens, what it reads, where it stops
# Jeromie Beasley, 22 Nov 2026, AI-assisted.
# THE DEVICE. A pair of positive amounts (u, v) -- forward and backward, two books, the two null directions of a line --
# is drawn at the point (A, B) = (G(u), G(v)) with the peel step G(z) = (z - 1)/(z + 1).  The square (-1,1)^2 is turned 45
# degrees so its edges are the two directions: that is the diamond.  Peel addition (+): a (+) b = (a + b)/(1 + a b).
# Every test states its kill condition before it runs.
import numpy as np
rng = np.random.default_rng(22)
G = lambda z: (z - 1) / (z + 1)
op = lambda a, b: (a + b) / (1 + a * b)        # peel addition
om = lambda a, b: (a - b) / (1 - a * b)        # peel difference
worst = {}
def rec(k, v): worst[k] = max(worst.get(k, 0), v)

print("T1  A cable segment of length d is a straight move in the diamond")
# Transfer matrix of a lossless cable segment in (V, lambda V'): [[cosh d, sinh d],[sinh d, cosh d]].  In the null basis it is
# diag(e^d, e^-d): forward book x e^d, backward book x e^-d.  Claim: after any chain of segments the point is
# (A (+) tanh(sum d / 2) , B (-) tanh(sum d / 2)), i.e. each edge coordinate just adds peel steps, in any order.
# Kill: any mismatch above 1e-12 against the matrix product, or any dependence on the order of segments.
for trial in range(2000):
    d = rng.uniform(-1.5, 1.5, size=rng.integers(1, 12)); u0, v0 = np.exp(rng.normal(size=2))
    M = np.eye(2)
    for di in d: M = np.array([[np.cosh(di), np.sinh(di)], [np.sinh(di), np.cosh(di)]]) @ M
    P = np.array([[1, 1], [1, -1]]) / np.sqrt(2)            # null basis
    D = P @ M @ P.T                                           # should be diag(e^D, e^-D)
    rec('T1 off-diagonal', abs(D[0, 1]) + abs(D[1, 0]))
    u1, v1 = u0 * D[0, 0], v0 * D[1, 1]
    t = np.tanh(d.sum() / 2)
    rec('T1 point', abs(G(u1) - op(G(u0), t)) + abs(G(v1) - om(G(v0), t)))
    dp = rng.permutation(d); rec('T1 order', abs(np.tanh(dp.sum() / 2) - t))
print("   worst off-diagonal %.1e, point %.1e, order %.1e" % (worst['T1 off-diagonal'], worst['T1 point'], worst['T1 order']))

print("T2  Both maps of the wound ball are read off ONE diamond point")
# A point at rapidity r on the unit hyperbola: (u, v) = (e^-r, e^r), so (A, B) = (-tanh(r/2), tanh(r/2)).
# Claim: each edge coordinate is the page map (Poincare radius tanh(r/2)); the peel difference across the edges, B (-) A,
# is the physical map (Klein radius, the cable's input admittance tanh r).  Kill: mismatch above 1e-12.
for r in rng.uniform(0, 8, 2000):
    A, B = G(np.exp(-r)), G(np.exp(r))
    rec('T2 edge', abs(B - np.tanh(r / 2))); rec('T2 across', abs(om(B, A) - np.tanh(r)))
print("   worst: edge = tanh(r/2) %.1e ; across = tanh r %.1e" % (worst['T2 edge'], worst['T2 across']))
w = np.log(3 + 2 * np.sqrt(2))
print("   at the wall rapidity ln(3+2 sqrt2): edge %.6f (page wall, Gamma^2 = %.4f), across %.6f" % (np.tanh(w / 2), np.tanh(w / 2) ** 2, np.tanh(w)))

print("T3  The two diagonals read direction and size of two books")
# Books (W+, W-) at reference 1: A = G(W+), B = G(W-).  Claim: B (-) A = G(W-/W+)  (direction: BallJoins J1, the peel of the
# ratio) and A (+) B = G(W+ W-)  (size: the peel of the product, i.e. of the squared geometric mean).
# Kill: mismatch above 1e-12.
for _ in range(2000):
    Wp, Wm = np.exp(rng.normal(scale=2, size=2)); A, B = G(Wp), G(Wm)
    rec('T3 dir', abs(om(B, A) - G(Wm / Wp))); rec('T3 size', abs(op(A, B) - G(Wp * Wm)))
print("   worst: direction %.1e ; size %.1e" % (worst['T3 dir'], worst['T3 size']))

print("T4  The wound field and the cell ladder in the diamond")
# Cell n of a uniform chain sits at (A_n, B_n) = (-tanh(n th/2), tanh(n th/2)): equal peel steps along the cross diagonal.
# Claim: the field share cosh(n th)/cosh(N th) = [(1 + A_N B_N)/(1 - A_N B_N)] / [(1 + A_n B_n)/(1 - A_n B_n)],
# because cosh x = (1 - A B)/(1 + A B) on that diagonal.  Kill: mismatch above 1e-12.
for _ in range(500):
    th = rng.uniform(.001, .5); N = rng.integers(1, 200); N = min(N, int(30 / th)); n = rng.integers(0, N + 1)   # keep N th <= 30: past that 1 - tanh^2 underflows in double precision
    # store each coordinate by its gap to the rim, 1 - t = 2/(1 + e^x): near the rim 't' alone loses digits (first run: 3.6e-4)
    gap = lambda x: 2 / (1 + np.exp(x))
    def share(x):                      # (1 - t^2)/(1 + t^2) with 1 - t^2 = gap (2 - gap)
        g = gap(x); return g * (2 - g) / (1 + (1 - g) ** 2)
    lhs = np.cosh(n * th) / np.cosh(N * th); rhs = share(N * th) / share(n * th)
    rec('T4', abs(lhs - rhs) / lhs)
print("   worst relative %.1e" % worst['T4'])

print("T5  What rides straight, and where the diamond stops")
# Claim A (try to kill): a uniform line with loss AND phase, propagation gamma = alpha + i beta, is still diagonal in the
# null basis, so it is still a straight per-edge peel step, now complex.  Kill: off-diagonal above 1e-12, or order dependence.
P = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
def line(g): return np.array([[np.cosh(g), np.sinh(g)], [np.sinh(g), np.cosh(g)]], complex)
offd = 0; ordr = 0
for _ in range(2000):
    g1, g2 = rng.normal(size=2) + 1j * rng.normal(size=2)
    D = P @ line(g1) @ line(g2) @ P.T; offd = max(offd, abs(D[0, 1]) + abs(D[1, 0]))
    ordr = max(ordr, np.linalg.norm(line(g1) @ line(g2) - line(g2) @ line(g1)))
print("   lossy + phased uniform line: worst off-diagonal %.1e, order dependence %.1e" % (offd, ordr))
# Claim B (try to kill): 'a junction between two different lines also rides as per-edge addition'.  A junction with
# impedance ratio z keeps V and I; in normalized units it is J = diag(1, z).  In the null basis it mixes the two books
# (that mixing IS the reflection Gamma = (z-1)/(z+1)).  If junction and line give different results in the two orders,
# no per-edge addition can carry them.
def J(z): return np.array([[1, 0], [0, z]], complex)
for z, g in [(3 + 2 * np.sqrt(2), 0.5), (2.0, 0.3j), (0.5, 0.8 + 0.4j)]:
    Dj = P @ J(z) @ P.T
    print("   junction z=%.3f, line g=%s: books mixed by %.4f (Gamma=%.4f); |order1-order2| = %.4f" % (
        z, g, abs(Dj[0, 1] / Dj[0, 0]), (z - 1) / (z + 1), np.linalg.norm(J(z) @ line(g) - line(g) @ J(z))))
print("T6  Grid reach: what a step-by-step walker reaches is a diamond")
# Walker on a square grid, one cell per step, four directions.  Claim: the cells reached in exactly n steps or fewer are
# |x| + |y| <= n, a diamond, never a disk.  Kill: any reached cell outside, or any diamond cell not reached.
n = 12; R = {(0, 0)}; F = {(0, 0)}
for _ in range(n):
    F = {(x + dx, y + dy) for x, y in F for dx, dy in [(1, 0), (-1, 0), (0, 1), (0, -1)]} | F; R |= F
D = {(x, y) for x in range(-n, n + 1) for y in range(-n, n + 1) if abs(x) + abs(y) <= n}
print("   reached = diamond:", R == D, " cells:", len(R), "=", 2 * n * n + 2 * n + 1)

print("\nSUMMARY of worst errors:", {k: float('%.1e' % v) for k, v in worst.items()})
