# SCRIPT: SHAPE-DEVICES-01  each shape as its own measuring device (triangle, square, pentagon, hexagon, the five Platonic solids)
# Jeromie Beasley, 22 Nov 2026, AI-assisted.
# THE DEVICE. A shape is a set of flat faces a_k . x <= 1.  A point inside carries one positive BOOK per face: its gap to that
# face, l_k(x) = 1 - a_k . x.  Reading between two points (the shape's own distance, Hilbert's rule, the same rule that makes
# the ball's Klein / physical map):  d(x,y) = 1/2 log max over face pairs (i,j) of [ l_i(x) l_j(y) ] / [ l_i(y) l_j(x) ].
# On a two-face shape (an interval) this is the peel step: d = artanh(y) - artanh(x).
import numpy as np
rng = np.random.default_rng(5)
phi = (1 + 5 ** .5) / 2
def norm_rows(A): return A / np.linalg.norm(A, axis=1, keepdims=True)
def cyc(v): return [v, v[[1, 2, 0]], v[[2, 0, 1]]]
def signs(v):
    out = []
    for s in np.array(np.meshgrid(*[[1, -1]] * len(v))).T.reshape(-1, len(v)):
        w = v * s
        if not any(np.allclose(w, o) for o in out): out.append(w)
    return out
def poly2(n): return np.array([[np.cos(2 * np.pi * k / n), np.sin(2 * np.pi * k / n)] for k in range(n)])
cube = np.vstack([np.eye(3), -np.eye(3)])
octa = norm_rows(np.array(signs(np.ones(3))))
tetra = norm_rows(np.array([[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]], float))
dode = norm_rows(np.array([w for v in signs(np.array([0, 1, phi])) for w in cyc(v)]))          # 12 face normals
ico = norm_rows(np.array(signs(np.ones(3)) + [w for v in signs(np.array([0, 1 / phi, phi])) for w in cyc(v)]))  # 20
# scale faces so each solid's inner radius is 1 (a_k . x <= 1 with |a_k| = 1)
SH = {'triangle': poly2(3), 'square': poly2(4), 'pentagon': poly2(5), 'hexagon': poly2(6),
      'tetrahedron': tetra, 'cube': cube, 'octahedron': octa, 'dodecahedron': dode, 'icosahedron': ico}
def books(A, x): return 1 - A @ x
def d_faces(A, x, y):
    lx, ly = books(A, x), books(A, y); r = np.log(ly) - np.log(lx)
    return .5 * (r.max() - r.min()) if False else .5 * (np.max(-r[:, None] + r[None, :]))
def d_cross(inside_t, x, y):
    # direct cross-ratio: hit the boundary along the line through x and y (inside_t(p, u) = largest t with p + t u inside)
    u = (y - x) / np.linalg.norm(y - x); tp = inside_t(x, u); tm = -inside_t(x, -u); s = np.linalg.norm(y - x)
    return .5 * np.log((tp * (s - tm)) / ((tp - s) * (-tm)))
def t_poly(A):
    def f(p, u):
        au = A @ u; gap = 1 - A @ p; return np.min(gap[au > 1e-15] / au[au > 1e-15])
    return f
def t_ball(p, u):
    b = p @ u; c = p @ p - 1; return -b + np.sqrt(b * b - c)
def rand_in(A, dim):
    while True:
        x = rng.uniform(-1, 1, dim) * (2 if A is not None else 1)
        if (A is None and x @ x < .9) or (A is not None and np.all(books(A, x) > .05)): return x

print("H0  The face-book reading equals the shape's own cross-ratio distance (Hilbert)")
# Why this proves it: the cross-ratio along the line to the two boundary hits IS the definition of the shape's distance;
# if the face-book formula matches it on random pairs in every shape, the device reads the shape's own geometry.
# Kill: mismatch above 1e-9 in any shape.
for name, A in SH.items():
    w = 0
    for _ in range(400):
        x, y = rand_in(A, A.shape[1]), rand_in(A, A.shape[1]); w = max(w, abs(d_faces(A, x, y) - d_cross(t_poly(A), x, y)))
    print("   %-12s faces %2d  worst %.1e" % (name, len(A), w))

print("H1  On an interval the reading is the peel step: the ball's physical (Klein) map")
A1 = np.array([[1.], [-1.]]); w = 0
for _ in range(1000):
    x, y = rng.uniform(-.99, .99, 2); w = max(w, abs(d_faces(A1, np.array([x]), np.array([y])) - abs(np.arctanh(y) - np.arctanh(x))))
print("   worst %.1e  (coordinate = tanh of distance, the Klein / admittance reading)" % w)

def from_books_simplex(A, l):
    # solve 1 - A x = c l for x and c (dim+1 unknowns, dim+1 equations)
    n = A.shape[1]; M = np.hstack([A, l[:, None]]); sol = np.linalg.solve(M, np.ones(n + 1)); return sol[:n]
print("H2  Which shapes are flat and which bend: the midline test, done along each shape's OWN straight moves")
# Why this decides it: join the midpoints of two sides of a triangle of points; in a flat geometry the midline is exactly
# half the third side, in the ball's geometry it is always shorter.  The midpoints must be taken along the device's own
# straight moves, or a flat geometry with many shortest paths (first run: the triangle) falsely looks bent.
#   simplex shapes: the straight move is the geometric mean of the books;  ball/disk: the straight chord (unique there).
# Kill for 'simplex flat': any ratio off 1 by more than 1e-9.  Kill for 'ball bends one way': any ratio above 1.
def midline(dist, sampler, midf):
    rs = []
    for _ in range(600):
        x, y, z = sampler(), sampler(), sampler(); dyz = dist(y, z)
        if dyz > 1e-3: rs.append(dist(midf(x, y), midf(x, z)) / (dyz / 2))
    return np.min(rs), np.max(rs)
for name in ['triangle', 'tetrahedron']:
    A = SH[name]
    lo, hi = midline(lambda a, b: d_faces(A, a, b), lambda: rand_in(A, A.shape[1]),
                     lambda a, b: from_books_simplex(A, np.sqrt(books(A, a) * books(A, b))))
    print("   %-12s midline/half from %.12f to %.12f" % (name, lo, hi))
def mid_chord(x, y):
    lo, hi = 0., 1.
    for _ in range(80):
        m = (lo + hi) / 2; p = x + m * (y - x)
        if d_cross(t_ball, x, p) < d_cross(t_ball, p, y): lo = m
        else: hi = m
    return x + lo * (y - x)
for dim, nm in [(2, 'disk'), (3, 'ball')]:
    lo, hi = midline(lambda a, b: d_cross(t_ball, a, b), lambda: rand_in(None, dim), mid_chord)
    print("   %-12s midline/half from %.4f to %.4f" % (nm, lo, hi))

print("H3  The simplex shapes read moves straight and in any order")
# Triangle and tetrahedron: books are free (any positive books, rescaled, are a point).  Claim: scaling the books by
# e^{t_k} moves the reading by the same amount from ANY starting point (translation), so moves add in any order.
# Kill: distance before/after a common book move differs by more than 1e-12.
for name in ['triangle', 'tetrahedron']:
    A = SH[name]; w = 0
    for _ in range(500):
        x, y = rand_in(A, A.shape[1]), rand_in(A, A.shape[1]); t = rng.normal(size=len(A))
        x2 = from_books_simplex(A, books(A, x) * np.exp(t)); y2 = from_books_simplex(A, books(A, y) * np.exp(t))
        w = max(w, abs(d_faces(A, x, y) - d_faces(A, x2, y2)))
    print("   %-12s worst change under a common book move %.1e" % (name, w))

print("H4  Fork: the diamond's per-edge reading vs the square's own reading")
# Diamond (POINCARE-DIAMOND-01) reads each pair of opposite faces as its own peel line and adds them; the square's own
# rule takes the max over ALL face pairs, including cross pairs.  Compare on random pairs.
A = SH['square']; rot = np.array([[1, 1], [-1, 1]]) / np.sqrt(2)
diffs = []
for _ in range(2000):
    x, y = rand_in(A, 2), rand_in(A, 2); X, Y = rot @ x * np.sqrt(2) / 2 * 0 + x, y
    # axes of the square poly2(4) are the coordinate axes after rotating by 45 deg; faces at a . x = 1 with a = (cos, sin) of 0,90,180,270
    per_edge = sum(abs(np.arctanh(y[i]) - np.arctanh(x[i])) for i in range(2)) / 1
    own = d_faces(A, x, y); diffs.append(own / max(per_edge, 1e-12))
diffs = np.array(diffs)
print("   square own reading / diamond per-edge sum: from %.3f to %.3f (own = max over axes when the cross pairs stay quiet)" % (diffs.min(), diffs.max()))

print("H5  Fork, part two: are the square and cube flat under their own natural moves?")
# The square and cube are products of intervals, so each axis has its own free peel move (scale the book pair of that
# axis, 1 + x_i and 1 - x_i, by e^{+t} and e^{-t}).  The diamond's per-edge reading is unchanged by such moves by
# construction.  Claim to test: the shape's own reading (all face pairs) is unchanged too.  Kill: a change above 1e-9.
def peel_move(x, t): return np.tanh(np.arctanh(x) + t)
for name, A in [('square', np.vstack([np.eye(2), -np.eye(2)])), ('cube', cube)]:
    n = A.shape[1]; w = 0; w2 = 0
    for _ in range(2000):
        x, y = rng.uniform(-.9, .9, n), rng.uniform(-.9, .9, n); t = rng.normal(size=n)
        w = max(w, abs(d_faces(A, x, y) - d_faces(A, peel_move(x, t), peel_move(y, t))))
        t1 = rng.normal() * np.ones(n)
        w2 = max(w2, abs(d_faces(A, x, y) - d_faces(A, peel_move(x, t1), peel_move(y, t1))))
    print("   %-7s own reading, worst change: different move per axis %.4f ; same move on every axis %.4f" % (name, w, w2))
