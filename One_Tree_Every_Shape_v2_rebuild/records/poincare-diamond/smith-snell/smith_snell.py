# SCRIPT: SMITH-SNELL-01  the Smith disk as the diamond's equal, and how Snell's law plays out on both
# Jeromie Beasley, 22 Nov 2026, AI-assisted.  Peel step G(z) = (z-1)/(z+1); peel addition a (+) b = (a+b)/(1+ab).
# Waves on a line of impedance Z: V = sqrt(Z)(a+b), I = (a-b)/sqrt(Z); forward amount a, backward amount b; Smith point r = b/a.
# Every test states its kill condition before it runs.
import numpy as np
rng = np.random.default_rng(7)
G = lambda z: (z - 1) / (z + 1)
op = lambda a, b: (a + b) / (1 + a * b)
W = {}
def rec(k, v): W[k] = max(W.get(k, 0), float(v))

def waves_to_VI(a, b, Z): return np.sqrt(Z) * (a + b), (a - b) / np.sqrt(Z)
def VI_to_waves(V, I, Z): return (V / np.sqrt(Z) + I * np.sqrt(Z)) / 2, (V / np.sqrt(Z) - I * np.sqrt(Z)) / 2

print("S1  On the Smith disk a junction IS a peel addition")
# Claim: crossing from line Z1 into line Z2 (V and I continuous) takes the Smith point r2 (seen in line 2) to
# r1 = r2 (+) G(Z2/Z1), the same peel addition the diamond used for cable segments.  Kill: mismatch above 1e-12.
for _ in range(3000):
    Z1, Z2 = np.exp(rng.normal(size=2)); r2 = 0.95 * rng.uniform() * np.exp(2j * np.pi * rng.uniform())
    V, I = waves_to_VI(1.0, r2, Z2); a1, b1 = VI_to_waves(V, I, Z1)
    rec('S1', abs(b1 / a1 - op(r2, G(Z2 / Z1))))
print("   worst %.1e" % W['S1'])

print("S2  On the Smith disk a stretch of uniform line is a turn (and a shrink if lossy)")
# Claim: going back a distance d along a line with propagation gamma = alpha + i beta takes r to r exp(-2 gamma d):
# lossless keeps |r| (a pure turn), loss shrinks |r| by exp(-2 alpha d).  Kill: mismatch above 1e-12.
for _ in range(3000):
    Z = np.exp(rng.normal()); g = rng.uniform(0, .5) + 1j * rng.uniform(0, 6); d = rng.uniform(0, 2)
    r = 0.9 * rng.uniform() * np.exp(2j * np.pi * rng.uniform())
    a_back, b_back = 1.0 * np.exp(g * d), r * np.exp(-g * d)      # forward wave grows going back, backward shrinks
    rec('S2', abs(b_back / a_back - r * np.exp(-2 * g * d)))
print("   worst %.1e" % W['S2'])

print("S3  The two charts are duals: each straightens what the other bends")
# Claim A: junctions with no line between them compose by peel addition in ANY order on the Smith disk
#   (ratios multiply, peel steps add).  Claim B: lines with no junction between compose by peel addition in ANY
#   order in the diamond (tested in POINCARE-DIAMOND-01 T1, T5).  Claim C: a junction and a line do NOT commute on
#   either chart.  Kill: A off by more than 1e-12, or C showing order-independence.
for _ in range(3000):
    zs = np.exp(rng.normal(size=rng.integers(2, 8))); r = 0.9 * rng.uniform() * np.exp(2j * np.pi * rng.uniform())
    x = r
    for z in zs: x = op(x, G(z))
    y = r
    for z in rng.permutation(zs): y = op(y, G(z))
    rec('S3 junction order', abs(x - y)); rec('S3 junction product', abs(x - op(r, G(np.prod(zs)))))
r = 0.3 + 0.2j; g = 1j * 0.7; z = 3 + 2 * np.sqrt(2)
print("   junctions: worst order %.1e, product %.1e" % (W['S3 junction order'], W['S3 junction product']))
print("   junction(wall) then line vs line then junction(wall): %.4f vs %.4f  (differ, as they must)" %
      (abs(op(r, G(z)) * np.exp(-2 * g)), abs(op(r * np.exp(-2 * g), G(z)))))

print("S4  Snell + Fresnel are one peel step of the TRANSVERSE impedance ratio")
# Snell keeps n sin(theta) across the face.  Each side has a transverse impedance: TE  Z = Z0/(n cos th),
# TM  Z = Z0 cos th / n.  Claim: the textbook Fresnel reflections are exactly the peel step of their ratio:
#   r_TE = (n1 c1 - n2 c2)/(n1 c1 + n2 c2) = G(Z2/Z1),  r_TM(field convention of Orfanidis) = (n1 c2 - n2 c1)/(n1 c2 + n2 c1) = G(Z2/Z1),
# and the books close: reflected + transmitted power = 1 with T = Re(Y2)/Y1 |t|^2.  Kill: mismatch above 1e-12.
for _ in range(3000):
    n1, n2 = rng.uniform(1, 3, 2); th = rng.uniform(0, np.pi / 2 - 1e-3)
    s2 = n1 * np.sin(th) / n2; c1 = np.cos(th); c2 = np.sqrt(1 - s2 ** 2 + 0j)
    if np.imag(c2) < 0: c2 = -c2
    for pol in ('TE', 'TM'):
        Z1 = 1 / (n1 * c1) if pol == 'TE' else c1 / n1; Z2 = 1 / (n2 * c2) if pol == 'TE' else c2 / n2
        fres = (n1 * c1 - n2 * c2) / (n1 * c1 + n2 * c2) if pol == 'TE' else (n1 * c2 - n2 * c1) / (n1 * c2 + n2 * c1)
        rec('S4 fresnel', abs(fres - G(Z2 / Z1)))
        Y1, Y2 = 1 / Z1, 1 / Z2; t = 2 * Y1 / (Y1 + Y2)               # transmitted voltage-wave ratio
        rec('S4 books', abs(abs(G(Z2 / Z1)) ** 2 + np.real(Y2) / Y1 * abs(t) ** 2 - 1))
print("   worst Fresnel %.1e, books R+T-1 %.1e" % (W['S4 fresnel'], W['S4 books']))

def stack(n_list, d_list, n_in, n_out, th, pol, k0=1.0):
    # characteristic-matrix (Born and Wolf) transfer through layers; returns transmitted power fraction
    beta = n_in * np.sin(th)
    def q(n):
        v = np.sqrt(n ** 2 - beta ** 2 + 0j); return v if np.imag(v) >= 0 else -v
    Y = lambda n: q(n) if pol == 'TE' else n ** 2 / q(n)
    M = np.eye(2, dtype=complex)
    for n, d in zip(n_list, d_list):
        dl = k0 * q(n) * d; y = Y(n)
        M = M @ np.array([[np.cos(dl), -1j * np.sin(dl) / y], [-1j * y * np.sin(dl), np.cos(dl)]])
    y0, ys = Y(n_in), Y(n_out)
    t = 2 * y0 / (y0 * M[0, 0] + y0 * ys * M[0, 1] + M[1, 0] + ys * M[1, 1])
    return np.real(ys) / np.real(y0) * abs(t) ** 2

print("S5  Brewster: the junction vanishes, and a whole two-material stack goes straight")
# At tan th = n2/n1 the TM transverse impedances are equal, z = 1, peel step 0: the face is invisible.  Because
# Brewster from 1 into 2 implies Brewster from 2 back into 1, EVERY face of an alternating stack vanishes at once, so
# for TM the stack is pure line: straight in the diamond, transmission 1 for any number and thickness of layers.
# Kill: TM transmission below 1 - 1e-12 at Brewster, or TE reaching 1 there.
n1, n2 = 1.0, 1.5; thB = np.arctan(n2 / n1)
for _ in range(300):
    N = rng.integers(1, 40); ns = [n2, n1] * N; ds = rng.uniform(.1, 5, 2 * N)
    rec('S5 TM', 1 - stack(ns, ds, n1, n1, thB, 'TM')); rec('S5 TE max', stack(ns, ds, n1, n1, thB, 'TE'))
print("   Brewster %.4f deg: worst TM loss %.1e ; best TE transmission %.4f" % (np.degrees(thB), W['S5 TM'], W['S5 TE max']))

print("S6  Total internal reflection: the point rides the Smith rim")
# Past the critical angle cos th2 is imaginary, the transverse impedance is pure reactance, so |r| = 1 exactly; only
# the angle of r moves (the Goos-Hanchen phase).  Kill: | |r| - 1 | above 1e-12 anywhere past critical.
n1, n2 = 1.5, 1.0; thc = np.arcsin(n2 / n1)
for th in np.linspace(thc + 1e-4, np.pi / 2 - 1e-4, 500):
    c1 = np.cos(th); c2 = 1j * np.sqrt((n1 * np.sin(th) / n2) ** 2 - 1)
    for Z1, Z2 in [(1 / (n1 * c1), 1 / (n2 * c2)), (c1 / n1, c2 / n2)]: rec('S6', abs(abs(G(Z2 / Z1)) - 1))
print("   critical %.4f deg: worst rim error %.1e" % (np.degrees(thc), W['S6']))

print("S7  Frustrated TIR through a gap IS the wound-field cable (cosh/sinh)")
# Inside a gap past critical the wave is evanescent: the line step is REAL, kappa d -- the screened (cable) equation
# of the wound ball.  Claim (TE, glass-gap-glass): 1/T = 1 + ((q^2 + kappa^2)/(2 q kappa))^2 sinh^2(kappa d),
# q = n1 cos th, kappa = sqrt(n1^2 sin^2 th - n2^2).  Kill: mismatch with the transfer-matrix stack above 1e-10 relative.
for _ in range(2000):
    th = rng.uniform(thc + .01, np.pi / 2 - .01); d = rng.uniform(0, 6)
    q = n1 * np.cos(th); ka = np.sqrt((n1 * np.sin(th)) ** 2 - n2 ** 2)
    Tc = 1 / (1 + ((q ** 2 + ka ** 2) / (2 * q * ka)) ** 2 * np.sinh(ka * d) ** 2)
    Tm = stack([n2], [d], n1, n1, th, 'TE'); rec('S7', abs(Tm - Tc) / Tc)
print("   worst relative %.1e" % W['S7'])

print("S8  Where Snell meets the wall z = 3 + 2 sqrt2 (|r|^2 = 1/2)")
# Readout, not a test: the incidence angle at which a face reflects exactly half the power.
from scipy.optimize import brentq
for (a, b) in [(1.0, 1.5), (1.5, 1.0), (1.0, 2.4)]:
    def R(th, pol):
        c1 = np.cos(th); s2 = a * np.sin(th) / b; c2 = np.sqrt(1 - s2 ** 2 + 0j)
        Z1 = 1 / (a * c1) if pol == 'TE' else c1 / a; Z2 = 1 / (b * c2) if pol == 'TE' else c2 / b
        return abs(G(Z2 / Z1)) ** 2
    top = np.arcsin(min(1, b / a)) - 1e-9 if a > b else np.pi / 2 - 1e-9
    out = []
    for pol in ('TE', 'TM'):
        f = lambda th: R(th, pol) - .5
        grid = np.linspace(1e-6, top, 4000); v = [f(x) for x in grid]
        hits = [brentq(f, grid[i], grid[i + 1]) for i in range(len(grid) - 1) if v[i] * v[i + 1] < 0]
        out.append(pol + ': ' + (', '.join('%.3f deg' % np.degrees(h) for h in hits) or 'none before critical/grazing'))
    print("   n %.1f -> %.1f   " % (a, b) + ' ; '.join(out))

print("\nSUMMARY worst:", {k: float('%.1e' % v) for k, v in W.items()})
