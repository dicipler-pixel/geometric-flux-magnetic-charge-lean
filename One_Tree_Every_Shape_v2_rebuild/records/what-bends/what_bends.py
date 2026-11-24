# SCRIPT: WHAT-BENDS-01  three options for what bends, each with its kill line written before the run
# Jeromie Beasley, 23 Nov 2026, AI-assisted.
import numpy as np, math, time
rng = np.random.default_rng(1123)
N = 50_000_000
s = np.ones(N + 8, bool); s[:2] = False
for i in range(2, int((N + 8) ** .5) + 1):
    if s[i]: s[i * i::i] = False
tw = np.nonzero(s[:N] & s[2:N + 2])[0]; tw = tw[tw >= 11]

print('B1  Is the BALL doing the bending, or the order of the primes?  The twin chain is walked in the ball exactly as on the page')
print('    (step = ratio of one twin start to the next, along the arm of its end digit).  Then the same steps are walked in shuffled order.')
print('    Kill for -the order of the primes bends-: the real chain ends inside the middle 95 percent of the shuffled chains.')
def walk(ax, r):
    v = np.array([1., 0, 0, 0])
    for a, x in zip(ax[::-1], r[::-1]):
        c, sh = math.cosh(x), math.sinh(x); t = v[0]; v[0] = c * t + sh * v[a + 1]; v[a + 1] = sh * t + c * v[a + 1]
    return math.acosh(v[0])
arm = {1: 0, 7: 1, 9: 2}
for n in (600, 2400, 9600):
    T = tw[:n + 1]; ax = np.array([arm[int(a % 10)] for a in T[1:]]); r = np.log(T[1:] / T[:-1]); real = walk(ax, r); sh = []
    for _ in range(400):
        p = rng.permutation(n); sh.append(walk(ax[p], r[p]))
    sh = np.array(sh); lo, hi = np.percentile(sh, [2.5, 97.5])
    flat = np.linalg.norm([r[ax == k].sum() for k in range(3)])          # the flat reader: steps on one arm just add, order cannot matter
    print('   %5d pairs: path length %.3f ; flat reader end %.3f (any order) ; ball end, real order %.3f ; shuffled %.3f to %.3f  -> %s'
          % (n, r.sum(), flat, real, lo, hi, 'inside: the order adds nothing here' if lo <= real <= hi else 'OUTSIDE: the order matters'))

print('\nB2  Is the end-digit record flat?  Consecutive twin starts end in 1, 7 or 9.  If each end digit were drawn on its own, every')
print('    cell below would read 1.000.  Kill for -the end digits carry a covariance-: all nine cells within 1 percent of 1.')
d = tw % 10; idx = {1: 0, 7: 1, 9: 2}; M = np.zeros((3, 3))
a = np.array([idx[int(x)] for x in d[:2_000_00]]) if False else np.vectorize(idx.get)(d)
np.add.at(M, (a[:-1], a[1:]), 1); E = np.outer(M.sum(1), M.sum(0)) / M.sum(); R = M / E
print('   twin pairs counted: %d' % len(tw))
for i, nm in enumerate((1, 7, 9)): print('   from %d  to 1: %.4f   to 7: %.4f   to 9: %.4f' % (nm, *R[i]))
print('   largest departure from 1: %.1f percent ; one-sigma counting noise about %.2f percent -> %s' % (100 * np.abs(R - 1).max(), 100 / math.sqrt(E.min()), 'NOT flat' if np.abs(R - 1).max() > .01 else 'flat'))

print('\nB3  Do the zeros behave like steps that commute (free to sit anywhere) or steps that do not (they push each other apart)?')
print('    Share of neighbouring gaps smaller than 0.3 of the average: 26 percent if free, about 3 percent if they push.')
print('    Kill for -the zeros push-: share of 15 percent or more.')
import mpmath as mp
t0 = time.time(); z = []
for k in range(1, 401):
    z.append(float(mp.im(mp.zetazero(k))))
    if time.time() - t0 > 420: break
z = np.array(z); u = z / (2 * np.pi) * (np.log(z / (2 * np.pi)) - 1) + 7 / 8; g = np.diff(u); g = g / g.mean()
print('   zeros used: %d ; share of small gaps %.1f percent -> %s' % (len(z), 100 * np.mean(g < .3), 'they push' if np.mean(g < .3) < .15 else 'KILLED'))
