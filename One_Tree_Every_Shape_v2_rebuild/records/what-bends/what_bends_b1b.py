# SCRIPT: WHAT-BENDS-01b  B1 again with the step sizes left in their real order and only the arms (end digits) shuffled.
# Kill for -the order of the end digits bends-: real chain inside the middle 95 percent of the arm-shuffled chains.
import numpy as np, math
rng = np.random.default_rng(1124)
N = 3_000_000
s = np.ones(N + 8, bool); s[:2] = False
for i in range(2, int((N + 8) ** .5) + 1):
    if s[i]: s[i * i::i] = False
tw = np.nonzero(s[:N] & s[2:N + 2])[0]; tw = tw[tw >= 11]
def walk(ax, r):
    v = np.array([1., 0, 0, 0])
    for a, x in zip(ax[::-1], r[::-1]):
        c, sh = math.cosh(x), math.sinh(x); t = v[0]; v[0] = c * t + sh * v[a + 1]; v[a + 1] = sh * t + c * v[a + 1]
    return math.acosh(v[0])
arm = {1: 0, 7: 1, 9: 2}
for n in (600, 2400, 9600):
    T = tw[:n + 1]; ax = np.array([arm[int(a % 10)] for a in T[1:]]); r = np.log(T[1:] / T[:-1]); real = walk(ax, r)
    sh = np.array([walk(rng.permutation(ax), r) for _ in range(400)]); lo, hi = np.percentile(sh, [2.5, 97.5])
    # skip the first 20 big steps: tail only
    k = 20; real_t = walk(ax[k:], r[k:]); sht = np.array([walk(rng.permutation(ax[k:]), r[k:]) for _ in range(400)]); lo2, hi2 = np.percentile(sht, [2.5, 97.5])
    print('%5d pairs: real %.4f ; arms shuffled %.4f to %.4f -> %s   | after the first 20 steps: real %.4f ; shuffled %.4f to %.4f -> %s'
          % (n, real, lo, hi, 'inside' if lo <= real <= hi else 'OUTSIDE', real_t, lo2, hi2, 'inside' if lo2 <= real_t <= hi2 else 'OUTSIDE'))
