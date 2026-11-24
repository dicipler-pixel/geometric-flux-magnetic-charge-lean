# SCRIPT: OTES-V2-DATA-01  measured numbers embedded in One Tree, Every Shape v2 (same counts as WHAT-BENDS-01, PRIME-COVARIANCE-01)
import numpy as np, json, mpmath as mp
N = 50_000_000
s = np.ones(N + 4096, bool); s[:2] = False
for i in range(2, int((N + 4096) ** .5) + 1):
    if s[i]: s[i * i::i] = False
base = np.count_nonzero(s[:N] & s[2:N + 2])
gaps = list(range(2, 62, 2)) + [210, 2310]
cov = [[h, round(np.count_nonzero(s[:N] & s[h:N + h]) / base, 4)] for h in gaps]
tw = np.nonzero(s[:N] & s[2:N + 2])[0]; tw = tw[tw >= 11]
idx = {1: 0, 7: 1, 9: 2}; a = np.vectorize(idx.get)(tw % 10); M = np.zeros((3, 3)); np.add.at(M, (a[:-1], a[1:]), 1)
R = M / (np.outer(M.sum(1), M.sum(0)) / M.sum())
z = np.array([float(mp.im(mp.zetazero(k))) for k in range(1, 401)]); u = z / (2 * np.pi) * (np.log(z / (2 * np.pi)) - 1) + 7 / 8
g = np.diff(u); g = g / g.mean()
json.dump({'N': N, 'twins': int(len(tw)), 'cov': cov, 'dig': np.round(R, 4).tolist(), 'zer': np.round(np.cumsum(np.r_[0, g]), 4).tolist(),
           'zshare': round(float(np.mean(g < .3)), 4)}, open('data.json', 'w'))
print(len(tw), cov[:6], R.round(4).tolist(), float(np.mean(g < .3)))
