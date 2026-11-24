# SCRIPT: PRIME-COVARIANCE-01  is the two-point covariance of the primes flat?  Kill: pair counts at every even gap equal within 2 percent (then it is flat)
import numpy as np
N = 50_000_000
s = np.ones(N + 4096, bool); s[:2] = False
for i in range(2, int((N + 4096) ** .5) + 1):
    if s[i]: s[i * i::i] = False
base = np.count_nonzero(s[:N] & s[2:N + 2])
def ss(h):
    r = 1.0; m = h; p = 3
    while m % 2 == 0: m //= 2
    while p * p <= m:
        if m % p == 0:
            r *= (p - 1) / (p - 2)
            while m % p == 0: m //= p
        p += 2
    if m > 1: r *= (m - 1) / (m - 2)
    return r
print('prime pairs (p, p+h) below %d, counted / twin count, against the product over the odd primes dividing h' % N)
worst = 0
for h in (2, 4, 6, 8, 10, 12, 14, 30, 210, 2310):
    c = np.count_nonzero(s[:N] & s[h:N + h]) / base; worst = max(worst, abs(c / ss(h) - 1))
    print('   gap %5d   measured %.4f   predicted %.4f' % (h, c, ss(h)))
print('worst mismatch with the prediction %.2e -> NOT flat' % worst)
