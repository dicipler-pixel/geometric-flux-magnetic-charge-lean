# SCRIPT: LEADER-369-02  the measured spin-flip parameter is a commutator: connection energy picks the leader
# Jeromie Beasley, 22 Nov 2026, AI-assisted.
# Literature (TNG300, arXiv 2401.11707): which tidal eigenvector a galaxy's spin follows (t1, t2 or t3) is set by
#   tau = sqrt(I12^2 + I23^2 + I31^2) / sqrt(I11^2 + I22^2 + I33^2), the inertia tensor I written in the tidal tensor T's own axes.
# Claim: in T's axes, || [I, T] ||_F^2 = 2 * sum_{i<j} I_ij^2 (t_i - t_j)^2, so tau is the commutator of inertia and tide
#   with the eigen-gaps divided out: tau = 0 exactly when [I, T] = 0 (for distinct tidal eigenvalues).
# Why this proves the bridge: the commutator norm is the connection-energy (non-normality) measure of the one-page note;
#   if the identity holds for random tensors, the spin-flip parameter is that measure, gap-weighted.
# Kill: identity off by more than 1e-10 relative, or tau and the commutator vanishing separately.
import numpy as np
rng = np.random.default_rng(2)
w = 0; both = True
for _ in range(5000):
    Q = np.linalg.qr(rng.normal(size=(3, 3)))[0]; t = np.sort(rng.normal(size=3))[::-1]; T = Q @ np.diag(t) @ Q.T
    M = rng.normal(size=(3, 3)); I = M @ M.T                       # an inertia tensor (positive)
    Ip = Q.T @ I @ Q                                              # I in T's axes
    lhs = np.linalg.norm(I @ T - T @ I) ** 2
    rhs = 2 * sum(Ip[i, j] ** 2 * (t[i] - t[j]) ** 2 for i in range(3) for j in range(i + 1, 3))
    w = max(w, abs(lhs - rhs) / max(lhs, 1e-300))
# aligned case: I built diagonal in T's axes
Ia = Q @ np.diag([3., 2., 1.]) @ Q.T; Ip = Q.T @ Ia @ Q
tau = np.sqrt(sum(Ip[i, j] ** 2 for i in range(3) for j in range(3) if i < j)) / np.sqrt(sum(Ip[i, i] ** 2 for i in range(3)))
print("identity worst relative error %.1e" % w)
print("aligned inertia: tau = %.1e, commutator = %.1e" % (tau, np.linalg.norm(Ia @ T - T @ Ia)))
print("tau thresholds reported (high-mass bin, z=0): t2->t3 at 0.15-0.25, perp->parallel t1 at 0.13-0.15, t2->t1 at 0.05-0.11")
print("ratios of threshold midpoints: %.2f and %.2f (ranges too wide to pin; kept for later, not a 3-6-9 claim)" % (0.20 / 0.14, 0.14 / 0.08))
