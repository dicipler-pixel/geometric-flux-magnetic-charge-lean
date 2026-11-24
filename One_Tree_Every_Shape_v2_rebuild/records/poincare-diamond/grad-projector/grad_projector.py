# SCRIPT: GRAD-PROJECTOR-01  is the gradient of a projector itself a smaller projector?  (checking Jeromie's logic)
# Jeromie Beasley, 23 Nov 2026, AI-assisted.
# Claims, each with its kill condition before the run (P(t) a smooth family of rank-r projectors in N dimensions, dP its derivative):
#  C1 dP lives only between P and its complement: P dP P = 0 and (1-P) dP (1-P) = 0.        kill: either above 1e-10
#  C2 dP is NOT itself a projector (dP^2 != dP), but its range is a projector Q that splits as Q = Q_in + Q_out with
#     Q_in inside P, Q_out outside P, so Q commutes with P.                                      kill: [Q, P] above 1e-8
#  C3 Q is smaller: rank Q_in <= min(r, N-r), rank Q_out the same.                                  kill: any rank above
#  C4 'both ways': repeat with Q_in as the new projector; ranks never grow down the ladder.        kill: a rank grows
#  C5 the size of the gradient is the quantum metric: |dP|^2 = 2 Tr(P dP dP) (the connection energy of the family). kill: above 1e-10
import numpy as np
from scipy.linalg import expm, orth
rng = np.random.default_rng(1)
def family(N, r, K):
    # P(t) = U(t) P0 U(t)^dagger with U = exp(t A), A anti-Hermitian
    A = rng.normal(size=(N, N)) + 1j * rng.normal(size=(N, N)); A = A - A.conj().T
    P0 = np.diag([1.] * r + [0.] * (N - r)).astype(complex)
    def P(t): U = expm(t * A); return U @ P0 @ U.conj().T
    return P, A
w = dict(C1=0, C2=0, C5=0); bad3 = 0; bad4 = 0
for trial in range(300):
    N = rng.integers(3, 12); r = rng.integers(1, N); P, A = family(N, r, 1); t = rng.normal()
    Pt = P(t); h = 1e-5; dP = A @ Pt - Pt @ A   # exact derivative of U P0 U^dagger (first run used finite differences: 3e-8 error)
    I = np.eye(N)
    w['C1'] = max(w['C1'], np.linalg.norm(Pt @ dP @ Pt), np.linalg.norm((I - Pt) @ dP @ (I - Pt)))
    B = orth(dP, rcond=1e-6); Q = B @ B.conj().T
    w['C2'] = max(w['C2'], np.linalg.norm(Q @ Pt - Pt @ Q))
    Qin = Pt @ Q @ Pt; rin = int(round(np.real(np.trace(Qin)))); rout = int(round(np.real(np.trace((I - Pt) @ Q @ (I - Pt)))))
    if rin > min(r, N - r) or rout > min(r, N - r): bad3 += 1
    w['C5'] = max(w['C5'], abs(np.linalg.norm(dP) ** 2 - 2 * np.real(np.trace(Pt @ dP @ dP))))
    # C4: next rung uses Q_in moved by the same flow
    def Pn(s, Qin=Qin): U = expm((s - t) * A); return U @ Qin @ U.conj().T
    d2 = A @ Qin - Qin @ A; B2 = orth(d2, rcond=1e-6)
    rin2 = int(round(np.real(np.trace(Qin @ (B2 @ B2.conj().T) @ Qin)))) if B2.size else 0
    if rin2 > rin: bad4 += 1
print("C1 gradient only between P and its complement: worst %.1e" % w['C1'])
print("C2 range of the gradient is a projector that commutes with P: worst %.1e" % w['C2'])
print("C3 inside and outside pieces each no bigger than min(r, N-r): violations %d of 300" % bad3)
print("C4 down the ladder the inside rank never grows: violations %d of 300" % bad4)
print("C5 |dP|^2 = 2 Tr(P dP dP): worst %.1e" % w['C5'])
print("dP itself idempotent? example |dP^2 - dP| = %.3f (it is not a projector; its range is)" % np.linalg.norm(dP @ dP - dP))
