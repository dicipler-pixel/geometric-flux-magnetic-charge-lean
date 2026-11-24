# SCRIPT: LEADER-369-03  the wall inside a galaxy: Lindblad resonances, the peel step = kappa / (2 Omega)
# Jeromie Beasley, 22 Nov 2026, AI-assisted.  Guess from the hypothesis agent, checked here.
# A disc with Omega ~ R^-p has kappa/(2 Omega) = a = sqrt(1 - p/2).  Inner resonance Omega - kappa/2 = Omega_p, outer
# Omega + kappa/2 = Omega_p, so Omega_inner / Omega_outer = (1 + a)/(1 - a) and its peel step is exactly a.
import numpy as np
G = lambda z: (z - 1) / (z + 1)
print("W1  Kill if the flat-curve ratio is not 3 + 2 sqrt2 to 1e-9, or Kepler's is not 3")
for name, p in [('Kepler (one central mass: the Sun)', 1.5), ('flat curve (a galaxy disc)', 1.0), ('solid body', 0.0)]:
    a = np.sqrt(1 - p / 2); r = (1 + a) / (1 - a) if a < 1 else np.inf
    print("   %-36s kappa/2Omega = %.6f  frequency ratio = %s  peel = %.6f" % (name, a, r, a))
R = np.linspace(.5, 50, 400000); Om = 1 / R; k = np.sqrt(R * np.gradient(Om ** 2, R) + 4 * Om ** 2)
ilr = R[np.argmin(abs(Om - k / 2 - .1))]; olr = R[np.argmin(abs(Om + k / 2 - .1))]
print("   numeric flat disc, radii OLR/ILR = %.4f (3 + 2 sqrt2 = %.4f)" % (olr / ilr, 3 + 2 * 2 ** .5))
print("W2  Real galaxies (PHANGS, arXiv 2410.13353 case studies): kill if the median OLR/ILR is outside 4.3 to 7.3")
gal = {'NGC 1097': (9.6, 1.0, 1.6), 'NGC 3627': (6.8, 0.6, 0.6), 'NGC 4321': (7.2, 0.9, 0.9), 'NGC 4579': (7.4, 0.4, 0.4)}
rat = []
for g, (o, i1, i2) in gal.items():
    print("   %-9s OLR %.1f kpc / ILR %.1f-%.1f kpc = %.1f to %.1f" % (g, o, i1, i2, o / i2, o / i1)); rat.append((o / i2, o / i1))
lo = np.median([x[0] for x in rat]); hi = np.median([x[1] for x in rat])
print("   median %.1f to %.1f -> %s (real centres rise like a solid body, which pushes the inner resonance in)" % (lo, hi, 'KILLED' if lo > 7.3 else 'survives'))
print("W3  The Milky Way at the Sun from Oort constants A = 15.3, B = -11.9 km/s/kpc (Bovy 2017): kill if a is off the wall by > 5%")
A, B = 15.3, -11.9; a = np.sqrt(-B / (A - B))
print("   kappa/2Omega = %.3f (wall 0.707, Kepler 0.500): off by %.1f%% -> %s ; frequency ratio %.2f" % (a, 100 * (1 - a / 2 ** -.5), 'KILLED (narrowly)' if abs(1 - a / 2 ** -.5) > .05 else 'survives', (1 + a) / (1 - a)))
