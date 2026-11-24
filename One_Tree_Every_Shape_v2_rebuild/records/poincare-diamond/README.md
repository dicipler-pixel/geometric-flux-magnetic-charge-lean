# Poincaré Diamond — measuring device (Jeromie Beasley, 22 Nov 2026, AI-assisted)

Two positive books (u, v) — forward and backward — are drawn at (A, B) = (Γ(u), Γ(v)), Γ(z) = (z−1)/(z+1).
The square (−1,1)² turned 45° is the diamond; its edges are the two directions.

Script POINCARE-DIAMOND-01 (`diamond_tests.py`, output `diamond_tests.out`). Every test has a kill condition.

| Test | Claim | Result |
|---|---|---|
| T1 | A cable segment is one peel step per edge, any order | pass, 1e-12 |
| T2 | One point carries both wound-ball maps: edge = tanh(ρ/2) (page), B⊖A = tanh ρ (physical) | pass, 2e-16 |
| T3 | Diagonals: B⊖A = Γ(v/u) direction, A⊕B = Γ(uv) size | pass, 3e-15 |
| T4 | Wound field share from the diamond, cosh ρ = (1−AB)/(1+AB) on the cross diagonal | pass, 6e-16 — only when coordinates are stored as gap to the rim (first run lost 4 digits) |
| T5 | Loss + phase together still ride straight (complex peel steps); a junction between different lines does not | pass both ways: lossy/phased line 1e-14; junction mixes books by exactly Γ, order changes the result |
| T6 | Step-by-step grid reach is a diamond | pass, 313 cells |

Correction to the earlier note: the diamond does NOT stop at phase. It stops at junctions (impedance changes), where the books mix by Γ.
Prior art: light-cone coordinates diagonalise boosts and make rapidity additive (textbook). The page is `Poincare_Diamond_v1.html`. Untested against a measurement.
