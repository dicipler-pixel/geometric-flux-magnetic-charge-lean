# Smith disk as the diamond's equal, and Snell (Jeromie Beasley, 22 Nov 2026, AI-assisted)

Script SMITH-SNELL-01 (`smith_snell.py`, output `smith_snell.out`); page `Smith_Snell_v1.html`.

| Test | Claim | Result |
|---|---|---|
| S1 | On the Smith disk a junction is a peel addition, r -> r (+) G(Z2/Z1) | pass, 7e-16 |
| S2 | A stretch of line turns the Smith point (shrinks it if lossy) | pass, 4e-16 |
| S3 | Duality: junctions compose by peel addition in any order on the Smith disk; lines do on the diamond; junction and line never commute | pass, 8e-15 |
| S4 | Snell + Fresnel = one peel step of the transverse impedance ratio; reflected + transmitted = 1 | pass, 7e-16 |
| S5 | Brewster: TM face vanishes; an alternating two-material stack is fully transparent for TM at any count/thickness | pass, 2e-15 (TE best 0.973) |
| S6 | Past critical the point rides the rim, abs(r) = 1 | pass, 2e-16 |
| S7 | Frustrated total reflection through a gap follows the cosh/sinh cable law | pass, 2e-12 |
| S8 | Angles where a face reflects half the power (the wall, z = 3 + 2 sqrt2) | readout, see .out |

Prior art: the Smith chart as a hyperbolic (Poincaré) disk with Möbius maps is known; transverse-impedance Fresnel and the frustrated-total-reflection formula are textbook. Untested against a measurement.
