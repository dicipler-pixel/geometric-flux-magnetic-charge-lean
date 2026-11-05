# A conditional stance on magnetic monopoles

Formalization prepared for Jeromie Beasley’s research programme, 4 November 2026 (America/Chicago).

**Stance:** the displayed IQGT sphere curvature has nonzero normalized flux. That mathematical fact alone does not determine a physical electromagnetic magnetic charge. A specified nonzero-unit electromagnetic identification transfers the charge. Without that identification, both numerical magnetic assignments are consistent with the same geometric record.

This is a formalization of a precise subset of the stance, not a proof that physical monopoles exist, do not exist, or are undecidable in a physical theory. The full-corpus manuscript reading remains incomplete.

## What Lean proves

| Module | Checked result |
|---|---|
| `Geometry.lean` | The explicit lower Pauli matrix `(I − d·σ)/2` is Hermitian; it is idempotent when `x²+y²+z²=1`; its trace is one. |
| `Geometry.lean` | For the supplied curvature coefficient `omega θ = sin θ / 2`, the polar integral is 1, the oriented iterated sphere-coordinate integral is `2π`, and its normalization by `2π` is 1. The surface-coordinate density already includes the Jacobian. |
| `Geometry.lean` | Opposite curvature coefficients have cancelling flux. That cancellation does not make either individual coefficient’s flux vanish. |
| `Geometry.lean` | The two local gauge-coefficient functions `(1−cos θ)/2` and `−(1+cos θ)/2` both have derivative `omega θ` and differ by 1. |
| `Geometry.lean` | The supplied radial-field surface density `g sin θ` has flux `4πg`, nonzero exactly when `g` is nonzero. |
| `Extension.lean` | There is no continuous extension through the axis origin agreeing with the distinct positive- and negative-axis lower Pauli projectors. The proof uses actual convergent real sequences and uniqueness of limits. |
| `Bridge.lean` | Within the stated record language, the same integer geometric charge permits zero and nonzero magnetic-flux assignments. Neither universal existence inference nor universal absence inference follows in this language. |
| `Bridge.lean` | Given `magneticFlux = q * geometricCharge` and `q ≠ 0`, magnetic nonzero flux is equivalent to nonzero geometric charge. |
| `Bridge.lean` | A zero-flux admissibility condition restricts a model class; it is not a universal zero-flux theorem over all records. |
| `Bridge.lean` | `formal_stance` combines the normalized unit-flux result, the two explicit record countermodels, and the conditional transfer theorem. |

There are 24 theorem declarations across the three modules. All are proved rather than postulated. The negative-control files are deliberately false and are intentionally excluded from the default library build.

## Read the bridge literally

```lean
def ElectromagneticBridge (q : ℝ) (r : ChargeRecord) : Prop :=
  r.magneticFlux = q * (r.geometricCharge : ℝ)

theorem bridge_transfers_charge (q : ℝ) (hq : q ≠ 0) (r : ChargeRecord)
    (hbridge : ElectromagneticBridge q r) :
    MagneticallyCharged r ↔ GeometricallyCharged r
```

The bridge equality is an explicit **hypothesis**. The code does not discover or validate it. Here `q` is a nonzero flux unit, not an electric charge with an unannounced units convention. `MagneticallyCharged` means only that the selected numerical flux is nonzero; interpreting that flux as magnetic charge also presumes a closed physical spatial surface and a valid electromagnetic field model.

`ChargeRecord.geometricCharge : ℤ` assumes an integer-valued input record. Its integrality is not derived from a Chern–Weil theorem. The countermodels are mathematical record assignments, not constructed physical universes or Maxwell solutions.

## Exact boundaries of the geometry formalization

The projector algebra and the curvature-integral calculation are separately checked. **Their Berry-curvature derivation is not formalized here.** In particular, the package does not yet prove

`BerryCurvature(lowerProjector) = (sin θ / 2) dθ ∧ dφ`.

It also does not construct an eigenline bundle, a first Chern class, its integrality, a global patched U(1) connection or its transition-function winding. The local gauge-coefficient identities are scalar calculus statements, not those missing bundle constructions. The axis obstruction is a parameter-space continuity result, not an electromagnetic source theorem.

No spacetime pullback, Maxwell source equation, Stokes theorem, physical field identification, finite-energy soliton, experimental existence result, or new whole-programme unification theorem is claimed. The radial flux calculation integrates a supplied density; it does not solve Maxwell’s equations. Hopf charge, instanton second Chern number, spectral flow and angular moment `ℓ=0` are not identified with electromagnetic magnetic charge.

## Reproduce

Pinned toolchain: Lean **4.19.0**. Pinned Mathlib commit:

`c44e0c8ee63ca166450922a373c7409c5d26b00b` (release `v4.19.0`).

With Lean/Elan, Git and Python 3 installed, run from this directory:

```sh
lake exe cache get
python3 scripts/verify.py
```

The script builds the project, regenerates `AxiomAudit.lean`, checks the dependency axioms of every theorem, and requires all six false controls to be rejected. `lake-manifest.json` locks the transitive dependency revisions. Network access is needed for the pinned dependencies and their cache on first setup.

The shipped `verification/` contains the actual build, axiom and rejected-control logs and `verification.json`. A completed run is reported only when the script exits successfully. The allowed foundational dependencies are `propext`, `Classical.choice`, and `Quot.sound`. No new axiom declarations, `sorry`, `admit`, or `native_decide` are used in the proof modules. Standard Lean compilation checks the proof terms; a separate independent kernel-replay tool has not been run.

## Six deliberately false controls

1. Set the unit normalized flux to zero.
2. Infer magnetic charge from geometric charge without the bridge.
3. Infer absence of magnetic charge from geometric charge without the bridge.
4. Drop the nonzero flux-unit condition from charge transfer.
5. Treat the origin value `(I−0·σ)/2 = I/2` as idempotent.
6. Set the north-minus-south gauge-coefficient difference to zero.

The verifier also rejects infrastructure/import errors as a substitute for mathematical rejection. These controls test the implementation boundary; they do not validate a physical interpretation.

## Sources and provenance

- The curvature coefficient and lower Pauli projector are the explicit example discussed from IQGT Appendix B in this conversation. The sign follows the supplied positive-curvature convention and the stated coordinate orientation.
- The record-language independence and explicit electromagnetic-bridge predicate formalize the distinctions in the preceding answer.
- Mathlib supplies the real/complex/matrix infrastructure, interval integration of sine, differentiation, sequence limits, and proof tactics. This package claims no priority for the standard Pauli/Berry-monopole example.

No changes were published or pushed to any repository.
