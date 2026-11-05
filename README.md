<div align="center">

# From Geometric Flux to Magnetic Charge — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/geometric-flux-magnetic-charge-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/geometric-flux-magnetic-charge-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-47-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)

Jeromie Beasley

</div>

---

## What this is

The paper *From Geometric Flux to Magnetic Charge: A Checked Pauli Curvature and an Explicit
Physical Bridge* (version 4, 5 November 2026, research draft) and its two Lean developments.

* **Read the paper:** [`paper/Geometric_Flux_and_Magnetic_Charge_v4.pdf`](paper/Geometric_Flux_and_Magnetic_Charge_v4.pdf)
  (11 pages), or the [HTML version](paper/Geometric_Flux_and_Magnetic_Charge_v4.html). Source and
  build scripts are in [`paper/`](paper/).
* **One Lean library, one chain from the matrix to the integer.** Everything the paper marks as
  Lean-checked now lives in the single Lean v4.34.1 library `FluxCharge`:

| Module | What | Theorems |
| :--- | :--- | ---: |
| `FluxCharge.Monopole` | the Berry derivation: curvature from the actual derivatives of P is `sin θ / 2` | 17 |
| `FluxCharge.Geometry` | ported original: projector algebra, flux integrals, gauges, radial flux | 13 |
| `FluxCharge.Bridge` | ported original: charge records, the bridge as a hypothesis | 9 |
| `FluxCharge.Extension` | ported original: no continuous axis extension | 2 |
| `FluxCharge.Seam` | **the join** (below) | 6 |
| | **total**, with 9 false controls | **47** |

### The seam (`FluxCharge/Seam.lean`)

* `lowerProjector_eq_proj`: the original package's `lowerProjector x y z` and the derivation's
  `proj (x, y, z)` are the same matrix.
* `proj_nvec_idempotent`: along the sphere, the derived projector is a genuine projector.
* `derivedCurvature_eq`: the curvature built from Lean's `deriv` of the projector entries is
  `sin θ / 2` at every (θ, φ).
* `derived_curvature_unit_flux`: integrated over the coordinate rectangle, that derived curvature
  has normalized flux exactly **1**.
* `matrix_to_integer`: the three together, in one statement.

Before v5 the paper joined the 17-theorem derivation and the 24-theorem flux package in writing.
That join is now a checked theorem. Only the physical bridge F_B = κ f*Ω, the bundle and the
Chern-class interpretation remain written mathematics, as the paper says.

* **The original archive.** [`monopole_stance/`](monopole_stance/) keeps the original Lean v4.19.0
  package exactly as it was verified, with its own pinned Mathlib, `verify.py` and evidence. The
  port in `FluxCharge/` changes content in one place only: `Geometry` takes `omega` from
  `Monopole`, where it is derived, instead of defining it. Two port fixes are proof-script only:
  `north/south_derivative` without `convert`, and a limit lemma pinned to ℝ.

## The Berry derivation (`FluxCharge/`)

For a unit direction `n(θ, φ)` the lower eigenprojector of `H = n·σ` is `P(n) = ½(I − n·σ)`.
With the actual derivatives of `θ ↦ P(n(θ, φ))`, the curvature `i Tr(P [∂_θ P, ∂_φ P])` is
`sin θ / 2`. Over the whole sphere that is a flux of `2π`, i.e. first Chern number 1.

### What is proved (`FluxCharge/Monopole.lean`, 17 theorems)

| Result | Theorem |
| :--- | :--- |
| `[a·σ, b·σ] = 2i (a×b)·σ` | `pauli_comm` |
| `P` is affine in `n`: `P(n + h a) − P(n) = h D(a)`, `D(a) = −½ a·σ` | `proj_affine` |
| `i Tr(P(n) [D(a), D(b)]) = ½ n·(a×b)` for all real vectors | `curvature_formula` |
| the six component derivatives of `n(θ, φ)` | `hasDerivAt_nvec_*` |
| chain rule for `P` along any differentiable path in ℝ³, entry by entry | `hasDerivAt_proj_comp` |
| actual θ- and φ-derivatives of every entry of `P(n(θ, φ))` | `hasDerivAt_proj_θ`, `hasDerivAt_proj_φ` |
| `n·(∂_θ n × ∂_φ n) = sin θ` | `triple_product` |
| curvature `= sin θ / 2` | `berry_curvature` |
| the same, built from Lean's `deriv` of the actual projector entries | `berry_curvature_from_derivatives` |
| vanishes only at the poles | `berry_curvature_eq_zero_iff` |
| the complementary band carries the opposite curvature | `complement_curvature` |

**Not proved here:** the line bundle, its Chern class as a topological invariant, any spatial
pullback, and any electromagnetic identification. In the note the electromagnetic bridge is an
explicit hypothesis, and it stays one.

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml), with one job per development.

**`check` job (FluxCharge, Lean v4.34.1):**

1. build against Lean v4.34.1 and Mathlib v4.34.1;
2. independent replay of every module in Lean's kernel checker (`leanchecker`);
3. an axiom audit of every named theorem, where only `propext`, `Classical.choice` and
   `Quot.sound` are allowed (so no `sorry`);
4. two deliberately false statements that must fail for a mathematical reason: the curvature
   without the ½ (`monopole_wrong_factor`), and the θ-derivative with the wrong sign
   (`monopole_wrong_derivative_sign`).

The theorem inventory is fixed in [`scripts/config.json`](scripts/config.json).

**`monopole_stance` job (Lean v4.19.0):** fetches the pinned Mathlib cache and runs the original
`monopole_stance/scripts/verify.py`. That builds the package, rejects any `axiom`, `sorry` or
`native_decide` in the sources, audits all 24 theorems' axioms (`propext`, `Classical.choice`,
`Quot.sound` only), and requires all six negative controls to fail.

## Relation to other work

* **IQGT paper.** The same two-level example appears in Appendix B of *Intrinsic Quantum
  Geometric Tensor on the Grassmannian and Spectral Lower Bounds on Dissipation*
  (DOI [10.5281/zenodo.20768258](https://doi.org/10.5281/zenodo.20768258)). That paper's own
  94-theorem Lean record is in
  [iqgt-grassmannian-lean](https://github.com/dicipler-pixel/iqgt-grassmannian-lean) and is
  separate from this repository.
* **History.** The Berry derivation was first developed on the `monopole-berry` branch of
  `iqgt-grassmannian-lean`. Paper v4 cites that branch's commit
  [`7851127`](https://github.com/dicipler-pixel/iqgt-grassmannian-lean/commit/78511277b439ea02e9fb5c292f69503890148e00)
  and its CI run as the checked revision, and that record still stands. `FluxCharge/Monopole.lean`
  here is byte-for-byte the same file. It was moved here so that the note has one home and the
  published IQGT record stays unchanged.

## Licence

Code and proofs: MIT ([`LICENSE`](LICENSE)). Written text: CC BY 4.0
([`LICENSE-CC-BY-4.0.md`](LICENSE-CC-BY-4.0.md)). See [`LICENSING.md`](LICENSING.md).

## Build it yourself

```bash
# the Berry derivation (Lean v4.34.1)
lake exe cache get
lake build
python3 scripts/verify.py

# the original package (Lean v4.19.0)
cd monopole_stance
lake exe cache get
python3 scripts/verify.py
```

## Credits

* **Direction, ideas and responsibility for the work:** Jeromie Beasley.
* **ChatGPT (OpenAI):** drafting of the paper *From Geometric Flux to Magnetic Charge*, the original
  `monopole_stance` package, and the entrywise derivative theorems and
  `berry_curvature_from_derivatives`.
* **Claude (Anthropic):** the first version of `Monopole.lean`, the chain-rule lemma
  `hasDerivAt_proj_comp`, the wrong-sign false control, independent review, and setting up
  this repository.

The AI systems worked under the author's direction. Every proof here is checked by Lean, not
taken on trust from any of them.
