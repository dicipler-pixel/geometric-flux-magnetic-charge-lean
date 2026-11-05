<div align="center">

# From Geometric Flux to Magnetic Charge — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/geometric-flux-magnetic-charge-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/geometric-flux-magnetic-charge-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-17-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)

Jeromie Beasley

</div>

---

## What this is

The machine-checked part of the note *From Geometric Flux to Magnetic Charge*: the Berry
curvature of the lower Pauli eigenprojector, computed exactly and end to end.

For a unit direction `n(θ, φ)` the lower eigenprojector of `H = n·σ` is `P(n) = ½(I − n·σ)`.
With the actual derivatives of `θ ↦ P(n(θ, φ))`, the curvature `i Tr(P [∂_θ P, ∂_φ P])` is
`sin θ / 2`. Over the whole sphere that is a flux of `2π`, i.e. first Chern number 1.

## What is proved (`FluxCharge/Monopole.lean`, 17 theorems)

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

Every push runs [the proof check](.github/workflows/build.yml):

1. build against Lean v4.34.1 and Mathlib v4.34.1;
2. independent replay of every module in Lean's kernel checker (`leanchecker`);
3. an axiom audit of every named theorem, where only `propext`, `Classical.choice` and
   `Quot.sound` are allowed (so no `sorry`);
4. two deliberately false statements that must fail for a mathematical reason: the curvature
   without the ½ (`monopole_wrong_factor`), and the θ-derivative with the wrong sign
   (`monopole_wrong_derivative_sign`).

The theorem inventory is fixed in [`scripts/config.json`](scripts/config.json).

## Relation to other work

* **IQGT paper.** The same two-level example appears in Appendix B of *Intrinsic Quantum
  Geometric Tensor on the Grassmannian and Spectral Lower Bounds on Dissipation*
  (DOI [10.5281/zenodo.20768258](https://doi.org/10.5281/zenodo.20768258)). That paper's own
  94-theorem Lean record is in
  [iqgt-grassmannian-lean](https://github.com/dicipler-pixel/iqgt-grassmannian-lean) and is
  separate from this repository.
* **History.** This module was first developed on the `monopole-berry` branch of
  `iqgt-grassmannian-lean`, at commit `7851127`. It was moved here so that the note has one
  home and the published IQGT record stays unchanged.
* **The original monopole package.** The note's earlier 24-declaration Lean package is not yet
  in this repository, and it is not counted in the 17 above.

## Licence

Code and proofs: MIT ([`LICENSE`](LICENSE)). Written text: CC BY 4.0
([`LICENSE-CC-BY-4.0.md`](LICENSE-CC-BY-4.0.md)). See [`LICENSING.md`](LICENSING.md).

## Build it yourself

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## Credits

* **Direction, ideas and responsibility for the work:** Jeromie Beasley.
* **ChatGPT (OpenAI):** drafting of the note *From Geometric Flux to Magnetic Charge*, the original
  monopole package, and the entrywise derivative theorems and `berry_curvature_from_derivatives`.
* **Claude (Anthropic):** the first version of `Monopole.lean`, the chain-rule lemma
  `hasDerivAt_proj_comp`, the wrong-sign false control, independent review, and setting up
  this repository.

The AI systems worked under the author's direction. Every proof here is checked by Lean, not
taken on trust from any of them.
