<div align="center">

# From Geometric Flux to Magnetic Charge — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/geometric-flux-magnetic-charge-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/geometric-flux-magnetic-charge-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-99%20%2B%20161-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)

Jeromie Beasley · GPT (OpenAI) · Claude (Anthropic)

</div>

---

## What this is

The paper *From Geometric Flux to Magnetic Charge: A Checked Pauli Curvature and an Explicit
Physical Bridge* (version 6 draft, 23 November 2026) and its unified Lean development. The v5
paper and the v4 before it remain in the repository as the earlier record.

* **Read the draft:** [`paper/Geometric_Flux_and_Magnetic_Charge_v6.pdf`](paper/Geometric_Flux_and_Magnetic_Charge_v6.pdf)
  or the [HTML version](paper/Geometric_Flux_and_Magnetic_Charge_v6.html). Source and
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
| `FluxCharge.Topology` | pole obstruction, latitude-cut independence and derived band-flux cancellation | 9 |
| `FluxCharge.Bundle` | **the eigenline bundle in two charts** (below) | 43 |
| | **total for the flux-charge chain**, with 11 false controls | **99** |
| `FluxCharge.SpectralWall` | *adjacent:* the ISCO spectral wall, and the partial/total derivative certificate | 56 |
| `FluxCharge.TwoLevelWall` | *adjacent:* the non-Hermitian two-level wall, and the corrected projector statement | 26 |
| `FluxCharge.JordanWall` | *adjacent:* Jordan propagator, projector divergence, wall normal form | 32 |
| `FluxCharge.PeelWall` | *adjacent:* the peel wall — exact discriminant, square-zero wall, both square-root limits | 47 |
| | **adjacent total**, outside the flux-charge chain | **161** |

### The spectral-wall modules (adjacent)

Three modules import Mathlib only and depend on nothing in the flux-charge chain; they formalize
statements from the author's black-hole manuscript rather than from this note. `scripts/config.json`
counts them separately (`expected_adjacent_theorems`) and `scripts/verify.py` audits their axioms by
the same rules.

* `SpectralWall` — the circular-orbit generator `M r = !![0, 1; -W r, 0]` with
  `W r = (r - 6)/(r^3 (r - 3))`: `M^2 = -W • 1`, nonzero nilpotent at `r = 6`, the sign dichotomy
  `0 < W ↔ 6 < r`, eigenvalues `± i sqrt W` outside and `± sqrt (-W)` inside, both one-sided limits
  of `2 sqrt |W| / sqrt |r - 6|` to `2 / sqrt 648`, the growing eigenvector `(1, sqrt (-W))` and
  `deriv sqrt (-W) → atBot` at the wall, `p 6 = 3`. It also certifies the derivative ambiguity:
  the second **partial** at fixed `L^2` gives `2W`, while the second derivative **along** the family
  gives `1/81` at `r = 6`, so the wall exists for one reading and not the other.
* `TwoLevelWall` — `H g = σx + i g σz`: `H^2 = (1 - g^2) • 1`, the nilpotent at `g = 1`, the
  counterexample showing the hand-written projector formula is **not** idempotent for `|g| ≥ 1`,
  its repair on `|g| < 1`, and the proof that no orthogonal idempotent resolution exists at `g = 1`.
* `JordanWall` — the Jordan propagator `exp (lam t) • (1 + t N)` with its linear-in-time entry and
  entrywise derivative; the single-projector divergence `‖P+‖ * gap → ‖b‖` with the pair projector
  staying finite (determinant 1); and the wall normal form: `trace W = 2 lam`, `det W = lam^2` gives
  `(W - lam • 1)^2 = 0`, with a model whose gap unfolds as `2 sqrt |d|`. The peel wall
  (`trace (W+1) = 0`, `(W+1)^2 = 0`) is that normal form at `lam = -1`.

### The eigenline bundle (`FluxCharge/Bundle.lean`)

The sections of paper §4 are now objects, not prose: `uN` and `uS` are unit lower eigenvectors of
`pauli (nvec θ φ)` (`pauli_mulVec_uN`, `pauli_mulVec_uS`, unit norms `uN_normSq`, `uS_normSq`)
and lie in the range of the lower projector (`proj_mulVec_uN`, `proj_mulVec_uS`); they are related
by the transition function, `uS θ φ = e^{iφ} • uN θ φ` (`uS_eq_smul_uN`), whose winding number is
one (`transitionPhase_winding_integral`, with the literal `+I` normalization refuted as `-1` by
`transitionPhase_winding_integral_plus_I`). The Berry connections are computed from Lean's `deriv`
of those actual section components, not supplied: `berryConnection_uN` gives
`(1 − cos θ)/2`, `berryConnection_uS` gives `−(1 + cos θ)/2`, so `connection_gauge_difference`
is `A_N − A_S = 1` for one connection read in two charts, `curvature_from_connection` gives
`dA_N = (sin θ / 2) dθ`, and `chern_number_one` records gauge difference, winding and normalized
flux all equal to 1. What this does **not** give: an abstract first Chern class or Chern–Weil
theory, invariance under general coordinate or gauge changes, integer-valuedness of winding
numbers for arbitrary circle maps, spatial pullbacks with their degree formula, or any
electromagnetic identification.

### The seam (`FluxCharge/Seam.lean`)

* `lowerProjector_eq_proj`: the original package's `lowerProjector x y z` and the derivation's
  `proj (x, y, z)` are the same matrix.
* `proj_nvec_idempotent`: along the sphere, the derived projector is a genuine projector.
* `derivedCurvature_eq`: the curvature built from Lean's `deriv` of the projector entries is
  `sin θ / 2` at every (θ, φ).
* `derived_curvature_unit_flux`: integrated over the coordinate rectangle, that derived curvature
  has normalized flux exactly **1**.
* `matrix_to_integer`: the three together, in one statement.

### Pole obstruction, latitude-cut independence and derived band-flux cancellation

`FluxCharge/Topology.lean` adds three precise results:

* **Pole obstruction** (`no_global_regular_gauge`): no real function with derivative
  `ω(θ) = sin θ / 2` everywhere has equal values at `0` and `π`. The fundamental theorem
  of calculus forces the endpoint difference to be 1. In the axisymmetric ansatz
  `A = a(θ) dφ`, this is the scalar obstruction underlying the two-patch description.
  The theorem does not quantify over arbitrary smooth one-forms on the sphere or formalize
  the implication from smooth pole regularity to coefficient endpoint conditions.
* **Latitude-cut independence** (`flux_is_transition_jump`, `flux_one_at_every_cut`): for
  the fixed north and south coefficients, splitting the polar integral at any `θ₀` gives
  `a_N(θ₀) − a_S(θ₀) = 1`. For `0 ≤ θ₀ ≤ π` these are the two cap contributions;
  the theorem also holds for every real cut as an oriented interval-integral identity.
  This checks moving the latitude cut, rather than arbitrary coordinate or gauge changes.
* **Derived band-flux cancellation** (`derivedCurvatureCompl_eq`, `derived_compl_flux`,
  `total_chern_zero`): actual entrywise derivatives of `I − P` give curvature `−sin θ / 2`,
  normalized flux −1, and zero sum with the lower band's +1. Despite its historical name,
  `total_chern_zero` states an equality of normalized real integrals; it does not construct
  a Chern class.

The former written join between the projector derivation and the flux integral is now
checked inside one library. `matrix_to_integer` proves that the normalized real integral
equals 1; it is not a general integer-valued quantization theorem. `FluxCharge.Bundle` now
constructs the two local sections, the transition map, its winding and the connections the
paper describes, so the section-level side of the bundle is checked for this example. The
remaining boundaries are an abstract Chern class, invariance under general coordinate and gauge
changes, pullbacks with their degree formula, and a system-specific physical field
identification such as `F_B = κ f*Ω`. No physical Dirac string or magnetic particle is
inferred from the parameter-space calculation.

* **A separate note in this tree.** [`One_Tree_Every_Shape_v2_rebuild/`](One_Tree_Every_Shape_v2_rebuild/REBUILD.md)
  is Jeromie Beasley's interactive page *One Tree, Every Shape* v2 (23 November 2026, built with AI
  assistance), with its rebuild kit and the computational records behind its eyes
  (`records/what-bends/`, `records/poincare-diamond/`). It is not part of the Lean library, is not
  counted in any inventory here, and `lake build` ignores it: `FluxCharge/` is the only Lean root.

* **The original archive.** [`monopole_stance/`](monopole_stance/) keeps the original Lean v4.19.0
  package exactly as it was verified, with its own pinned Mathlib, `verify.py` and evidence. The
  port in `FluxCharge/` changes content in one place only: `Geometry` takes `omega` from
  `Monopole`, where it is derived, instead of defining it. Two port fixes are proof-script only:
  `north/south_derivative` without `convert`, and a limit lemma pinned to ℝ.

## The Berry derivation (`FluxCharge/`)

For a unit direction `n(θ, φ)` the lower eigenprojector of `H = n·σ` is `P(n) = ½(I − n·σ)`.
With the actual derivatives of `θ ↦ P(n(θ, φ))`, the curvature `i Tr(P [∂_θ P, ∂_φ P])` is
`sin θ / 2`. Its coordinate flux is `2π` and its normalized real integral is 1.
The standard eigenline-bundle interpretation identifies this with first Chern number 1;
that identification is written mathematics here.

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
| scalar coefficient vanishes iff `sin θ = 0` (the poles when `0 ≤ θ ≤ π`) | `berry_curvature_eq_zero_iff` |
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
4. **11 deliberately false controls**, each required to fail for a mathematical reason:
   zero unit flux; unconditional magnetic-existence inference; unconditional magnetic-absence
   inference; charge transfer with a zero flux unit; idempotence at the degenerate origin;
   zero chart-coefficient difference; the missing curvature factor ½; the wrong projector
   derivative sign; doubled derived flux; equal north-coefficient values at both poles;
   and a total two-band flux of 2.

The verification script checks the fixed inventory of **99 theorem declarations and 11 controls**.
It also rejects control failures caused by broken imports or missing identifiers. The archived
24 declarations are already included through their port in the 56; they are not 24 additional
results of the unified library.

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

