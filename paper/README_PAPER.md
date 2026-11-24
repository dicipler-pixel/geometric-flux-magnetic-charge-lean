# From Geometric Flux to Magnetic Charge — version 6 (draft)

Jeromie Beasley · GPT (OpenAI) · Claude (Anthropic) · 23 November 2026 · Research draft

Open `Geometric_Flux_and_Magnetic_Charge_v6.pdf` or the self-contained HTML with the same stem.
Version 5 files remain as the earlier paper record; version 4 files before that.

Version 6 adds §4's construction: the two local sections of the lower eigenline, their transition
function `e^{iφ}` with winding one, and the Berry connections computed from the proof system's own
derivatives of those sections, giving `(1 − cos θ)/2` and `−(1 + cos θ)/2`, the gauge difference
`A_N − A_S = 1`, the curvature `sin θ / 2` and normalized flux `1`. The coefficients that version 5
supplied are now derived. The paper also records the sign convention explicitly: the literal
leading-`+i` normalization of the winding integral is `−1`, and the printed `Im(conj g · g')`
normalization is `+1`; both are checked.

## One current proof environment

The root `FluxCharge` library uses Lean 4.34.1 and Mathlib v4.34.1: seven modules, 99 theorem
declarations and 11 false controls. The original 24 declarations are included through their port,
rather than additional to the 99. `FluxCharge.Bundle` is the new module (43 declarations); the
unchanged `monopole_stance/` project preserves the original Lean 4.19.0 archive.

`scripts/verify.py` builds the library, audits every named theorem against the three permitted
standard axioms, and requires all 11 controls to fail for a mathematical reason. `verification_v6/`
records the local run; the same inventory is checked by CI run 45299889323 on proof commit
`70903e6` (branch `main`).

## Exact boundaries

The pole theorem rules out a scalar primitive with equal values at 0 and π. Its interpretation as an
obstruction to a smooth global axisymmetric potential uses a written regularity argument. The cut
theorem varies latitude within fixed north/south formulas. The cancellation theorem concerns
normalized real integrals, despite the retained name `total_chern_zero`.

The two local sections, the transition map and the connections are constructed. What remains written
mathematics is the identification with an abstract first Chern class of a smooth line bundle, general
coordinate and gauge invariance, spatial pullbacks and the degree formula, and a system-specific
physical field identification such as `F_B = κ f*Ω`. The note proves neither existence nor absence of
a physical magnetic particle.

## Rebuild

Requires Python 3 with NumPy, Matplotlib, SymPy, PyMuPDF and lxml, plus a working pdfLaTeX
installation with Latin Modern and Pandoc.

```sh
python3 plot_functions_v6.py
pdflatex -interaction=nonstopmode -halt-on-error Geometric_Flux_and_Magnetic_Charge_v6.tex
pdflatex -interaction=nonstopmode -halt-on-error Geometric_Flux_and_Magnetic_Charge_v6.tex
python3 build_html_v6.py
python3 check_paper_v6.py
```

`paper_validation_v6.json` records the symbolic checks, the full source inventory, PDF/HTML checks
and source hashes. It supplements Lean CI. In this draft the symbolic script checks the same section
identities that `FluxCharge.Bundle` now proves, so the two are independent cross-checks rather than
one standing in for the other.
