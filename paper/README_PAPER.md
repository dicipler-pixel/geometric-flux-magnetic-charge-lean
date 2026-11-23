# From Geometric Flux to Magnetic Charge — version 5

Jeromie Beasley · GPT (OpenAI) · Claude (Anthropic) · 5 November 2026 · Research draft

Open `Geometric_Flux_and_Magnetic_Charge_v5.pdf` or the self-contained HTML with the same stem. Version 4 files remain as the earlier paper record.

Version 5 centres the unified proof chain: explicit projector, actual entrywise derivatives, derived curvature, equality of the matrix encodings, and normalized real flux 1. It adds pole obstruction, latitude-cut independence and derived band-flux cancellation, with their exact scalar and coordinate-integral meanings. Appendix A maps all 56 theorem declarations to their claims.

## One current proof environment

The root `FluxCharge` library uses Lean 4.34.1 and Mathlib v4.34.1: six modules, 56 theorem declarations and 11 false controls. The original 24 declarations are included through their port, rather than additional to the 56. The unchanged `monopole_stance/` project preserves the original Lean 4.19.0 archive.

The paper pins proof commit `d02b612e508e083e94baaf7d781ef15b76953f68` and [successful CI run 42027723304](https://github.com/dicipler-pixel/geometric-flux-magnetic-charge-lean/actions/runs/42027723304). The unified job builds, independently replays all six modules, audits every theorem against the three permitted standard axioms, and rejects all 11 controls. `verification_v5/` preserves its report, job log, dependency manifest and downloaded artifact. All six supplied module hashes match the report.

## Exact boundaries

The pole theorem rules out a scalar primitive with equal values at 0 and π. Its interpretation as an obstruction to a smooth global axisymmetric potential uses a written regularity argument. The cut theorem varies latitude within fixed north/south formulas. The cancellation theorem concerns normalized real integrals, despite the retained name `total_chern_zero`.

The global eigenline bundle, transition winding, Chern-class identification, general coordinate/gauge invariance, spatial pullback and degree formula remain written mathematics. A physical field identification such as `F_B = κ f*Ω` requires additional system-specific input. The note proves neither existence nor absence of a physical magnetic particle.

## Rebuild

Requires Python 3 with NumPy, Matplotlib, SymPy, PyMuPDF and lxml, plus a working pdfLaTeX installation with Latin Modern and Pandoc.

```sh
python3 plot_functions_v5.py
pdflatex -interaction=nonstopmode -halt-on-error Geometric_Flux_and_Magnetic_Charge_v5.tex
pdflatex -interaction=nonstopmode -halt-on-error Geometric_Flux_and_Magnetic_Charge_v5.tex
python3 build_html_v5.py
python3 check_paper_v5.py
```

`paper_validation_v5.json` records exact symbolic checks, the full source inventory, PDF/HTML checks and source hashes. It supplements Lean CI. The PDF was rendered and inspected: all theorem names and references are present, all three contributors appear in the byline, the disclosure precedes the abstract, and there are no Type 3 fonts or overfull boxes.
