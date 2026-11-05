# From Geometric Flux to Magnetic Charge — version 4

Jeromie Beasley · GPT (OpenAI) · Claude (Anthropic) · 5 November 2026 · Research draft

Open `Geometric_Flux_and_Magnetic_Charge_v4.pdf` for the 11-page paper, or the same-named self-contained HTML for a mobile-readable version with MathML equations.

This revision factors both entrywise projector derivative proofs through the reusable `hasDerivAt_proj_comp` lemma. The supplied companion patch contributes the general-lemma implementation and a wrong-sign control. The public derivative statements and end-to-end curvature theorem are unchanged. This release credits Jeromie Beasley, GPT (OpenAI), and Claude (Anthropic); the supplied patch's co-author credit is preserved in the repository.

## Two proof environments

`monopole_stance/` preserves the original Lean 4.19.0 project unchanged: 24 declarations, the exact dependency manifest, the axiom audit and six rejected controls. Its README describes that original project's scope; it predates the new derivation.

`berry_derivation/` contains the new 17-theorem module, its two false controls and CI evidence. It belongs to the IQGT project using Lean 4.34.1. The full IQGT repository has 111 audited declarations across five modules and eight false controls; those counts include the new module and the other IQGT work. The two environments are not one importable Lean project. The paper identifies their explicit matrix and scalar formulas in writing and does not claim a cross-project import theorem.

The new module proves the Pauli commutator, the exact affine increment of the projector, the trace formula, six component derivatives, both entrywise projector derivatives, the curvature built from Lean's actual derivatives, the spherical triple product, the curvature coefficient, its scalar zero criterion, and the opposite sign for the complementary projector. It does not construct a bundle, Chern class or physical electromagnetic field.

## Rebuild the paper

Requires Python 3 with NumPy, Matplotlib, SymPy, PyMuPDF and lxml, plus pdfLaTeX and Pandoc.

```sh
python3 plot_functions.py
pdflatex -interaction=nonstopmode -halt-on-error Geometric_Flux_and_Magnetic_Charge_v4.tex
pdflatex -interaction=nonstopmode -halt-on-error Geometric_Flux_and_Magnetic_Charge_v4.tex
python3 build_html.py
python3 check_paper.py
```

`paper_validation.json` records symbolic calculations and document checks. These supplement the Lean evidence. The PDF was rendered and inspected; references resolve, the figure is embedded, the assistance disclosure precedes the abstract, and no Type 3 fonts or overfull boxes remain.

No Zenodo or journal submission is part of this revision.
