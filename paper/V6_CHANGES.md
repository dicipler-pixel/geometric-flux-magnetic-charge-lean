# What version 6 changes, for review

Scope: the paper gains one construction and narrows one boundary. Nothing else in the argument
moves, and no physical claim is added.

## Lean side (committed first, `e721c9c`)

`FluxCharge/Bundle.lean`, 43 theorem declarations, imports `FluxCharge.Geometry`. Inventory
56 → 99 in `scripts/config.json`; `FluxCharge.lean` imports the module; README table and boundaries
paragraph updated. Verified by `scripts/verify.py` on Lean 4.34.1 / Mathlib `d13f23b723b8`:
`OK: 99 theorems, axioms used: [Classical.choice, Quot.sound, propext], 11 false controls rejected`.
Evidence: `verification_v6/`.

## Paper text

1. **Version line**: 5.0 / 5 November → 6.0 / 23 November.
2. **Abstract**: says the library constructs the eigenline bundle — two local unit sections,
   transition `e^{iφ}` with winding one, connections computed from those sections, gauge difference,
   curvature, normalized flux — and that the counts are 99 declarations / 11 controls. The
   "we distinguish" sentence now names an *abstract first Chern class* rather than a written
   eigenline-bundle interpretation, because the sections and the winding are no longer merely written.
3. **§1, second and third paragraphs**: adds that the revision constructs the objects the bundle
   language names, and lists the bundle among the new results.
4. **§4 (new Proposition 4.2, "The two charts, checked")**: five items — unit lower eigenvectors and
   range of `P_-`; `u_S = e^{iφ} u_N`; winding one; `A_{N,S}` from the sections equal to
   `(1 − cos θ)/2` and `−(1 + cos θ)/2`; `a_N − a_S = 1` and `da_N = ω dθ`. The proof names the
   declarations and states that `a_N, a_S` were supplied in v5 and are derived here.
5. **§4, sign paragraph**: `conj(g) g' = i`, so the literal leading-`+i` normalization integrates to
   `−1` and the printed `Im(conj g · g')` normalization to `+1`; both are checked and the second is
   used. This is deliberate: the earlier brief for the work had the sign wrong, and the paper now
   records the correction instead of hiding it.
6. **§4, closing paragraph**: what remains written mathematics is the identification with an abstract
   first Chern class, general coordinate and gauge invariance, pullback degree theory, and the
   physical identification.
7. **§"What the checked calculation adds"**: the first boundary item is split into its checked part
   (sections, transition, winding, coefficient difference) and its remaining part (abstract class).
8. **§"Formal verification and reproducibility"**: module table gains `FluxCharge.Bundle` 43 and the
   total becomes 99; the "99 count theorem declarations" sentence; "seven modules"; "exactly 99
   theorems and 11 false controls"; the evidence paragraph now separates version 5's commit
   `d02b612` and CI run `42027723304` (which covered 56 declarations) from version 6's local run and
   `verification_v6/`, and says a CI run for a pushed revision should replace it.
9. **Appendix**: intro counts updated; new table of the 43 bundle declarations with roles; note that
   the supporting lemmas of that module are audited through the theorems that use them, and why no
   new false control is added.

## Points worth your attention

- Proposition 4.2 item 4 asserts the connection coefficients are computed from the sections. That is
  the substantive strengthening over v5; the Lean declarations are `berryConnection_uN` and
  `berryConnection_uS`.
- The sign paragraph is a factual correction to the working brief, not to the paper's own earlier
  text (v5 never asserted a winding integral).
- The paper still cites v5's CI for v5. If you push, that paragraph needs the new commit and run.

## Support files

`plot_functions_v6.py`, `build_html_v6.py`, `check_paper_v6.py`,
`figures/curvature_and_gauges_v6.{pdf,png}`, `paper_validation_v6.json` (32 checks, none failed),
`CHECKSUMS_v6.sha256`, `README_PAPER.md`. Version 5 files and version 4 files remain unchanged.
