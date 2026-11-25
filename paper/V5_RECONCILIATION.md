# The two version 5s — what actually differs, and which one is the paper

There are two copies of version 5 in this repository's history:

- **`main`** — the v5 package (paper, six proof modules, `verification_v5/`), imported on 23 November 2026.
- **branch `v5-seam`** — the author's own development history, eleven commits, tip `ea61635`.

## They are the same paper

Byte comparison of `main` (`3431cda`) against `ea61635`:

| path | result |
| --- | --- |
| `paper/Geometric_Flux_and_Magnetic_Charge_v5.tex`, `.pdf`, `.html` | **identical** |
| `FluxCharge/{Monopole,Geometry,Bridge,Extension,Seam,Topology}.lean` | **identical** |
| `monopole_stance/` (24-theorem Lean 4.19.0 archive) | **identical** |
| `verification_v5/` logs, `FalseControls/`, `.github/workflows/build.yml`, `lakefile.toml`, `lean-toolchain` | **identical** |

So "two v5s" is not two papers. It is one paper stored twice.

## The three files that did differ

1. `FluxCharge.lean` — `main` imports four modules added later (`Bundle`, `SpectralWall`, `TwoLevelWall`, `JordanWall`, `PeelWall`); `v5-seam` predates them. Nothing to reconcile: the v5 paper never claims those.
2. `lake-manifest.json` — `main` tracks it so a build can be reproduced from the repository alone; `v5-seam` inherits the v5 `.gitignore`, which excluded it. Tracking is the stronger choice and is kept.
3. **`verification_v5/lean-evidence.zip`** — present only on `v5-seam`. This is the one real loss, and it has been restored on branch `openmath/audit-fixes`.

## Which one is the paper

The paper is the file, and the file is the same in both. The difference that matters for citation is *evidence*: `main`'s v5 was checked by CI runs 12 and 13 on commits `d02b612` and `ea61635` (both `success`), and every commit since has been checked by the same workflow. `v5-seam` therefore does not need merging for its content; after restoring the evidence zip, there is nothing on it that `main` lacks.

**Recommendation:** keep `main` as the canonical line; keep `v5-seam` as the author's history without merging it. If the author prefers the branch to be the line, that is a rebase of `main` onto it, not a merge — and it should be done deliberately, not silently.
