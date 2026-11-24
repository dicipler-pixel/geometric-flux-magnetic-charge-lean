# Working fork policy — Open Math OS

From this point on, work done by the Open Math OS agent lands on the branch `openmath/work` and reaches
`main` only by a pull request the author merges. `main` stays the author's line; the branch is the
agent's.

## What the agent does

1. Commit on `openmath/work` (never force-push it, never rewrite `main`).
2. Push the branch and open a pull request into `main`; the pull request body states what changed,
   what was checked, and what was **not** checked.
3. Leave the merge to the author. After a merge, rebase or fast-forward `openmath/work` onto the new
   `main` before starting more work.

## What the author can rely on

- Every push to either branch runs `.github/workflows/build.yml`: `lake build` on the pinned
  Lean 4.34.1 + Mathlib, an independent kernel replay of the modules, the axiom audit
  (`scripts/verify.py`), and the eleven deliberately false controls, which must fail.
- The audit covers two inventories and reports them apart: **99** declarations in the flux-charge
  chain (the count the paper quotes) and **161** in the adjacent wall modules.
- No `sorry`, no `admit`, no `native_decide`, no new axioms: `verify.py` rejects any theorem whose
  axiom set leaves `{propext, Classical.choice, Quot.sound}`.

## What a pull request from this branch will say

Each one carries, in its body: the theorem or file added, the exact command run and its closing line
(for example `OK: 99 theorems + 161 adjacent, … 11 false controls rejected`), the CI run it produced,
and an explicit list of what was not established — a rendering check is not a proof, a reproducible
computation is not a theorem, and "the paper says so" is not evidence.

## History up to the branch point

`main` at `3431cda` already contains the agent's earlier work, pushed directly before this policy
existed: the v5 tree, `FluxCharge/Bundle.lean`, the v6 paper draft with `verification_v6/`, the four
spectral-wall modules, and the *One Tree, Every Shape* v2 kit with its render check. Nothing is being
rewritten; the policy applies from here on.
