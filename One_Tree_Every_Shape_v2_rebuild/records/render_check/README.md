# RENDER-CHECK-01 — the page drawn in all three solids

Evidence that `page/One_Tree_Every_Shape_v2.html` renders and that every eye runs, produced on
24 November 2026 by the Open Math OS agent; the page and its build are the author's (Jeromie Beasley,
23 November 2026).

## What was run

`page/shot2.js` (SCRIPT: OTES-SHOT-02), unchanged, against the shipped page:

    node shot2.js          # from a directory containing the page

Toolchain: Node v22.11.0; Playwright `chromium-headless-shell` 159.0.8154.6; Chromium launched with
`--use-gl=swiftshader --enable-unsafe-swiftshader --no-sandbox` (software WebGL, since the machine has
no GPU); viewport 1280×800. Nothing in the page or the script was modified.

## Result

- exit status 0; `errors []` — no page errors and no console errors;
- all **12 eyes driven in all three solids** (icosahedron, cube, tetrahedron) through
  `window.API.frame(0.05, id, null)`;
- 24 screenshots written; the three kept here are the same eye, `bBrd` ("12 What bends — every
  option"), in each solid: `icosahedron_board.jpg`, `cube_board.jpg`, `tetrahedron_board.jpg`;
- byline read from the live DOM: `Jeromie Beasley · 3D mixer · v2`;
- `shot2_run.log` is the full stdout, including the panel text the page computes at runtime for the
  six "what bends" eyes (e.g. `bDig`: 239,099 twin pairs below 50,000,000; transitions
  0.9196 · 1.0948 · 0.9858).

Files the evidence is bound to (SHA-256):

    26b29068280a8836eb70cb4bcfff454436308f397ce179078b0de894151a6f54  page/One_Tree_Every_Shape_v2.html
    961055289ac00430c037575e9fa2e5be05b04d781975910568a962ce69c485bb  page/data.json

The same session also checked reproducibility: `build_v2.py` regenerates the page **byte-identical**
to the shipped file (724,494 bytes), and `data.py` regenerates `data.json` byte-identical.

## What this does not establish

It is a rendering check, not a proof. It says the page draws and its code runs without errors on this
one browser build; it says nothing about whether the measured covariances support the reading the page
puts on them, and the v1 page was not rebuilt (its source page, *One Tree, One Ball*, is not in the kit
by design — see `REBUILD.md`).
