# One Tree, Every Shape v2 - rebuild kit (Jeromie Beasley, 23 Nov 2026, built with AI assistance)

## To rebuild the v2 page
Needs Python 3 only. From inside the `page` folder:

    python3 build_v2.py One_Tree_Every_Shape_v1.html v2_eyes.js data.json One_Tree_Every_Shape_v2_rebuilt.html

The result is byte-for-byte the same as `One_Tree_Every_Shape_v2.html` in this kit.

## To change the page
- New or changed eyes: edit `v2_eyes.js` (the six what-bends eyes), then run the line above.
- Panel text for each eye, the byline, and the changes to eyes 5 and 6: in `build_v2.py`.
- Measured numbers shown in eyes 7, 8, 9: `data.json`. To recount them: `python3 data.py` (needs numpy and mpmath; about two minutes).

## To check the page
    node shot2.js        (needs Node with playwright)
Opens all 12 eyes in the icosahedron, cube and tetrahedron, saves pictures, and prints any page errors.

## What is in the kit
- `page/One_Tree_Every_Shape_v2.html` - the finished page. Opens on its own in any browser.
- `page/One_Tree_Every_Shape_v1.html` - the first page, unchanged. v2 is built from it.
- `page/v2_eyes.js`, `build_v2.py`, `data.py`, `data.json`, `shot2.js`, `README_v2.md` - the v2 build.
- `page/new_eyes.js`, `build.py`, `shot.js`, `README.md` - how v1 was built. `build.py` starts from the One Tree, One Ball
  (Seiberg-Witten 4) page, which is not in this kit; v1 itself is, so v2 does not need it.
- `records/what-bends/` - PRIME-COVARIANCE-01, WHAT-BENDS-01, WHAT-BENDS-01b with outputs.
- `records/poincare-diamond/` - every shape script with its output, including `shape-audit/` (SHAPE-AUDIT-01).

Everything here is also on GitHub: dicipler-pixel/votkp-lean, branch claude/moving-matrix-of-balls, folder research/.
