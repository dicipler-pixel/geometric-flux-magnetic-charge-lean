# Audit of the shape system (Jeromie Beasley, 23 Nov 2026, AI-assisted)

Script SHAPE-AUDIT-01 (`shape_audit.py`, output `shape_audit.out`). Every earlier shape script on this branch was rerun first
(POINCARE-DIAMOND-01, SHAPE-DEVICES-01, SHAPE-SMITH-01, BALL-TO-SHAPES-01, PLATO-SHAPES-01, PARTICLE-SHAPES-01, SMITH-SNELL-01,
GRAD-PROJECTOR-01): all eight reproduce their recorded output exactly.

| Test | Question | Result |
|---|---|---|
| A1 | SHAPE-SMITH-01 T1 read 2.9e-2 for the angle-keeping chart against its own 1e-6 kill line and was not flagged. Is the chart wrong? | No. That test stood 1e-6 inside the rim, where a corner cannot be reached. On the rim itself: 7e-31 (3, 4, 5, 6 sides) |
| A2 | SHAPE-SMITH-01 T2 read 2.5e-6 against its own 1e-6 line. Does the chart keep angles? | Yes: 1e-19 rad with a two-sided step. The earlier reading was the one-sided step's own error |
| A3 | Pentagon faces (untested) and the five solids: same from every point? | Only the triangle (9.000000) and the tetrahedron (13.333333). Pentagon, square, hexagon, cube, octahedron, dodecahedron, icosahedron all change with the point |
| A4 | The tree carried into a solid along rays: still one step length in the solid's own reading? | No. First-level edges keep ln 5 = 1.609; third-level edges run 0.64 to 2.84. Carried edges bend by up to 5% of their chord |
| A5 | The tetrahedron's own moves | A peel step on one face book is the solid's own motion (2e-13), length 1/2 ln z, lengths add (1e-11). The loop A B A^-1 B^-1 always closes (5e-13) at z = 2, 3, 5, the wall, 7, 50: no wall in the tetrahedron. Places reached grow like a grid (189 by four steps), not a tree (937) |
| A6 | Two books in every shape | The own reading is exactly the average of a forward and a backward one-way reading. From the centre toward a face they differ: 0.916 out, 0.470 back (0.182 back in the tetrahedron) |

Prior art: Hilbert geometry; flat only for the simplex (de la Harpe; Foertsch and Karlsson); a polytope that is not a simplex has only
its projective symmetries as motions (Lemmens and Walsh). A5 (c) follows from the simplex result; it is run here, not new.
Untested against a measurement.
