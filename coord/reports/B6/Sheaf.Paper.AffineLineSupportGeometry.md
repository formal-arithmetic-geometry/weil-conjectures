## What changed

Proved `WeilConjectures.PurityFiniteSetting.affineLine_support_geometry` in
`Sheaf.Paper.AffineLineSupportGeometry`, with its signature unchanged. The proof constructs
local Noetherianity and compactness separately, uses Mathlib's finite-presentation and affine
projection instances for the relative affine line, and derives quasi-compactness of the basic-open
inclusion from the line's local Noetherianity (Stacks 01OX). Finite-type composition and
finite-type-over-Noetherian then provide all remaining conclusions. Updated the item's node to
record this shorter route. No definitions, statements, visibility or public imports changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PurityFiniteSetting.affineLine_support_geometry`
(node `lem-pur-affine-line-support-geometry`). There are zero holes left in the item and zero
holes added; no split-offs. No unproved project theorem is used in the proof.

## No longer needed

Removed proof imports `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` and
`Mathlib.RingTheory.Spectrum.Prime.Topology`. No quasi-separatedness conclusion is needed.

The proof no longer directly needs nodes `lem-weil-pbc-spec-localization-away-basic-open` or
`lem-weil-pbc-affine-scheme-qcqs`: local Noetherianity of the line implies quasi-compactness of
every open immersion into it, so there is no localization/chart-cover calculation to carry out.
The remaining declared dependencies are used, including the finite-type definition, affine-space
definition, open-immersion definition, finite-type composition, finite-type-over-Noetherian,
and quasi-compact-open-immersion finite type. The existing Mathlib leaf
`lem-weil-pbc-noetherian-open-subscheme-noetherian` records the compact-open input behind 01OX.
No project module is withdrawn. No top-level `tool_uses` approval existed to remove.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original plan's Step 3 was longer than
necessary: the already available local Noetherianity makes the coordinate-localization argument
unnecessary. This is below the unit level; the unit's statement and its realized steps are
unchanged. The empty base and nonreduced or nonseparated finite-type bases require no extra
hypothesis in either the statement or this proof.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
