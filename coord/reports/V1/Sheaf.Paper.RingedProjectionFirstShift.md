## What changed

Proved `SheafOfModules.ringedProjectionFirstShift` without changing its signature.
Use the existing `ringedProjectionMateExact` witnesses, curry the tensor comparison,
and identify the canonical mate with the existing library projection transformation.
Its first-factor comparison square supplies `NatTrans.CommShift` using the proved
`CategoryTheory.Adjunction.commShift_rightAdjointProjectionMapFlipApp`.
A proved private helper constructs the triangle morphism; its connecting square is
naturality followed by the shift equation. Added the proof-only import
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift`.
Updated the node's proof, dependencies and proof origin to match this route.
Resumed verification on 2026-10-19: the retained module compiles cleanly through
`lcompile.py` in 8.8 seconds against the current build. Its theorem signature is
identical to the current source, and the added proof import creates no cycle.

## Proved and sorry left

Closed the one original hole: `SheafOfModules.ringedProjectionFirstShift`
(node `lem-sfb-ringed-projection-first-shift`). Added zero holes; none remain in
the delivered module. This is a proof from existing declarations, including
`SheafOfModules.ringedProjectionMateExact`, whose existing proof obligation is
unchanged. No new intermediate obligation or arbitrary witness construction.

## No longer needed

Removed proof-only imports `Mathlib.CategoryTheory.Triangulated.Adjunction`,
`Mathlib.CategoryTheory.Adjunction.Basic`, `Mathlib.CategoryTheory.Shift.CommShift`,
`Mathlib.CategoryTheory.Triangulated.Basic` and
`Sheaf.Paper.RingedTopoiDerivedPullback`.
The adjunction exactness theorem is unused because `ringedProjectionMateExact`
already supplies exactness. The basic adjunction, shift and triangle interfaces
are available through the retained imports.

Direct proof dependencies `lem-weil-pbc-ringed-topoi-derived-pullback`,
`lem-sf-triangulated-right-adjoint`,
`lem-weil-pbc-adjunction-shift-compatibility-unique` and
`lem-weil-pbc-adjunction-of-natural-bijection` are unnecessary here: the existing
mate-exact theorem supplies exactness and compatible shifts, and the proved
library projection-map theorem implements the adjunct calculation.
Removed `lem-weil-pbc-ringed-topoi-derived-pullback` from the item's `tool_uses`.
The corresponding modules may still be needed elsewhere, including below
`ProjectionMateExact`; no claim is made that they leave the targets' closure.
The unit statement and its realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned explicit mate calculation is already proved abstractly in the source
library's `Adjunction.ProjectionMapShift`. The geometric input needed to apply it
is precisely the first-factor tensor comparison equation already included in
`ringedProjectionMateExact`. No statement or definition repair was needed.
The earlier sandbox's duplicate original file was retained in `scratchpad/`,
so it is not accidentally delivered as a second Lean module.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
