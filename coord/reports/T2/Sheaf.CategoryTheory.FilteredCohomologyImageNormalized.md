## What changed

Retired the duplicate `Sheaf.CategoryTheory.FilteredCohomologyImageNormalized`
module using `deleted.txt`. Migrated its sole direct consumer,
`Sheaf.CategoryTheory.FilteredCohomologyImagePresentation`, to the proof import
`WeilConjectures.CategoryTheory.FilteredCohomologyImageNormalized`. Reattached
`lem-sp-filtered-cohomology-image-normalized-quotient` to the existing upstream
theorem. No upstream source, theorem signature, definition, or target changed.

Change record: `coord/changes/retire-filtered-cohomology-image-normalized-T2.md`.

The complete upstream theorem signature and proof match the retired theorem
modulo whitespace. Server compilation of the adapted consumer succeeded.
A separate server audit of the upstream theorem reports exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## Proved and sorry left

This is the listed retirement repair, with zero original holes.
Holes closed: 0 of 0. Holes added: 0. Split off: 0. Holes left: none.
`CategoryTheory.DecreasingFiltration.cohomologyImage_graded_normalized`
remains completely proved in the adopted upstream module.
The adapted `cohomologyImage_graded_presentation` proof is unchanged and compiles.
No existing proved body was replaced by an admission.

## No longer needed

Pruned module: `Sheaf.CategoryTheory.FilteredCohomologyImageNormalized`.
Removed its proof import from `Sheaf.CategoryTheory.FilteredCohomologyImagePresentation`
and replaced it with the canonical upstream module. The duplicate module's own
public import of `WeilConjectures.CategoryTheory.FilteredCohomologyImage` and proof
imports of `WeilConjectures.CategoryTheory.FilteredNormalizedQuotientPresentation`
and `WeilConjectures.CategoryTheory.FilteredCohomologyImageCycleMap` disappear
with that duplicate; the upstream proof still uses those dependencies.
No mathematical node or dependency is pruned: the normalized quotient node and
all its parent edges stay, attached to the canonical theorem. The unit route stays.
No other module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed module, but the current queue marks
this item `retire`; the current module already contains zero holes. The adopted
upstream twin proves exactly the same theorem. The old `PROOFDIFF_UNSAFE`
retirement inventory cites parallel dependency copies; the live Sheaf module
and its consumer now import the upstream dependency family, following the recent
cohomology-image, cycle-map, and normalized-quotient retirements. This packet
therefore completes the listed retirement rather than creating another proof.
Searches used msearch (leanfinder, loogle, grep) and direct rg of both library
roots. Direct source comparison found the exact upstream implementation.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
