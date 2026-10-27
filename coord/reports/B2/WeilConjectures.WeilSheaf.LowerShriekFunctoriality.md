## What changed

Proved `AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerShriek_iso` in `lean/WeilConjectures/WeilSheaf/LowerShriekFunctoriality.lean`. The proof chooses a Nagata compactification, pulls it back along the given Cartesian square, constructs the two chosen Cartesian squares, and composes the native proper and open natural base-change isomorphisms with the compactification-model and full-subcategory inclusion comparisons. Added the proof-only imports `WeilConjectures.Compactification.BaseChange`, `Sheaf.WeilSheaf.NativeProperNaturalBaseChange`, and `Sheaf.WeilSheaf.NativeOpenNaturalBaseChange`. Updated the item node to record this direct route.

## Proved and sorry left

Closed the sole item hole, `AlgebraicGeometry.WeilComplex.nonempty_upperStar_derivedLowerShriek_iso` (1 of 1). There are zero `sorry`s left in the item module and no new `sorry`s or split-off statements.

## No longer needed

The proof does not separately require the planned abstract pullback-exactness and constructibility nodes, the abstract compact-support triangulated node, or the finite-type composition and separatedness helper nodes listed in the former four-step DAG route: the native comparison APIs and the explicit instances in the theorem provide the required facts directly. No existing imports used by earlier declarations in this module were removed.

## Where the brief, the DAG or earlier work was wrong

The prior DAG proof plan expanded the compactification calculation into separate abstract pullback, constructibility, and target-preservation steps. In the current Lean library those obligations are already packaged by the native basic, compactification-model, proper-base-change, and open-base-change declarations. The theorem statement was unchanged; only the proof route and its dependency record were shortened.

## New nodes

None.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
