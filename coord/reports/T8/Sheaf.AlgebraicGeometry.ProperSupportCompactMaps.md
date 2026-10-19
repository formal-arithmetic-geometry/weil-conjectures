## What changed

Proved `AlgebraicGeometry.Etale.compactProperSupportClosed` using properness cancellation and the closed-range criterion for proper immersions. Proved `AlgebraicGeometry.Etale.compactProductSupportProper` by rewriting the product support structure map as the first projection of a pullback followed by the proper support map. The item module was copied into the sandbox with its original public imports unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.compactProperSupportClosed` and `AlgebraicGeometry.Etale.compactProductSupportProper` (2 of 6 proof holes in the item module).

Remaining existing holes: `AlgebraicGeometry.Etale.compactSupportCoefficientRestriction_existsUnique`, `AlgebraicGeometry.Etale.compactSupportCoefficientExtension_isIso`, `AlgebraicGeometry.ProEtale.compactSupportCoefficientRestriction_existsUnique`, and `AlgebraicGeometry.ProEtale.compactSupportCoefficientExtension_isIso`. No new sorry declarations were added.

## No longer needed

No imports or DAG nodes were pruned. The exploratory constant-sheaf imports were removed before delivery because the retained proofs do not use them.

## Where the brief, the DAG or earlier work was wrong

The DAG proof list is empty, so it provides no additional Lean-level route. The two geometric statements are directly available from Mathlib's properness stability and closed-range APIs.

## New nodes

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
