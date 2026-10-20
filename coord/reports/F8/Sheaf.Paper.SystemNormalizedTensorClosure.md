## What changed

Filled `WeilConjectures.SemilinearSections.normalized_inverseImage_closure`.
The proof obtains the actual `PullTransitionFormula` from the geometric calculus,
uses it to identify the inverse-image reduction with the image of the original
reduction, and derives invertibility by `IsIso.of_isIso_fac_right`. It retains the
pull transition formula and the target system's reduction cocycle. The existing
`normalized_tensor_closure` proof was left unchanged. No imports were added or
removed.

## Proved and sorry left

Closed the sole sorry in the item: `normalized_inverseImage_closure`.
No sorry remains in this module and no new sorry was added.

## No longer needed

None. The proof uses `Sheaf.Paper.SemilinearDerivedSections` for the geometric
calculus and `Sheaf.Paper.SystemTensorReductionFormula` for the tensor theorem
already present in the module. No DAG proof dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

Nothing found. The inverse-image proof plan is realized directly by the supplied
pull transition formula and the reduction cocycle field.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
