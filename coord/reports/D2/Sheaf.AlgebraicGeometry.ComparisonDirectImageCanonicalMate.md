## What changed

Completed the two proofs in `Sheaf.AlgebraicGeometry.ComparisonDirectImageCanonicalMate` without changing any declaration signature, construction, docstring, or import interface.

`isIso_comparisonDirectImageCanonicalMate` applies the already proved `isIso_comparisonDirectImagePlus` to the definitionally identical canonical transformation. `comparisonDirectImageCanonicalMate_fac` applies `Functor.rightDerivedFunctorPlusBaseChange_fac` to its defining underived comparison. The remote single-file compiler accepts both proofs (exit 0, 3.2 seconds).

## Proved and sorry left

Closed 2 holes:

- `AlgebraicGeometry.ProEtale.isIso_comparisonDirectImageCanonicalMate`.
- `AlgebraicGeometry.ProEtale.comparisonDirectImageCanonicalMate_fac`.

No holes remain in the assigned module. No holes or split-off statements were added. The definition of `comparisonDirectImageCanonicalMate` is unchanged.

## No longer needed

No imports added or removed: the existing imports are public and are retained as the established interface for consumers. No extra proof dependencies, continuity lemmas, resolution arguments, or new modules are needed. Invertibility is already the theorem of `Sheaf.AlgebraicGeometry.ComparisonDirectImage`; normalization is already the universal-property equation of `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`.

No DAG nodes or modules are claimed pruned: the canonical-mate node is now attached to `FixedComparisonDirectImageMate`, whose full counit-mate calculation remains relevant to its own statement and consumers.

## Where the brief, the DAG or earlier work was wrong

The brief identifies this module through the blueprint tag `lem-weil-pbc-comparison-direct-image-canonical-mate`, but that node's current Lean attachment is `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`. Consequently no node currently has `lean.module` equal to the assigned module. This delivery closes the two existing holes in the assigned compatibility API and does not overwrite the current node attachment or the full counit-mate proof route. Its existing first proof step already describes the invertibility argument reused here; the assigned unit-normalization theorem is exactly the generic derived-base-change factorization.

Searches through the supplied leanfinder, loogle and grep wrappers found no more specific Mathlib result. Reading the project library found both exact results above. No statement or definition repair, forced consumer adaptation, or new node was necessary.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
