## What changed

Proved `AlgebraicGeometry.Etale.derivedOpenImmersionFullyFaithful` with its existing
signature and visibility. The first conjunct composes the source library's
`rightDerivedFunctorCompMapDerivedCategoryIso`, the derived natural isomorphism of the
open-immersion counit, the exact identity comparison, and `mapDerivedCategoryIdIso`.
The second conjunct applies sheaf-level disjoint-support vanishing to every homology
object and transports zero along `mapDerivedCategoryCompIso`.

Only the item module and its node's proof metadata change. Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`.
All public imports and declaration signatures remain unchanged; no consumer adaptations
or definition/statement change records are needed. The unit's statement and route are kept.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.derivedOpenImmersionFullyFaithful`
(node `lem-exc-open-fully-faithful`). No holes added, split off, or left in the delivery.
The proof compiles against the published library. Delivery preflight checks its axioms.
Both empty-open and empty-complement cases are covered by the existing sheaf-level
counit and disjoint-range theorems without any nonemptiness hypothesis.

## No longer needed

Removed proof imports:
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`;
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`;
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` as a direct
  import (it is provided by the exact-composition API import);
- both duplicate imports of `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`
  (exactness instances already come from the public functor interface);
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective` as redundant direct imports.

The item no longer needs the separately stated nodes
`lem-weil-pbc-kinjective-total-derived`, `prop-weil-pbc-kinjective-resolutions-exist`,
`lem-weil-pbc-right-adjoint-preserves-kinjective`, or
`lem-weil-pbc-kinjective-hom-derived` as proof dependencies. The generic comparison
already proves the required computation and naturality using the canonical
K-injective infrastructure. In particular, it needs no preservation-of-K-injectives
hypothesis on direct image when the functor applied afterward is exact.
Removed the three corresponding obsolete entries from the node's top-level
`tool_uses` (the Hom node had no such entry). This is pruning for this item's proof;
other users may still need those nodes or modules.

## Where the brief, the DAG or earlier work was wrong

The planned explicit resolution, Hom identification, and preservation-of-K-injectives
argument is unnecessary because the source library already has a fully proved
composition comparison with an exact functor. No mathematical statement was false,
and no target, definition, or theorem signature was changed. The second conclusion
can be checked on homology, avoiding a separate zero-complex construction.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
