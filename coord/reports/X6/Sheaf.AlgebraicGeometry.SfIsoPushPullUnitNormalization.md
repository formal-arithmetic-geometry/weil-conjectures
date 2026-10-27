## What changed

Filled `AlgebraicGeometry.Etale.SfP1Transport.unit_comp_pushPull` without changing its
statement or the definition of `pushPull`. Proved private helpers normalize homotopy representatives, ordinary
cancellation, and its exact derived counterpart. Generic homotopy and derived
calculations avoid unfolding geometric functors during proof checking. The final proof expands the actual
comparison maps and cancels adjacent inverse comparisons. Updated the item node to this route.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Etale.SfP1Transport.unit_comp_pushPull`
(node `lem-sf-iso-pushpull-unit-normalization`). All five private helpers are proved.
Original holes closed: 1 of 1. Holes added: 0. Sorries left in the delivery: none.

Validation: the clean single-file server compile passed in 35.2 seconds. A temporary
`#print axioms AlgebraicGeometry.Etale.SfP1Transport.unit_comp_pushPull` reported only
`propext`, `Classical.choice`, and `Quot.sound`; the diagnostic command was then removed.
The public theorem signature and public imports are unchanged. No shared definition was
changed and no importer adaptation is needed.

## No longer needed

The proof does not need these former proof dependencies or their private imports:

- `prop-weil-pbc-inverse-image-modules-exact` / `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  native exactness instances and native ModuleCat-valued sheaf adjunctions suffice.
- `lem-weil-pbc-inverse-image-composition-module-linear` /
  `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`: the native composition
  unit equation already applies to ModuleCat-valued sheaves.
- `lem-weil-pbc-exact-functor-derived-functor` /
  `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`: use the existing exact comparison API.
- `lem-sp-exact-derived-transformation-pasting` /
  `Sheaf.CategoryTheory.ExactDerivedTransformationPasting`: normalize the finite composite
  directly using the proved source-library factorization equations.
- `lem-sfb-derived-adjunction-cochain-unit` /
  `Sheaf.CategoryTheory.DerivedAdjunctionCochainUnit`: the source's levelwise derived
  adjunction unit formula is already normalized on homotopy complexes.
- `lem-sfb-resolving-derived-adjunction-normalization` /
  `Sheaf.SixFunctors.ResolvingDerivedAdjunction`: transport of the actual derived adjunction
  is the definition of `mapDerivedCategoryAdjunction`.

Removed the redundant direct private imports of `Mathlib.CategoryTheory.Adjunction.Mates`
and `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; their needed API is provided by
the retained statement imports and the source derived-comparison import. Removed the six
obsolete tool approvals listed above from the item node. These dependencies are unnecessary
for this proof; no claim is made about their other consumers, and no module is withdrawn.

The item import closure also drops these indirect dependencies, for nine modules removed
from this item's closure in total:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinearCore`
  (`lem-weil-pbc-inverse-image-composition-module-linear-core`).
- `Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition`
  (`lem-pur-exact-restriction-composition`).
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`.

These files are retained in the adopted library. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned lifting through variable-ring module sheaves is unnecessary for the actual
statement, whose category is native sheaves valued in `ModuleCat A`. The native composition
and identity unit lemmas already specialize to these coefficients. The resolving-class
argument is likewise replaced by the existing normalized levelwise derived-adjunction API.
The statement and the unit route are preserved. The proof applies also to identity
isomorphisms, automorphisms, empty schemes, the zero ring, and arbitrary unbounded complexes;
it uses no nonempty, nonzero, boundedness, properness, or base-change premise.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
