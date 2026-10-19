## What changed

Completed the four theorem proofs in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage` without changing any
statement, definition, instance attribute, universe, or coefficient hypothesis.

* `finiteCoefficientPullbackSections_naturality`: extensionality on scalar sections
  and continuous functions, followed by connected-component representatives and the
  first-projection equation for the base-change pullback lift.
* `finiteCoefficientModuleDirectImage_additive`: the additive functor structure is
  sectionwise definitional equality, including the unchanged restriction of scalars.
* `finiteCoefficientModules_hasKInjectiveResolutions`: apply the existing
  `SheafOfModules.isGrothendieckAbelianOfUniverses` in site universes u+1/u and
  ring/module universe u+1, then use the existing Grothendieck K-injective instance.
* `finiteCoefficientRealization_isEquivalence`: specialize the already proved
  `finiteCoefficientRealization_isEquivalence_ring` to the commutative coefficient ring.

Added the proof-only import
`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`. The import-direction
check accepts it. Both retained public imports supply all the removed public imports
transitively, so the public import closure is unchanged. No consumers need adaptation.
No new intermediate theorem or module was introduced.

Recorded the redundant public import removals and every transitive consumer in
`coord/changes/F7-finite-coefficient-direct-image-imports.md`. A fresh server compile
completed without errors or warnings in 3.4 seconds. The first resumed dry run
required this import change record; no proof or signature repair was requested.

## Proved and sorry left

Closed all four original holes, by declaration name:

* `AlgebraicGeometry.ProEtale.finiteCoefficientPullbackSections_naturality`
* `AlgebraicGeometry.ProEtale.finiteCoefficientModuleDirectImage_additive`
* `AlgebraicGeometry.ProEtale.finiteCoefficientModules_hasKInjectiveResolutions`
* `AlgebraicGeometry.ProEtale.finiteCoefficientRealization_isEquivalence`

Zero holes remain in the item. Zero holes were added or split off.
The realization proof reuses the existing ring-general equivalence, rather than
introducing another scalar-extension argument. The statements cover the empty scheme
and zero ring without additional hypotheses; the sectionwise and Grothendieck arguments
make no nonemptiness or nontriviality assumption.

## No longer needed

Removed redundant direct imports (all remain publicly reexported through the retained
imports, so this does not prune any module from the public closure):

* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
  (including its duplicate import line)
* `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
* `Mathlib.CategoryTheory.Adjunction.Additive`
* `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`
* `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`
* `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`
* `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous`
* `Mathlib.CategoryTheory.Triangulated.Subcategory`

No DAG node or module is made unreachable. The unit route is unchanged. In particular,
no arbitrary-ring operations, adjunctions, or derived functors were replaced.

## Where the brief, the DAG or earlier work was wrong

The inherited sandbox had no report and did not compile. Its naturality proof needed
an explicit continuous-map extensionality step and the pullback projection equation;
its additive proof supplied a zero-map field that the Additive structure does not have;
and its Grothendieck proof referred to an unavailable small-universe theorem.
The existing independent-universe Grothendieck theorem repairs that last issue directly.

The item docstrings cite `def-weil-pbc-proetale-operations`, but the current node's Lean
attachment is to `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, and no current
node has this item's module as its lean.module. Its current proof text concerns those
other operations, so it has not been overwritten with these four local proof details.
The existing `lem-weil-pbc-ring-sheaves-grothendieck` and finite-coefficient realization
interfaces already supply the needed substantive results. No new node is needed.
Searches used the dispatcher's recorded LeanFinder and Loogle results, the required
msearch grep query, and direct rg searches of the project and Mathlib.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
