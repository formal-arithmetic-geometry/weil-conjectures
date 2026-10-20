## What changed

Proved the bounded/unbounded exchange comparison by compatibility of the canonical
right-derived comparison with the derived adjunction units and counits. Localization
extensionality and the unit factorization formulas identify the units; the adjunction
bijection and triangle identities identify the counits. The exact derived square
comparison restricts to its bounded counterpart, so the two mates agree.

The argument is proved privately for arbitrary suitable abelian coefficient categories,
which also supplies the module-coefficient comparison needed in degree zero. The existing
`Functor.rightDerivedBaseChange_zero_unit` supplies the degree-zero normalization.
An explicit unit-characterization proof identifies the generic bounded base change with
the etale bounded exchange before applying this theorem; an explicit homology-inclusion
identity prevents unfolding the derived constructions at the final normalization step.
Naturality transports its fixed homology comparisons to `exchangeSourceZeroIso` and
`exchangeTargetZeroIso`. The existing module/abelian underived-exchange theorem then
proves the coefficient compatibility clause.

Public statements and endpoint definitions are unchanged. All auxiliary lemmas are private
and proved in the item module. No other Lean module is changed. The node's proof,
proof dependencies, and proof origin now describe this route; obsolete tool approvals
are removed. The Kunneth unit's statements and proof steps remain in place.

The import-surface change and its consumer checks are recorded in
`coord/changes/K7-unbounded-exchange-agrees-proof-route.md`.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap_agrees_plus`.
- `AlgebraicGeometry.Etale.exactDerivedBaseChangeMap_homology_zero` (both conjuncts).

Holes closed: 2. Holes added: 0. Split off: 0. Remaining `sorry`: none in the delivery.
No axiom or data definition is added.

Validation: the complete module compiled through `lcompile.py` in 19.1 seconds,
including `#print axioms` for both public theorems, with no warnings. Both report
exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Public
signature and endpoint-definition comparisons against the original source pass.
Explicit functor arguments and comparison lemmas avoid unfolding derived descent
while checking the final normalization. All four direct importers also compile
unchanged against this item and its pruned imports through `lcompile.py --all`;
no consumer adaptations are required. The temporary consumer copies were removed
before delivery.

## No longer needed

The canonical derived-unit argument replaces the explicit common injective-resolution
construction. No extra resolution, K-injective Hom computation, or separate module-linear
exchange construction is needed here. The generic exact-functor and adjunction APIs
already provide those underlying constructions. The degree-zero calculation reuses the
proved generic theorem rather than reconstructing its augmentation proof.

Removed direct imports (a redundant import may remain available transitively):

- `Mathlib`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`.
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
- `WeilConjectures.SixFunctors.BaseChange.Square`.
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

Removed direct proof dependencies:

- `lem-weil-pbc-module-sheaves-enough-injectives`.
- `lem-weil-pbc-dplus-injective-representative`.
- `lem-weil-pbc-kinjective-total-derived`.
- `lem-weil-pbc-kinjective-hom-derived`.
- `prop-weil-pbc-kinjective-resolutions-exist`.
- `prop-weil-pbc-inverse-image-modules-exact`.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`.
- `lem-pc-derived-adjoint-functors`.
- `def-weil-pbc-bounded-derived-subcategories`.
- `lem-weil-pbc-exact-functor-derived-functor`.
- `def-weil-pbc-derived-square-iso`.
- `lem-weil-pbc-left-exact-injective-resolution-degree-zero`.
- `lem-weil-pbc-exact-functor-complex-cohomology`.
- `lem-weil-pbc-module-direct-image-left-exact`.
- `lem-weil-pbc-underived-exchange-module-linear`.

The unchanged statement dependencies are retained. This is pruning this item's route,
not a request to withdraw source-library declarations or modules used elsewhere.

Removed obsolete entries from the node's `tool_uses` approvals:

- `lem-weil-pbc-module-sheaves-enough-injectives`.
- `lem-weil-pbc-kinjective-total-derived`.
- `lem-pc-derived-adjoint-functors`.
- `lem-weil-pbc-module-direct-image-left-exact`.
- `prop-weil-pbc-kinjective-resolutions-exist`.
- `lem-weil-pbc-exact-functor-derived-functor`.

## Where the brief, the DAG or earlier work was wrong

No statement repair was required. The node and existing theorem docstrings describe a
longer resolution-based proof; the formal proof instead uses the canonical comparison's
universal property and the existing degree-zero base-change theorem. Factoring the mate
calculation over arbitrary abelian categories avoids expensive elaboration after
specialization to etale sheaves. No definition was altered to obtain the compile bound.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
