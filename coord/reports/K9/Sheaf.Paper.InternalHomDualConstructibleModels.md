## What changed

Filled the proofs of `scalarDualDifferential_laws`, `scalarModules_additive`, and
`realization_additive` in `Sheaf.Paper.InternalHomDualConstructibleModels`.
The scalar dual now has a proved shape law and square-zero law: reversed indices
preserve adjacency, and precomposition by the original two differentials vanishes.
The scalar module functor preserves sums definitionally. The composite point/scheme
inverse-image adjunction supplies finite-colimit preservation, hence additivity of
inverse image through binary biproducts. Each lifted module functor
preserves sums on its underlying morphisms; their composition with extension of scalars
is additive. Removed private proof imports unused by the three auxiliary proofs.
No statement, definition, attribute, or public import was changed.

## Proved and sorry left

Closed three of the four original holes:

- `AlgebraicGeometry.ProEtale.InternalHomDualModels.scalarDualDifferential_laws`.
- `AlgebraicGeometry.ProEtale.InternalHomDualModels.scalarModules_additive`.
- `AlgebraicGeometry.ProEtale.InternalHomDualModels.realization_additive`.

One original hole remains, with no new holes:
`AlgebraicGeometry.ProEtale.InternalHomDualModels.internalHomDual_constructible_models`
(blueprint: `lem-sfb-internal-hom-dual-constructible-models`). Its statement and full
natural-language proof remain unchanged. This is a partial proof delivery, not a
completion or decomposition of the main constructibility theorem.

## No longer needed

The following private proof imports are unused by the completed auxiliary proofs and
were removed. The unfinished main theorem keeps its original DAG proof plan; these
removals do not claim that all of its planned mathematical dependencies are unnecessary.
No node or module is withdrawn. `Mathlib.LinearAlgebra.Dual.Lemmas` remains for the
scalar linear dual API. All public imports are preserved.

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`.
- `Sheaf.Paper.FiniteDiscreteCondensedRing`.
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`.
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`.
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`.
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso`.
- `WeilConjectures.Algebra.Homology.HomComplex`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement`.
- `Mathlib.LinearAlgebra.Basis.VectorSpace`.
- `Mathlib.RingTheory.Noetherian.Basic`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
- `Mathlib.RingTheory.Finiteness.Basic`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent`.
- `Sheaf.Paper.CartesianCoefficients`.

## Where the brief, the DAG or earlier work was wrong

No statement error was required to close the auxiliary holes. The main theorem's
remaining assembly involves representation comparisons: `ScalarPerfectDualRealization`
uses sectionwise sheaf modules and a total-Hom scalar dual; the item uses internal
module objects and a direct signed scalar dual. `LocalModelCohomologyDescent` uses
internal modules over the actual scalar section ring instead of `ModuleCat A`.
Those interfaces cannot be applied by direct definitional conversion. Their bridge
and the main theorem are not claimed proved in this delivery. The existing private
`FiniteConstantModelResolution.scalarModules_additive` already gives the elementary
argument now used for the public auxiliary theorem.

An additional dependency-record detail for the next worker: the primary attachment of
`lem-weil-pbc-ringed-internal-hom-exact-restriction` is currently
`RingedHomUniverses.rightShift_existsUnique`, which supplies normalized target shifts,
not itself the slice-restriction isomorphism used by Step 3. The reexported restriction
API must be located and specialized rather than applying that primary declaration.

Validation: the remote delivery probe compiled all 24 declarations in 6.2 seconds,
with only the main theorem reported as using `sorry` directly. The final line-wrap
correction is checked again by the delivery command.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
