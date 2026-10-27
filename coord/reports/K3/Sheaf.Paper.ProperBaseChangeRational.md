## What changed

Proved the four coefficient and preservation declarations in `Sheaf.Paper.ProperBaseChangeRational`. The localization comparison uses the existing localized direct image theorem; finite and algebraic-closure coefficient comparisons use existing derived push comparison instances; rational bounded-constructible preservation uses the existing finiteness-coefficient preservation interface. Exploratory proof-only files were removed.

## Proved and sorry left

Proved: `isIso_rationalizationPushHom_boundedBelow`, `isIso_finiteCoefficientPushHom_boundedBelow`, `isIso_algClCoefficientPushHom_boundedBelow`, and `properPushforward_boundedConstructible_rational`.

Sorry left: `isIso_properProjectionMap_boundedConstructible_rational` and `isIso_properBaseChange_boundedConstructible_rational`, with existing statements and DAG nodes. No new sorry was added.

## No longer needed

Removed proof-only imports (their projection/exchange plans remain attached to the two open declarations):

- `Sheaf.Paper.CartesianCoefficientsFiniteFree`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`
- `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`
- `Mathlib.CategoryTheory.Monoidal.Mod`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `WeilConjectures.Algebra.Homology.FilteredColimitsTensor`
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Sheaf.Paper.CompletedCondensedCoefficients`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `Sheaf.Paper.CoefficientHeartTriangulated`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.Paper.CartesianCoefficients`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Sheaf.Paper.IntegralModelsOperations`
- `Sheaf.CategoryTheory.Adjunction.CoefficientExchange`
- `Mathlib.CategoryTheory.Shift.Adjunction`
- `Mathlib.CategoryTheory.Triangulated.Adjunction`
- `Mathlib.CategoryTheory.Shift.CommShift`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`
- `Sheaf.Paper.CondensedModuleDerivedPushpull`
- `Sheaf.Paper.IntegralProperBaseChange`
- `Sheaf.SixFunctors.IntegralModelsGenerators`
- `Sheaf.SixFunctors.ScalarSixPullback`

No module is withdrawn: the two retained formula declarations still need their existing proof plans. The four proved clauses use shorter existing comparison and preservation interfaces. Public imports are unchanged.

## Where the brief, the DAG or earlier work was wrong

The assigned module has six separate holes. Four admit existing library proofs. The two formula proofs remain open; exploratory coefficient-isomorphism reflection and naturality helpers compiled, but their concrete integral-model specializations did not compile within the per-file limit. This is an incomplete proof, not a false statement or a tool failure. No replacement hypothesis or weakened conclusion was used.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
