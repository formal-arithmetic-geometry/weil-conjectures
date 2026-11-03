/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalRealization
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarComplexTensorPullback

/-! The three native left scalar tensor chain maps.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: def-sf-finite-scalar-tensor-native-left-paths).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat
attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive
attribute [local irreducible] sfIntrinsicModuleEquivalence
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

/-- The three actual left scalar tensor chain maps, named before degree projection.
Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: def-sf-finite-scalar-tensor-native-left-paths).
The tuple consists of the realized fixed tensor pullback, total realization after fixed
pullback, and the total tensor map of the scalar comparisons. All maps are explicit. -/
def finiteScalarTensorNativeLeftPaths
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :=
  (((sfIntrinsicModuleEquivalence X R).functor.mapHomologicalComplex (.up ℤ)).map
      ((finiteScalarFixedComplexTensorPullbackForCoefficients
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).app (P, Q)),
   ((finiteScalarRepresentativeTotalRealization R X).app
      (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
        (.up ℤ)).obj P,
       ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
        (.up ℤ)).obj Q),
    (uncurry.obj
      ((proEtaleOrdinaryTensor X (proEtaleConstantRing X R)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ))).map
      (Prod.mkHom ((finiteScalarComplexPullbackComparison R p).inv.app P)
        ((finiteScalarComplexPullbackComparison R p).inv.app Q))))

end WeilConjectures
