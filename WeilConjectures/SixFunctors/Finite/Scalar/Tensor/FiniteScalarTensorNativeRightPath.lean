/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalRealization

/-! The native right scalar tensor chain path.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: def-sf-finite-scalar-tensor-native-right-path).
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

/-- The existing right scalar tensor chain path, named before taking degree components.
Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: def-sf-finite-scalar-tensor-native-right-path).
This is the original three-factor chain-map composite, with no new data chosen. -/
def finiteScalarTensorNativeRightPath
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :=
  (finiteScalarComplexPullbackComparison R p).inv.app
      ((finiteScalarRepresentativeTotalTensor
        (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R)))).obj (P, Q)) ≫
    ((proEtaleRingModulePullback p (proEtaleConstantRing Y R)
      (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).mapHomologicalComplex
      (.up ℤ)).map ((finiteScalarRepresentativeTotalRealization R Y).app (P, Q)) ≫
    (finiteScalarIntrinsicComplexTensorPullback R p).app
      (((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ)).obj P,
       ((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ)).obj Q)

end WeilConjectures
