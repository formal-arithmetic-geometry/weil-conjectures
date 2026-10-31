/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTensorIso
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalRealization
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorSharedRepresentativeEquation

/-! # Scalar tensor representative normalization on the shared functors

Source: Stacks Tags 04VK and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-representative-data-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
-- Share the already proved coefficient-instance shortcuts used by the canonical map.
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

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

attribute [local irreducible] SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleCanonicalTensorComparison
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

/-- The specified representative equation in the shared total-functor coordinates.
Source: Stacks Tags 04VK and 07A4.
(blueprint: lem-sf-finite-scalar-tensor-representative-data-normalization).

Proof: start with finiteScalarTensorSharedRepresentative_normalization for the
shared representative and total object. Substitute the ordinary realization
wrapper and its component equation, then unfold finiteScalarTotalTensorIso.
The two ordinary total maps are then identical. -/
theorem finiteScalarTensorRepresentativeData_normalization
    (R : Type u) [CommRing R] [Finite R]
    {Y : Scheme.{u}}
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R))
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (hP : finiteScalarFlatRepresentatives Y R P)
    (hQ : finiteScalarFlatRepresentatives Y R Q) :
    (sfIntrinsicDerivedEquivalence Y R).functor.map
        ((finiteScalarRepresentativeTensorIso
          (ModuleCat.{u + 1} (ULift.{u + 1} R)) Y
          (finiteScalarFlatRepresentatives Y R)
          (finiteScalarFlatRepresentatives_kFlat Y R)).hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) ≫
      ((finiteScalarTensorRealization Y R aY).hom.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q) ≫
      aY.tensor.map (Prod.mkHom
        ((sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app P)
        ((sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app Q)) =
    (sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app
        ((finiteScalarRepresentativeTotalTensor
          (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R)))).obj (P, Q)) ≫
      DerivedCategory.Q.map
        ((finiteScalarRepresentativeTotalRealization R Y).app (P, Q)) ≫
      aY.representative.hom.app
        (⟨((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj P, finiteScalarPreservesRepresentatives Y R P hP⟩,
         ⟨((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj Q, finiteScalarPreservesRepresentatives Y R Q hQ⟩) := by
  simpa only [finiteScalarRepresentativeTotalRealization,
    finiteScalarRepresentativeTotalRealizationForFunctor_app, finiteScalarTotalTensorIso] using
      finiteScalarTensorSharedRepresentative_normalization R aY P Q hP hQ

end WeilConjectures
