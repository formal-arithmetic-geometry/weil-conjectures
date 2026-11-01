/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Fixed.FiniteScalarFixedTensorData
public import WeilConjectures.SixFunctors.Supporting.Tensor.RepresentativeTensorCube
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalRealization
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRepresentativeNormalization

/-! # The specified scalar tensor representative data

Source: Stacks Tags 04VK and 07A4.
(blueprint: def-sf-finite-scalar-tensor-representative-data).
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
  finiteScalarFixedTensorDataForCoefficients

/-- Package the actual scalar realization and its already stated representative law.
Every functor and map is the specified construction, and only the compatibility
proof comes from the existing representative theorem. No witness is selected.
Source: Stacks Tags 04VK and 07A4.
(blueprint: def-sf-finite-scalar-tensor-representative-data). -/
noncomputable def finiteScalarTensorRepresentativeData
    (R : Type u) [CommRing R] [Finite R] (T : Scheme.{u})
    (a : ProEtaleTensorModel T (proEtaleConstantRing T R)) :
    ScalarTensorRepresentativeData
      (CochainComplex (Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
      (CochainComplex (proEtaleRingModules T (proEtaleConstantRing T R)) ℤ)
      (DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))))
      (DerivedCategory (proEtaleRingModules T (proEtaleConstantRing T R))) where
  toTensorFixedRepresentativeData := finiteScalarFixedTensorDataForCoefficients
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) T
    (finiteScalarFlatRepresentatives T R) (finiteScalarFlatRepresentatives_kFlat T R)
  q' := DerivedCategory.Q
  U := (sfIntrinsicModuleEquivalence T R).functor.mapHomologicalComplex (.up ℤ)
  E := (sfIntrinsicDerivedEquivalence T R).functor
  e := (sfIntrinsicModuleEquivalence T R).functor.mapDerivedCategoryFactors
  P' := proEtaleFlatRepresentatives T (proEtaleConstantRing T R)
  preserves := finiteScalarPreservesRepresentatives T R
  t' := uncurry.obj ((proEtaleOrdinaryTensor T (proEtaleConstantRing T R)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  T' := a.tensor
  r' := a.representative
  b := finiteScalarRepresentativeTotalRealization R T
  tau := finiteScalarTensorRealization T R a
  normalization := finiteScalarTensorRepresentativeData_normalization R a

end WeilConjectures
