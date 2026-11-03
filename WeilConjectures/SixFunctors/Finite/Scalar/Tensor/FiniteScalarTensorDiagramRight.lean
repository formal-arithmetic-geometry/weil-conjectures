/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorSummandDiagram
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackRightSummand

/-! Use the right composite injection formula, proved by naturality and totalization.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-diagram-right).
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
attribute [local implicit_reducible] finiteScalarTensorSummandDiagram
  finiteScalarTensorNativeChainDiagram finiteScalarTensorNativeLeftPaths
  finiteScalarTensorNativeRightPath

/-- Use the right composite injection formula, proved by naturality and totalization.
Source: Stacks Tag 07A4, constituents of total tensor comparison.
(blueprint: lem-sf-finite-scalar-tensor-diagram-right).

Proof: unfold the diagram's corresponding fields. Use the right composite injection formula, proved
by naturality and totalization. The diagram introduces
no new maps, so its field equation is precisely that existing native formula. -/
theorem finiteScalarTensorDiagram_right
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    let D := finiteScalarTensorSummandDiagram R p P Q a b n h
    D.j0 ≫ D.right = D.ordinaryRight ≫ D.j3 := by
  dsimp only
  exact finiteScalarTensorPullback_right_summand R p P Q a b n h

end WeilConjectures
