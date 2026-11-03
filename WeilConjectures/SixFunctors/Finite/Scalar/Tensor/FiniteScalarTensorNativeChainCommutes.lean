/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorNativeChainDiagram
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorDiagramCommutes

/-! The native scalar tensor chain diagram commutes.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-native-chain-commutes).
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

attribute [local implicit_reducible] finiteScalarTensorNativeChainDiagram
  finiteScalarTensorSummandDiagram
attribute [local irreducible] finiteScalarTensorNativeLeftPaths finiteScalarTensorNativeRightPath

/-- The actual native scalar tensor chain diagram commutes.
Source: Stacks Tag 07A4, constituents of the signed total tensor comparison.
(blueprint: lem-sf-finite-scalar-tensor-native-chain-commutes).

Proof: test equality of chain maps in every degree and then on every mapped coproduct
injection. The commutative native summand diagram gives precisely this equality on
injections. Its edges are the degree components of the chain diagram's edges, so the
pasting calculation applies without changing any native tensor or pullback map. -/
theorem finiteScalarTensorNativeChain_commutes
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    let G := finiteScalarTensorNativeChainDiagram R p P Q
    G.l1 ≫ G.l2 ≫ G.l3 = G.right := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p ⋙
      (sfIntrinsicModuleEquivalence X R).functor)
  intro a b h
  exact finiteScalarTensorDiagram_commutes R p P Q a b n h

end WeilConjectures
