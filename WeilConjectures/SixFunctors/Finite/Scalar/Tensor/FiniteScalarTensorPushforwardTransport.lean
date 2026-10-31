/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison

/-! # Constant-ring direct-image identification on sections

Source: Stacks Tags 00YV and 03EL.
(blueprint: lem-sf-finite-scalar-tensor-pushforward-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
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
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  CategoryTheory.Functor.leftAdjoint
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.presheafToSheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
  AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization
  AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
  AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage
  AlgebraicGeometry.ProEtale.lowerStar
  CategoryTheory.Functor.sheafPushforwardContinuous
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures

/-- Identifying the two constant-ring direct images acts as the identity on sections.
Source: Stacks Tag 00YV, functoriality of module objects.
(blueprint: lem-sf-finite-scalar-tensor-pushforward-transport).

Proof: forget to presheaves of abelian groups. Mapping the equality isomorphism
through this forgetful functor gives the equality morphism between identical
presheaves, hence the identity. Evaluate that identity at the section. -/
theorem finiteScalarTensorPushforward_transport (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : proEtaleRingModules X (proEtaleConstantRing X R)) (W : Y.ProEtᵒᵖ)
    (m : M.val.obj ((proEtaleBaseChange p).op.obj W)) :
    (((eqToIso (finiteScalarConstantPushforward_eq R p)).inv.app M).val.app W) m = m := by
  let A := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y R)
  let U := SheafOfModules.forget A ⋙ PresheafOfModules.toPresheaf A.obj
  have h : U.map ((eqToIso (finiteScalarConstantPushforward_eq R p)).inv.app M) = 𝟙 _ := by
    rw [eqToIso.inv, eqToHom_app, eqToHom_map]
    rfl
  have hh := congrArg (fun f ↦ f.app W) h
  exact congrArg (fun f ↦ f.hom m) hh

end WeilConjectures
