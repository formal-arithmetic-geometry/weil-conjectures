/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPushforwardTransport

/-! # Scalar inverse mate preserves pullback unit sections

Source: Stacks Tags 00YV and 03EL.
(blueprint: lem-sf-finite-scalar-tensor-pullback-mate-unit).
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

private theorem realizationUnit_map (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    {M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} R))}
    (f : M ⟶ N) (W : T.ProEtᵒᵖ) (m : M.obj.obj W) :
    ((sfIntrinsicModuleEquivalence T R).functor.map f).val.app W
        (sfIntrinsicRealizationUnit T R M W m) =
      sfIntrinsicRealizationUnit T R N W (f.hom.app W m) := by
  exact (congrArg (fun z ↦ z.app W m)
    ((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (ProEtale.finiteCoefficientIntrinsicScalarMap T R)).unit.naturality
        ((ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} R)).map
          f.hom))).symm

private theorem directComparison_inv_unit (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
    (W : Y.ProEtᵒᵖ) (m : M.obj.obj ((proEtaleBaseChange p).op.obj W)) :
    ((sfIntrinsicDirectImageComparison p R).inv.app M).val.app W
      (sfIntrinsicRealizationUnit Y R
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj M) W m) =
      sfIntrinsicRealizationUnit X R M ((proEtaleBaseChange p).op.obj W) m := by
  have hd := (sfIntrinsicDirectImageComparison_existsUnique p R).exists.choose_spec M W m
  have hi := congrArg (fun z ↦ z.val.app W
    (sfIntrinsicRealizationUnit X R M ((proEtaleBaseChange p).op.obj W) m))
      ((sfIntrinsicDirectImageComparison p R).hom_inv_id_app M)
  change ((sfIntrinsicDirectImageComparison p R).inv.app M).val.app W
    (((sfIntrinsicDirectImageComparison p R).hom.app M).val.app W _) = _ at hi
  change ((sfIntrinsicDirectImageComparison p R).hom.app M).val.app W _ = _ at hd
  rw [hd] at hi
  exact hi

set_option maxHeartbeats 500000 in
-- Compare the two section models in the inverse-mate unit equation.
/-- The scalar inverse mate preserves the pullback adjunction units on scalar sections.
Source: Stacks Tags 00YV and 07A6, uniqueness of inverse image.
(blueprint: lem-sf-finite-scalar-tensor-pullback-mate-unit).

Proof: use the unit equation of the inverse mate defining the comparison. The
scalar realization unit is natural. The right-adjoint comparison preserves these
units by its defining normalization, and identifying the two constant-ring direct
images acts identically on sections. Evaluating the mate unit equation and
substituting these two identities gives the assertion. -/
theorem finiteScalarTensorPullback_mate_unit (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R)))
    (W : Y.ProEtᵒᵖ) (m : M.obj.obj W) :
    ((finiteScalarOrdinaryPullbackComparison R p).hom.app M).val.app
        ((proEtaleBaseChange p).op.obj W)
        (((proEtaleRingModuleAdjunction p (proEtaleConstantRing Y R)
          (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).unit.app
            ((sfIntrinsicModuleEquivalence Y R).functor.obj M)).val.app W
              (sfIntrinsicRealizationUnit Y R M W m)) =
      sfIntrinsicRealizationUnit X R
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj M)
        ((proEtaleBaseChange p).op.obj W)
        (((ProEtale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).unit.app M).hom.app W m) := by
  let a := ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let b := proEtaleRingModuleAdjunction p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
  let r := (sfIntrinsicDirectImageComparison p R).symm ≪≫
    isoWhiskerLeft (sfIntrinsicModuleEquivalence X R).functor
      (eqToIso (finiteScalarConstantPushforward_eq R p)).symm
  have hm := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ r.hom) M
  have hc : ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ r.hom)).natTrans =
      (finiteScalarOrdinaryPullbackComparison R p).hom := by
    unfold finiteScalarOrdinaryPullbackComparison
    rfl
  change (sfIntrinsicModuleEquivalence Y R).functor.map (a.unit.app M) ≫
      r.hom.app _ = b.unit.app _ ≫ _ at hm
  change (sfIntrinsicModuleEquivalence Y R).functor.map (a.unit.app M) ≫
      r.hom.app _ = b.unit.app _ ≫
      (proEtaleConstantRingPushforward R p).map
        (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ r.hom)).natTrans.app M) at hm
  rw [hc] at hm
  have h := congrArg (fun z ↦ z.val.app W (sfIntrinsicRealizationUnit Y R M W m)) hm
  change _ = ((finiteScalarOrdinaryPullbackComparison R p).hom.app M).val.app
    ((proEtaleBaseChange p).op.obj W) _ at h
  change (r.hom.app _).val.app W
    (((sfIntrinsicModuleEquivalence Y R).functor.map (a.unit.app M)).val.app W
      (sfIntrinsicRealizationUnit Y R M W m)) = _ at h
  have hmap := realizationUnit_map Y R (a.unit.app M) W m
  have hh := congrArg ((r.hom.app _).val.app W) hmap
  have h : (r.hom.app _).val.app W
      (sfIntrinsicRealizationUnit Y R
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj
          ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj M)) W
            ((a.unit.app M).hom.app W m)) =
      ((finiteScalarOrdinaryPullbackComparison R p).hom.app M).val.app
        ((proEtaleBaseChange p).op.obj W)
          (((b.unit.app ((sfIntrinsicModuleEquivalence Y R).functor.obj M)).val.app W)
            (sfIntrinsicRealizationUnit Y R M W m)) := hh.symm.trans h
  have hr (K : Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} R))) :
      r.hom.app K = (sfIntrinsicDirectImageComparison p R).inv.app K ≫
        (eqToIso (finiteScalarConstantPushforward_eq R p)).inv.app
          ((sfIntrinsicModuleEquivalence X R).functor.obj K) := rfl
  rw [hr] at h
  dsimp only [SheafOfModules.comp_val, PresheafOfModules.comp_app] at h
  change (((eqToIso (finiteScalarConstantPushforward_eq R p)).inv.app _).val.app W)
    (((sfIntrinsicDirectImageComparison p R).inv.app _).val.app W _) = _ at h
  have ht := finiteScalarTensorPushforward_transport R p _ W
    (((sfIntrinsicDirectImageComparison p R).inv.app _).val.app W
      (sfIntrinsicRealizationUnit Y R _ W ((a.unit.app M).hom.app W m)))
  exact h.symm.trans (ht.trans
    (directComparison_inv_unit R p _ W ((a.unit.app M).hom.app W m)))

end WeilConjectures
