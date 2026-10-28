/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionData
import all Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionRealizationAux

/-!
# Private mate calculations for open coefficient restriction

Source: Stacks Project, Tags 03DI and 03CY; derived.tex, Tag 015F; categories.tex,
Tag 04VG (blueprint: lem-sf-open-extension-scalar-restriction-coherence).

The comparisons are the published `sfOpenRestriction` and its exact termwise
localization. Normalization is expressed on the open adjunction unit: on each
nonzero summand of the defining extension presheaf it is the identity; maps from
all remaining values, which are zero, are unique. Thus this unit equation is
precisely the pre-sheafification normalization, without a choice of stalks.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Scheme


variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

attribute [local irreducible] ProEtale.openImmersionLowerShriekAdjunction
attribute [local irreducible] sfIntrinsicModuleEquivalence

private theorem inverse_realization_mate (T : Scheme.{u}) (φ : A →+* B) :
    mateEquiv (sfIntrinsicModuleEquivalence T B).symm.toAdjunction
        (sfIntrinsicModuleEquivalence T A).symm.toAdjunction
        (TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction T φ).hom) =
      TwoSquare.mk _ _ _ _ (sfRealizationRestriction T φ).hom := by
  apply (mateEquiv (sfIntrinsicModuleEquivalence T B).symm.toAdjunction
    (sfIntrinsicModuleEquivalence T A).symm.toAdjunction).symm.injective
  simp only [Equiv.symm_apply_apply]
  ext M : 1
  simp only [sfInverseRealizationRestriction, mateEquiv_symm_apply,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [Equivalence.symm, Equivalence.toAdjunction, Equivalence.unit,
    Equivalence.counit, TwoSquare.mk, TwoSquare.natTrans, Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  all_goals rfl

private theorem inverse_realization_comp (T : Scheme.{u})
    (φ : A →+* B) (ψ : B →+* C)
    (M : proEtaleRingModules T (proEtaleConstantRing T C)) :
    (sfIntrinsicModuleEquivalence T A).inverse.map
        ((sfCoefficientRestrictionComp T φ ψ).hom.app M) ≫
      (sfInverseRealizationRestriction T (ψ.comp φ)).hom.app M =
    (sfInverseRealizationRestriction T φ).hom.app
        ((proEtaleCoefficientRestrictScalars T ψ).obj M) ≫
      (sfFixedRestriction T φ).map ((sfInverseRealizationRestriction T ψ).hom.app M) := by
  have h : (TwoSquare.mk _ _ _ _
        (sfInverseRealizationRestriction T (ψ.comp φ)).hom).whiskerTop
        (sfCoefficientRestrictionComp T φ ψ).hom =
      (TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction T ψ).hom) ≫ₕ
        (TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction T φ).hom) := by
    apply (mateEquiv (sfIntrinsicModuleEquivalence T C).symm.toAdjunction
      (sfIntrinsicModuleEquivalence T A).symm.toAdjunction).injective
    rw [mate_whisker_top, inverse_realization_mate]
    erw [mateEquiv_vcomp _ (sfIntrinsicModuleEquivalence T B).symm.toAdjunction,
      inverse_realization_mate, inverse_realization_mate]
    ext N : 1
    simp only [TwoSquare.whiskerRight, TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    exact (realization_comp T φ ψ N).symm
  simpa only [TwoSquare.whiskerTop, TwoSquare.hComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using congr_app h M

private theorem realization_inv_comp (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} C))) :
    (sfRealizationRestriction T φ).inv.app ((sfFixedRestriction T ψ).obj M) ≫
      (proEtaleCoefficientRestrictScalars T φ).map
        ((sfRealizationRestriction T ψ).inv.app M) ≫
      (sfCoefficientRestrictionComp T φ ψ).hom.app
        ((sfIntrinsicModuleEquivalence T C).functor.obj M) =
    (sfRealizationRestriction T (ψ.comp φ)).inv.app M := by
  apply (cancel_epi ((sfRealizationRestriction T (ψ.comp φ)).hom.app M)).mp
  rw [← cancel_epi ((sfCoefficientRestrictionComp T φ ψ).hom.app
    ((sfIntrinsicModuleEquivalence T C).functor.obj M))]
  rw [← Category.assoc, ← realization_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

private theorem forward_realization_mate (T : Scheme.{u}) (φ : A →+* B) :
    mateEquiv (sfIntrinsicModuleEquivalence T B).toAdjunction
        (sfIntrinsicModuleEquivalence T A).toAdjunction
        (TwoSquare.mk _ _ _ _ (sfRealizationRestriction T φ).inv) =
      TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction T φ).inv := by
  ext M : 1
  simp only [sfInverseRealizationRestriction, mateEquiv_apply,
    Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp,
    Category.assoc]
  dsimp only [Equivalence.symm, Equivalence.toAdjunction, Equivalence.unit,
    Equivalence.counit, TwoSquare.mk, TwoSquare.natTrans, Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  all_goals rfl

omit [Finite A] [Finite B] in
private theorem fixed_open_mate {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    mateEquiv
        (ProEtale.openImmersionLowerShriekAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
        (ProEtale.openImmersionLowerShriekAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
        (TwoSquare.mk _ _ _ _ (sfFixedOpenRestriction j φ).hom) =
      TwoSquare.mk
        (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
        (sfFixedRestriction Z φ) (sfFixedRestriction U φ)
        (ProEtale.openImmersionRestriction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
        (𝟙 _) := by
  ext N : 1
  simp only [mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans, NatTrans.id_app,
    NatTrans.comp_app, Functor.comp_obj, Functor.comp_map,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  slice_lhs 1 2 => exact fixed_normalized j φ _
  erw [Category.comp_id]
  have h := congrArg ((sfFixedRestriction U φ).map)
    ((ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).right_triangle_components N)
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id] at h
  exact h

omit [Finite A] [Finite B] [Finite C] in
private theorem fixed_open_comp {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) (ψ : B →+* C)
    (M : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} (ULift.{u + 1, u} C))) :
    (sfFixedOpenRestriction j (ψ.comp φ)).hom.app M =
      (sfFixedOpenRestriction j φ).hom.app ((sfFixedRestriction U ψ).obj M) ≫
        (sfFixedRestriction Z φ).map ((sfFixedOpenRestriction j ψ).hom.app M) := by
  apply ((ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  slice_lhs 1 2 => exact fixed_normalized j (ψ.comp φ) M
  slice_rhs 1 2 => exact fixed_normalized j φ ((sfFixedRestriction U ψ).obj M)
  have h := congrArg ((sfFixedRestriction U φ).map) (fixed_normalized j ψ M).symm
  simp only [Functor.map_comp] at h
  exact h

/-- The intrinsic open comparison is the mate of its coefficient square.
Source: Stacks Tags 03DI and 03CY.
Proof: expand its inverse-realization, fixed-open and realization factors. Apply
the fixed open unit equation and the realization mate identities. Compatibility
of mates with horizontal pasting yields the inverse transported square.
(blueprint: lem-sf-open-scalar-mate-calculations). -/
private theorem open_mate {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    mateEquiv (sfIntrinsicExtensionByZeroAdjunction j B)
        (sfIntrinsicExtensionByZeroAdjunction j A)
        (TwoSquare.mk _ _ _ _ (sfOpenRestriction j φ).hom) =
      TwoSquare.mk _ _ _ _ (sfOpenRestrictionCoefficientSquare j φ).inv := by
  let bU := (sfIntrinsicModuleEquivalence U B).symm.toAdjunction
  let aU := (sfIntrinsicModuleEquivalence U A).symm.toAdjunction
  let bZ := (sfIntrinsicModuleEquivalence Z B).toAdjunction
  let aZ := (sfIntrinsicModuleEquivalence Z A).toAdjunction
  let b := ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j
  let a := ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j
  let s₁ := TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction U φ).hom
  let s₂ := TwoSquare.mk _ _ _ _ (sfFixedOpenRestriction j φ).hom
  let s₃ := TwoSquare.mk _ _ _ _ (sfRealizationRestriction Z φ).inv
  have h := mateEquiv_hcomp (bU.comp b) (aU.comp a) bZ aZ (s₁ ≫ᵥ s₂) s₃
  rw [mateEquiv_hcomp bU aU b a] at h
  dsimp only [s₁, s₂, s₃, aU, bU, aZ, bZ, a, b] at h
  rw [inverse_realization_mate, fixed_open_mate, forward_realization_mate] at h
  have hs : (s₁ ≫ᵥ s₂) ≫ᵥ s₃ =
      TwoSquare.mk _ _ _ _ (sfOpenRestriction j φ).hom := by
    ext M : 1
    simp only [s₁, s₂, s₃, sfOpenRestriction, TwoSquare.vComp,
      TwoSquare.mk, TwoSquare.natTrans, Functor.comp_map, Functor.map_comp,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [s₁, s₂, s₃] at hs
  rw [hs] at h
  change mateEquiv (sfIntrinsicExtensionByZeroAdjunction j B)
    (sfIntrinsicExtensionByZeroAdjunction j A) _ = _ at h
  refine h.trans ?_
  ext M : 1
  simp only [sfOpenRestrictionCoefficientSquare, TwoSquare.hComp,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.id_app, Functor.comp_obj, Functor.comp_map,
    Iso.trans_inv, Iso.symm_inv, Iso.refl_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
  all_goals rfl


private theorem open_normalized {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    SfOpenRestrictionNormalized j φ (sfOpenRestriction j φ) := by
  intro M
  have h := unit_mateEquiv (sfIntrinsicExtensionByZeroAdjunction j B)
    (sfIntrinsicExtensionByZeroAdjunction j A)
    (TwoSquare.mk _ _ _ _ (sfOpenRestriction j φ).hom) M
  rw [open_mate] at h
  dsimp only [TwoSquare.mk, TwoSquare.natTrans, Functor.id_obj] at h
  rw [← Category.assoc, ← h]
  simp


end AlgebraicGeometry.Scheme
