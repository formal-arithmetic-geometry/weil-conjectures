/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportStrictScalarMate
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarCocycle
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.SmoothPurity.PurStrictScalar.ConstantCompletedScalarAssociativity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Ordinary open tensor balancing and coefficient composition

Source: Stacks 0E8I and 07A6; strict scalar composition, auxiliary Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

attribute [local irreducible] pbcScalarAdjunction proEtaleRingModulePullback
  PurCompactSupport.openAdjunction proEtaleRingRestrictionPullbackInv
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

private theorem derivedRestriction_left_unit
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (U : A ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (ρ : U ≅ 𝟭 A) :
    (Functor.mapDerivedCategoryCompIso U U).symm ≪≫
        Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft U ρ) =
      Functor.isoWhiskerLeft U.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso A) ≪≫
        Functor.rightUnitor U.mapDerivedCategory := by
  apply Iso.ext
  ext X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft U ρ) X
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_comp_id U) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hn hu
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U U).hom.app X)).mp
  rw [Iso.hom_inv_id_app_assoc]
  simp only [← Category.assoc]
  rw [← hn]
  simp only [Category.assoc]
  simp only [NatTrans.id_app] at hu
  rw [reassoc_of% hu]
  erw [Category.comp_id, Category.comp_id]

private theorem identityConjugate {A : Type*} [Category A]
    {F U : A ⥤ A} (a : F ⊣ U) (e : U ≅ 𝟭 A) :
    a.leftAdjointIdIso e = ((conjugateIsoEquiv a Adjunction.id).symm e).symm := by
  rfl

private theorem normalizedComparison_eq
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {U : B ⥤ A} {V : C ⥤ B} {W : C ⥤ A}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (d : V ⋙ U ≅ W) :
    ((a.comp b).ofNatIsoRight d).leftAdjointUniq c =
      a.leftAdjointCompIso b c d := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Adjunction.leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, Adjunction.leftAdjointCompIso,
    conjugateIsoEquiv_symm_apply_hom, Iso.symm_hom, conjugateEquiv_symm_apply_app,
    Adjunction.ofNatIsoRight_counit, NatTrans.id_app, NatTrans.comp_app,
    Functor.whiskerRight_app]
  rw [(F ⋙ G).map_id, Category.id_comp]

open AlgebraicGeometry.ProEtale in
attribute [local irreducible] reductionChange reductionDerivedChange
  pbcDerivedScalarAdjunction PurCompactSupport.tensorComposition
  PurCompactSupport.tensorIdentity

private theorem tensorComposition_identity_left {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (K : DerivedCategory (pbcModules W R)) :
    (PurCompactSupport.tensorComposition (𝟙 R) (𝟙 R) (𝟙 R)
      (Category.id_comp _)).hom.app K =
      (pbcDerivedExtend (𝟙 R)).map ((PurCompactSupport.tensorIdentity R).hom.app K) := by
  let ρ := (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose
  let δ := Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso _
  have he : pbcRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _) =
      Functor.isoWhiskerLeft (pbcRestrict (𝟙 R)) ρ := by
    apply Iso.ext
    ext M U x
    exact (pbcRestrictComp_exists (𝟙 R) (𝟙 R) (𝟙 R)
      (Category.id_comp _)).exists.choose_spec M U x |>.trans
        ((PurCompactSupport.restrictIdentity_existsUnique R).exists.choose_spec M U x).symm
  have hd : pbcDerivedRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _) =
      Functor.isoWhiskerLeft (pbcDerivedRestrict (𝟙 R)) δ ≪≫
        Functor.rightUnitor (pbcDerivedRestrict (𝟙 R)) := by
    unfold pbcDerivedRestrictComp
    rw [he]
    exact derivedRestriction_left_unit (pbcRestrict (𝟙 R)) ρ
  have h := congrArg (fun e ↦ e.hom.app K)
    (Adjunction.leftAdjointCompIso_id_comp (pbcDerivedScalarAdjunction (𝟙 R))
      (pbcDerivedScalarAdjunction (𝟙 R)) _ δ hd)
  have hn := normalizedComparison_eq (pbcDerivedScalarAdjunction (𝟙 R))
    (pbcDerivedScalarAdjunction (𝟙 R)) (pbcDerivedScalarAdjunction (𝟙 R))
    (pbcDerivedRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _))
  unfold PurCompactSupport.tensorComposition
  change ((((pbcDerivedScalarAdjunction (𝟙 R)).comp
    (pbcDerivedScalarAdjunction (𝟙 R))).ofNatIsoRight
      (pbcDerivedRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _))).leftAdjointUniq
        (pbcDerivedScalarAdjunction (𝟙 R))).hom.app K = _
  rw [hn]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h
  erw [Category.comp_id] at h
  have hu : (pbcDerivedScalarAdjunction (𝟙 R)).leftAdjointIdIso δ =
      PurCompactSupport.tensorIdentity R := by
    unfold PurCompactSupport.tensorIdentity
    exact identityConjugate _ _
  rw [hu] at h
  exact h

private theorem tensorComposition_identity_left_of_eq {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) (a : R ⟶ R)
    (ha : a = 𝟙 R) (hc : a ≫ a = a) (K : DerivedCategory (pbcModules W R)) :
    (PurCompactSupport.tensorComposition a a a hc).hom.app K =
      (pbcDerivedExtend a).map
        ((eqToIso (congrArg (fun a ↦ pbcDerivedExtend a) ha) ≪≫
          PurCompactSupport.tensorIdentity R).hom.app K) := by
  cases ha
  rw [eqToIso_refl, Iso.refl_trans]
  exact tensorComposition_identity_left R K

section LocalizationHelpers
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L)

end LocalizationHelpers

end WeilConjectures.PurStrictScalar
