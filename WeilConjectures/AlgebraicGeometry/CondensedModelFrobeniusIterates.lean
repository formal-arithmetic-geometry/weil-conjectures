/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperatorsBase

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobeniusNaturality

/-! Canonical condensed model Frobenius comparison, a step of the operator theorem. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory

-- Exact termwise descent preserves the comparison squares and the two unitors.
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
private theorem derive_kappa (F G H : C ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) (τ : G ≅ 𝟭 C) :
    Functor.mapDerivedCategoryNatIso
      (e ≪≫ Functor.isoWhiskerLeft F τ ≪≫ Functor.rightUnitor F) =
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso τ ≪≫ Functor.mapDerivedCategoryIdIso C) ≪≫
      Functor.rightUnitor F.mapDerivedCategory := by
  apply Iso.ext
  have hi : (Functor.mapDerivedCategoryNatIso (Functor.rightUnitor F)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hw := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F τ
  have hu := Functor.mapDerivedCategoryCompIso_comp_id F
  simp only [Functor.mapDerivedCategoryNatIso_trans, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_comp, hi,
    Category.comp_id, Category.assoc]
  rw [← reassoc_of% hw, reassoc_of% hu]
  ext K
  simp only [NatTrans.comp_app, Functor.rightUnitor_hom_app, NatTrans.id_app,
    Functor.id_obj, Functor.comp_obj]
  erw [Category.comp_id, Category.comp_id]
private theorem derive_trans (F G H : C ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (d : G ≅ H) :
    Functor.mapDerivedCategoryNatIso (e ≪≫ d) =
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryNatIso d := by
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_trans e d
private theorem derive_square (A B F G H J : C ⥤ C)
    [A.Additive] [B.Additive] [F.Additive] [G.Additive] [H.Additive] [J.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (cA : A ≅ F ⋙ G) (cB : B ≅ H ⋙ J)
    (e : A ≅ B) (e₁ : F ≅ H) (e₂ : G ≅ J)
    (he : e ≪≫ cB = cA ≪≫ Functor.isoWhiskerRight e₁ G ≪≫
      Functor.isoWhiskerLeft H e₂) :
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryNatIso cB ≪≫
        Functor.mapDerivedCategoryCompIso H J =
      Functor.mapDerivedCategoryNatIso cA ≪≫ Functor.mapDerivedCategoryCompIso F G ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso e₁) G.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft H.mapDerivedCategory (Functor.mapDerivedCategoryNatIso e₂) := by
  apply Iso.ext
  have hh := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom) he
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hh
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e₁ G),
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerLeft H e₂]
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ (Functor.mapDerivedCategoryCompIso H J).hom) hh
private theorem derive_left_kappa (F G H : C ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) (τ : F ≅ 𝟭 C) :
    Functor.mapDerivedCategoryNatIso
      (e ≪≫ Functor.isoWhiskerRight τ G ≪≫ Functor.leftUnitor G) =
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso τ ≪≫ Functor.mapDerivedCategoryIdIso C)
        G.mapDerivedCategory ≪≫ Functor.leftUnitor G.mapDerivedCategory := by
  apply Iso.ext
  have hi : (Functor.mapDerivedCategoryNatIso (Functor.leftUnitor G)).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hw := Functor.mapDerivedCategoryNatIso_isoWhiskerRight τ G
  have hu := Functor.mapDerivedCategoryCompIso_id_comp G
  simp only [Functor.mapDerivedCategoryNatIso_trans, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_comp, hi,
    Category.comp_id, Category.assoc]
  rw [← reassoc_of% hw, reassoc_of% hu]
  ext K
  simp only [NatTrans.comp_app, Functor.leftUnitor_hom_app, NatTrans.id_app]
  erw [Category.comp_id, Category.comp_id]
end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

open CondensedOpenProper Scheme

-- Prove the compositor calculation before specializing either category or pullback.
section Abstract
variable {C : Type*} [Category C] {S : Type*} [Category S] {X : S}
  (H : ℕ → (X ⟶ X))
  (hAddIndex : ∀ m n : ℕ, H (m + n) = H m ≫ H n)
  (hCommIndex : ∀ (n : ℕ) (g : X ⟶ X), g ≫ H n = H n ≫ g)
  (F : (X ⟶ X) → C ⥤ C)
  (cc : ∀ f g : X ⟶ X, F (f ≫ g) ≅ F g ⋙ F f)
  (Q : ∀ {f g : X ⟶ X}, f = g → (F f ≅ F g))
  (τ : ∀ n : ℕ, F (H n) ≅ 𝟭 C)
private def abstractKappa (b : ℕ) (g φ : X ⟶ X)
    (w : φ = H b ≫ g) : F φ ≅ F g :=
  Q w ≪≫ cc (H b) g ≪≫
    Functor.isoWhiskerLeft (F g) (τ b) ≪≫ Functor.rightUnitor (F g)
private theorem abstract_comp
    (hQself : ∀ f : X ⟶ X, Q (rfl : f = f) = Iso.refl (F f))
    (hQeq : ∀ {f g : X ⟶ X} (e : f = g) (M : C),
      (Q e).hom.app M = eqToHom (congrArg (fun z ↦ (F z).obj M) e))
    (hL : ∀ {a b : X ⟶ X} (e : a = b) (t : X ⟶ X) (M : C),
      (cc a t).hom.app M ≫ (Q e).hom.app ((F t).obj M) =
        (Q (congrArg (· ≫ t) e)).hom.app M ≫ (cc b t).hom.app M)
    (hR : ∀ (t : X ⟶ X) {a b : X ⟶ X} (e : a = b) (M : C),
      (cc t a).hom.app M ≫ (F t).map ((Q e).hom.app M) =
        (Q (congrArg (t ≫ ·) e)).hom.app M ≫ (cc t b).hom.app M)
    (hA : ∀ (f g h : X ⟶ X) (M : C),
      (cc (f ≫ g) h).hom.app M ≫ (cc f g).hom.app ((F h).obj M) =
        (Q (Category.assoc f g h)).hom.app M ≫
          (cc f (g ≫ h)).hom.app M ≫ (F f).map ((cc g h).hom.app M))
    (hA' : ∀ (f g h : X ⟶ X) (M : C),
      (cc f (g ≫ h)).hom.app M ≫ (F f).map ((cc g h).hom.app M) =
        (Q (Category.assoc f g h).symm).hom.app M ≫
          (cc (f ≫ g) h).hom.app M ≫ (cc f g).hom.app ((F h).obj M))
    (hN : ∀ (n : ℕ) (g : X ⟶ X) (M : C),
      (cc g (H n)).hom.app M ≫ (F g).map ((τ n).hom.app M) =
        (Q (hCommIndex n g)).hom.app M ≫
          (cc (H n) g).hom.app M ≫
            (τ n).hom.app ((F g).obj M))
    (hAdd : ∀ m n : ℕ,
      Q (hAddIndex m n) ≪≫
        cc (H m) (H n) ≪≫
        Functor.isoWhiskerRight (τ n) (F (H m)) ≪≫
        Functor.leftUnitor (F (H m)) ≪≫ τ m = τ (m + n))
    (b c : ℕ) (g h φ ψ : X ⟶ X)
    (wφ : φ = H b ≫ g)
    (wψ : ψ = H c ≫ h)
    (w : φ ≫ ψ = H (b + c) ≫ (g ≫ h)) :
    abstractKappa H F cc Q τ (b + c) (g ≫ h) (φ ≫ ψ) w ≪≫ cc g h =
      cc φ ψ ≪≫
        Functor.isoWhiskerRight (abstractKappa H F cc Q τ c h ψ wψ) (F φ) ≪≫
        Functor.isoWhiskerLeft (F h) (abstractKappa H F cc Q τ b g φ wφ) := by
  subst φ ψ
  apply Iso.ext
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    abstractKappa, Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  conv_rhs =>
    simp only [hQself, Iso.refl_hom, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
  rw [(cc (H b) g).hom.naturality_assoc,
    (cc (H b) g).hom.naturality_assoc]
  simp only [Functor.comp_map, Functor.comp_obj]
  rw [reassoc_of% (hA _ _ _ _)]
  rw [← Functor.map_comp_assoc]
  rw [hA']
  simp only [Functor.map_comp, Category.assoc]
  have hnm := congrArg ((F (H b)).map)
    (hN c g ((F h).obj M))
  simp only [Functor.map_comp] at hnm
  rw [reassoc_of% hnm]
  have hswap := congrArg ((F (H b)).map)
    (hL (hCommIndex c g) h M)
  simp only [Functor.map_comp] at hswap
  rw [reassoc_of% hswap]
  have hassoc := congrArg ((F (H b)).map)
    (hA (H c) g h M)
  simp only [Functor.map_comp] at hassoc
  rw [reassoc_of% hassoc]
  rw [reassoc_of% (hR _ _ _), reassoc_of% (hR _ _ _), reassoc_of% (hR _ _ _),
    reassoc_of% (hA' _ _ _ _)]
  have hnat := congrArg ((F (H b)).map)
    ((τ c).hom.naturality ((cc g h).hom.app M))
  simp only [Functor.id_map, Functor.map_comp] at hnat
  rw [reassoc_of% hnat, (τ b).hom.naturality]
  simp only [Functor.id_map]
  have hadd := congrArg (fun e ↦ e.hom.app ((F (g ≫ h)).obj M)) (hAdd b c)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.comp_obj,
    Functor.id_obj, Category.id_comp] at hadd
  rw [← hadd]
  simp only [Category.assoc]
  rw [reassoc_of% (hL _ _ _)]
  simp only [hQeq, eqToHom_trans_assoc]
private theorem abstract_iso_comp
    (hQself : ∀ f : X ⟶ X, Q (rfl : f = f) = Iso.refl (F f))
    (hAiso : ∀ f g h : X ⟶ X,
      cc f (g ≫ h) ≪≫ Functor.isoWhiskerRight (cc g h) (F f) ≪≫
        Functor.associator (F h) (F g) (F f) =
      Q (Category.assoc f g h).symm ≪≫ cc (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (F h) (cc f g))
    (hNiso : ∀ (n : ℕ) (g : X ⟶ X),
      (cc g (H n)).hom ≫ Functor.whiskerRight (τ n).hom (F g) ≫
        (Functor.leftUnitor _).hom =
      (Q (hCommIndex n g)).hom ≫ (cc (H n) g).hom ≫
        Functor.whiskerLeft (F g) (τ n).hom ≫ (Functor.rightUnitor _).hom)
    (hAdd : ∀ m n : ℕ,
      Q (hAddIndex m n) ≪≫
        cc (H m) (H n) ≪≫
        Functor.isoWhiskerRight (τ n) (F (H m)) ≪≫
        Functor.leftUnitor (F (H m)) ≪≫ τ m = τ (m + n))
    (b c : ℕ) (g h φ ψ : X ⟶ X)
    (wφ : φ = H b ≫ g)
    (wψ : ψ = H c ≫ h)
    (w : φ ≫ ψ = H (b + c) ≫ (g ≫ h)) :
    abstractKappa H F cc Q τ (b + c) (g ≫ h) (φ ≫ ψ) w ≪≫ cc g h =
      cc φ ψ ≪≫
        Functor.isoWhiskerRight (abstractKappa H F cc Q τ c h ψ wψ) (F φ) ≪≫
        Functor.isoWhiskerLeft (F h) (abstractKappa H F cc Q τ b g φ wφ) := by
  have hQeq : ∀ {f g : X ⟶ X} (e : f = g) (M : C),
      (Q e).hom.app M = eqToHom (congrArg (fun z ↦ (F z).obj M) e) := by
    intro f g e M
    cases e
    simp only [hQself, Iso.refl_hom, NatTrans.id_app, eqToHom_refl]
  have hA' : ∀ (f g h : X ⟶ X) (M : C),
      (cc f (g ≫ h)).hom.app M ≫ (F f).map ((cc g h).hom.app M) =
        (Q (Category.assoc f g h).symm).hom.app M ≫
          (cc (f ≫ g) h).hom.app M ≫ (cc f g).hom.app ((F h).obj M) := by
    intro f g h M
    have hh := congrArg (fun e ↦ e.hom.app M) (hAiso f g h)
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Category.comp_id] using hh
  apply abstract_comp H hAddIndex hCommIndex F cc Q τ hQself hQeq
    ?_ ?_ ?_ hA' ?_ hAdd b c g h φ ψ wφ wψ w
  · intro a b e t M
    cases e
    simp only [hQself, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
    exact Category.comp_id _
  · intro t a b e M
    cases e
    simp only [hQself, Iso.refl_hom, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact Category.comp_id _
  · intro f g h M
    rw [hA']
    simp only [hQeq, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · intro n g M
    have hh := congrArg (fun e ↦ e.app M) (hNiso n g)
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
      Category.comp_id] using hh
end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

-- First prove the canonical comparison identities before passing to derived categories.
section
variable {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)

set_option maxHeartbeats 1000000 in
-- The pullback comparison types require extra elaboration heartbeats.
private lemma moduleFrobenius_add (m n : ℕ) :
    upperStarCongr Λ (iterateFrobenius_add hp X hX m n) ≪≫
      upperStarComp Λ (X.iterateFrobenius hp hX m) (X.iterateFrobenius hp hX n) ≪≫
      Functor.isoWhiskerRight (upperStarIterateFrobeniusIso Λ hp hX n) _ ≪≫
      Functor.leftUnitor _ ≪≫ upperStarIterateFrobeniusIso Λ hp hX m =
      upperStarIterateFrobeniusIso Λ hp hX (m + n) := by
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id (upperStarLowerStarAdjunction Λ _)).injective
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp _
      (upperStarLowerStarAdjunction Λ (X.iterateFrobenius hp hX m ≫
        X.iterateFrobenius hp hX n)),
    ← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction Λ _).comp
      (upperStarLowerStarAdjunction Λ (X.iterateFrobenius hp hX m))),
    ← conjugateEquiv_comp _ (Adjunction.id.comp
      (upperStarLowerStarAdjunction Λ (X.iterateFrobenius hp hX m))),
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction Λ (X.iterateFrobenius hp hX m)),
    conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight]
  have h₁ := congrArg Iso.hom (conjugateIsoEquiv_upperStarComp Λ
    (X.iterateFrobenius hp hX m) (X.iterateFrobenius hp hX n))
  have h₂ := congrArg Iso.hom (conjugateIsoEquiv_upperStarCongr Λ
    (iterateFrobenius_add hp X hX m n))
  simp only [conjugateIsoEquiv_apply_hom] at h₁ h₂
  rw [h₁, h₂]
  refine NatTrans.ext (funext fun M ↦ Mod.hom_ext _ _ ?_)
  simp only [Iso.symm_hom, NatTrans.comp_app, Mod.comp_hom', Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app,
    conjugateEquiv_upperStarIterateFrobeniusIso_hom_app_hom,
    lowerStarComp_hom_app_hom, lowerStarCongr_inv_app_hom,
    Category.id_comp, Category.assoc, lowerStar_obj_X]
  have h := congrArg (fun e ↦ e.inv.app M.X)
    (ProEtale.lowerStarIterateFrobeniusIso_add Ab.{u + 1} hp hX n m)
  simpa only [Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app,
    Category.comp_id, Category.id_comp, Category.assoc] using h

attribute [local irreducible] upperStar upperStarCongr
private def okappa (b : ℕ) (g φ : X ⟶ X)
    (w : φ = X.iterateFrobenius hp hX b ≫ g) : upperStar Λ φ ≅ upperStar Λ g :=
  abstractKappa (X.iterateFrobenius hp hX) (upperStar Λ)
    (fun f g ↦ upperStarComp Λ f g) (upperStarCongr Λ)
    (upperStarIterateFrobeniusIso Λ hp hX) b g φ w
set_option maxHeartbeats 1000000 in
-- Specialize the abstract comparison to ordinary module pullback.
private theorem moduleKappa_comp (b c : ℕ) (g h φ ψ : X ⟶ X)
    (wφ : φ = X.iterateFrobenius hp hX b ≫ g)
    (wψ : ψ = X.iterateFrobenius hp hX c ≫ h)
    (w : φ ≫ ψ = X.iterateFrobenius hp hX (b + c) ≫ (g ≫ h)) :
    okappa Λ hp hX (b + c) (g ≫ h) (φ ≫ ψ) w ≪≫ upperStarComp Λ g h =
      upperStarComp Λ φ ψ ≪≫
        Functor.isoWhiskerRight (okappa Λ hp hX c h ψ wψ) (upperStar Λ φ) ≪≫
        Functor.isoWhiskerLeft (upperStar Λ h) (okappa Λ hp hX b g φ wφ) := by
  apply abstract_iso_comp (X.iterateFrobenius hp hX)
    (iterateFrobenius_add hp X hX)
    (fun n g ↦ Scheme.comp_iterateFrobenius hp g hX hX n) (upperStar Λ)
    (fun f g ↦ upperStarComp Λ f g) (upperStarCongr Λ)
    (upperStarIterateFrobeniusIso Λ hp hX)
    ?_ ?_ ?_ (moduleFrobenius_add Λ hp hX) b c g h φ ψ wφ wψ w
  · intro f
    exact upperStarCongr_self Λ rfl
  · intro f g h
    exact upperStarComp_assoc Λ f g h
  · intro n g
    exact upperStarComp_hom_comp_whiskerRight_upperStarIterateFrobeniusIso_hom
      Λ hp hX hX n g

end

-- Transport the ordinary identities through exact derived descent.
private lemma derive_congr {T : Scheme.{u}} {f g : T ⟶ T} (w : f = g) :
    Functor.mapDerivedCategoryNatIso (upperStarCongr Λ w) = eqToIso (congrArg (P Λ) w) := by
  cases w
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl
private lemma derive_okappa {T : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (hT : (p : Γ(T, ⊤)) = 0) (b : ℕ) (g φ : T ⟶ T)
    (w : φ = T.iterateFrobenius hp hT b ≫ g) :
    Functor.mapDerivedCategoryNatIso (okappa Λ hp hT b g φ w) =
      kappa Λ p hp hT b g φ w := by
  rw [okappa, abstractKappa, CategoryTheory.derive_trans,
    CategoryTheory.derive_kappa, derive_congr]
  simp only [kappa, pComp, Iso.trans_assoc]
private lemma derived_comparison_square {T : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (hT : (p : Γ(T, ⊤)) = 0) (b c : ℕ) (g h φ ψ : T ⟶ T)
    (wφ : φ = T.iterateFrobenius hp hT b ≫ g)
    (wψ : ψ = T.iterateFrobenius hp hT c ≫ h)
    (w : φ ≫ ψ = T.iterateFrobenius hp hT (b + c) ≫ (g ≫ h))
    (hc : okappa Λ hp hT (b + c) (g ≫ h) (φ ≫ ψ) w ≪≫ upperStarComp Λ g h =
      upperStarComp Λ φ ψ ≪≫
        Functor.isoWhiskerRight (okappa Λ hp hT c h ψ wψ) (upperStar Λ φ) ≪≫
        Functor.isoWhiskerLeft (upperStar Λ h) (okappa Λ hp hT b g φ wφ)) :
    kappa Λ p hp hT (b + c) (g ≫ h) (φ ≫ ψ) w ≪≫ pComp Λ g h =
      pComp Λ φ ψ ≪≫
        Functor.isoWhiskerRight (kappa Λ p hp hT c h ψ wψ) (P Λ φ) ≪≫
        Functor.isoWhiskerLeft (P Λ h) (kappa Λ p hp hT b g φ wφ) := by
  have hd := CategoryTheory.derive_square _ _ _ _ _ _
    (upperStarComp Λ φ ψ) (upperStarComp Λ g h)
    (okappa Λ hp hT (b + c) (g ≫ h) (φ ≫ ψ) w)
    (okappa Λ hp hT c h ψ wψ) (okappa Λ hp hT b g φ wφ) hc
  rw [derive_okappa, derive_okappa, derive_okappa] at hd
  simpa only [pComp, Iso.trans_assoc] using hd

section
variable {X : Scheme.{u}}

attribute [local irreducible] upperStar upperStarCongr
private lemma ordinary_unit (g : X ⟶ X) :
    upperStarComp Λ (𝟙 X) g ≪≫
      Functor.isoWhiskerLeft (upperStar Λ g) (upperStarId Λ X) ≪≫
      Functor.rightUnitor _ = upperStarCongr Λ (Category.id_comp g) := by
  rw [upperStarComp_id_left]
  apply Iso.ext
  ext M
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
set_option maxHeartbeats 1000000 in
-- The pullback comparison types require extra elaboration heartbeats.
private lemma zero_kappa {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (g φ : X ⟶ X) (w : φ = X.iterateFrobenius hp hX 0 ≫ g) :
    (upperStarCongr Λ w ≪≫
      upperStarComp Λ (X.iterateFrobenius hp hX 0) g ≪≫
      Functor.isoWhiskerLeft (upperStar Λ g) (upperStarIterateFrobeniusIso Λ hp hX 0) ≪≫
      Functor.rightUnitor _) =
    upperStarCongr Λ (w.trans ((congrArg (· ≫ g)
      (Scheme.iterateFrobenius_zero hp X hX)).trans (Category.id_comp g))) := by
  obtain ⟨v, _, hv, _⟩ :=
    (condensed_frobenius_linear_trivialization Λ X p hp
      ⟨hp, Scheme.natCast_eq_zero_of_natCast_top_eq_zero hX⟩ 0).2.2.2.2.2 rfl
  have ht : ∀ (H : X ⟶ X) (v : H = 𝟙 X) (φ : X ⟶ X) (w : φ = H ≫ g),
      upperStarCongr Λ w ≪≫ upperStarComp Λ H g ≪≫
        Functor.isoWhiskerLeft (upperStar Λ g)
          (eqToIso (congrArg (upperStar Λ) v) ≪≫ upperStarId Λ X) ≪≫
        Functor.rightUnitor _ =
      upperStarCongr Λ (w.trans ((congrArg (· ≫ g) v).trans (Category.id_comp g))) := by
    intro H v φ w
    cases v
    cases w
    conv_lhs => rw [upperStarCongr_self]
    simpa only [eqToIso_refl, Iso.refl_trans] using ordinary_unit Λ g
  rw [hv]
  exact ht _ v φ w
end

private lemma kappa_zero {T : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (hT : (p : Γ(T, ⊤)) = 0) (w : (𝟙 T) = T.iterateFrobenius hp hT 0 ≫ 𝟙 T) :
    kappa Λ p hp hT 0 (𝟙 T) (𝟙 T) w = Iso.refl _ := by
  have hz := zero_kappa Λ hp hT (𝟙 T) (𝟙 T) w
  conv_rhs at hz => rw [upperStarCongr_self]
  have hd := congrArg (fun z ↦ Functor.mapDerivedCategoryNatIso z) hz
  change Functor.mapDerivedCategoryNatIso (okappa Λ hp hT 0 (𝟙 T) (𝟙 T) w) =
    Functor.mapDerivedCategoryNatIso (Iso.refl (upperStar Λ (𝟙 T))) at hd
  rw [derive_okappa] at hd
  apply Iso.ext
  rw [hd]
  exact Functor.mapDerivedCategoryNatIso_refl

private lemma kappa_comp {T : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (hT : (p : Γ(T, ⊤)) = 0) (b c : ℕ) (g h φ ψ : T ⟶ T)
    (wφ : φ = T.iterateFrobenius hp hT b ≫ g)
    (wψ : ψ = T.iterateFrobenius hp hT c ≫ h)
    (w : φ ≫ ψ = T.iterateFrobenius hp hT (b + c) ≫ (g ≫ h)) :
    kappa Λ p hp hT (b + c) (g ≫ h) (φ ≫ ψ) w ≪≫ pComp Λ g h =
      pComp Λ φ ψ ≪≫
        Functor.isoWhiskerRight (kappa Λ p hp hT c h ψ wψ) (P Λ φ) ≪≫
        Functor.isoWhiskerLeft (P Λ h) (kappa Λ p hp hT b g φ wφ) := by
  apply derived_comparison_square Λ hp hT b c g h φ ψ wφ wψ w
  exact moduleKappa_comp Λ hp hT b c g h φ ψ wφ wψ w

section

attribute [local irreducible] upperStar upperStarCongr
private lemma ordinary_right_unit {T : Scheme.{u}} (f : T ⟶ T) :
    upperStarComp Λ f (𝟙 T) ≪≫
      Functor.isoWhiskerRight (upperStarId Λ T) (upperStar Λ f) ≪≫
      Functor.leftUnitor _ = upperStarCongr Λ (Category.comp_id f) := by
  rw [upperStarComp_id_right]
  apply Iso.ext
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
set_option maxHeartbeats 1000000 in
-- The pullback comparison types require extra elaboration heartbeats.
private lemma iterate_one {T : Scheme.{u}} (f : End T) {K : D Λ T}
    (θ : (P Λ f).obj K ≅ K) : iterateStructure Λ f θ 1 =
      eqToIso (congrArg (fun h : End T ↦ (P Λ h).obj K) (pow_one f)) ≪≫ θ := by
  have h := CategoryTheory.derive_left_kappa (upperStar Λ (𝟙 T)) (upperStar Λ f)
    (upperStar Λ (f ≫ 𝟙 T)) (upperStarComp Λ f (𝟙 T)) (upperStarId Λ T)
  rw [ordinary_right_unit, derive_congr] at h
  have hh := congrArg (fun z ↦ z.hom.app K) h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, eqToIso.hom,
    eqToHom_app] at hh
  erw [Category.comp_id ((P Λ f).map ((pId Λ T).hom.app K))] at hh
  have hh' : (pComp Λ f (𝟙 T)).hom.app K ≫
      (P Λ f).map ((pId Λ T).hom.app K) =
      eqToHom (congrArg (fun z ↦ (P Λ z).obj K) (Category.comp_id f)) := by
    simpa only [pComp, pId, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Category.assoc] using hh.symm
  apply Iso.ext
  change (eqToIso (congrArg (fun z : End T ↦ (P Λ z).obj K) (pow_succ f 0))).hom ≫
      (pComp Λ f (𝟙 T)).hom.app K ≫ (P Λ f).map ((pId Λ T).hom.app K) ≫ θ.hom =
    (eqToIso (congrArg (fun z : End T ↦ (P Λ z).obj K) (pow_one f))).hom ≫ θ.hom
  rw [reassoc_of% hh']
  simp only [eqToIso.hom, eqToHom_trans_assoc]
end

section

-- The remaining argument is induction with explicitly tracked pullback compositors.
private def step {T : Scheme.{u}} (f : End T) (m : ℕ) (K : D Λ T) :
    (P Λ (f ^ (m + 1))).obj K ≅ (P Λ f).obj ((P Λ (f ^ m)).obj K) :=
  eqToIso (congrArg (fun h : End T ↦ (P Λ h).obj K) (pow_succ f m)) ≪≫
    (pComp Λ f (f ^ m)).app K
set_option maxHeartbeats 1000000 in
-- The pullback comparison types require extra elaboration heartbeats.
private theorem transfer {T : Scheme.{u}} (f g : End T) (K : D Λ T)
    (θ : (P Λ g).obj K ≅ K) (e : P Λ f ≅ P Λ g)
    (κ : ∀ m : ℕ, P Λ (f ^ m) ≅ P Λ (g ^ m))
    (h₀ : (κ 0).app K ≪≫ (pId Λ T).app K = (pId Λ T).app K)
    (hs : ∀ m : ℕ, (κ (m + 1)).app K ≪≫ step Λ g m K =
      step Λ f m K ≪≫ (P Λ f).mapIso ((κ m).app K) ≪≫
        e.app ((P Λ (g ^ m)).obj K)) (m : ℕ) :
    (κ m).app K ≪≫ iterateStructure Λ g θ m =
      iterateStructure Λ f (e.app K ≪≫ θ) m := by
  induction m with
  | zero => exact h₀
  | succ m ih =>
    have hh := congrArg Iso.hom (hs m)
    have hi := congrArg Iso.hom ih
    simp only [step, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc] at hh hi
    apply Iso.ext
    simp only [iterateStructure, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [reassoc_of% hh]
    rw [← e.hom.naturality_assoc, ← Functor.map_comp_assoc, hi]
private lemma kappa_congr_app {T : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (hT : (p : Γ(T, ⊤)) = 0) (b c : ℕ) (hb : b = c) (g h φ ψ : T ⟶ T)
    (hg : g = h) (hφ : φ = ψ)
    (w : φ = T.iterateFrobenius hp hT b ≫ g)
    (w' : ψ = T.iterateFrobenius hp hT c ≫ h) (K : D Λ T) :
    (kappa Λ p hp hT b g φ w).app K =
      eqToIso (congrArg (fun z ↦ (P Λ z).obj K) hφ) ≪≫
        (kappa Λ p hp hT c h ψ w').app K ≪≫
          eqToIso (congrArg (fun z ↦ (P Λ z).obj K) hg.symm) := by
  cases hb
  cases hg
  cases hφ
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_refl]
attribute [local irreducible] upperStar upperStarCongr kappa
set_option maxHeartbeats 1000000 in
-- The pullback comparison types require extra elaboration heartbeats.
private theorem power_transfer {T : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (hT : (p : Γ(T, ⊤)) = 0) (a : ℕ) (f g : End T) (K : D Λ T)
    (θ : (P Λ g).obj K ≅ K)
    (wf : ∀ n : ℕ, f ^ n = T.iterateFrobenius hp hT (a * n) ≫ g ^ n)
    (e1 : f = T.iterateFrobenius hp hT a ≫ g)
    (hzero : ∀ w : (𝟙 T) = T.iterateFrobenius hp hT 0 ≫ 𝟙 T,
      kappa Λ p hp hT 0 (𝟙 T) (𝟙 T) w = Iso.refl _)
    (hcomp : ∀ (b c : ℕ) (g h φ ψ : T ⟶ T)
      (wφ : φ = T.iterateFrobenius hp hT b ≫ g)
      (wψ : ψ = T.iterateFrobenius hp hT c ≫ h)
      (w : φ ≫ ψ = T.iterateFrobenius hp hT (b + c) ≫ (g ≫ h)),
      kappa Λ p hp hT (b + c) (g ≫ h) (φ ≫ ψ) w ≪≫ pComp Λ g h =
        pComp Λ φ ψ ≪≫
          Functor.isoWhiskerRight (kappa Λ p hp hT c h ψ wψ) (P Λ φ) ≪≫
          Functor.isoWhiskerLeft (P Λ h) (kappa Λ p hp hT b g φ wφ))
    (m : ℕ) :
    (kappa Λ p hp hT (a * m) (g ^ m) (f ^ m) (wf m)).app K ≪≫
        iterateStructure Λ g θ m =
      iterateStructure Λ f ((kappa Λ p hp hT a g f e1).app K ≪≫ θ) m := by
  apply transfer Λ f g K θ (kappa Λ p hp hT a g f e1)
    (fun n ↦ kappa Λ p hp hT (a * n) (g ^ n) (f ^ n) (wf n)) ?_ ?_ m
  · have hw0 : (𝟙 T) = T.iterateFrobenius hp hT 0 ≫ 𝟙 T := by
      simpa only [End.asHom, Nat.mul_zero, pow_zero, End.one_def] using
        (congrArg End.asHom (wf 0))
    have hz := hzero hw0
    have hz' : kappa Λ p hp hT (a * 0) (g ^ 0) (f ^ 0) (wf 0) = Iso.refl _ := by
      change kappa Λ p hp hT 0 (𝟙 T) (𝟙 T) hw0 = Iso.refl _
      exact hz
    rw [hz']
    change Iso.refl _ ≪≫ (pId Λ T).app K = (pId Λ T).app K
    exact Iso.refl_trans _
  · intro n
    have ha : a * (n + 1) = a + a*n := by rw [Nat.mul_succ, Nat.add_comm]
    have wp : f ≫ f ^ n = T.iterateFrobenius hp hT (a + a * n) ≫ (g ≫ g ^ n) := by
      simpa only [End.asHom, ha, pow_succ, End.mul_def] using
        (congrArg End.asHom (wf (n + 1)))
    have hc := congrArg (fun z ↦ z.hom.app K)
      (hcomp a (a * n) g (g ^ n) f (f ^ n) e1 (wf n) wp)
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app] at hc
    rw [kappa_congr_app Λ hp hT (a * (n + 1)) (a + a * n) ha
      (g ^ (n + 1)) (g ≫ g ^ n) (f ^ (n + 1)) (f ≫ f ^ n)
      (congrArg End.asHom (pow_succ g n)) (congrArg End.asHom (pow_succ f n))
      (wf (n + 1)) wp K]
    apply Iso.ext
    simp only [step, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc, eqToHom_refl, Category.id_comp]
    rw [hc]
end

section

-- Identify the model operators, including the degree-one equality transports.
private lemma kappa_source {T : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (hT : (p : Γ(T, ⊤)) = 0) (b : ℕ) (g φ ψ : T ⟶ T)
    (v : φ = ψ) (w : φ = T.iterateFrobenius hp hT b ≫ g) (K : D Λ T) :
    (kappa Λ p hp hT b g φ w).app K =
      eqToIso (congrArg (fun f ↦ (P Λ f).obj K) v) ≪≫
        (kappa Λ p hp hT b g ψ (v.symm.trans w)).app K := by
  cases v
  simp only [eqToIso_refl, Iso.refl_trans]
attribute [local irreducible] upperStar upperStarCongr kappa
set_option maxHeartbeats 1000000 in
-- The pullback comparison types require extra elaboration heartbeats.
private lemma assembly {T : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    (hT : (p : Γ(T, ⊤)) = 0) (a : ℕ) (f g : End T) (K : D Λ T)
    (θ : (P Λ g).obj K ≅ K) (ψ : ℕ → End T) (v : ∀ m, ψ m = f ^ m)
    (w : ∀ m, ψ m = T.iterateFrobenius hp hT (a * m) ≫ g ^ m)
    (e : f = T.iterateFrobenius hp hT a ≫ g)
    (hi : ∀ m, (kappa Λ p hp hT (a * m) (g ^ m) (f ^ m)
          ((v m).symm.trans (w m))).app K ≪≫ iterateStructure Λ g θ m =
        iterateStructure Λ f ((kappa Λ p hp hT a g f e).app K ≪≫ θ) m)
    (h1 : ∀ η : (P Λ f).obj K ≅ K, iterateStructure Λ f η 1 =
      eqToIso (congrArg (fun z : End T ↦ (P Λ z).obj K) (pow_one f)) ≪≫ η)
    (m : ℕ) :
    (kappa Λ p hp hT (a * m) (g ^ m) (ψ m) (w m)).app K ≪≫
        iterateStructure Λ g θ m =
      eqToIso (congrArg (fun z ↦ (P Λ z).obj K) (v m)) ≪≫
        iterateStructure Λ f
          (eqToIso (congrArg (fun z ↦ (P Λ z).obj K) ((v 1).trans (pow_one f)).symm) ≪≫
            (kappa Λ p hp hT (a * 1) (g ^ 1) (ψ 1) (w 1)).app K ≪≫
              iterateStructure Λ g θ 1) m := by
  have hs (n : ℕ) :
      (kappa Λ p hp hT (a * n) (g ^ n) (ψ n) (w n)).app K ≪≫
          iterateStructure Λ g θ n =
        eqToIso (congrArg (fun z ↦ (P Λ z).obj K) (v n)) ≪≫
          iterateStructure Λ f ((kappa Λ p hp hT a g f e).app K ≪≫ θ) n := by
    rw [kappa_source Λ hp hT (a * n) (g ^ n) (ψ n) (f ^ n) (v n)]
    rw [Iso.trans_assoc, hi]
  have hone :
      eqToIso (congrArg (fun z ↦ (P Λ z).obj K) ((v 1).trans (pow_one f)).symm) ≪≫
        (kappa Λ p hp hT (a * 1) (g ^ 1) (ψ 1) (w 1)).app K ≪≫
          iterateStructure Λ g θ 1 = (kappa Λ p hp hT a g f e).app K ≪≫ θ := by
    rw [hs 1, h1]
    apply Iso.ext
    simp only [Iso.trans_hom, eqToIso.hom, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
  rw [hone]
  exact hs m
end

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The canonical linearized model structure is the iterate of its degree-one structure.
Source: latest blueprint, lem-fd-realness-pushforward.proof.md, Step 1;
original operator comparison proof steps 1--3.
(blueprint: lem-fd-condensed-model-frobenius-iterates).

Proof: absolute Frobenius on the small pro-etale site has a canonical trivialization
whose component is restriction along the inverse relative Frobenius. Pasting relative
Frobenius squares identifies the trivialization at a sum of exponents with the composite
of the two trivializations. The coefficient component is the specified scalar comparison;
uniqueness in the extension/restriction adjunction gives this same identity for module
pullbacks. Naturalness under the geometric Frobenius moves this identity through the
factorization defining kappa. Exact termwise descent preserves it. Substitute the
recursive definition of iterateStructure and move kappa across the preceding structure
isomorphism by naturality. Induction on m, with the identity unitor and the equality
frobeniusIterate_one inserted at the base case, yields the displayed equality of
isomorphisms, including every pullback compositor. All proofs w m are equal by proof
irrelevance, so the equality holds for any factorization witness. -/
theorem condensed_model_frobenius_iterates
    (ell : ℕ) [Fact ell.Prime]
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D₀ X₀)) (w : Factorization D₀ X₀) :
      (∀ m : ℕ, 1 ≤ m →
        modelStructure D₀ X₀ ell K w m =
          modelIterate D₀ X₀ ell K w m) := by
  let Λ := Profinite.padicAlgClRingObj ell
  let T := (D₀.geometricFiber X₀).left
  let hT : (D₀.p : Γ(T, ⊤)) = 0 := D₀.model_characteristic
    (pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))) ≫ X₀.hom)
  let f : End T := End.of (modelEnd D₀ X₀).left
  let g : End T := End.of (StrictWeil.modelFrobenius D₀ X₀).hom
  let ψ : ℕ → End T := fun m ↦ End.of (frobeniusIterate (modelEnd D₀ X₀) m).left
  have v (n : ℕ) : ψ n = f ^ n :=
    congrArg End.of (frobeniusIterate_left (modelEnd D₀ X₀) n)
  have ww (n : ℕ) : ψ n = T.iterateFrobenius D₀.prime hT (D₀.a * n) ≫ g ^ n :=
    congrArg End.of (w n)
  have wf (n : ℕ) : f ^ n = T.iterateFrobenius D₀.prime hT (D₀.a * n) ≫ g ^ n :=
    (v n).symm.trans (ww n)
  have e1 : f = T.iterateFrobenius D₀.prime hT D₀.a ≫ g := by
    simpa only [End.asHom, pow_one, Nat.mul_one] using (congrArg End.asHom (wf 1))
  have hi (n : ℕ) := power_transfer Λ D₀.prime hT D₀.a f g K.carrier.obj
    (ambientStructure Λ K) wf e1 (kappa_zero Λ D₀.prime hT)
    (kappa_comp Λ D₀.prime hT) n
  intro m _
  have hh := assembly Λ D₀.prime hT D₀.a f g K.carrier.obj
    (ambientStructure Λ K) ψ v ww e1 hi (iterate_one Λ f) m
  exact hh

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
