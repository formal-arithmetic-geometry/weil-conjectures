/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperatorsBase
import WeilConjectures.AlgebraicGeometry.LocalFrobeniusTrace
import WeilConjectures.TraceFormula.BaseChange.WeilObject

/-! Canonical condensed model Frobenius comparison, a step of the operator theorem. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

open CondensedOpenProper

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

-- Keep comparisons of pullbacks from unfolding the site and localization constructions.
attribute [local irreducible] upperStar Functor.mapDerivedCategory

private theorem conjugate_transport {I C : Type*} [Category C] (F G : I → C)
    (e : ∀ i, F i ≅ G i) {i j : I} (h : i = j) :
    (e i).inv ≫ eqToHom (congrArg F h) ≫ (e j).hom =
      eqToHom (congrArg G h) := by
  subst h
  simp

set_option maxHeartbeats 2000000 in
-- Expanding the full-subcategory and total-derived comparison chains needs a larger budget.
private theorem modelLocal_ambient (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (φ : X ⟶ X)
    (B : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (uφ : (P (Profinite.padicAlgClRingObj ell) φ.left).obj B.obj ≅ B.obj)
    (x : RationalPoint X) (hx : x ≫ φ = x) :
    (localIdentification ell B x).inv ≫
      modelLocal ell φ (modelObject ell φ B uφ) x hx ≫
      (localIdentification ell B x).hom =
    eqToHom (congrArg
      (fun f : Spec (.of k) ⟶ X.left ↦ (P (Profinite.padicAlgClRingObj ell) f).obj B.obj)
      (congrArg (fun t ↦ t.left) hx).symm) ≫
      (pComp (Profinite.padicAlgClRingObj ell) x.left φ.left).hom.app B.obj ≫
      (P (Profinite.padicAlgClRingObj ell) x.left).map uφ.hom := by
  unfold modelLocal
  rw [WeilBoundedConstructible.weilStalk_obj_frobenius_hom_eq]
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.eqToHom_hom', boundedConstructibleUpperStarComp_hom_app_hom,
    boundedConstructibleUpperStar_map_hom]
  change (localIdentification ell B x).inv ≫
    (eqToHom (congrArg (fun t : RationalPoint X ↦
        (upperStar (Profinite.padicAlgClRingObj ell) t.left).leftDerivedFunctor.obj B.obj)
      hx.symm) ≫
    (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ell) x.left φ.left).hom.app B.obj ≫
    (upperStar (Profinite.padicAlgClRingObj ell) x.left).leftDerivedFunctor.map
      (((boundedConstructibleUpperStarCompatibility
          (Profinite.padicAlgClRingObj ell) ell φ).app B).hom ≫
        (leftDerivedUpperStarIsoMapDerivedCategory
          (Profinite.padicAlgClRingObj ell) φ.left).hom.app B.obj ≫ uφ.hom)) ≫
    (localIdentification ell B x).hom = _
  simp only [localIdentification, boundedConstructibleUpperStarCompatibility,
    ObjectProperty.liftCompιIso, Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  dsimp only [boundedConstructibleUpperStar, ObjectProperty.lift,
    ObjectProperty.ι, inducedFunctor, Functor.comp_obj]
  simp only [Category.id_comp, Category.comp_id]
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.map_comp, Iso.symm_hom, Category.assoc]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory]
  simp only [NatTrans.naturality, NatTrans.naturality_assoc,
    Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have ht := conjugate_transport
    (fun t : RationalPoint X ↦
      (upperStar (Profinite.padicAlgClRingObj ell) t.left).leftDerivedFunctor.obj B.obj)
    (fun t : RationalPoint X ↦ (P (Profinite.padicAlgClRingObj ell) t.left).obj B.obj)
    (fun t ↦ (Functor.leftDerivedFunctorIsoMapDerivedCategory
      (upperStar (Profinite.padicAlgClRingObj ell) t.left)).app B.obj) hx.symm
  simp only [Iso.app_inv, Iso.app_hom, Over.comp_left] at ht
  rw [reassoc_of% ht]
  simp only [pComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc]

private theorem iso_comp_trivialization_hom_app
    {A E : Type*} [Category A] [Category E]
    {F₀ F₁ F : A ⥤ E} {H : E ⥤ E}
    (e : F₀ ≅ F₁) (c : F₁ ≅ F ⋙ H) (κ : H ≅ 𝟭 E) (M : A) :
    (e ≪≫ c ≪≫ Functor.isoWhiskerLeft F κ ≪≫ Functor.rightUnitor F).hom.app M =
      e.hom.app M ≫ c.hom.app M ≫ κ.hom.app (F.obj M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  erw [Category.comp_id]

private theorem fixed_point_factorization {C : Type*} [Category C]
    {s X : C} (H g φ : X ⟶ X) (w : φ = H ≫ g) (comm : g ≫ H = H ≫ g)
    (x : s ⟶ X) (hf : x ≫ φ = x) (σ : s ⟶ s) (sq : x ≫ g = σ ≫ x) :
    x = (σ ≫ x) ≫ H := by
  rw [← sq, Category.assoc, comm, ← w, hf]

private theorem source_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (b : ℕ)
    {k : Type u} [Field k] [IsSepClosed k] (hs : (p : Γ(Spec (.of k), ⊤)) = 0)
    (σ : Spec (.of k) ⟶ Spec (.of k))
    (hi : (Spec (.of k)).iterateFrobenius hp hs b ≫ σ = 𝟙 _)
    (x : Spec (.of k) ⟶ X) (ex : x = (σ ≫ x) ≫ X.iterateFrobenius hp hX b)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarIsoIdOfIsSepClosed Λ σ).inv.app ((upperStar Λ x).obj M) ≫
      (upperStarComp Λ σ x).inv.app M =
    eqToHom (congrArg (fun f ↦ (upperStar Λ f).obj M) ex) ≫
      (upperStarComp Λ (σ ≫ x) (X.iterateFrobenius hp hX b)).hom.app M ≫
      (upperStar Λ (σ ≫ x)).map
        (𝟙 _ ≫ (upperStarIterateFrobeniusIso Λ hp hX b).hom.app M) := by
  exact upperStarIsoIdOfIsSepClosed_inv_app_comp_upperStarComp_inv_app
    Λ hp hX b hs σ hi x (X.iterateFrobenius hp hX b) rfl ex
    (upperStarIsoIdOfIsSepClosed Λ σ)
    (fun N ↦ upperStarIterateFrobeniusIso_comp_upperStarIsoIdOfIsSepClosed
      Λ hp hs b σ hi N) M

private theorem ordinary_local_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (b : ℕ)
    {k : Type u} [Field k] [IsSepClosed k] (hs : (p : Γ(Spec (.of k), ⊤)) = 0)
    (φ g : X ⟶ X) (w : φ = X.iterateFrobenius hp hX b ≫ g)
    (x : Spec (.of k) ⟶ X) (hf : x ≫ φ = x)
    (σ : Spec (.of k) ⟶ Spec (.of k)) (sq : x ≫ g = σ ≫ x)
    (hi : (Spec (.of k)).iterateFrobenius hp hs b ≫ σ = 𝟙 _)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    eqToHom (congrArg (fun f ↦ (upperStar Λ f).obj M) hf.symm) ≫
      (upperStarComp Λ x φ).hom.app M ≫
      (upperStar Λ x).map
        (eqToHom (congrArg (fun f ↦ (upperStar Λ f).obj M) w) ≫
          (upperStarComp Λ (X.iterateFrobenius hp hX b) g).hom.app M ≫
          (upperStarIterateFrobeniusIso Λ hp hX b).hom.app ((upperStar Λ g).obj M)) =
    (upperStarIsoIdOfIsSepClosed Λ σ).inv.app ((upperStar Λ x).obj M) ≫
      (upperStarComp Λ σ x).inv.app M ≫
      eqToHom (congrArg (fun f ↦ (upperStar Λ f).obj M) sq.symm) ≫
      (upperStarComp Λ x g).hom.app M := by
  have ex := fixed_point_factorization (X.iterateFrobenius hp hX b) g φ w
    (Scheme.comp_iterateFrobenius hp g hX hX b) x hf σ sq
  have hn := source_normalization Λ hp hX b hs σ hi x ex M
  simp only [Category.id_comp] at hn
  symm
  rw [reassoc_of% hn, ← eqToHom_comp_map_aux_assoc (fun f ↦ upperStar Λ f) sq.symm,
    ← eqToHom_comp_comp_hom_app_aux_assoc (fun f ↦ upperStar Λ f)
      (fun a b ↦ upperStarComp Λ a b) sq.symm,
    map_comp_hom_app_aux (fun f ↦ upperStar Λ f) (fun a b ↦ upperStarComp Λ a b),
    reassoc_of% (upperStarComp_assoc_app_eqToHom Λ x g
      (X.iterateFrobenius hp hX b) M)]
  simp only [Functor.map_comp]
  rw [comp_hom_app_comp_map_eqToHom_aux_assoc (fun f ↦ upperStar Λ f)
    (fun a b ↦ upperStarComp Λ a b) x w M]
  rw [← Functor.map_comp,
    upperStarComp_hom_app_comp_map_upperStarIterateFrobeniusIso_hom_app
      Λ hp hX hX b g M]
  simp only [Functor.map_comp]
  rw [comp_hom_app_comp_map_eqToHom_aux_assoc (fun f ↦ upperStar Λ f)
    (fun a b ↦ upperStarComp Λ a b) x (Scheme.comp_iterateFrobenius hp g hX hX b) M]
  simp only [eqToHom_trans_assoc]

section ExactNatIso

variable {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory E]
  {F G H : A ⥤ E} [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private theorem exact_natIso_trans (e : F ≅ G) (e' : G ≅ H) :
    Functor.mapDerivedCategoryNatIso (e ≪≫ e') =
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryNatIso e' := by
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_trans e e'

private theorem exact_natIso_symm (e : F ≅ G) :
    Functor.mapDerivedCategoryNatIso e.symm = (Functor.mapDerivedCategoryNatIso e).symm := by
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_symm e

private theorem exact_natIso_refl (F : A ⥤ E) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Functor.mapDerivedCategoryNatIso (Iso.refl F) = Iso.refl F.mapDerivedCategory := by
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl (F := F)

end ExactNatIso

section ExactFunctorTrivialization

private theorem exact_trivialization_comp
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory E]
    (F : A ⥤ E) (H : E ⥤ E)
    [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (κ : H ≅ 𝟭 E) :
    (Functor.mapDerivedCategoryNatIso
      (Functor.isoWhiskerLeft F κ ≪≫ Functor.rightUnitor F)).hom =
    (Functor.mapDerivedCategoryCompIso F H).hom ≫
      Functor.whiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso κ ≪≫ Functor.mapDerivedCategoryIdIso E).hom := by
  simp only [exact_natIso_trans, Iso.trans_hom]
  have h := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F κ
  have u := Functor.mapDerivedCategoryCompIso_comp_id F
  have hr : (Functor.mapDerivedCategoryNatIso (Functor.rightUnitor F)).hom =
      𝟙 F.mapDerivedCategory := by
    exact Functor.mapDerivedCategoryNatIso_refl (F := F)
  rw [hr]
  simp only [Functor.comp_id, Category.comp_id]
  ext K
  have hK := NatTrans.congr_app h K
  have uK := NatTrans.congr_app u K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hK uK ⊢
  rw [← Category.assoc, ← hK, Category.assoc, uK, NatTrans.id_app]
  erw [Category.comp_id]

private theorem exact_trivialization_comp_iso
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory E]
    (F : A ⥤ E) (H : E ⥤ E) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (κ : H ≅ 𝟭 E) :
    Functor.mapDerivedCategoryNatIso
        (Functor.isoWhiskerLeft F κ ≪≫ Functor.rightUnitor F) =
      Functor.mapDerivedCategoryCompIso F H ≪≫
        Functor.isoWhiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso κ ≪≫ Functor.mapDerivedCategoryIdIso E) ≪≫
        Functor.rightUnitor _ := by
  apply Iso.ext
  ext K
  simpa only [Functor.comp_id, Functor.comp_obj, Functor.id_obj, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom,
    Functor.rightUnitor_hom_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.comp_id, Category.assoc] using
      NatTrans.congr_app (exact_trivialization_comp F H κ) K

private theorem exact_whiskerRight
    {A E F : Type*} [Category A] [Category E] [Category F]
    [Abelian A] [Abelian E] [Abelian F]
    [HasDerivedCategory A] [HasDerivedCategory E] [HasDerivedCategory F]
    {U U' : A ⥤ E} [U.Additive] [U'.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
    (e : U ≅ U') (V : E ⥤ F) [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V] :
    Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e V) ≪≫
        Functor.mapDerivedCategoryCompIso U' V =
      Functor.mapDerivedCategoryCompIso U V ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso e) V.mapDerivedCategory := by
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_isoWhiskerRight e V

end ExactFunctorTrivialization

private theorem iso_pullback_diagram
    {A E : Type*} [Category A] [Category E]
    (F : A ⥤ E) (H G : A ⥤ A) (S : E ⥤ E) (F₀ F₁ F₂ : A ⥤ E)
    (δ₀ : F ≅ F₀) (c₀ : F₀ ≅ H ⋙ F) (α : H ≅ G) (τ : S ≅ 𝟭 E)
    (c₁ : F₁ ≅ F ⋙ S) (δ₁ : F₁ ≅ F₂) (c₂ : F₂ ≅ G ⋙ F)
    (e : ∀ M, δ₀.hom.app M ≫ c₀.hom.app M ≫ F.map (α.hom.app M) =
      τ.inv.app (F.obj M) ≫ c₁.inv.app M ≫ δ₁.hom.app M ≫ c₂.hom.app M) :
    δ₀ ≪≫ c₀ ≪≫ Functor.isoWhiskerRight α F =
      (Functor.isoWhiskerLeft F τ ≪≫ Functor.rightUnitor F).symm ≪≫
        c₁.symm ≪≫ δ₁ ≪≫ c₂ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app, Category.id_comp, Category.assoc] using e M

private theorem iso_pullback_diagram_trivialization
    {A E : Type*} [Category A] [Category E]
    (F : A ⥤ E) (H G J : A ⥤ A) (S : E ⥤ E) (T : A ⥤ A)
    (F₀ F₁ F₂ : A ⥤ E) (δ₀ : F ≅ F₀) (c₀ : F₀ ≅ H ⋙ F)
    (a : H ≅ T) (d : T ≅ G ⋙ J) (κ : J ≅ 𝟭 A) (τ : S ≅ 𝟭 E)
    (c₁ : F₁ ≅ F ⋙ S) (δ₁ : F₁ ≅ F₂) (c₂ : F₂ ≅ G ⋙ F)
    (e : ∀ M, δ₀.hom.app M ≫ c₀.hom.app M ≫
      F.map (a.hom.app M ≫ d.hom.app M ≫ κ.hom.app (G.obj M)) =
      τ.inv.app (F.obj M) ≫ c₁.inv.app M ≫ δ₁.hom.app M ≫ c₂.hom.app M) :
    δ₀ ≪≫ c₀ ≪≫ Functor.isoWhiskerRight
        (a ≪≫ d ≪≫ Functor.isoWhiskerLeft G κ ≪≫ Functor.rightUnitor G) F =
      (Functor.isoWhiskerLeft F τ ≪≫ Functor.rightUnitor F).symm ≪≫
        c₁.symm ≪≫ δ₁ ≪≫ c₂ := by
  apply iso_pullback_diagram
  intro M
  rw [iso_comp_trivialization_hom_app]
  exact e M

private theorem exact_pullback_diagram
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory E]
    (F : A ⥤ E) (H G : A ⥤ A) (S : E ⥤ E) (F₀ F₁ F₂ : A ⥤ E)
    [F.Additive] [H.Additive] [G.Additive] [S.Additive]
    [F₀.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    (δ₀ : F ≅ F₀) (c₀ : F₀ ≅ H ⋙ F) (α : H ≅ G) (τ : S ≅ 𝟭 E)
    (c₁ : F₁ ≅ F ⋙ S) (δ₁ : F₁ ≅ F₂) (c₂ : F₂ ≅ G ⋙ F)
    (e : δ₀ ≪≫ c₀ ≪≫ Functor.isoWhiskerRight α F =
      (Functor.isoWhiskerLeft F τ ≪≫ Functor.rightUnitor F).symm ≪≫
        c₁.symm ≪≫ δ₁ ≪≫ c₂) :
    Functor.mapDerivedCategoryNatIso δ₀ ≪≫
        (Functor.mapDerivedCategoryNatIso c₀ ≪≫ Functor.mapDerivedCategoryCompIso H F) ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso α) F.mapDerivedCategory =
      (Functor.isoWhiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso τ ≪≫ Functor.mapDerivedCategoryIdIso E)).symm ≪≫
        (Functor.mapDerivedCategoryNatIso c₁ ≪≫ Functor.mapDerivedCategoryCompIso F S).symm ≪≫
        Functor.mapDerivedCategoryNatIso δ₁ ≪≫
        (Functor.mapDerivedCategoryNatIso c₂ ≪≫ Functor.mapDerivedCategoryCompIso G F) := by
  have hd := congrArg (fun t ↦ Functor.mapDerivedCategoryNatIso t ≪≫
    Functor.mapDerivedCategoryCompIso G F) e
  simp only [exact_natIso_trans, exact_natIso_symm, Iso.trans_assoc] at hd
  rw [exact_whiskerRight] at hd
  rw [← exact_natIso_trans (Functor.isoWhiskerLeft F τ) (Functor.rightUnitor F),
    exact_trivialization_comp_iso] at hd
  simp only [Iso.trans_symm, Iso.trans_assoc] at hd
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.comp_id, Category.id_comp, Category.assoc]
    using congrArg (fun t ↦ t.hom.app K) hd

private theorem componentwiseTransport_naturality
    {I A E : Type*} [Category A] [Category E] (F : I → A ⥤ E)
    {i j : I} (h : i = j) {M N : A} (f : M ⟶ N) :
    (F i).map f ≫ eqToHom (congrArg (fun i ↦ (F i).obj N) h) =
      eqToHom (congrArg (fun i ↦ (F i).obj M) h) ≫ (F j).map f := by
  cases h
  simp

private def componentwiseTransport {I A E : Type*} [Category A] [Category E]
    (F : I → A ⥤ E) {i j : I} (h : i = j) : F i ≅ F j :=
  NatIso.ofComponents (fun M ↦ eqToIso (congrArg (fun i ↦ (F i).obj M) h))
    (fun f ↦ componentwiseTransport_naturality F h f)

private theorem componentwiseTransport_hom_app
    {I A E : Type*} [Category A] [Category E] (F : I → A ⥤ E)
    {i j : I} (h : i = j) (M : A) :
    (componentwiseTransport F h).hom.app M =
      eqToHom (congrArg (fun i ↦ (F i).obj M) h) := rfl

private theorem componentwiseTransport_eq_eqToIso
    {I A E : Type*} [Category A] [Category E] (F : I → A ⥤ E)
    {i j : I} (h : i = j) :
    componentwiseTransport F h = eqToIso (congrArg F h) := by
  cases h
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [componentwiseTransport_hom_app, eqToIso.hom, eqToHom_refl, NatTrans.id_app]

private theorem exact_pullback_congr
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    Functor.mapDerivedCategoryNatIso (upperStarEqToIso Λ h) =
      componentwiseTransport (P Λ) h := by
  cases h
  have hc : upperStarEqToIso Λ (rfl : f = f) = Iso.refl _ := by
    ext M
    simp [upperStarEqToIso]
  rw [hc, exact_natIso_refl, componentwiseTransport_eq_eqToIso]
  rfl

set_option maxHeartbeats 2000000 in
-- Elaborating the exact derived pullback comparison requires the module-category instances.
private theorem exact_kappa
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (b : ℕ)
    (φ g : X ⟶ X) (w : φ = X.iterateFrobenius hp hX b ≫ g) :
    Functor.mapDerivedCategoryNatIso
      (upperStarEqToIso Λ w ≪≫ upperStarComp Λ (X.iterateFrobenius hp hX b) g ≪≫
        Functor.isoWhiskerLeft (upperStar Λ g)
          (upperStarIterateFrobeniusIso Λ hp hX b) ≪≫ Functor.rightUnitor _) =
    kappa Λ p hp hX b g φ w := by
  rw [exact_natIso_trans, exact_natIso_trans,
    exact_pullback_congr, exact_trivialization_comp_iso,
    componentwiseTransport_eq_eqToIso]
  simp only [kappa, pComp, Iso.trans_assoc]

set_option maxHeartbeats 2000000 in
-- The several exact pullback functors each synthesize the module-category instances.
private theorem exact_local_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (b : ℕ)
    {k : Type u} [Field k] [IsSepClosed k] (hs : (p : Γ(Spec (.of k), ⊤)) = 0)
    (φ g : X ⟶ X) (w : φ = X.iterateFrobenius hp hX b ≫ g)
    (x : Spec (.of k) ⟶ X) (hf : x ≫ φ = x)
    (σ : Spec (.of k) ⟶ Spec (.of k)) (sq : x ≫ g = σ ≫ x)
    (hi : (Spec (.of k)).iterateFrobenius hp hs b ≫ σ = 𝟙 _)
    (K : D Λ X) :
    eqToHom (congrArg (fun f ↦ (P Λ f).obj K) hf.symm) ≫
      (pComp Λ x φ).hom.app K ≫ (P Λ x).map ((kappa Λ p hp hX b g φ w).hom.app K) =
    (pointReparametrization Λ σ).inv.app ((P Λ x).obj K) ≫
      (pComp Λ σ x).inv.app K ≫
      eqToHom (congrArg (fun f ↦ (P Λ f).obj K) sq.symm) ≫
      (pComp Λ x g).hom.app K := by
  let α := upperStarEqToIso Λ w ≪≫ upperStarComp Λ (X.iterateFrobenius hp hX b) g ≪≫
    Functor.isoWhiskerLeft (upperStar Λ g) (upperStarIterateFrobeniusIso Λ hp hX b) ≪≫
    Functor.rightUnitor _
  have e := iso_pullback_diagram_trivialization
    (upperStar Λ x) (upperStar Λ φ) (upperStar Λ g)
    (upperStar Λ (X.iterateFrobenius hp hX b)) (upperStar Λ σ)
    (upperStar Λ (X.iterateFrobenius hp hX b ≫ g))
    (upperStar Λ (x ≫ φ)) (upperStar Λ (σ ≫ x)) (upperStar Λ (x ≫ g))
    (upperStarEqToIso Λ hf.symm) (upperStarComp Λ x φ)
    (upperStarEqToIso Λ w) (upperStarComp Λ (X.iterateFrobenius hp hX b) g)
    (upperStarIterateFrobeniusIso Λ hp hX b) (upperStarIsoIdOfIsSepClosed Λ σ)
    (upperStarComp Λ σ x) (upperStarEqToIso Λ sq.symm) (upperStarComp Λ x g)
    (fun M ↦ by simpa only [upperStarEqToIso_hom_app] using
      ordinary_local_comparison Λ hp hX b hs φ g w x hf σ sq hi M)
  have hd := exact_pullback_diagram (upperStar Λ x) (upperStar Λ φ) (upperStar Λ g)
    (upperStar Λ σ) (upperStar Λ (x ≫ φ)) (upperStar Λ (σ ≫ x)) (upperStar Λ (x ≫ g))
    (upperStarEqToIso Λ hf.symm) (upperStarComp Λ x φ) α (upperStarIsoIdOfIsSepClosed Λ σ)
    (upperStarComp Λ σ x) (upperStarEqToIso Λ sq.symm) (upperStarComp Λ x g) e
  rw [show Functor.mapDerivedCategoryNatIso α = kappa Λ p hp hX b g φ w from
    exact_kappa Λ hp hX b φ g w] at hd
  simp only [exact_pullback_congr] at hd
  simpa only [pComp, pointReparametrization, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    componentwiseTransport_hom_app,
    Category.assoc] using congrArg (fun t ↦ t.hom.app K) hd

set_option maxHeartbeats 2000000 in
-- Elaborating the concrete module-category instances needs a larger budget.
private theorem concrete_comparison
    (ell : ℕ) [Fact ell.Prime]
    {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (b : ℕ)
    {k : Type u} [Field k] [IsSepClosed k] (hs : (p : Γ(Spec (.of k), ⊤)) = 0)
    (φ g : X ⟶ X) (w : φ = X.iterateFrobenius hp hX b ≫ g)
    (x : Spec (.of k) ⟶ X) (hf : x ≫ φ = x)
    (σ : Spec (.of k) ⟶ Spec (.of k)) (sq : x ≫ g = σ ≫ x)
    (hi : (Spec (.of k)).iterateFrobenius hp hs b ≫ σ = 𝟙 _)
    (K : D (Profinite.padicAlgClRingObj ell) X) :
    eqToHom (congrArg (fun f ↦ (P (Profinite.padicAlgClRingObj ell) f).obj K) hf.symm) ≫
      (pComp (Profinite.padicAlgClRingObj ell) x φ).hom.app K ≫
        (P (Profinite.padicAlgClRingObj ell) x).map
          ((kappa (Profinite.padicAlgClRingObj ell) p hp hX b g φ w).hom.app K) =
    (pointReparametrization (Profinite.padicAlgClRingObj ell) σ).inv.app
        ((P (Profinite.padicAlgClRingObj ell) x).obj K) ≫
      (pComp (Profinite.padicAlgClRingObj ell) σ x).inv.app K ≫
      eqToHom (congrArg (fun f ↦ (P (Profinite.padicAlgClRingObj ell) f).obj K) sq.symm) ≫
      (pComp (Profinite.padicAlgClRingObj ell) x g).hom.app K := by
  exact exact_local_comparison (Profinite.padicAlgClRingObj ell) hp hX b hs
    φ g w x hf σ sq hi K

private theorem retraction_cancel {C : Type*} [Category C]
    {A B : C} (x : A ⟶ B) (r : B ⟶ A) (hx : x ≫ r = 𝟙 A)
    (f : A ⟶ A) (h : f ≫ x = x) : f = 𝟙 A := by
  calc
    f = f ≫ (x ≫ r) := by rw [hx, Category.comp_id]
    _ = (f ≫ x) ≫ r := (Category.assoc _ _ _).symm
    _ = 𝟙 A := by rw [h, hx]

private theorem pointFrobenius_inverse {k : Type u} [Field k]
    {X : Over (Spec (.of k))} {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X.left, ⊤)) = 0) (hs : (p : Γ(Spec (.of k), ⊤)) = 0) (b : ℕ)
    (φ : X ⟶ X) (g : X.left ⟶ X.left)
    (w : φ.left = X.left.iterateFrobenius hp hX b ≫ g)
    (x : RationalPoint X) (hx : x ≫ φ = x)
    (σ : Spec (.of k) ⟶ Spec (.of k)) (sq : x.left ≫ g = σ ≫ x.left) :
    (Spec (.of k)).iterateFrobenius hp hs b ≫ σ = 𝟙 _ := by
  have hf : x.left ≫ φ.left = x.left := congrArg (fun t ↦ t.left) hx
  have hi : (Spec (.of k)).iterateFrobenius hp hs b ≫ σ = 𝟙 _ := by
    have hnat := Scheme.comp_iterateFrobenius (Y := Spec (.of k)) hp x.left hX hs b
    have ht : ((Spec (.of k)).iterateFrobenius hp hs b ≫ σ) ≫ x.left = x.left := by
      calc
        _ = (Spec (.of k)).iterateFrobenius hp hs b ≫ (x.left ≫ g) := by
          rw [Category.assoc, ← sq]
        _ = (x.left ≫ X.left.iterateFrobenius hp hX b) ≫ g := by
          rw [← Category.assoc, ← hnat]
        _ = x.left ≫ φ.left := by rw [Category.assoc, ← w]
        _ = x.left := hf
    exact retraction_cancel x.left X.hom (Over.w x) _ ht
  exact hi

set_option maxHeartbeats 2000000 in
-- Keep the comparison isomorphism abstract while composing the local operators.
private theorem modelLocal_of_comparison (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [IsSepClosed k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (φ : X ⟶ X) (g : X.left ⟶ X.left)
    (κ : P (Profinite.padicAlgClRingObj ell) φ.left ≅ P (Profinite.padicAlgClRingObj ell) g)
    (B : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (θ : (P (Profinite.padicAlgClRingObj ell) g).obj B.obj ≅ B.obj)
    (x : RationalPoint X) (hx : x ≫ φ = x)
    (hf : x.left ≫ φ.left = x.left)
    (σ : Spec (.of k) ⟶ Spec (.of k)) (sq : x.left ≫ g = σ ≫ x.left)
    (hc : eqToHom (congrArg
      (fun f : Spec (.of k) ⟶ X.left ↦ (P (Profinite.padicAlgClRingObj ell) f).obj B.obj)
      hf.symm) ≫
        (pComp (Profinite.padicAlgClRingObj ell)
          (show Spec (.of k) ⟶ X.left from x.left) φ.left).hom.app B.obj ≫
        (P (Profinite.padicAlgClRingObj ell)
          (show Spec (.of k) ⟶ X.left from x.left)).map (κ.hom.app B.obj) =
      (pointReparametrization (Profinite.padicAlgClRingObj ell) σ).inv.app
          ((P (Profinite.padicAlgClRingObj ell)
            (show Spec (.of k) ⟶ X.left from x.left)).obj B.obj) ≫
        (pComp (Profinite.padicAlgClRingObj ell) σ
          (show Spec (.of k) ⟶ X.left from x.left)).inv.app B.obj ≫
        eqToHom (congrArg (fun f : Spec (.of k) ⟶ X.left ↦
          (P (Profinite.padicAlgClRingObj ell) f).obj B.obj) sq.symm) ≫
        (pComp (Profinite.padicAlgClRingObj ell)
          (show Spec (.of k) ⟶ X.left from x.left) g).hom.app B.obj) :
    (localIdentification ell B x).inv ≫
      modelLocal ell φ (modelObject ell φ B (κ.app B.obj ≪≫ θ)) x hx ≫
        (localIdentification ell B x).hom =
      stalkReturn (Profinite.padicAlgClRingObj ell) x.left g σ sq θ.hom := by
  rw [modelLocal_ambient]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.map_comp]
  rw [reassoc_of% hc]
  rfl

-- Keep the geometric equations abstract during the derived operator comparison.
private theorem modelLocal_stalkReturn (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [IsSepClosed k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X.left, ⊤)) = 0)
    (hs : (p : Γ(Spec (.of k), ⊤)) = 0) (b : ℕ)
    (φ : X ⟶ X) (g : X.left ⟶ X.left)
    (w : φ.left = X.left.iterateFrobenius hp hX b ≫ g)
    (B : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left))
    (θ : (P (Profinite.padicAlgClRingObj ell) g).obj B.obj ≅ B.obj)
    (x : RationalPoint X) (hx : x ≫ φ = x)
    (σ : Spec (.of k) ⟶ Spec (.of k)) (sq : x.left ≫ g = σ ≫ x.left)
    (hf : x.left ≫ φ.left = x.left)
    (hi : (Spec (.of k)).iterateFrobenius hp hs b ≫ σ = 𝟙 _) :
    (localIdentification ell B x).inv ≫
      modelLocal ell φ (modelObject ell φ B
        ((kappa (Profinite.padicAlgClRingObj ell) p hp hX b g φ.left w).app B.obj ≪≫ θ))
        x hx ≫ (localIdentification ell B x).hom =
      stalkReturn (Profinite.padicAlgClRingObj ell) x.left g σ sq θ.hom := by
  exact modelLocal_of_comparison ell φ g
    (kappa (Profinite.padicAlgClRingObj ell) p hp hX b g φ.left w) B θ x hx hf σ sq
    (concrete_comparison ell hp hX b hs
      φ.left g w x.left hf σ sq hi B.obj)

private theorem localPositivePower_eq {T : Scheme.{u}} (f : T ⟶ T) (n : ℕ) :
    WeilConjectures.localPositivePower f n = ((End.of f) ^ (n + 1)).asHom := by
  induction n with
  | zero => simp [WeilConjectures.localPositivePower]
  | succ n ih =>
      simp only [WeilConjectures.localPositivePower, ih, pow_succ', End.mul_def]

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

set_option maxHeartbeats 2000000 in
-- Unfolding the two derived/full-subcategory comparison chains needs a larger budget.
/-- The canonical fixed lift of an extension-valued point has the normalized stalk return.
Source: latest blueprint, lem-fd-realness-pushforward.proof.md, Step 1;
original operator comparison proof step 12.
(blueprint: lem-fd-condensed-model-frobenius-local).

Proof: base change the extension-valued point along the inclusion of its finite
subfield into the fixed algebraic closure. The pullback universal property constructs x
and proves its specified model projection. The q^m power map is identity on that finite
subfield, so naturalness of model Frobenius proves hx. The coefficient action and the
same finite-field identity give the semilinear square wx by the two pullback projections.
Use naturalness of the absolute Frobenius module trivialization along x. Its component
at the geometric point is the inverse of the canonical point reparametrization, as is
seen on all profinite test objects. Substitute the modelObject structure and the
published exact-to-derived and full-subcategory identifications. The two ways around
the resulting pullback square agree by pullback coherence; after composing pullback of
theta^[m], their common composite is stalkReturn. This is equality of actual derived
module morphisms, before cohomology. The argument uses neither compactification nor a
global operator. The case m=0 is excluded and the empty scheme has no points to check. -/
theorem condensed_model_frobenius_local
    [IsSeparated X₀.hom] (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D₀.p)]
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D₀ X₀)) (w : Factorization D₀ X₀)
    (hB : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D₀.geometricFiber X₀).left)
      K.carrier.obj) :
(∀ (m : ℕ) (hm : 1 ≤ m) (z : D₀.extensionPoints X₀ m hm),
        ∃ (x : RationalPoint (D₀.geometricFiber X₀))
          (hx : x ≫ frobeniusIterate (modelEnd D₀ X₀) m = x)
          (wx : x.left ≫ ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m) =
            ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m) ≫ x.left),
          x.left ≫ pullback.fst X₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))) =
            Spec.map (CommRingCat.ofHom (D₀.extensionSubfield m hm).subtype) ≫ z.left ∧
          (localIdentification ell ⟨K.carrier.obj, hB⟩ x).inv ≫
            modelLocal ell (frobeniusIterate (modelEnd D₀ X₀) m)
              (modelObject ell (frobeniusIterate (modelEnd D₀ X₀) m) ⟨K.carrier.obj, hB⟩
                (modelStructure D₀ X₀ ell K w m)) x hx ≫
            (localIdentification ell ⟨K.carrier.obj, hB⟩ x).hom =
          stalkReturn (Profinite.padicAlgClRingObj ell) x.left
            ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m)
            ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m) wx
            (iterateStructure (Profinite.padicAlgClRingObj ell)
              (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) (ambientStructure _ K) m).hom) := by
  intro m hm z
  change (Over.mk (Spec.map (CommRingCat.ofHom (D₀.extensionEmbedding m hm))) ⟶ X₀) at z
  let x : RationalPoint (D₀.geometricFiber X₀) :=
    Over.homMk (WeilConjectures.localExtensionPoint D₀ X₀ m hm z) (by
      change WeilConjectures.localExtensionPoint D₀ X₀ m hm z ≫
        pullback.snd X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))) = 𝟙 _
      exact pullback.lift_snd _ _ _)
  have hx : x ≫ frobeniusIterate (modelEnd D₀ X₀) m = x := by
    let L := D₀.extensionSubfield m hm
    have hc : Nat.card L = D₀.q ^ m :=
      (FiniteField.exists_unique_subfield_of_closure D₀.p D₀.a D₀.q D₀.prime D₀.exponent_pos
        D₀.cardinality_eq D₀.k₀ D₀.card_base D₀.k m hm).choose_spec.2.1
    have hq : 0 < D₀.q := by
      rw [← D₀.card_base]
      exact Nat.card_pos
    let : Finite L := (Nat.card_pos_iff.mp (by rw [hc]; exact pow_pos hq m)).2
    let : Fintype L := Fintype.ofFinite L
    have hz : z.left ≫ X₀.left.iterateFrobenius D₀.prime
        (D₀.model_characteristic X₀.hom) (D₀.a * m) = z.left := by
      have ht := Scheme.isFrobenius_iterateFrobenius D₀.prime X₀.left
        (D₀.model_characteristic X₀.hom) (D₀.a * m)
      have hp (r : L) : r = r ^ D₀.p ^ (D₀.a * m) := by
        rw [pow_mul, ← D₀.cardinality_eq, ← hc, Nat.card_eq_fintype_card]
        exact (FiniteField.pow_card r).symm
      simpa only [Spec.map_id, Category.id_comp] using ht z.left (𝟙 _) hp
    let pr := pullback.fst X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))
    have hpr (n : ℕ) : ((End.of (D₀.schemeFrobenius X₀)) ^ n).asHom ≫ pr =
        pr ≫ X₀.left.iterateFrobenius D₀.prime (D₀.model_characteristic X₀.hom)
          (D₀.a * n) := by
      have h1 : D₀.schemeFrobenius X₀ ≫ pr =
          pr ≫ X₀.left.iterateFrobenius D₀.prime (D₀.model_characteristic X₀.hom) D₀.a :=
        (D₀.relativeFrobenius_projections X₀).1
      induction n with
      | zero => simp [End.one_def, Scheme.iterateFrobenius_zero]
      | succ n ih =>
          rw [pow_succ', End.mul_def, Category.assoc, h1, ← Category.assoc, ih,
            Category.assoc, ← Scheme.iterateFrobenius_add, Nat.mul_succ]
    apply Over.OverMorphism.ext
    change x.left ≫ (frobeniusIterate (modelEnd D₀ X₀) m).left = x.left
    apply pullback.hom_ext
    · rw [Category.assoc, frobeniusIterate_left]
      simp only [modelEnd, Over.homMk_left]
      change x.left ≫ (((End.of (D₀.schemeFrobenius X₀)) ^ m).asHom ≫ pr) =
        x.left ≫ pr
      rw [hpr, ← Category.assoc]
      change (WeilConjectures.localExtensionPoint D₀ X₀ m hm z ≫ pr) ≫
        X₀.left.iterateFrobenius D₀.prime (D₀.model_characteristic X₀.hom)
          (D₀.a * m) = WeilConjectures.localExtensionPoint D₀ X₀ m hm z ≫ pr
      dsimp only [pr, WeilConjectures.localExtensionPoint]
      rw [pullback.lift_fst, Category.assoc, hz]
    · change (x.left ≫ (frobeniusIterate (modelEnd D₀ X₀) m).left) ≫
        (D₀.geometricFiber X₀).hom = x.left ≫ (D₀.geometricFiber X₀).hom
      rw [Category.assoc, Over.w]
  have wx : x.left ≫ ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m) =
      ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m) ≫ x.left := by
    have h := WeilConjectures.localExtensionPoint_return D₀ X₀ m hm z
    rw [localPositivePower_eq, localPositivePower_eq, Nat.sub_add_cancel hm] at h
    simpa only [x, Over.homMk_left, StrictWeil.modelFrobenius, StrictWeil.pointFrobenius,
      WeilConjectures.FiniteFieldDatum.geometricFrobenius,
      WeilConjectures.frobeniusPointIso,
      FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv] using h
  refine ⟨x, hx, wx, ?_, ?_⟩
  · dsimp [x]
    simp [WeilConjectures.localExtensionPoint]
  · let hX := D₀.model_characteristic
      (pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))) ≫ X₀.hom)
    let hs := D₀.model_characteristic
      (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))
    have hi := pointFrobenius_inverse D₀.prime hX hs (D₀.a * m)
      (frobeniusIterate (modelEnd D₀ X₀) m) _ (w m) x hx _ wx
    exact modelLocal_stalkReturn ell D₀.prime hX hs
      (D₀.a * m) (frobeniusIterate (modelEnd D₀ X₀) m) _ (w m)
      ⟨K.carrier.obj, hB⟩ (iterateStructure _ _ (ambientStructure _ K) m) x hx _ wx
      (congrArg (fun t ↦ t.left) hx) hi

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
