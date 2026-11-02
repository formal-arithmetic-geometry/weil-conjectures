/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointTrivializationComposition
import WeilConjectures.CategoryTheory.PullbackFamily

/-! # Composition of actual semilinear point comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

private def genericComparison {B : Type*} [Category B] {E : B → Type*}
    [∀ X, Category (E X)]
    (P : ∀ {X Y : B}, (X ⟶ Y) → E Y ⥤ E X)
    (c : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {S : B} (τ : ∀ f : S ⟶ S, P f ≅ 𝟭 (E S))
    {Y : B} (a : Y ⟶ Y) {z z' : S ⟶ Y} {σ : S ⟶ S}
    (h : z ≫ a = σ ≫ z') : P z' ⋙ 𝟭 (E S) ≅ P a ⋙ P z :=
  Functor.isoWhiskerLeft (P z') (τ σ).symm ≪≫ (c σ z').symm ≪≫
    eqToIso (congrArg (fun f ↦ P f) h.symm) ≪≫ c z a

private theorem genericComparison_hom_app {B : Type*} [Category B] {E : B → Type*}
    [∀ X, Category (E X)]
    (P : ∀ {X Y : B}, (X ⟶ Y) → E Y ⥤ E X)
    (c : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {S : B} (τ : ∀ f : S ⟶ S, P f ≅ 𝟭 (E S))
    {Y : B} (a : Y ⟶ Y) {z z' : S ⟶ Y} {σ : S ⟶ S}
    (h : z ≫ a = σ ≫ z') (M : E Y) :
    (genericComparison P c τ a h).hom.app M = (τ σ).inv.app ((P z').obj M) ≫
      (c σ z').inv.app M ≫
      eqToHom (congrArg (fun f ↦ (P f).obj M) h.symm) ≫ (c z a).hom.app M := by
  simp only [genericComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    eqToIso.hom, eqToHom_app]

private theorem genericCompCongrRight {B : Type*} [Category B] {E : B → Type*}
    [∀ X, Category (E X)]
    (P : ∀ {X Y : B}, (X ⟶ Y) → E Y ⥤ E X)
    (c : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {S X Y : B} (f : S ⟶ X) {g g' : X ⟶ Y} (h : g = g') (M : E Y) :
    (c f g).inv.app M ≫
        eqToHom (congrArg (fun t ↦ (P t).obj M) (congrArg (f ≫ ·) h)) ≫
        (c f g').hom.app M =
      (P f).map (eqToHom (congrArg (fun t ↦ (P t).obj M) h)) := by
  subst g'
  simp

private theorem genericComparison_comp {B : Type*} [Category B] {E : B → Type*}
    [∀ X, Category (E X)]
    (P : ∀ {X Y : B}, (X ⟶ Y) → E Y ⥤ E X)
    (c : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    (A : PullbackAssoc P c)
    {S : B} (τ : ∀ f : S ⟶ S, P f ≅ 𝟭 (E S))
    (hτ : ∀ (f g : S ⟶ S) (N : E S), (τ (f ≫ g)).inv.app N =
      (τ f).inv.app N ≫ (P f).map ((τ g).inv.app N) ≫ (c f g).inv.app N)
    {Y : B} (a b : Y ⟶ Y) (z₀ z₁ z₂ : S ⟶ Y) (σ ρ : S ⟶ S)
    (h₁ : z₀ ≫ a = σ ≫ z₁) (h₂ : z₁ ≫ b = ρ ≫ z₂)
    (h : z₀ ≫ (a ≫ b) = (σ ≫ ρ) ≫ z₂) (M : E Y) :
    (genericComparison P c τ b h₂).hom.app M ≫
        (genericComparison P c τ a h₁).hom.app ((P b).obj M) =
      (genericComparison P c τ (a ≫ b) h).hom.app M ≫
        (P z₀).map ((c a b).hom.app M) := by
  have hc₁ : (c (z₀ ≫ a) b).hom.app M =
      eqToHom (congrArg (fun t ↦ (P t).obj M) (congrArg (· ≫ b) h₁)) ≫
        (c (σ ≫ z₁) b).hom.app M ≫
        eqToHom (congrArg (fun t ↦ (P t).obj ((P b).obj M)) h₁.symm) := by
    have ht := congrArg (fun v ↦ v ≫ eqToHom
      (congrArg (fun t ↦ (P t).obj ((P b).obj M)) h₁.symm))
      (pullbackComp_hom_app_comp_eqToHom_left (c := c) h₁ b M)
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using ht
  have hc₂ : (c (σ ≫ z₁) b).hom.app M =
      eqToHom (congrArg (fun t ↦ (P t).obj M) (Category.assoc σ z₁ b)) ≫
        (c σ (z₁ ≫ b)).hom.app M ≫ (P σ).map ((c z₁ b).hom.app M) ≫
        (c σ z₁).inv.app ((P b).obj M) := by
    have ht := congrArg (fun v ↦ v ≫ (c σ z₁).inv.app ((P b).obj M))
      (A.hom_app σ z₁ b M)
    simpa only [Category.assoc (obj := E S), Iso.hom_inv_id_app,
      Category.comp_id (obj := E S), Functor.comp_obj] using ht
  have hc₃ : (c σ ρ).inv.app ((P z₂).obj M) ≫ (c (σ ≫ ρ) z₂).inv.app M =
      (P σ).map ((c ρ z₂).inv.app M) ≫ (c σ (ρ ≫ z₂)).inv.app M ≫
        eqToHom (congrArg (fun t ↦ (P t).obj M) (Category.assoc σ ρ z₂).symm) := by
    have he : (c (σ ≫ ρ) z₂).app M ≪≫ (c σ ρ).app ((P z₂).obj M) =
        eqToIso (congrArg (fun t ↦ (P t).obj M) (Category.assoc σ ρ z₂)) ≪≫
          (c σ (ρ ≫ z₂)).app M ≪≫ (P σ).mapIso ((c ρ z₂).app M) := by
      apply Iso.ext
      simpa only [Iso.trans_hom, Iso.app_hom, eqToIso.hom, Functor.mapIso_hom,
        Category.assoc] using A.hom_app σ ρ z₂ M
    simpa only [Iso.trans_inv, Iso.app_inv, eqToIso.inv, Functor.mapIso_inv,
      Category.assoc (obj := E S)]
      using congrArg Iso.inv he
  have hn := (τ σ).inv.naturality
    ((genericComparison P c τ b h₂).hom.app M)
  symm
  simp only [genericComparison_hom_app,
    Category.assoc (obj := E S)]
  rw [A.hom_app_comp_map_hom_app z₀ a b M]
  rw [reassoc_of% hc₁, reassoc_of% hc₂, hτ]
  simp only [Category.assoc (obj := E S)]
  rw [reassoc_of% hc₃]
  simp only [eqToHom_trans_assoc]
  rw [reassoc_of% (genericCompCongrRight P c σ h₂.symm M)]
  have hn' := congrArg (fun v ↦ v ≫
    (c σ z₁).inv.app ((P b).obj M) ≫
    eqToHom (congrArg (fun t ↦ (P t).obj ((P b).obj M)) h₁.symm) ≫
    (c z₀ a).hom.app ((P b).obj M)) hn.symm
  simpa only [genericComparison_hom_app,
    Functor.id_map, Functor.comp_obj, Functor.id_obj, Functor.map_comp,
    Category.assoc (obj := E S)] using hn'


private theorem genericComparison_change {B : Type*} [Category B] {E : B → Type*}
    [∀ X, Category (E X)]
    (P : ∀ {X Y : B}, (X ⟶ Y) → E Y ⥤ E X)
    (c : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {S : B} (τ : ∀ f : S ⟶ S, P f ≅ 𝟭 (E S))
    {Y : B} {a b : Y ⟶ Y} (z z' : S ⟶ Y) {σ ρ : S ⟶ S}
    (ha : a = b) (hσ : σ = ρ)
    (h : z ≫ a = σ ≫ z') (h' : z ≫ b = ρ ≫ z') (M : E Y) :
    (genericComparison P c τ a h).hom.app M ≫
        (P z).map (eqToHom (congrArg (fun t ↦ (P t).obj M) ha)) =
      (genericComparison P c τ b h').hom.app M := by
  subst b
  subst ρ
  simp only [eqToHom_refl, Functor.map_id, Functor.comp_obj, Functor.id_obj,
    Category.comp_id (obj := E S)]

private theorem genericComparison_map_comp {B : Type*} [Category B] {E : B → Type*}
    [∀ X, Category (E X)]
    (P : ∀ {X Y : B}, (X ⟶ Y) → E Y ⥤ E X)
    (c : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    (A : PullbackAssoc P c)
    {S : B} (τ : ∀ f : S ⟶ S, P f ≅ 𝟭 (E S))
    (hτ : ∀ (f g : S ⟶ S) (N : E S), (τ (f ≫ g)).inv.app N =
      (τ f).inv.app N ≫ (P f).map ((τ g).inv.app N) ≫ (c f g).inv.app N)
    {Y : B} (a b : Y ⟶ Y) (z₀ z₁ z₂ : S ⟶ Y) (σ ρ : S ⟶ S)
    (h₁ : z₀ ≫ a = σ ≫ z₁) (h₂ : z₁ ≫ b = ρ ≫ z₂)
    (h : z₀ ≫ (a ≫ b) = (σ ≫ ρ) ≫ z₂) (M : E Y)
    (φ : (P a).obj M ⟶ M) (ψ : (P b).obj M ⟶ M) :
    (genericComparison P c τ b h₂).hom.app M ≫ (P z₁).map ψ ≫
        (genericComparison P c τ a h₁).hom.app M ≫ (P z₀).map φ =
      (genericComparison P c τ (a ≫ b) h).hom.app M ≫
        (P z₀).map ((c a b).hom.app M ≫ (P a).map ψ ≫ φ) := by
  have hn := (genericComparison P c τ a h₁).hom.naturality ψ
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% (genericComparison_comp P c A τ hτ a b z₀ z₁ z₂ σ ρ h₁ h₂ h M)]
  simp only [Functor.map_comp]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem pullback_assoc : PullbackAssoc (upperStar Λ) (fun f g ↦ upperStarComp Λ f g) := by
  intro X Y Z V f g h
  exact upperStarComp_assoc Λ f g h

private theorem trivialization_inv_comp {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (f g : Spec (.of Ω) ⟶ Spec (.of Ω))
    (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of Ω)))) :
    (upperStarIsoIdOfIsSepClosed Λ (f ≫ g)).inv.app N =
      (upperStarIsoIdOfIsSepClosed Λ f).inv.app N ≫
        (upperStar Λ f).map ((upperStarIsoIdOfIsSepClosed Λ g).inv.app N) ≫
        (upperStarComp Λ f g).inv.app N := by
  apply (cancel_epi ((upperStarIsoIdOfIsSepClosed Λ (f ≫ g)).hom.app N)).1
  rw [Iso.hom_inv_id_app]
  rw [← sepClosedPointTrivialization_comp Λ f g N]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]

private theorem trivialization_inv_iso_comp {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (f g : Spec (.of Ω) ⟶ Spec (.of Ω)) :
    (upperStarIsoIdOfIsSepClosed Λ (f ≫ g)).symm =
      (upperStarIsoIdOfIsSepClosed Λ f).symm ≪≫
        (Functor.leftUnitor (upperStar Λ f)).symm ≪≫
        Functor.isoWhiskerRight (upperStarIsoIdOfIsSepClosed Λ g).symm (upperStar Λ f) ≪≫
        (upperStarComp Λ f g).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Category.id_comp, Category.assoc] using
    trivialization_inv_comp Λ f g N

private theorem upperStarCongr_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    upperStarCongr Λ h = eqToIso (congrArg (fun t ↦ upperStar Λ t) h) := rfl

private theorem pointComparison_eq {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {Y : Scheme.{u}} (a : Y ⟶ Y) {z z' : Spec (.of Ω) ⟶ Y}
    {σ : Spec (.of Ω) ⟶ Spec (.of Ω)} (h : z ≫ a = σ ≫ z') :
    pointComparison Λ (upperStarIsoIdOfIsSepClosed Λ σ) a h =
      CategoryTheory.genericComparison (upperStar Λ) (fun f g ↦ upperStarComp Λ f g)
        (fun f ↦ upperStarIsoIdOfIsSepClosed Λ f) a h := rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedModule

private theorem positivePower_add {Y : Scheme.{u}} (a : Y ⟶ Y) (n m : ℕ) :
    localPositivePower a (n + m + 1) = localPositivePower a n ≫ localPositivePower a m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change localPositivePower a (n + m + 1) ≫ a =
      localPositivePower a n ≫ (localPositivePower a m ≫ a)
    rw [ih, Category.assoc]

private theorem step_eq (l : ℕ) [Fact l.Prime] {Y : Scheme.{u}}
    (a : Y ⟶ Y) (M : Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (n : ℕ) :
    iterateStep l a M θ n = evaluateStep
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a n))
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a (n + 1)))
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) (localPositivePower a n) a)
      M θ := by
  unfold iterateStep
  rfl

private theorem chain_succ {C : Type*} [Category C] (P : ℕ → C) (M : C)
    (initial : P 0 ≅ M) (step : ∀ n : ℕ, P (n + 1) ≅ P n) (n : ℕ) :
    isoChain P M initial step (n + 1) = step n ≪≫ isoChain P M initial step n := rfl

private theorem genericIterationProps {X : Scheme.{u}} {C : Type*} [Category C]
    (P : (X ⟶ X) → C ⥤ C)
    (c : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f)
    (a : X ⟶ X) (N : C) (θ : (P a).obj N ≅ N)
    (c₀ : P (localPositivePower a 0) ≅ P a) (hc₀ : c₀ =
      eqToIso (congrArg P (show localPositivePower a 0 = a from rfl)))
    (S : ∀ n, (P (localPositivePower a (n + 1))).obj N ≅
      (P (localPositivePower a n)).obj N)
    (hS : ∀ n, S n = evaluateStep (P (localPositivePower a n)) (P a)
      (P (localPositivePower a (n + 1))) (c (localPositivePower a n) a) N θ)
    (I : ∀ n, (P (localPositivePower a n)).obj N ≅ N)
    (hI : I = isoChain (fun n ↦ (P (localPositivePower a n)).obj N) N
      (evaluateInitial (P (localPositivePower a 0)) (P a) c₀ N θ) S) :
    I 0 = θ ∧ ∀ n, I (n + 1) = (c (localPositivePower a n) a).app N ≪≫
      (P (localPositivePower a n)).mapIso θ ≪≫ I n := by
  subst I
  constructor
  · change evaluateInitial (P a) (P a) c₀ N θ = θ
    rw [hc₀]
    exact Iso.refl_trans θ
  · intro n
    rw [chain_succ, hS]
    exact Iso.trans_assoc _ _ _

private theorem iterate_def (l : ℕ) [Fact l.Prime] {Y : Scheme.{u}}
    (a : Y ⟶ Y) (M : Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M) :
    iterate l a M θ = isoChain
      (fun n ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (localPositivePower a n)).obj M) M
      (evaluateInitial
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a 0))
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
        (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l)
          (show localPositivePower a 0 = a from rfl)) M θ) (iterateStep l a M θ) := by
  unfold iterate
  rfl

private theorem append_block {X : Scheme.{u}} {C : Type*} [Category C]
    (P : (X ⟶ X) → C ⥤ C)
    (c : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f)
    (hc : ∀ (f g e : X ⟶ X) (N : C),
      (c (f ≫ g) e).hom.app N ≫ (c f g).hom.app ((P e).obj N) =
        eqToHom (congrArg (fun t ↦ (P t).obj N) (Category.assoc f g e)) ≫
          (c f (g ≫ e)).hom.app N ≫ (P f).map ((c g e).hom.app N))
    (f g e f' : X ⟶ X) (h : f' = f ≫ g)
    (N : C) (θ : (P e).obj N ⟶ N) (U : (P g).obj N ⟶ N)
    (V : (P f).obj N ⟶ N) :
    (c f' e).hom.app N ≫ (P f').map θ ≫
        eqToHom (congrArg (fun t ↦ (P t).obj N) h) ≫
        (c f g).hom.app N ≫ (P f).map U ≫ V =
      eqToHom (congrArg (fun t ↦ (P t).obj N)
        (show f' ≫ e = f ≫ (g ≫ e) by rw [h, Category.assoc])) ≫
        (c f (g ≫ e)).hom.app N ≫
        (P f).map ((c g e).hom.app N ≫ (P g).map θ ≫ U) ≫ V := by
  subst f'
  simp only [eqToHom_refl, Category.id_comp]
  rw [(c f g).hom.naturality_assoc, Functor.comp_map]
  rw [← Category.assoc ((c (f ≫ g) e).hom.app N)
    ((c f g).hom.app ((P e).obj N)), hc]
  simp only [Functor.map_comp, Category.assoc (obj := C), eqToHom_refl, Category.id_comp]

private theorem chain_add {X : Scheme.{u}} {C : Type*} [Category C]
    (P : (X ⟶ X) → C ⥤ C)
    (c : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f)
    (hc : ∀ (f g e : X ⟶ X) (N : C),
      (c (f ≫ g) e).hom.app N ≫ (c f g).hom.app ((P e).obj N) =
        eqToHom (congrArg (fun t ↦ (P t).obj N) (Category.assoc f g e)) ≫
          (c f (g ≫ e)).hom.app N ≫ (P f).map ((c g e).hom.app N))
    (a : X ⟶ X) (N : C) (θ : (P a).obj N ⟶ N)
    (I : ∀ n : ℕ, (P (localPositivePower a n)).obj N ⟶ N)
    (h₀ : I 0 = θ)
    (hs : ∀ n, I (n + 1) = (c (localPositivePower a n) a).hom.app N ≫
      (P (localPositivePower a n)).map θ ≫ I n) (n m : ℕ) :
    I (n + m + 1) =
      eqToHom (congrArg (fun t ↦ (P t).obj N) (positivePower_add a n m)) ≫
        (c (localPositivePower a n) (localPositivePower a m)).hom.app N ≫
        (P (localPositivePower a n)).map (I m) ≫ I n := by
  induction m with
  | zero =>
    simpa only [Nat.add_zero, h₀, localPositivePower, eqToHom_refl, Category.id_comp]
      using hs n
  | succ m ih =>
    change I ((n + m + 1) + 1) = _
    rw [hs, ih]
    simpa only [localPositivePower, hs] using append_block P c hc
      (localPositivePower a n) (localPositivePower a m) a
      (localPositivePower a (n + m + 1)) (positivePower_add a n m)
      N θ (I m) (I n)

@[irreducible] private def concatenation {X : Scheme.{u}} {C : Type*} [Category C]
    (P : (X ⟶ X) → C ⥤ C)
    (c : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f)
    (a : X ⟶ X) (N : C)
    (I : ∀ n, (P (localPositivePower a n)).obj N ≅ N) (n m : ℕ) :
    (P (localPositivePower a (n + m + 1))).obj N ≅ N :=
  eqToIso (congrArg (fun t ↦ (P t).obj N) (positivePower_add a n m)) ≪≫
    (c (localPositivePower a n) (localPositivePower a m)).app N ≪≫
    (P (localPositivePower a n)).mapIso (I m) ≪≫ I n

private theorem chain_add_iso {X : Scheme.{u}} {C : Type*} [Category C]
    (P : (X ⟶ X) → C ⥤ C)
    (c : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f)
    (hc : ∀ (f g e : X ⟶ X) (N : C),
      (c (f ≫ g) e).hom.app N ≫ (c f g).hom.app ((P e).obj N) =
        eqToHom (congrArg (fun t ↦ (P t).obj N) (Category.assoc f g e)) ≫
          (c f (g ≫ e)).hom.app N ≫ (P f).map ((c g e).hom.app N))
    (a : X ⟶ X) (N : C) (θ : (P a).obj N ≅ N)
    (I : ∀ n : ℕ, (P (localPositivePower a n)).obj N ≅ N)
    (h₀ : I 0 = θ)
    (hs : ∀ n, I (n + 1) = (c (localPositivePower a n) a).app N ≪≫
      (P (localPositivePower a n)).mapIso θ ≪≫ I n) (n m : ℕ) :
    I (n + m + 1) = concatenation P c a N I n m := by
  unfold concatenation
  have hh : ∀ n, (I (n + 1)).hom = (c (localPositivePower a n) a).hom.app N ≫
      (P (localPositivePower a n)).map θ.hom ≫ (I n).hom := by
    intro n
    simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] using
      congrArg Iso.hom (hs n)
  have ht := chain_add P c hc a N θ.hom (fun n ↦ (I n).hom)
    (congrArg Iso.hom h₀) hh n m
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.app_hom, eqToIso.hom, Functor.mapIso_hom] using ht

private theorem chain_add_wrapped {X : Scheme.{u}} {C : Type*} [Category C]
    (P : (X ⟶ X) → C ⥤ C)
    (c : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f)
    (hc : ∀ (f g e : X ⟶ X) (N : C),
      (c (f ≫ g) e).hom.app N ≫ (c f g).hom.app ((P e).obj N) =
        eqToHom (congrArg (fun t ↦ (P t).obj N) (Category.assoc f g e)) ≫
          (c f (g ≫ e)).hom.app N ≫ (P f).map ((c g e).hom.app N))
    (a : X ⟶ X) (N : C) (θ : (P a).obj N ≅ N)
    (c₀ : P (localPositivePower a 0) ≅ P a) (hc₀ : c₀ =
      eqToIso (congrArg P (show localPositivePower a 0 = a from rfl)))
    (S : ∀ n, (P (localPositivePower a (n + 1))).obj N ≅
      (P (localPositivePower a n)).obj N)
    (hS : ∀ n, S n = evaluateStep (P (localPositivePower a n)) (P a)
      (P (localPositivePower a (n + 1))) (c (localPositivePower a n) a) N θ)
    (I : ∀ n, (P (localPositivePower a n)).obj N ≅ N)
    (hI : I = isoChain (fun n ↦ (P (localPositivePower a n)).obj N) N
      (evaluateInitial (P (localPositivePower a 0)) (P a) c₀ N θ) S) (n m : ℕ) :
    I (n + m + 1) = concatenation P c a N I n m := by
  have hp := genericIterationProps P c a N θ c₀ hc₀ S hS I hI
  exact chain_add_iso P c hc a N θ I hp.1 hp.2 n m

private theorem family_chain_add {E : Scheme.{u} → Type*}
    [∀ X, Category (E X)]
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → E Y ⥤ E X)
    (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    (A : PullbackAssoc P c) {Y : Scheme.{u}} (a : Y ⟶ Y) (N : E Y)
    (θ : (P a).obj N ≅ N)
    (c₀ : P (localPositivePower a 0) ≅ P a)
    (hc₀ : c₀ = eqToIso (congrArg (fun t ↦ P t)
      (show localPositivePower a 0 = a from rfl)))
    (S : ∀ n, (P (localPositivePower a (n + 1))).obj N ≅
      (P (localPositivePower a n)).obj N)
    (hS : ∀ n, S n = evaluateStep (P (localPositivePower a n)) (P a)
      (P (localPositivePower a (n + 1))) (c (localPositivePower a n) a) N θ)
    (I : ∀ n, (P (localPositivePower a n)).obj N ≅ N)
    (hI : I = isoChain (fun n ↦ (P (localPositivePower a n)).obj N) N
      (evaluateInitial (P (localPositivePower a 0)) (P a) c₀ N θ) S) (n m : ℕ) :
    I (n + m + 1) =
      concatenation (fun f ↦ P f) (fun f g ↦ c f g) a N I n m := by
  exact chain_add_wrapped (fun f ↦ P f) (fun f g ↦ c f g)
    (fun f g e M ↦ A.hom_app f g e M) a N θ c₀ hc₀ S hS I hI n m

@[irreducible] private def rawTransport {E : Scheme.{u} → Type*}
    [∀ X, Category (E X)]
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → E Y ⥤ E X)
    (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {S : Scheme.{u}} (τ : ∀ f : S ⟶ S, P f ≅ 𝟭 (E S))
    {Y : Scheme.{u}} (a : Y ⟶ Y) (σ : S ⟶ S) (M : E Y)
    (I : ∀ n, (P (localPositivePower a n)).obj M ≅ M)
    (z z' : S ⟶ Y) (n : ℕ)
    (h : z ≫ localPositivePower a n = localPositivePower σ n ≫ z') :
    (P z').obj M ≅ (P z).obj M :=
  (CategoryTheory.genericComparison P c τ (localPositivePower a n) h).app M ≪≫
    (P z).mapIso (I n)

private theorem genericTransport_comp {E : Scheme.{u} → Type*}
    [∀ X, Category (E X)]
    (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → E Y ⥤ E X)
    (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    (A : PullbackAssoc P c) {S : Scheme.{u}}
    (τ : ∀ f : S ⟶ S, P f ≅ 𝟭 (E S))
    (hτ : ∀ f g : S ⟶ S, (τ (f ≫ g)).symm =
      (τ f).symm ≪≫ (Functor.leftUnitor (P f)).symm ≪≫
        Functor.isoWhiskerRight (τ g).symm (P f) ≪≫ (c f g).symm)
    {Y : Scheme.{u}} (a : Y ⟶ Y) (σ : S ⟶ S) (M : E Y)
    (I : ∀ n, (P (localPositivePower a n)).obj M ≅ M)
    (z₀ z₁ z₂ : S ⟶ Y) (n m : ℕ)
    (h₁ : z₀ ≫ localPositivePower a n = localPositivePower σ n ≫ z₁)
    (h₂ : z₁ ≫ localPositivePower a m = localPositivePower σ m ≫ z₂)
    (h : z₀ ≫ localPositivePower a (n + m + 1) =
      localPositivePower σ (n + m + 1) ≫ z₂)
    (hI : I (n + m + 1) =
      concatenation (fun f ↦ P f) (fun f g ↦ c f g) a M I n m) :
    rawTransport P c τ a σ M I z₁ z₂ m h₂ ≪≫
        rawTransport P c τ a σ M I z₀ z₁ n h₁ =
      rawTransport P c τ a σ M I z₀ z₂ (n + m + 1) h := by
  unfold rawTransport
  have hτ' : ∀ (f g : S ⟶ S) (N : E S), (τ (f ≫ g)).inv.app N =
      (τ f).inv.app N ≫ (P f).map ((τ g).inv.app N) ≫ (c f g).inv.app N := by
    intro f g N
    simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_inv_app, Category.id_comp, Category.assoc (obj := E S)] using
      congrArg (fun e ↦ e.hom.app N) (hτ f g)
  have hc : z₀ ≫ (localPositivePower a n ≫ localPositivePower a m) =
      (localPositivePower σ n ≫ localPositivePower σ m) ≫ z₂ := by
    rw [← positivePower_add, ← positivePower_add]
    exact h
  have hJ := CategoryTheory.genericComparison_change P c τ z₀ z₂
    (positivePower_add a n m) (positivePower_add σ n m) h hc M
  have hC := CategoryTheory.genericComparison_map_comp P c A τ hτ'
    (localPositivePower a n) (localPositivePower a m) z₀ z₁ z₂
    (localPositivePower σ n) (localPositivePower σ m) h₁ h₂ hc M (I n).hom (I m).hom
  have hIh := congrArg Iso.hom hI
  simp only [concatenation, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
    Functor.mapIso_hom] at hIh
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc (obj := E S)]
  symm
  rw [hIh]
  simp only [Functor.map_comp]
  rw [reassoc_of% hJ]
  simpa only [Functor.map_comp] using hC.symm

private theorem actual_iteration_add (l : ℕ) [Fact l.Prime] {Y : Scheme.{u}}
    (a : Y ⟶ Y) (M : Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (n m : ℕ) :
    iterate l a M θ (n + m + 1) = concatenation
      (fun f ↦ CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
      (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
      a M (iterate l a M θ) n m := by
  exact family_chain_add
    (E := fun T : Scheme.{u} ↦ CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T))
    (fun {X Y} f ↦ CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
    (fun {X Y Z} f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
    (CondensedRing.pullback_assoc (Profinite.padicAlgClRingObj l)) a M θ
    (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l)
      (show localPositivePower a 0 = a from rfl))
    (CondensedRing.upperStarCongr_eq (Profinite.padicAlgClRingObj l)
      (show localPositivePower a 0 = a from rfl))
    (iterateStep l a M θ) (step_eq l a M θ) (iterate l a M θ) (iterate_def l a M θ) n m


private theorem transport_raw_eq (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {Y : Scheme.{u}} (a : Y ⟶ Y) (M : Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z z' : Spec (.of D.k) ⟶ Y) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z') :
    transport l D a M θ z z' n h = (CondensedRing.pointSections l D.k).mapIso
      (rawTransport
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
        (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
        (fun f ↦ CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) f)
        a (frobeniusPointIso D).hom M (iterate l a M θ) z z' n h) := by
  unfold transport rawTransport
  rw [CondensedRing.pointComparison_eq]

private theorem mapped_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z : C} (e : X ≅ Y) (f : Y ≅ Z) (g : X ≅ Z)
    (h : e ≪≫ f = g) : F.mapIso e ≪≫ F.mapIso f = F.mapIso g := by
  rw [← Functor.mapIso_trans, h]

/-- The actual positive semilinear transports compose in their natural order.
Source: current blueprint coefficient pullback-composition paragraph, and local Frobenius
powers proof steps 2--3.

Proof: induction on the second word gives the concatenation formula for the iterated
Weil map. Its successor step is pullback associativity and naturality of the compositor.
The point comparison for a composite square is the two point comparisons in sequence:
expand its specified trivialization, apply its composition identity and pullback
associativity, and use naturality of the first trivialization. Naturality of the first
point comparison at the second Weil map then combines these two identities. Apply the
point-sections functor, which preserves composition. Equality casts in the two positive
power identities cancel; proof irrelevance identifies the return-equation proofs.
(blueprint: lem-wf-condensed-module-transport-composition). -/
theorem transport_comp (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {Y : Scheme.{u}} (a : Y ⟶ Y) (M : Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z₀ z₁ z₂ : Spec (.of D.k) ⟶ Y) (n m : ℕ)
    (h₁ : z₀ ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z₁)
    (h₂ : z₁ ≫ localPositivePower a m =
      localPositivePower (frobeniusPointIso D).hom m ≫ z₂)
    (h : z₀ ≫ localPositivePower a (n + m + 1) =
      localPositivePower (frobeniusPointIso D).hom (n + m + 1) ≫ z₂) :
    transport l D a M θ z₁ z₂ m h₂ ≪≫ transport l D a M θ z₀ z₁ n h₁ =
      transport l D a M θ z₀ z₂ (n + m + 1) h := by
  have hI := actual_iteration_add l a M θ n m
  have H := genericTransport_comp
    (E := fun T : Scheme.{u} ↦ CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T))
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
    (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
    (CondensedRing.pullback_assoc (Profinite.padicAlgClRingObj l))
    (fun f ↦ CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) f)
    (fun f g ↦ CondensedRing.trivialization_inv_iso_comp (Profinite.padicAlgClRingObj l) f g)
    a (frobeniusPointIso D).hom M (iterate l a M θ) z₀ z₁ z₂ n m h₁ h₂ h hI
  simp only [transport_raw_eq]
  exact mapped_comp (CondensedRing.pointSections l D.k) _ _ _ H

end WeilConjectures.CondensedModule
