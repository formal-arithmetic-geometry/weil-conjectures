/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.CategoryTheory.PullbackFamily
import WeilConjectures.TraceFormula.PullbackFamily
import WeilConjectures.WeilObject.Sheaf.StalkFrobenius

/-! # Powers of semilinear Weil returns under condensed pullback

Source: latest blueprint, lem-fd-realified-kernel-real, Step 2
(blueprint: lem-fd-condensed-pullback-power-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures

private theorem transport_comp {C D : Type*} [Category C] [Category D]
    (Z : C ⥤ D) (A B AB : C ⥤ C) (S T ST : D ⥤ D)
    (cX : AB ≅ B ⋙ A) (cS : ST ≅ T ⋙ S)
    (βa : Z ⋙ S ≅ A ⋙ Z) (βb : Z ⋙ T ≅ B ⋙ Z) (βab : Z ⋙ ST ≅ AB ⋙ Z)
    (τa : S ≅ 𝟭 D) (τb : T ≅ 𝟭 D) (τab : ST ≅ 𝟭 D)
    (hβ : ∀ M : C, cS.hom.app (Z.obj M) ≫ S.map (βb.hom.app M) ≫
      βa.hom.app (B.obj M) = βab.hom.app M ≫ Z.map (cX.hom.app M))
    (hτ : ∀ N : D, cS.hom.app N ≫ S.map (τb.hom.app N) ≫ τa.hom.app N =
      τab.hom.app N)
    (M : C) (ψa : A.obj M ⟶ M) (ψb : B.obj M ⟶ M) :
    τab.inv.app (Z.obj M) ≫ βab.hom.app M ≫
        Z.map (cX.hom.app M ≫ A.map ψb ≫ ψa) =
      (τb.inv.app (Z.obj M) ≫ βb.hom.app M ≫ Z.map ψb) ≫
        (τa.inv.app (Z.obj M) ≫ βa.hom.app M ≫ Z.map ψa) := by
  have hinv (N : D) : τab.inv.app N ≫ cS.hom.app N =
      τa.inv.app N ≫ S.map (τb.inv.app N) := by
    apply (cancel_mono (S.map (τb.hom.app N) ≫ τa.hom.app N)).mp
    simp only [Category.assoc]
    rw [hτ]
    simp
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (hβ M), reassoc_of% (hinv (Z.obj M))]
  have hn := βa.hom.naturality ψb
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have ht := τa.inv.naturality
    (τb.inv.app (Z.obj M) ≫ βb.hom.app M ≫ Z.map ψb)
  simpa only [Functor.id_map, Functor.id_obj, Functor.map_comp, Category.assoc] using
    (congrArg (fun q ↦ q ≫ βa.hom.app M ≫ Z.map ψa) ht).symm

open WeilConjectures

private theorem power_add {X : Scheme.{u}} (a : X ⟶ X) (n m : ℕ) :
    localPositivePower a (n + m + 1) = localPositivePower a n ≫ localPositivePower a m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (localPositivePower a (n + m + 1) ≫ a) =
      localPositivePower a n ≫ (localPositivePower a m ≫ a)
    rw [ih, Category.assoc]

private theorem power_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : X ⟶ X) (b : Y ⟶ Y) (h : a ≫ f = f ≫ b) (n : ℕ) :
    localPositivePower a n ≫ f = f ≫ localPositivePower b n := by
  induction n with
  | zero => exact h
  | succ n ih => simp only [localPositivePower, Category.assoc, h, ← reassoc_of% ih]

private theorem map_intertwining_power {C : Type*} [Category C]
    {K : Type*} [Field K] (V : C ⥤ ModuleCat.{w} K)
    {M N : C} (A : End M) (B : End N) (c : M ⟶ N) (e : ℕ)
    (h : A ≫ c = c ≫ B ^ e) :
    V.map A ≫ V.map c = V.map c ≫ ModuleCat.ofHom ((V.map B).hom ^ e) := by
  have hp : V.map (B ^ e) = (show End (V.obj N) from V.map B) ^ e := by
    change (Functor.mapEnd N V) (B ^ e) = ((Functor.mapEnd N V) B) ^ e
    exact (Functor.mapEnd N V).map_pow B e
  rw [← V.map_comp, h, V.map_comp, hp]
  congr 1
  apply ModuleCat.hom_ext
  exact (ModuleCat.endRingEquiv _).map_pow _ _

section Generic
variable {D : Scheme.{u} → Type v} [∀ X, Category.{w} (D X)]
  (P : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → D Y ⥤ D X)
  (c : ∀ {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z), P (a ≫ b) ≅ P b ⋙ P a)

private def iter {X : Scheme.{u}} (a : X ⟶ X) (M : D X)
    (θ : (P a).obj M ≅ M) : ∀ n : ℕ, (P (localPositivePower a n)).obj M ≅ M :=
  CondensedModule.isoChain (fun n ↦ (P (localPositivePower a n)).obj M) M
    (CondensedModule.evaluateInitial (P a) (P a) (Iso.refl _) M θ)
    (fun n ↦ CondensedModule.evaluateStep (P (localPositivePower a n)) (P a)
      (P (localPositivePower a (n + 1))) (c (localPositivePower a n) a) M θ)

private theorem iter_initial_eq {X : Scheme.{u}} (a : X ⟶ X) (M : D X)
    (θ : (P a).obj M ≅ M) (e : P a ≅ P a) (he : e = Iso.refl _) (n : ℕ) :
    CondensedModule.isoChain (fun n ↦ (P (localPositivePower a n)).obj M) M
      (CondensedModule.evaluateInitial (P a) (P a) e M θ)
      (fun n ↦ CondensedModule.evaluateStep (P (localPositivePower a n)) (P a)
        (P (localPositivePower a (n + 1))) (c (localPositivePower a n) a) M θ) n =
      iter P c a M θ n := by
  subst e
  rfl

private theorem iter_zero {X : Scheme.{u}} (a : X ⟶ X) (M : D X)
    (θ : (P a).obj M ≅ M) : iter P c a M θ 0 = θ := by
  apply Iso.ext
  change 𝟙 ((P a).obj M) ≫ θ.hom = θ.hom
  exact Category.id_comp θ.hom

private theorem iter_succ {X : Scheme.{u}} (a : X ⟶ X) (M : D X)
    (θ : (P a).obj M ≅ M) (n : ℕ) :
    iter P c a M θ (n + 1) = ((c (localPositivePower a n) a).app M ≪≫
      (P (localPositivePower a n)).mapIso θ) ≪≫ iter P c a M θ n := rfl

private theorem iter_pullback (hc : PullbackAssoc P c) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y) (h : a ≫ f = f ≫ b)
    (M : D Y) (θ : (P b).obj M ≅ M) (n : ℕ) :
    (iter P c a ((P f).obj M)
      ((pullbackFamilyComparison (c := c) f a b h).app M ≪≫ (P f).mapIso θ) n).hom =
    (pullbackFamilyComparison (c := c) f (localPositivePower a n) (localPositivePower b n)
      (power_square f a b h n)).hom.app M ≫ (P f).map (iter P c b M θ n).hom := by
  induction n with
  | zero =>
    simp only [iter_zero, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      localPositivePower]
  | succ n ih =>
    rw [iter_succ, iter_succ]
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    rw [ih]
    simp only [pullbackFamilyComparison_hom_app, Functor.map_comp, Category.assoc]
    have nat₁ := (c (localPositivePower a n) f).inv.naturality θ.hom
    have nat₂ := (c f (localPositivePower b n)).hom.naturality θ.hom
    simp only [Functor.comp_map] at nat₁ nat₂
    rw [reassoc_of% nat₁,
      map_comp_eqToHom_of_eq_assoc (P := P) (power_square f a b h n),
      reassoc_of% nat₂,
      pullbackFamilyComparison_comp_aux_assoc hc f _ _ _ _ (power_square f a b h n) h M]
    rfl

private theorem iter_cocycle (hc : PullbackAssoc P c) {X : Scheme.{u}}
    {a b d ab bd abd : X ⟶ X} (hab : ab = a ≫ b) (hbd : bd = b ≫ d)
    (habd : abd = ab ≫ d) (habd' : abd = a ≫ bd) (M : D X)
    (ψa : (P a).obj M ⟶ M) (ψb : (P b).obj M ⟶ M) (ψd : (P d).obj M ⟶ M)
    (ψab : (P ab).obj M ⟶ M)
    (hψab : ψab = eqToHom (congrArg (fun t ↦ (P t).obj M) hab) ≫
      (c a b).hom.app M ≫ (P a).map ψb ≫ ψa) :
    eqToHom (congrArg (fun t ↦ (P t).obj M) habd) ≫ (c ab d).hom.app M ≫
        (P ab).map ψd ≫ ψab =
      eqToHom (congrArg (fun t ↦ (P t).obj M) habd') ≫ (c a bd).hom.app M ≫
        (P a).map (eqToHom (congrArg (fun t ↦ (P t).obj M) hbd) ≫
          (c b d).hom.app M ≫ (P b).map ψd ≫ ψb) ≫ ψa := by
  subst hψab hab hbd habd
  simp only [eqToHom_refl, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [(c a b).hom.naturality_assoc ψd]
  simp only [Functor.comp_map]
  rw [reassoc_of% (hc.hom_app a b d M)]
  simp only [eqToHom_refl, Category.id_comp]

private theorem iter_add (hc : PullbackAssoc P c) {X : Scheme.{u}}
    (a : X ⟶ X) (M : D X) (θ : (P a).obj M ≅ M) (n m : ℕ) :
    (iter P c a M θ (n + m + 1)).hom =
      eqToHom (congrArg (fun t ↦ (P t).obj M) (power_add a n m)) ≫
        (c (localPositivePower a n) (localPositivePower a m)).hom.app M ≫
        (P (localPositivePower a n)).map (iter P c a M θ m).hom ≫
        (iter P c a M θ n).hom := by
  induction m with
  | zero =>
    simp only [Nat.add_zero, iter_succ, iter_zero, localPositivePower, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, eqToHom_refl, Category.id_comp, Category.assoc]
  | succ m ih =>
    simpa only [Nat.add_succ, iter_succ, localPositivePower, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Category.assoc,
      eqToHom_refl, Category.id_comp] using
      iter_cocycle P c hc (power_add a n m) rfl rfl (power_add a n (m + 1)) M
      (iter P c a M θ n).hom (iter P c a M θ m).hom θ.hom
      (iter P c a M θ (n + m + 1)).hom ih

private def returnMap {S X : Scheme.{u}} (τ : ∀ s : S ⟶ S, P s ≅ 𝟭 (D S))
    (σ : S ⟶ S) (a : X ⟶ X) (M : D X) (ψ : (P a).obj M ⟶ M)
    (z : S ⟶ X) (h : z ≫ a = σ ≫ z) : End ((P z).obj M) :=
  (pullbackFamilyStalkComparison (c := c) (τ σ) z a h).hom.app M ≫ (P z).map ψ

private theorem return_comp (hc : PullbackAssoc P c) {S X : Scheme.{u}}
    (τ : ∀ s : S ⟶ S, P s ≅ 𝟭 (D S))
    (hτ : ∀ s t (N : D S), (c s t).hom.app N ≫ (P s).map ((τ t).hom.app N) ≫
      (τ s).hom.app N = (τ (s ≫ t)).hom.app N)
    (σ ρ : S ⟶ S) (a b : X ⟶ X) (M : D X)
    (ψa : (P a).obj M ⟶ M) (ψb : (P b).obj M ⟶ M) (z : S ⟶ X)
    (ha : z ≫ a = σ ≫ z) (hb : z ≫ b = ρ ≫ z)
    (hab : z ≫ (a ≫ b) = (σ ≫ ρ) ≫ z) :
    returnMap P c τ (σ ≫ ρ) (a ≫ b) M
        ((c a b).hom.app M ≫ (P a).map ψb ≫ ψa) z hab =
      returnMap P c τ ρ b M ψb z hb ≫ returnMap P c τ σ a M ψa z ha := by
  have hβ (N : D X) :
      (c σ ρ).hom.app ((P z).obj N) ≫
        (P σ).map ((pullbackFamilyComparison (c := c) z ρ b hb.symm).hom.app N) ≫
        (pullbackFamilyComparison (c := c) z σ a ha.symm).hom.app ((P b).obj N) =
      (pullbackFamilyComparison (c := c) z (σ ≫ ρ) (a ≫ b) hab.symm).hom.app N ≫
        (P z).map ((c a b).hom.app N) := by
    simpa only [pullbackFamilyComparison_hom_app, Functor.map_comp, Category.assoc] using
      pullbackFamilyComparison_comp_aux hc z σ ρ a b ha.symm hb.symm N
  simpa only [returnMap, pullbackFamilyStalkComparison_hom_app,
    pullbackFamilyComparison_hom_app, Functor.map_comp, Category.assoc] using
    transport_comp (P z) (P a) (P b) (P (a ≫ b)) (P σ) (P ρ) (P (σ ≫ ρ))
      (c a b) (c σ ρ)
      (pullbackFamilyComparison (c := c) z σ a ha.symm)
      (pullbackFamilyComparison (c := c) z ρ b hb.symm)
      (pullbackFamilyComparison (c := c) z (σ ≫ ρ) (a ≫ b) hab.symm)
      (τ σ) (τ ρ) (τ (σ ≫ ρ)) hβ (hτ σ ρ) M ψa ψb

private theorem return_congr {S X : Scheme.{u}}
    (τ : ∀ s : S ⟶ S, P s ≅ 𝟭 (D S))
    {σ σ' : S ⟶ S} {a a' : X ⟶ X} (hσ : σ = σ') (ha : a = a')
    (M : D X) (ψ : (P a).obj M ⟶ M) (ψ' : (P a').obj M ⟶ M)
    (hψ : ψ = eqToHom (congrArg (fun a ↦ (P a).obj M) ha) ≫ ψ')
    (z : S ⟶ X) (h : z ≫ a = σ ≫ z) (h' : z ≫ a' = σ' ≫ z) :
    returnMap P c τ σ a M ψ z h = returnMap P c τ σ' a' M ψ' z h' := by
  subst hσ ha
  simpa using congrArg (fun ψ ↦ returnMap P c τ σ a M ψ z h) hψ

private def returnIter {S X : Scheme.{u}} (τ : ∀ s : S ⟶ S, P s ≅ 𝟭 (D S))
    (σ : S ⟶ S) (a : X ⟶ X) (M : D X) (θ : (P a).obj M ≅ M)
    (z : S ⟶ X) (n : ℕ)
    (h : z ≫ localPositivePower a n = localPositivePower σ n ≫ z) :
    End ((P z).obj M) :=
  returnMap P c τ (localPositivePower σ n) (localPositivePower a n) M
    (iter P c a M θ n).hom z h

private theorem returnIter_congr {S X : Scheme.{u}}
    (τ : ∀ s : S ⟶ S, P s ≅ 𝟭 (D S)) (σ : S ⟶ S) (a : X ⟶ X)
    (M : D X) (θ : (P a).obj M ≅ M) (z : S ⟶ X) {n m : ℕ} (hn : n = m)
    (h : z ≫ localPositivePower a n = localPositivePower σ n ≫ z)
    (h' : z ≫ localPositivePower a m = localPositivePower σ m ≫ z) :
    returnIter P c τ σ a M θ z n h = returnIter P c τ σ a M θ z m h' := by
  subst hn
  rfl

private theorem returnIter_add (hc : PullbackAssoc P c) {S X : Scheme.{u}}
    (τ : ∀ s : S ⟶ S, P s ≅ 𝟭 (D S))
    (hτ : ∀ s t (N : D S), (c s t).hom.app N ≫ (P s).map ((τ t).hom.app N) ≫
      (τ s).hom.app N = (τ (s ≫ t)).hom.app N)
    (σ : S ⟶ S) (a : X ⟶ X) (M : D X) (θ : (P a).obj M ≅ M)
    (z : S ⟶ X) (n m : ℕ)
    (hn : z ≫ localPositivePower a n = localPositivePower σ n ≫ z)
    (hm : z ≫ localPositivePower a m = localPositivePower σ m ≫ z)
    (hnm : z ≫ localPositivePower a (n + m + 1) =
      localPositivePower σ (n + m + 1) ≫ z) :
    returnIter P c τ σ a M θ z (n + m + 1) hnm =
      returnIter P c τ σ a M θ z m hm ≫ returnIter P c τ σ a M θ z n hn := by
  have hab : z ≫ (localPositivePower a n ≫ localPositivePower a m) =
      (localPositivePower σ n ≫ localPositivePower σ m) ≫ z := by
    rw [← Category.assoc, hn, Category.assoc, hm, Category.assoc]
  unfold returnIter
  rw [return_congr P c τ (power_add σ n m) (power_add a n m) M _ _
    (iter_add P c hc a M θ n m) z hnm hab]
  exact return_comp P c hc τ hτ _ _ _ _ M _ _ z hn hm hab

private theorem returnIter_mul_exists (hc : PullbackAssoc P c) {S X : Scheme.{u}}
    (τ : ∀ s : S ⟶ S, P s ≅ 𝟭 (D S))
    (hτ : ∀ s t (N : D S), (c s t).hom.app N ≫ (P s).map ((τ t).hom.app N) ≫
      (τ s).hom.app N = (τ (s ≫ t)).hom.app N)
    (σ : S ⟶ S) (a : X ⟶ X) (M : D X) (θ : (P a).obj M ≅ M)
    (z : S ⟶ X) (d : ℕ) (hd : 0 < d)
    (h : z ≫ localPositivePower a (d - 1) = localPositivePower σ (d - 1) ≫ z)
    (e : ℕ) (he : 1 ≤ e) :
    ∃ H : z ≫ localPositivePower a (e * d - 1) =
        localPositivePower σ (e * d - 1) ≫ z,
      returnIter P c τ σ a M θ z (e * d - 1) H =
        (returnIter P c τ σ a M θ z (d - 1) h) ^ e := by
  induction e, he using Nat.le_induction with
  | base => exact ⟨by simpa only [one_mul] using h, by simp⟩
  | succ e he ih =>
    obtain ⟨H, ih⟩ := ih
    have hi : (e + 1) * d - 1 = (e * d - 1) + (d - 1) + 1 := by
      rw [Nat.add_mul, one_mul]
      have : 0 < e * d := Nat.mul_pos (by omega) hd
      omega
    have H' : z ≫ localPositivePower a ((e + 1) * d - 1) =
        localPositivePower σ ((e + 1) * d - 1) ≫ z := by
      rw [hi, power_add, power_add, ← Category.assoc, H, Category.assoc, h,
        Category.assoc]
    refine ⟨H', ?_⟩
    have H'' : z ≫ localPositivePower a ((e * d - 1) + (d - 1) + 1) =
        localPositivePower σ ((e * d - 1) + (d - 1) + 1) ≫ z := by
      simpa only [hi] using H'
    rw [returnIter_congr P c τ σ a M θ z hi H' H'',
      returnIter_add P c hc τ hτ σ a M θ z _ _ H h H'', ih, pow_succ]
    rfl

private theorem returnIter_pullback (hc : PullbackAssoc P c) {S X Y : Scheme.{u}}
    (τ : ∀ s : S ⟶ S, P s ≅ 𝟭 (D S)) (σ : S ⟶ S)
    (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y) (hf : a ≫ f = f ≫ b)
    (M : D Y) (θ : (P b).obj M ≅ M) (z : S ⟶ X) (x : S ⟶ Y)
    (hx : z ≫ f = x) (n : ℕ)
    (ha : z ≫ localPositivePower a n = localPositivePower σ n ≫ z)
    (hb : x ≫ localPositivePower b n = localPositivePower σ n ≫ x) :
    returnIter P c τ σ a ((P f).obj M)
        ((pullbackFamilyComparison (c := c) f a b hf).app M ≪≫ (P f).mapIso θ) z n ha ≫
      ((c z f).inv.app M ≫ eqToHom (congrArg (fun x ↦ (P x).obj M) hx)) =
      ((c z f).inv.app M ≫ eqToHom (congrArg (fun x ↦ (P x).obj M) hx)) ≫
        returnIter P c τ σ b M θ x n hb := by
  subst x
  simp only [eqToHom_refl, Category.comp_id]
  unfold returnIter returnMap
  rw [iter_pullback P c hc]
  simpa only [Category.assoc] using
    pullbackFamilyStalkComparison_pullbackFamilyComparison hc (τ (localPositivePower σ n))
      f (localPositivePower a n) (localPositivePower b n) (power_square f a b hf n)
      (iter P c b M θ n) z ha hb

private theorem returnIter_pullback_power (hc : PullbackAssoc P c) {S X Y : Scheme.{u}}
    (τ : ∀ s : S ⟶ S, P s ≅ 𝟭 (D S))
    (hτ : ∀ s t (N : D S), (c s t).hom.app N ≫ (P s).map ((τ t).hom.app N) ≫
      (τ s).hom.app N = (τ (s ≫ t)).hom.app N)
    (σ : S ⟶ S) (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y) (hf : a ≫ f = f ≫ b)
    (M : D Y) (θ : (P b).obj M ≅ M) (z : S ⟶ X) (x : S ⟶ Y)
    (hx : z ≫ f = x) (n d e : ℕ) (hd : 0 < d) (he : 1 ≤ e) (hi : n = e * d - 1)
    (ha : z ≫ localPositivePower a n = localPositivePower σ n ≫ z)
    (hb : x ≫ localPositivePower b (d - 1) = localPositivePower σ (d - 1) ≫ x) :
    returnIter P c τ σ a ((P f).obj M)
        ((pullbackFamilyComparison (c := c) f a b hf).app M ≪≫ (P f).mapIso θ) z n ha ≫
      ((c z f).inv.app M ≫ eqToHom (congrArg (fun x ↦ (P x).obj M) hx)) =
      ((c z f).inv.app M ≫ eqToHom (congrArg (fun x ↦ (P x).obj M) hx)) ≫
        (returnIter P c τ σ b M θ x (d - 1) hb) ^ e := by
  subst n
  obtain ⟨H, hpow⟩ := returnIter_mul_exists P c hc τ hτ σ b M θ x d hd hb e he
  have h := returnIter_pullback P c hc τ σ f a b hf M θ z x hx (e * d - 1) ha H
  rw [hpow] at h
  exact h

private theorem evaluated_pullback_power (hc : PullbackAssoc P c) {S X Y : Scheme.{u}}
    (τ : ∀ s : S ⟶ S, P s ≅ 𝟭 (D S))
    (hτ : ∀ s t (N : D S), (c s t).hom.app N ≫ (P s).map ((τ t).hom.app N) ≫
      (τ s).hom.app N = (τ (s ≫ t)).hom.app N)
    {K : Type*} [Field K] (V : D S ⥤ ModuleCat.{w'} K)
    (σ : S ⟶ S) (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y) (hf : a ≫ f = f ≫ b)
    (M : D Y) (θ : (P b).obj M ≅ M) (z : S ⟶ X) (x : S ⟶ Y)
    (hx : z ≫ f = x) (n d e : ℕ) (hd : 0 < d) (he : 1 ≤ e) (hi : n = e * d - 1)
    (ha : z ≫ localPositivePower a n = localPositivePower σ n ≫ z)
    (hb : x ≫ localPositivePower b (d - 1) = localPositivePower σ (d - 1) ≫ x) :
    (V.mapIso (X := (P z).obj ((P f).obj M)) (Y := (P z).obj ((P f).obj M))
      ((pullbackFamilyStalkComparison (c := c) (τ (localPositivePower σ n))
        z (localPositivePower a n) ha).app ((P f).obj M) ≪≫
        (P z).mapIso (iter P c a ((P f).obj M)
          ((pullbackFamilyComparison (c := c) f a b hf).app M ≪≫ (P f).mapIso θ) n))).hom ≫
      V.map ((c z f).inv.app M ≫ eqToHom (congrArg (fun x ↦ (P x).obj M) hx)) =
      V.map ((c z f).inv.app M ≫ eqToHom (congrArg (fun x ↦ (P x).obj M) hx)) ≫
        ModuleCat.ofHom (((V.mapIso (X := (P x).obj M) (Y := (P x).obj M)
          ((pullbackFamilyStalkComparison (c := c) (τ (localPositivePower σ (d - 1)))
            x (localPositivePower b (d - 1)) hb).app M ≪≫
            (P x).mapIso (iter P c b M θ (d - 1)))).hom).hom ^ e) := by
  exact map_intertwining_power V _ _ _ e
    (returnIter_pullback_power P c hc τ hτ σ f a b hf M θ z x hx n d e hd he hi ha hb)

end Generic


private theorem nat_app_eq_of_essSurj {A B C : Type*}
    [Category A] [Category B] [Category C] (P : A ⥤ B) [P.EssSurj]
    {F G : B ⥤ C} (η ζ : F ⟶ G) (h : ∀ a, η.app (P.obj a) = ζ.app (P.obj a))
    (b : B) : η.app b = ζ.app b := by
  let e := P.objObjPreimageIso b
  apply (cancel_epi (F.map e.hom)).mp
  rw [η.naturality, ζ.naturality, h]

private def trivializationComposite {E : Type*} [Category E]
    {S T ST : E ⥤ E} (c : ST ≅ T ⋙ S) (τa : S ≅ 𝟭 E) (τb : T ≅ 𝟭 E) :
    ST ⟶ 𝟭 E where
  app N := c.hom.app N ≫ S.map (τb.hom.app N) ≫ τa.hom.app N
  naturality X Y f := by
    simp only [Functor.id_map, Category.assoc]
    rw [c.hom.naturality_assoc]
    simp only [Functor.comp_map]
    rw [← S.map_comp_assoc, τb.hom.naturality, Functor.id_map,
      S.map_comp, Category.assoc]
    have h := τa.hom.naturality f
    simp only [Functor.id_map] at h
    rw [h]

private theorem trivialization_comp_of_essSurj {A E : Type*} [Category A] [Category E]
    (P : A ⥤ E) [P.EssSurj] {S T ST : E ⥤ E} (c : ST ≅ T ⋙ S)
    (τa : S ≅ 𝟭 E) (τb : T ≅ 𝟭 E) (τab : ST ≅ 𝟭 E)
    (h : ∀ a, c.hom.app (P.obj a) ≫ S.map (τb.hom.app (P.obj a)) ≫
      τa.hom.app (P.obj a) = τab.hom.app (P.obj a)) (N : E) :
    c.hom.app N ≫ S.map (τb.hom.app N) ≫ τa.hom.app N = τab.hom.app N := by
  exact nat_app_eq_of_essSurj P (trivializationComposite c τa τb) τab.hom h N

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp
  CondensedRing.upperStarFromPointMod CondensedRing.upperStarIsoIdOfIsSepClosed
  CondensedRing.pointSections

private theorem tau_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {K : Type u} [Field K] [IsSepClosed K]
    (a b : Spec (.of K) ⟶ Spec (.of K))
    (N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of K)))) :
    (CondensedRing.upperStarComp Λ a b).hom.app N ≫
        (CondensedRing.upperStar Λ a).map
          ((CondensedRing.upperStarIsoIdOfIsSepClosed Λ b).hom.app N) ≫
        (CondensedRing.upperStarIsoIdOfIsSepClosed Λ a).hom.app N =
      (CondensedRing.upperStarIsoIdOfIsSepClosed Λ (a ≫ b)).hom.app N := by
  apply trivialization_comp_of_essSurj
    (CondensedRing.upperStarFromPointMod Λ (Spec (.of K)))
    (CondensedRing.upperStarComp Λ a b)
    (CondensedRing.upperStarIsoIdOfIsSepClosed Λ a)
    (CondensedRing.upperStarIsoIdOfIsSepClosed Λ b)
    (CondensedRing.upperStarIsoIdOfIsSepClosed Λ (a ≫ b)) ?_ N
  intro A
  rw [CondensedRing.upperStarIsoIdOfIsSepClosed_hom_app_upperStarFromPointMod Λ b A,
    CondensedRing.upperStarIsoIdOfIsSepClosed_hom_app_upperStarFromPointMod Λ a A,
    CondensedRing.upperStarIsoIdOfIsSepClosed_hom_app_upperStarFromPointMod Λ (a ≫ b) A]
  exact CondensedRing.upperStarComp_hom_app_comp_upperStarFromPointModComp Λ a b A

private theorem condensed_iter_eq (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    (a : X ⟶ X) (M : CondensedModule.Modules l X)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M) (n : ℕ) :
    CondensedModule.iterate l a M θ n =
      iter (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
        (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g) a M θ n := by
  unfold CondensedModule.iterate CondensedModule.iterateStep
  exact iter_initial_eq
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
    (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
    a M θ _ (CondensedRing.upperStarCongr_self _ _) n

private theorem condensed_assoc
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    PullbackAssoc (CondensedRing.upperStar Λ) (fun f g ↦ CondensedRing.upperStarComp Λ f g) := by
  intro X Y Z V f g h
  exact CondensedRing.upperStarComp_assoc Λ f g h

private theorem condensed_transport_eq (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {X : Scheme.{u}} (a : X ⟶ X) (M : CondensedModule.Modules l X)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ X) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    CondensedModule.transport l D a M θ z z n h =
      (CondensedRing.pointSections l D.k).mapIso
        (X := (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M)
        (Y := (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M)
        ((pullbackFamilyStalkComparison
          (c := fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
          (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
            (localPositivePower (frobeniusPointIso D).hom n))
          z (localPositivePower a n) h).app M ≪≫
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso
            (iter (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
              (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
              a M θ n)) := by
  unfold CondensedModule.transport
  rw [condensed_iter_eq]
  congr 2

private theorem evaluated_intertwining_congr {K : Type*} [Field K]
    {M N : ModuleCat.{w} K} (A A' : M ≅ M) (B B' : N ≅ N) (c : M ⟶ N) (e : ℕ)
    (hA : A = A') (hB : B = B')
    (h : A'.hom ≫ c = c ≫ ModuleCat.ofHom (B'.hom.hom ^ e)) :
    A.hom ≫ c = c ≫ ModuleCat.ofHom (B.hom.hom ^ e) := by
  subst A' B'
  exact h

/-- The specified fibre compositor identifies a pulled-back Weil return with a power
of a shorter return. No constructibility or finite-dimensionality is needed.

Source: latest blueprint, sec-deligne-laumon-a1/sk-p-dl-a1-some-weight/
lem-fd-realified-kernel-real.proof.md, Step 2, residue-degree pullback sentence
(blueprint: lem-fd-condensed-pullback-power-transport).

Proof: First prove the composition formula for semilinear point transports using
naturality, associativity of pullback compositors, and the composition law for the
canonical trivializations of pullback on a separably closed point. The last law can
be checked on modules pulled back from the condensed point, since this pullback is
an equivalence; there it is the existing comparison-composition identity. Induct on
the Weil iteration to commute it with pullback and to group an iteration into two
blocks. The transport-composition formula then identifies a return of length e*d
with the e-th power of the length-d return. The canonical inverse compositor
intertwines same-length returns by pullback-family naturality. Finally apply
pointSections, which preserves composition and powers. The exponent-one case is
the identity calculation; zero modules require no separate case. -/
theorem condensedPullbackPowerTransport (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    (hf : a ≫ f = f ≫ b) (M : CondensedModule.Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) b).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ X) (x : Spec (.of D.k) ⟶ Y)
    (hx : z ≫ f = x) (n d e : ℕ) (hd : 0 < d) (he : 1 ≤ e) (hi : n = e * d - 1)
    (ha : z ≫ localPositivePower a n = localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (hb : x ≫ localPositivePower b (d - 1) =
      localPositivePower (frobeniusPointIso D).hom (d - 1) ≫ x) :
    CondensedModule.operator l D a
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M)
        ((pullbackFamilyComparison (c := fun f g ↦ CondensedRing.upperStarComp
            (Profinite.padicAlgClRingObj l) f g) f a b hf).app M ≪≫
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).mapIso θ) z n ha ≫
      (CondensedRing.pointSections l D.k).map
        ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) z f).inv.app M ≫
          eqToHom (congrArg (fun x ↦
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) x).obj M) hx)) =
      (CondensedRing.pointSections l D.k).map
        ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) z f).inv.app M ≫
          eqToHom (congrArg (fun x ↦
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) x).obj M) hx)) ≫
        ModuleCat.ofHom ((CondensedModule.operator l D b M θ x (d - 1) hb).hom ^ e) := by
  subst x
  have hA := condensed_transport_eq l D a
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M)
    ((pullbackFamilyComparison (c := fun f g ↦ CondensedRing.upperStarComp
        (Profinite.padicAlgClRingObj l) f g) f a b hf).app M ≪≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).mapIso θ) z n ha
  have hB := condensed_transport_eq l D b M θ (z ≫ f) (d - 1) hb
  exact evaluated_intertwining_congr _ _ _ _ _ e hA hB
    (evaluated_pullback_power
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l))
      (fun f g ↦ CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g)
      (condensed_assoc _) (CondensedRing.upperStarIsoIdOfIsSepClosed
        (Profinite.padicAlgClRingObj l)) (tau_comp _) (CondensedRing.pointSections l D.k)
      (frobeniusPointIso D).hom f a b hf M θ z (z ≫ f) rfl n d e hd he hi ha hb)

end WeilConjectures
