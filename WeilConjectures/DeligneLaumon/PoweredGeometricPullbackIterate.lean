/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PoweredGeometricPullback
public import WeilConjectures.WeilSheaf.StalkFrobenius
import WeilConjectures.WeilSheaf.StalkCharpoly
import WeilConjectures.DeligneLaumon.PoweredGeometricPullbackFirstStructure

/-! # Iterated structure of powered geometric pullback -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

private lemma square_comp {Y Z : Scheme.{u}} (l : ℕ) [Fact l.Prime]
    (v : Z ⟶ Y) (a b ab : Z ⟶ Z) (c d cd : Y ⟶ Y)
    (ha : a ≫ v = v ≫ c) (hb : b ≫ v = v ≫ d)
    (hab : ab ≫ v = v ≫ cd) (eab : a ≫ b = ab) (ecd : c ≫ d = cd)
    (M : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l))
    (N : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l))
    (θ : (v)^*[_].obj M ⟶ N)
    (φc : (c)^*[_].obj M ⟶ M) (φd : (d)^*[_].obj M ⟶ M)
    (ψa : (a)^*[_].obj N ⟶ N) (ψb : (b)^*[_].obj N ⟶ N)
    (hca : (a)^*[_].map θ ≫ ψa =
      (ProEtale.upperStarCompIso _ ha).hom.app M ≫ (v)^*[_].map φc ≫ θ)
    (hdb : (b)^*[_].map θ ≫ ψb =
      (ProEtale.upperStarCompIso _ hb).hom.app M ≫ (v)^*[_].map φd ≫ θ) :
    (ab)^*[_].map θ ≫ (ProEtale.upperStarFactor _ eab).hom.app N ≫
        (a)^*[_].map ψb ≫ ψa =
      (ProEtale.upperStarCompIso _ hab).hom.app M ≫
        (v)^*[_].map ((ProEtale.upperStarFactor _ ecd).hom.app M ≫
          (c)^*[_].map φd ≫ φc) ≫ θ := by
  subst ab cd
  rw [ProEtale.upperStarFactor_rfl, ProEtale.upperStarFactor_rfl]
  have nt := (ProEtale.upperStarComp _ a b).hom.naturality θ
  have nc := (ProEtale.upperStarCompIso _ ha).hom.naturality φd
  have paste := ProEtale.upperStarCompIso_hom_app_paste (WeilCoefficients.{u} l)
    hb ha hab M
  simp only [Functor.comp_map] at nt nc
  rw [reassoc_of% nt]
  rw [← Functor.map_comp_assoc, hdb]
  simp only [Functor.map_comp, Category.assoc]
  rw [hca, reassoc_of% nc, reassoc_of% paste]


private lemma generic_unit_square
    {A B : Type*} [Category A] [Category B]
    (L : A ⥤ B) (I : A ⥤ A) (J : B ⥤ B) (i : I ≅ 𝟭 A) (j : J ≅ 𝟭 B)
    (e : L ⋙ J ≅ I ⋙ L)
    (he : e = (Functor.isoWhiskerLeft L j.symm).symm ≪≫ L.rightUnitor ≪≫
      L.leftUnitor.symm ≪≫ Functor.isoWhiskerRight i.symm L)
    (M : A) (N : B) (θ : L.obj M ⟶ N) :
    J.map θ ≫ j.hom.app N = e.hom.app M ≫ L.map (i.hom.app M) ≫ θ := by
  rw [he]
  simp [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Category.assoc, ← Functor.map_comp_assoc]

private lemma generic_unit_exchange
    {D : Type*} [Category D] {T : Type*} (F : T → D)
    {a b c : T} (p : a = b) (q : a = c) (r : c = b)
    {U V W Z : D} (s : U ≅ F b) (t : U ≅ V) (u : F b ≅ W) (w : W ≅ Z)
    (P : F a ≅ V) (Q : F c ≅ Z)
    (hP : P = eqToIso (congrArg F p) ≪≫ s.symm ≪≫ t)
    (hQ : Q = eqToIso (congrArg F r) ≪≫ u ≪≫ w) :
    P.symm ≪≫ eqToIso (congrArg F q) ≪≫ Q = t.symm ≪≫ s ≪≫ u ≪≫ w := by
  subst a c
  rw [hP, hQ]
  simp [Iso.trans_assoc]

private lemma generic_unit_left_path
    {D : Type*} [Category D] {T : Type*} (F : T → D)
    {a b : T} (p : a = b) {U V : D} (u : F b ≅ U) (v : U ≅ V)
    (P : F a ≅ V) (hP : P = eqToIso (congrArg F p) ≪≫ u ≪≫ v) :
    eqToIso (congrArg F p.symm) ≪≫ P = u ≪≫ v := by
  subst a
  rw [hP]
  simp

private lemma unit_exchange_eq {Y Z : Scheme.{u}} (l : ℕ) [Fact l.Prime]
    (v : Z ⟶ Y) (h : (𝟙 Z) ≫ v = v ≫ 𝟙 Y) :
    ProEtale.upperStarCompIso (WeilCoefficients.{u} l) h =
      (Functor.isoWhiskerLeft (v)^*[_] (ProEtale.upperStarId _ Z).symm).symm ≪≫
        (v)^*[_].rightUnitor ≪≫ (v)^*[_].leftUnitor.symm ≪≫
          Functor.isoWhiskerRight (ProEtale.upperStarId _ Y).symm (v)^*[_] := by
  exact generic_unit_exchange (fun t : Z ⟶ Y ↦ ProEtale.upperStar (WeilCoefficients.{u} l) t)
    (Category.id_comp v) h (Category.comp_id v) (v)^*[_].rightUnitor
    (Functor.isoWhiskerLeft (v)^*[_] (ProEtale.upperStarId _ Z).symm)
    (v)^*[_].leftUnitor.symm
    (Functor.isoWhiskerRight (ProEtale.upperStarId _ Y).symm (v)^*[_])
    (ProEtale.upperStarComp _ (𝟙 Z) v) (ProEtale.upperStarComp _ v (𝟙 Y))
    (ProEtale.upperStarComp_id_left _ v) (ProEtale.upperStarComp_id_right _ v)


private lemma square_unit {Y Z : Scheme.{u}} (l : ℕ) [Fact l.Prime]
    (v : Z ⟶ Y)
    (M : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l))
    (N : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l))
    (θ : (v)^*[_].obj M ⟶ N) (h : (𝟙 Z) ≫ v = v ≫ 𝟙 Y) :
    (𝟙 Z)^*[_].map θ ≫ (ProEtale.upperStarId _ Z).hom.app N =
      (ProEtale.upperStarCompIso _ h).hom.app M ≫
        (v)^*[_].map ((ProEtale.upperStarId _ Y).hom.app M) ≫ θ := by
  exact generic_unit_square (v)^*[_] (𝟙 Y)^*[_] (𝟙 Z)^*[_]
    (ProEtale.upperStarId _ Y) (ProEtale.upperStarId _ Z)
    (ProEtale.upperStarCompIso _ h) (unit_exchange_eq l v h) M N θ


private lemma square_maps_congr
    {A B : Type*} [Category A] [Category B] (H : B ⥤ B) (L : A ⥤ B)
    {M Z : A} {N : B} (θ : L.obj M ⟶ N) (E : H.obj (L.obj M) ⟶ L.obj Z)
    (φ φ' : H.obj N ⟶ N) (ψ ψ' : Z ⟶ M) (hφ : φ = φ') (hψ : ψ = ψ')
    (h : H.map θ ≫ φ' = E ≫ L.map ψ' ≫ θ) :
    H.map θ ≫ φ = E ≫ L.map ψ ≫ θ := by
  rw [hφ, hψ]
  exact h

private lemma frobeniusPowStr_zero_unit
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    (G : WeilSheaf k l Y) :
    G.frobeniusPowStr 0 =
      (ProEtale.upperStarId _ (Y ↘ Spec (.of k)).geometricFiber).hom.app G.obj.carrier.X := by
  have h := G.frobeniusPowStr_zero (by rw [pow_zero]; rfl)
  simp only [ProEtale.upperStarCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] at h
  exact h

private lemma generic_unit_left
    {A : Type*} [Category A] (F I : A ⥤ A) (i : I ≅ 𝟭 A)
    (e : F ≅ F ⋙ I)
    (he : e = F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F i.symm)
    (M : A) (φ : F.obj M ⟶ M) :
    e.hom.app M ≫ I.map φ ≫ i.hom.app M = φ := by
  rw [he]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app, Category.id_comp]
  rw [i.hom.naturality φ]
  simp

private lemma unit_left_comp {Y : Scheme.{u}} (l : ℕ) [Fact l.Prime]
    (f : Y ⟶ Y) (M : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l))
    (φ : (f)^*[_].obj M ⟶ M) :
    (ProEtale.upperStarFactor _ (Category.id_comp f)).hom.app M ≫
      (𝟙 Y)^*[_].map φ ≫ (ProEtale.upperStarId _ Y).hom.app M = φ := by
  have he : ProEtale.upperStarFactor (WeilCoefficients.{u} l) (Category.id_comp f) =
      (f)^*[_].rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (f)^*[_] (ProEtale.upperStarId _ Y).symm := by
    exact generic_unit_left_path
      (fun t : Y ⟶ Y ↦ ProEtale.upperStar (WeilCoefficients.{u} l) t)
      (Category.id_comp f) (f)^*[_].rightUnitor.symm
      (Functor.isoWhiskerLeft (f)^*[_] (ProEtale.upperStarId _ Y).symm)
      (ProEtale.upperStarComp _ (𝟙 Y) f) (ProEtale.upperStarComp_id_left _ f)
  exact generic_unit_left (f)^*[_] (𝟙 Y)^*[_] (ProEtale.upperStarId _ Y)
    (ProEtale.upperStarFactor _ (Category.id_comp f)) he M φ


private lemma frobeniusPowStr_add_all
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    (G : WeilSheaf k l Y) (a b : ℕ)
    (e : ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ b).hom ≫
      ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ a).hom =
        ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ (a + b)).hom) :
    (ProEtale.upperStarFactor _ e).hom.app G.obj.carrier.X ≫
      (((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ b).hom)^*[_].map
        (G.frobeniusPowStr a) ≫ G.frobeniusPowStr b = G.frobeniusPowStr (a + b) := by
  cases b with
  | zero =>
    change (ProEtale.upperStarFactor _ (Category.id_comp
      ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ a).hom)).hom.app G.obj.carrier.X ≫
        (𝟙 _)^*[_].map (G.frobeniusPowStr a) ≫ G.frobeniusPowStr 0 =
      G.frobeniusPowStr a
    rw [G.frobeniusPowStr_zero (by rw [pow_zero]; rfl)]
    simp only [ProEtale.upperStarCongr, eqToIso_refl, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp]
    exact unit_left_comp l _ G.obj.carrier.X (G.frobeniusPowStr a)
  | succ b =>
    exact G.upperStarFactor_hom_app_comp_frobeniusPowStr_add a (b + 1)
      (Nat.succ_le_succ (Nat.zero_le b)) e


private lemma frobeniusPowStr_add_eq
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    (G : WeilSheaf k l Y) (a b c : ℕ) (h : a + b = c)
    (e : ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ b).hom ≫
      ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ a).hom =
        ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ c).hom) :
    (ProEtale.upperStarFactor _ e).hom.app G.obj.carrier.X ≫
      (((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ b).hom)^*[_].map
        (G.frobeniusPowStr a) ≫ G.frobeniusPowStr b = G.frobeniusPowStr c := by
  subst c
  exact frobeniusPowStr_add_all G a b e

variable {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
  {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
  (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
  (r : ℕ)
  (hv : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ v =
    v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)

/-- The canonical identification of the underlying sheaf of the explicit pullback. -/
@[irreducible] noncomputable def poweredPullbackCarrierIso (G : WeilSheaf k₀ l X) :
    (v)^*[WeilCoefficients.{u} l].obj G.obj.carrier.X ≅
      ((poweredGeometricPullback v r hv).obj G).obj.carrier.X :=
  (ProEtale.AdicSheaf.forget _).mapIso
    (eqToIso (poweredGeometricPullback_obj_carrier v r hv G).symm)

private lemma powered_carrier_hom (G : WeilSheaf k₀ l X) :
    @Eq ((v)^*[WeilCoefficients.{u} l].obj G.obj.carrier.X ⟶
      ((poweredGeometricPullback v r hv).obj G).obj.carrier.X)
      (poweredPullbackCarrierIso v r hv G).hom
      ((ProEtale.AdicSheaf.forget _).map
        (eqToIso (poweredGeometricPullback_obj_carrier v r hv G).symm).hom) := by
  unfold poweredPullbackCarrierIso
  exact Functor.mapIso_hom _ _


private lemma square_congr
    {A B : Type*} [Category A] [Category B] (H : B ⥤ B) (L : A ⥤ B)
    {M Z : A} {N : B} (θ θ' : L.obj M ⟶ N) (hθ : θ = θ')
    (φ : H.obj N ⟶ N) (E : H.obj (L.obj M) ⟶ L.obj Z) (ψ : Z ⟶ M)
    (h : H.map θ' ≫ φ = E ≫ L.map ψ ≫ θ') :
    H.map θ ≫ φ = E ≫ L.map ψ ≫ θ := by
  subst θ'
  exact h

private lemma powered_first (G : WeilSheaf k₀ l X) :
    ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom)^*[_].map
        (poweredPullbackCarrierIso v r hv G).hom ≫
      ((poweredGeometricPullback v r hv).obj G).frobeniusStr =
    (ProEtale.upperStarCompIso _ hv).hom.app G.obj.carrier.X ≫
      (v)^*[_].map (G.frobeniusPowStr r) ≫
      (poweredPullbackCarrierIso v r hv G).hom := by
  exact square_congr
    (((C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom)^*[_]) (v)^*[_]
    (poweredPullbackCarrierIso v r hv G).hom
    ((ProEtale.AdicSheaf.forget _).map
      (eqToIso (poweredGeometricPullback_obj_carrier v r hv G).symm).hom)
    (powered_carrier_hom v r hv G) ((poweredGeometricPullback v r hv).obj G).frobeniusStr
    ((ProEtale.upperStarCompIso _ hv).hom.app G.obj.carrier.X) (G.frobeniusPowStr r)
    (poweredGeometricPullback_firstStructure v r hv G)


private lemma aut_pow_succ {A : Type*} [Category A] {M : A} (g : Aut M) (n : ℕ) :
    g.hom ≫ (g ^ n).hom = (g ^ (n + 1)).hom := by
  simpa only [pow_one] using g.pow_hom_comp_pow_hom n 1

private lemma aut_pow_add_eq {A : Type*} [Category A] {M : A} (g : Aut M)
    (a b c : ℕ) (h : a + b = c) : (g ^ b).hom ≫ (g ^ a).hom = (g ^ c).hom := by
  subst c
  exact g.pow_hom_comp_pow_hom a b

private lemma aut_pow_comm {A : Type*} [Category A] {M N : A}
    (a : Aut M) (b : Aut N) (v : M ⟶ N) (r : ℕ)
    (h : a.hom ≫ v = v ≫ (b ^ r).hom) (n : ℕ) :
    (a ^ n).hom ≫ v = v ≫ (b ^ (r * n)).hom := by
  induction n with
  | zero =>
    change (𝟙 _) ≫ v = v ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]
  | succ n ih =>
    rw [← aut_pow_succ a n, Category.assoc, ih, ← Category.assoc, h, Category.assoc,
      aut_pow_add_eq b (r * n) r (r * (n + 1)) (Nat.mul_succ r n).symm]

private lemma generic_power_square {Y Z : Scheme.{u}} (l : ℕ) [Fact l.Prime]
    (v : Z ⟶ Y) (a : Aut Z) (b : Aut Y) (r : ℕ)
    (hv : a.hom ≫ v = v ≫ (b ^ r).hom)
    (M : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l))
    (N : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l))
    (θ : (v)^*[_].obj M ⟶ N) (φ : ((b ^ r).hom)^*[_].obj M ⟶ M)
    (ψ : (a.hom)^*[_].obj N ⟶ N)
    (Φ : ∀ n : ℕ, ((b ^ (r * n)).hom)^*[_].obj M ⟶ M)
    (Ψ : ∀ n : ℕ, ((a ^ n).hom)^*[_].obj N ⟶ N)
    (hfirst : (a.hom)^*[_].map θ ≫ ψ =
      (ProEtale.upperStarCompIso _ hv).hom.app M ≫ (v)^*[_].map φ ≫ θ)
    (hzero : ((a ^ 0).hom)^*[_].map θ ≫ Ψ 0 =
      (ProEtale.upperStarCompIso _ (aut_pow_comm a b v r hv 0)).hom.app M ≫
        (v)^*[_].map (Φ 0) ≫ θ)
    (hΨ : ∀ n : ℕ, (ProEtale.upperStarFactor _ (aut_pow_succ a n)).hom.app N ≫
      (a.hom)^*[_].map (Ψ n) ≫ ψ = Ψ (n + 1))
    (hΦ : ∀ n : ℕ, (ProEtale.upperStarFactor _
      (aut_pow_add_eq b (r * n) r (r * (n + 1)) (Nat.mul_succ r n).symm)).hom.app M ≫
        ((b ^ r).hom)^*[_].map (Φ n) ≫ φ = Φ (n + 1))
    (n : ℕ) (hvn : (a ^ n).hom ≫ v = v ≫ (b ^ (r * n)).hom) :
    ((a ^ n).hom)^*[_].map θ ≫ Ψ n =
      (ProEtale.upperStarCompIso _ hvn).hom.app M ≫ (v)^*[_].map (Φ n) ≫ θ := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
    have h := square_comp l v a.hom (a ^ n).hom (a ^ (n + 1)).hom
      (b ^ r).hom (b ^ (r * n)).hom (b ^ (r * (n + 1))).hom
      hv (aut_pow_comm a b v r hv n) hvn (aut_pow_succ a n)
      (aut_pow_add_eq b (r * n) r (r * (n + 1)) (Nat.mul_succ r n).symm)
      M N θ φ (Φ n) ψ (Ψ n) hfirst (ih (aut_pow_comm a b v r hv n))
    rw [hΨ n, hΦ n] at h
    exact h


private lemma iterate_zero (G : WeilSheaf k₀ l X) (P : WeilSheaf k₁ l C)
    (θ : (v)^*[_].obj G.obj.carrier.X ⟶ P.obj.carrier.X) :
    (((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ 0).hom)^*[_].map θ ≫
        P.frobeniusPowStr 0 =
      (ProEtale.upperStarCompIso _ (aut_pow_comm
        (C ↘ Spec (.of k₁)).geometricGaloisFrobenius
        (X ↘ Spec (.of k₀)).geometricGaloisFrobenius v r hv 0)).hom.app G.obj.carrier.X ≫
        (v)^*[_].map (G.frobeniusPowStr (r * 0)) ≫ θ := by
  let FC := (C ↘ Spec (.of k₁)).geometricGaloisFrobenius
  let FX := (X ↘ Spec (.of k₀)).geometricGaloisFrobenius
  exact square_maps_congr (𝟙 _)^*[_] (v)^*[_] θ
    ((ProEtale.upperStarCompIso _ (aut_pow_comm FC FX v r hv 0)).hom.app G.obj.carrier.X)
    (P.frobeniusPowStr 0) ((ProEtale.upperStarId _ _).hom.app P.obj.carrier.X)
    (G.frobeniusPowStr (r * 0)) ((ProEtale.upperStarId _ _).hom.app G.obj.carrier.X)
    (frobeniusPowStr_zero_unit P) (frobeniusPowStr_zero_unit G)
    (square_unit l v G.obj.carrier.X P.obj.carrier.X θ
      (aut_pow_comm FC FX v r hv 0))

attribute [local irreducible] ProEtale.upperStarFactor frobeniusPowStr

private lemma iterate_square (G : WeilSheaf k₀ l X) (P : WeilSheaf k₁ l C)
    (θ : (v)^*[_].obj G.obj.carrier.X ⟶ P.obj.carrier.X)
    (hfirst : @Eq
      ((((C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom)^*[_]).obj
        ((v)^*[_].obj G.obj.carrier.X) ⟶ P.obj.carrier.X)
      (((C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom)^*[_].map
          (X := (v)^*[_].obj G.obj.carrier.X) (Y := P.obj.carrier.X) θ ≫ P.frobeniusStr)
      ((ProEtale.upperStarCompIso _ hv).hom.app G.obj.carrier.X ≫
        @CategoryStruct.comp _ _
          ((v)^*[_].obj ((((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)^*[_].obj
            G.obj.carrier.X)) ((v)^*[_].obj G.obj.carrier.X) P.obj.carrier.X
          ((v)^*[_].map (G.frobeniusPowStr r)) θ))
    (m : ℕ)
    (hvm : ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom ≫ v =
      v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom) :
    @Eq
      (((((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom)^*[_]).obj
        ((v)^*[_].obj G.obj.carrier.X) ⟶ P.obj.carrier.X)
      ((((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom)^*[_].map
          (X := (v)^*[_].obj G.obj.carrier.X) (Y := P.obj.carrier.X) θ ≫ P.frobeniusPowStr m)
      ((ProEtale.upperStarCompIso _ hvm).hom.app G.obj.carrier.X ≫
        @CategoryStruct.comp _ _
          ((v)^*[_].obj
            ((((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom)^*[_].obj
              G.obj.carrier.X)) ((v)^*[_].obj G.obj.carrier.X) P.obj.carrier.X
          ((v)^*[_].map (G.frobeniusPowStr (r * m))) θ) := by
  have hzero := iterate_zero (k₀ := k₀) (k₁ := k₁) (l := l)
    (X := X) (C := C) v r hv G P θ
  have hsucc (n : ℕ) :=
    P.upperStarFactor_hom_app_comp_frobeniusPowStr_succ n
      (aut_pow_succ (C ↘ Spec (.of k₁)).geometricGaloisFrobenius n)
  have hblock (n : ℕ) :=
    frobeniusPowStr_add_eq G (r * n) r (r * (n + 1)) (Nat.mul_succ r n).symm
      (aut_pow_add_eq (X ↘ Spec (.of k₀)).geometricGaloisFrobenius
        (r * n) r (r * (n + 1)) (Nat.mul_succ r n).symm)
  -- Keep the Frobenius expressions explicit: local let aliases cause slow kernel conversions.
  have core := generic_power_square
    (Y := (X ↘ Spec (.of k₀)).geometricFiber)
    (Z := (C ↘ Spec (.of k₁)).geometricFiber)
    l v (C ↘ Spec (.of k₁)).geometricGaloisFrobenius
    (X ↘ Spec (.of k₀)).geometricGaloisFrobenius r hv G.obj.carrier.X P.obj.carrier.X θ
    (G.frobeniusPowStr r) P.frobeniusStr (fun n ↦ G.frobeniusPowStr (r * n))
    (fun n ↦ P.frobeniusPowStr n)
  have first := core hfirst
  have zero := first hzero
  have succ := zero hsucc
  have block := succ (fun n ↦ hblock n)
  exact block m hvm


private lemma expand_exchange
    {A B : Type*} [Category A] [Category B] {F₀ F₁ F₂ F₃ : A ⥤ B}
    (α : F₀ ≅ F₁) (β : F₀ ≅ F₂) (γ : F₂ ≅ F₃) (e : F₁ ≅ F₃)
    (he : e = α.symm ≪≫ β ≪≫ γ) (M : A) {N : B}
    (f : F₁.obj M ⟶ N) (g : F₃.obj M ⟶ N)
    (h : f = e.hom.app M ≫ g) :
    α.hom.app M ≫ f = β.hom.app M ≫ γ.hom.app M ≫ g := by
  rw [h, he]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Iterating the powered pullback structure groups the source Weil maps into blocks of r.

Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 1--3, the assertion
that restriction after a finite constant extension raises Frobenius to that power
(blueprint: lem-zl-powered-geometric-pullback-iterate).

Proof: Write the definition of poweredGeometricPullback as powFunctor followed by
mapOfNatIso. At m=0 the identity-pullback unit gives the displayed square. At m=1 its
square is exactly poweredGeometricPullbackCommIso followed by the r-fold source Weil
map. For the induction step compose the m square with the first square, whiskered by
Fr_C^m. Naturality of upperStarComp moves the carrier identification past the pullbacks;
upperStarComp associativity and upperStarCongr identify the two outer composites using
Fr_C^(m+1) v = v Fr_X^(r*(m+1)). The source iterated Weil structure composition law
combines the blocks of lengths r*m and r into the block of length r*(m+1). The inverse
upperStarIsoLowerStarInv comparisons cancel. This proves equality of actual sheaf
morphisms, before evaluating at any geometric point or taking characteristic polynomials.
The argument includes r=0 and m=0, where the corresponding structure is the identity. -/
theorem poweredGeometricPullback_frobeniusPowStr (G : WeilSheaf k₀ l X) (m : ℕ)
    (hvm : ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom ≫ v =
      v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom) :
    (ProEtale.upperStarComp _
      ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom v).hom.app G.obj.carrier.X ≫
      (((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom)^*[_].map
        (poweredPullbackCarrierIso v r hv G).hom ≫
      ((poweredGeometricPullback v r hv).obj G).frobeniusPowStr m =
    (ProEtale.upperStarCongr _ hvm).hom.app G.obj.carrier.X ≫
      (ProEtale.upperStarComp _ v
        ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom).hom.app G.obj.carrier.X ≫
      (v)^*[_].map (G.frobeniusPowStr (r * m)) ≫
      (poweredPullbackCarrierIso v r hv G).hom := by
  have h := iterate_square (k₀ := k₀) (k₁ := k₁) (l := l) (X := X) (C := C)
    v r hv G ((poweredGeometricPullback v r hv).obj G)
    (poweredPullbackCarrierIso v r hv G).hom (powered_first v r hv G) m hvm
  exact expand_exchange
    (ProEtale.upperStarComp _
      ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom v)
    (ProEtale.upperStarCongr _ hvm)
    (ProEtale.upperStarComp _ v
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom)
    (ProEtale.upperStarCompIso _ hvm) (ProEtale.upperStarCompIso_eq _ hvm)
    G.obj.carrier.X
    ((((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom)^*[_].map
      (poweredPullbackCarrierIso v r hv G).hom ≫
        ((poweredGeometricPullback v r hv).obj G).frobeniusPowStr m)
    ((v)^*[_].map (G.frobeniusPowStr (r * m)) ≫
      (poweredPullbackCarrierIso v r hv G).hom) h

end AlgebraicGeometry.WeilSheaf
