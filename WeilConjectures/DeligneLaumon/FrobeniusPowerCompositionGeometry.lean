/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FrobeniusPowerCommutation
import WeilConjectures.WeilSheaf.BaseChangeField.Coherence

/-! # Geometric composition for the recursive Frobenius-power comparison

Source: the geometric orbit argument in `sk-i-dl-general-real`.
(blueprint: lem-zl-frobenius-power-composition-geometric).
-/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory Limits Endofunctor
namespace AlgebraicGeometry.ProEtaleWeilSheaf
open ProEtale

private noncomputable def factor {l : ℕ} [Fact l.Prime]
    {S T U : Scheme.{u}} {a : S ⟶ U} {b : S ⟶ T} {c : T ⟶ U}
    (e : b ≫ c = a) : (b)_*ᵃ[l] ⋙ (c)_*ᵃ[l] ≅ (a)_*ᵃ[l] :=
  adicLowerStarComp l b c ≪≫ adicLowerStarCongr l e

private theorem factor_hom {l : ℕ} [Fact l.Prime]
    {S T U : Scheme.{u}} {a : S ⟶ U} {b : S ⟶ T} {c : T ⟶ U}
    (e : b ≫ c = a) (M : AdicSheaf l S) :
    ((factor e).hom.app M).hom =
      (lowerStarFactor (WeilCoefficients.{u} l) e).hom.app M.X := by
  rw [factor, Iso.trans_hom, NatTrans.comp_app, Mod.comp_hom',
    adicLowerStarComp_hom_app_hom, adicLowerStarCongr_hom_app_hom]
  exact congrArg (fun α ↦ α.hom.app M.X)
    (lowerStarComp_trans_lowerStarCongr (WeilCoefficients.{u} l) e)

private theorem factor_inv {l : ℕ} [Fact l.Prime]
    {S T U : Scheme.{u}} {a : S ⟶ U} {b : S ⟶ T} {c : T ⟶ U}
    (e : b ≫ c = a) (M : AdicSheaf l S) :
    (factor e).inv.app M = (adicLowerStarCongr l e.symm).hom.app M ≫
      (adicLowerStarComp l b c).inv.app M := by
  apply Mod.hom_ext
  simp only [factor, Iso.trans_inv, NatTrans.comp_app, Mod.comp_hom',
    adicLowerStarCongr_inv_app_hom, adicLowerStarCongr_hom_app_hom]
  rfl

private theorem factor_assoc {l : ℕ} [Fact l.Prime]
    {S T U V : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U) (h : U ⟶ V)
    {fg : S ⟶ U} {gh : T ⟶ V} {fgh : S ⟶ V}
    (e₁ : f ≫ g = fg) (e₂ : g ≫ h = gh)
    (e₃ : fg ≫ h = fgh) (e₄ : f ≫ gh = fgh) (M : AdicSheaf l S) :
    (h)_*ᵃ[l].map ((factor e₁).hom.app M) ≫ (factor e₃).hom.app M =
      (factor e₂).hom.app ((f)_*ᵃ[l].obj M) ≫ (factor e₄).hom.app M := by
  apply Mod.hom_ext
  have H := NatTrans.congr_app
    (lowerStarFactor_assoc (WeilCoefficients.{u} l) f g h e₁ e₂ e₃ e₄) M.X
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Mod.comp_hom', adicLowerStar_map_hom, factor_hom, Functor.comp_obj,
    adicLowerStar_obj_X] using H

private theorem factor_unit {l : ℕ} [Fact l.Prime] {S T : Scheme.{u}}
    (f : S ⟶ T) (i : T ⟶ T) (hi : i = 𝟙 T) (e : f ≫ i = f)
    (M : AdicSheaf l S) :
    (factor e).hom.app M =
      (adicLowerStarCongr l hi).hom.app ((f)_*ᵃ[l].obj M) ≫
        (adicLowerStarId l T).hom.app ((f)_*ᵃ[l].obj M) := by
  subst i
  apply Mod.hom_ext
  have H := congrArg (fun α ↦ α.hom.app M.X)
    (lowerStarFactor_id_right (WeilCoefficients.{u} l) f)
  simp only [factor_hom, Mod.comp_hom', adicLowerStarCongr_hom_app_hom,
    adicLowerStarId_hom_app_hom, lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, adicLowerStar_obj_X] at H ⊢
  exact H.trans (Category.comp_id _)

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X : Scheme.{u}} [X.Over (Spec (.of k₀))]

@[irreducible] private noncomputable def powerStep (n : ℕ) :
    frobeniusPowPullback k₀ l X (n + 1) ≅
      frobeniusPowPullback k₀ l X n ⋙ WeilSheaf.frobeniusPullback k₀ l X :=
  adicLowerStarCongr l (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]) ≪≫
    (adicLowerStarComp l _ _).symm

private theorem iterate_succ (n : ℕ) :
    frobeniusPowPullbackIterateIso (k₀ := k₀) (l := l) (X := X) (n + 1) =
      powerStep n ≪≫ Functor.isoWhiskerRight (frobeniusPowPullbackIterateIso n) _ := by
  simp only [frobeniusPowPullbackIterateIso, powerStep, Iso.trans_assoc]

private theorem composition_zero (m : ℕ) (M : AdicSheaf l
    (X ↘ Spec (.of k₀)).geometricFiber) :
    (frobeniusPowerCompositionIso m 0).hom.app M =
      (frobeniusPowPullbackIterateIso 0).hom.app
          ((frobeniusPowPullback k₀ l X m).obj M) ≫
        (frobeniusPowPullbackIterateIso m).hom.app M := by
  have H := (frobeniusPowPullbackIterateIso (k₀ := k₀) (l := l) (X := X) 0).hom.naturality
    ((frobeniusPowPullbackIterateIso m).hom.app M)
  simpa only [frobeniusPowerCompositionIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app, eqToHom_refl, Functor.id_map,
    Category.comp_id, Functor.comp_map, Functor.iterate_zero] using H

private theorem composition_succ (m n : ℕ) (M : AdicSheaf l
    (X ↘ Spec (.of k₀)).geometricFiber) :
    (frobeniusPowerCompositionIso m (n + 1)).hom.app M =
      (powerStep n).hom.app ((frobeniusPowPullback k₀ l X m).obj M) ≫
        (WeilSheaf.frobeniusPullback k₀ l X).map
          ((frobeniusPowerCompositionIso m n).hom.app M) := by
  have H := (powerStep (k₀ := k₀) (l := l) (X := X) n).hom.naturality
    ((frobeniusPowPullbackIterateIso m).hom.app M)
  simp only [Functor.comp_map] at H
  have E : (eqToIso ((WeilSheaf.frobeniusPullback k₀ l X).iterate_add m (n + 1)).symm
      ).hom.app M =
      (WeilSheaf.frobeniusPullback k₀ l X).map
        ((eqToIso ((WeilSheaf.frobeniusPullback k₀ l X).iterate_add m n).symm).hom.app M) := by
    simp only [eqToIso.hom, eqToHom_app, eqToHom_map]
  simp only [frobeniusPowerCompositionIso, iterate_succ, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc, E]
  rw [reassoc_of% H]

/-- The recursively defined comparison with ordinary iterates agrees with geometric
pushforward composition. Source: step 2 of the geometric orbit argument in
`sk-i-dl-general-real`.

Proof: Induct on the second exponent. At zero, naturality of the identity comparison
and the pushforward unit law identify both maps. At a successor, naturality of the
recursive power comparison gives the same recursion as associativity of pushforward
factorisation. Cancel the two outer factorisation isomorphisms to identify the steps.
(blueprint: lem-zl-frobenius-power-composition-geometric). -/
theorem frobeniusPowerCompositionIso_geometric (m n : ℕ)
    (h : ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ m).inv ≫
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ n).inv =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (m + n)).inv) :
    frobeniusPowerCompositionIso (k₀ := k₀) (l := l) (X := X) m n =
      adicLowerStarComp l _ _ ≪≫ adicLowerStarCongr l h ≪≫
        frobeniusPowPullbackIterateIso (m + n) := by
  induction n with
  | zero =>
    apply Iso.ext
    apply NatTrans.ext
    funext M
    rw [composition_zero]
    have H := factor_unit
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ m).inv
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ 0).inv
      (by rw [pow_zero]; rfl) h M
    change _ = (factor h).hom.app M ≫ _
    rw [H]
    rfl
  | succ n ih =>
    have hmn : ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ m).inv ≫
        ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ n).inv =
        ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (m + n)).inv := by
      rw [pow_add, Aut.Aut_mul_def, Iso.trans_inv]
    have hn : ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ n).inv ≫
        (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.inv =
        ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (n + 1)).inv := by
      rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]
    have hsum : ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (m + n)).inv ≫
        (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.inv =
        ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (m + (n + 1))).inv := by
      rw [Nat.add_succ, pow_succ, Aut.Aut_mul_def, Iso.trans_inv]
    erw [iterate_succ (m + n)]
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have H := factor_assoc
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ m).inv
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ n).inv
      (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.inv hmn hn hsum h M
    have H' := congrArg (fun t ↦
      (factor hn).inv.app ((frobeniusPowPullback k₀ l X m).obj M) ≫
        t ≫ (factor hsum).inv.app M) H
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app] at H'
    have S : (powerStep n).hom.app ((frobeniusPowPullback k₀ l X m).obj M) ≫
        (WeilSheaf.frobeniusPullback k₀ l X).map ((factor hmn).hom.app M) =
        (factor h).hom.app M ≫ (powerStep (m + n)).hom.app M := by
      simpa only [factor_inv, powerStep, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, Category.assoc, Functor.comp_obj, Category.comp_id] using H'
    rw [composition_succ, ih hmn]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    simp only [factor, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
      Category.assoc] at S
    rw [reassoc_of% S]

end AlgebraicGeometry.ProEtaleWeilSheaf
