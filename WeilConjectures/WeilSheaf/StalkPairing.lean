/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkMonoidal

/-!
# Iterated Weil structures and monoidal structures

A morphism `e : P ⊗ Q ⟶ R` of the underlying sheaves of Weil sheaves which is compatible with
the Weil structures, `(φ_P ⊗ φ_Q) ≫ e = μ ≫ Fr^* e ≫ φ_R`, is compatible with the iterated Weil
structures `φ_m` (`AlgebraicGeometry.WeilSheaf.frobeniusPowIso`), and similarly for a unit
`𝟙 ⟶ R`. Together with `AlgebraicGeometry.WeilSheaf.stalkPairing_frobenius`, such a pairing
induces a pairing of stalks compatible with the local Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section IteratedWeilStructure

lemma frobeniusPowIso_zero_hom_hom (F : WeilSheaf k₀ l X) :
    (F.frobeniusPowIso 0).hom.hom =
      (lowerStarCongr (WeilCoefficients.{u} l) (by rw [pow_zero]; rfl)).hom.app
          F.obj.carrier.X ≫
        (lowerStarId (WeilCoefficients.{u} l) _).hom.app F.obj.carrier.X := by
  simp [frobeniusPowIso, adicLowerStarId, adicLowerStarCongr_hom_app_hom]
  rfl

lemma frobeniusPowIso_succ_hom_hom (F : WeilSheaf k₀ l X) (m : ℕ) :
    (F.frobeniusPowIso (m + 1)).hom.hom =
      (lowerStarCongr (WeilCoefficients.{u} l)
          (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv])).hom.app F.obj.carrier.X ≫
        (lowerStarComp (WeilCoefficients.{u} l) _ _).inv.app F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
          (F.frobeniusPowIso m).hom.hom ≫ F.obj.str.hom.hom := by
  simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Mod.comp_hom',
    adicLowerStarCongr_hom_app_hom, Iso.symm_hom, adicLowerStarComp_inv_app_hom,
    Functor.mapIso_hom, adicLowerStar_map_hom]

/-- A pairing of the underlying sheaves of Weil sheaves compatible with the Weil structures is
compatible with the iterated Weil structures. -/
theorem frobeniusPowIso_tensor (P Q R : WeilSheaf k₀ l X)
    (e : P.obj.carrier.X ⊗ Q.obj.carrier.X ⟶ R.obj.carrier.X)
    (h : (P.obj.str.hom.hom ⊗ₘ Q.obj.str.hom.hom) ≫ e =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
          P.obj.carrier.X Q.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map e ≫
          R.obj.str.hom.hom) (m : ℕ) :
    ((P.frobeniusPowIso m).hom.hom ⊗ₘ (Q.frobeniusPowIso m).hom.hom) ≫ e =
      μ (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv)_*[_]
          P.obj.carrier.X Q.obj.carrier.X ≫
        (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv)_*[_].map e ≫
          (R.frobeniusPowIso m).hom.hom := by
  induction m with
  | zero =>
    rw [frobeniusPowIso_zero_hom_hom, frobeniusPowIso_zero_hom_hom,
      frobeniusPowIso_zero_hom_hom]
    have hc := NatTrans.IsMonoidal.tensor
      (τ := (lowerStarCongr (WeilCoefficients.{u} l)
        (show ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv = 𝟙 _ by
          rw [pow_zero]; rfl)).hom ≫
        (lowerStarId (WeilCoefficients.{u} l) _).hom) P.obj.carrier.X Q.obj.carrier.X
    simp only [NatTrans.comp_app, Functor.LaxMonoidal.id_μ, Category.comp_id] at hc
    rw [← hc, Category.assoc]
    congr 1
    have := ((lowerStarCongr (WeilCoefficients.{u} l)
        (show ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv = 𝟙 _ by
          rw [pow_zero]; rfl)).hom ≫ (lowerStarId (WeilCoefficients.{u} l) _).hom).naturality e
    simp only [NatTrans.comp_app, Functor.id_map, Category.assoc] at this
    exact this.symm
  | succ m ih =>
    rw [frobeniusPowIso_succ_hom_hom, frobeniusPowIso_succ_hom_hom,
      frobeniusPowIso_succ_hom_hom, ← tensorHom_comp_tensorHom_assoc,
      ← tensorHom_comp_tensorHom_assoc, ← tensorHom_comp_tensorHom_assoc, h, μ_natural_assoc,
      ← Functor.map_comp_assoc, ih]
    have hc : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).inv =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv ≫
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv := by
      rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]
    have h₁ := NatTrans.IsMonoidal.tensor (τ := (lowerStarComp (WeilCoefficients.{u} l)
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv) P.obj.carrier.X
        Q.obj.carrier.X
    have h₂ := NatTrans.IsMonoidal.tensor (τ := (lowerStarCongr (WeilCoefficients.{u} l) hc).hom)
      P.obj.carrier.X Q.obj.carrier.X
    have n₁ := (lowerStarComp (WeilCoefficients.{u} l)
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.naturality e
    have n₂ := (lowerStarCongr (WeilCoefficients.{u} l) hc).hom.naturality e
    simp only [Functor.comp_map] at n₁
    have hμ := Functor.LaxMonoidal.comp_μ
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv)_*[WeilCoefficients.{u} l]
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
      P.obj.carrier.X Q.obj.carrier.X
    rw [Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% hμ, ← reassoc_of% h₁, ← reassoc_of% h₂, reassoc_of% n₂, reassoc_of% n₁]

/-- A unit of the underlying sheaf of a Weil sheaf compatible with the Weil structure is
compatible with the iterated Weil structures. -/
theorem frobeniusPowIso_unit (R : WeilSheaf k₀ l X) (η : 𝟙_ _ ⟶ R.obj.carrier.X)
    (h : ε ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l] ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map η ≫
          R.obj.str.hom.hom = η) (m : ℕ) :
    ε (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv)_*[WeilCoefficients.{u} l] ≫
        (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv)_*[_].map η ≫
          (R.frobeniusPowIso m).hom.hom = η := by
  induction m with
  | zero =>
    rw [frobeniusPowIso_zero_hom_hom]
    have hc := NatTrans.IsMonoidal.unit
      (τ := (lowerStarCongr (WeilCoefficients.{u} l)
        (show ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv = 𝟙 _ by
          rw [pow_zero]; rfl)).hom ≫
        (lowerStarId (WeilCoefficients.{u} l) _).hom)
    have := ((lowerStarCongr (WeilCoefficients.{u} l)
        (show ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv = 𝟙 _ by
          rw [pow_zero]; rfl)).hom ≫ (lowerStarId (WeilCoefficients.{u} l) _).hom).naturality η
    simp only [NatTrans.comp_app, Functor.LaxMonoidal.id_ε, Functor.id_map,
      Category.assoc] at hc this
    rw [this, reassoc_of% hc]
  | succ m ih =>
    have hc : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).inv =
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv ≫
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv := by
      rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]
    have h₁ := NatTrans.IsMonoidal.unit (τ := (lowerStarComp (WeilCoefficients.{u} l)
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv)
    have h₂ := NatTrans.IsMonoidal.unit (τ := (lowerStarCongr (WeilCoefficients.{u} l) hc).hom)
    have n₁ := (lowerStarComp (WeilCoefficients.{u} l)
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.naturality η
    have n₂ := (lowerStarCongr (WeilCoefficients.{u} l) hc).hom.naturality η
    simp only [Functor.comp_map] at n₁
    simp only [Functor.LaxMonoidal.comp_ε] at h₁
    rw [frobeniusPowIso_succ_hom_hom, reassoc_of% n₂, reassoc_of% h₂, reassoc_of% n₁,
      reassoc_of% h₁, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc, ih, h]

end IteratedWeilStructure

end AlgebraicGeometry.WeilSheaf
