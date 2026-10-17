/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeField
public import WeilConjectures.WeilSheaf.BaseChangeField.Derived
public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
public import WeilConjectures.WeilSheaf.BaseChangeField.GlobalSections
public import WeilConjectures.WeilSheaf.Cohomology

/-!
# Cohomology under a finite extension of the base field

Let `k₀'/k₀` be an extension of finite fields of degree `r`, `X` a `k₀`-scheme of finite type
and `X' = X ×_{k₀} k₀'`. The cohomology `Hⁱ(X' ⊗ k̄', ℚ̄_ℓ)` of `X'` relative to `k₀'` is
`Hⁱ(X ⊗ k̄, ℚ̄_ℓ)`, with the geometric Frobenius of `k₀'` acting as the `r`-th power `Fʳ` of
that of `k₀` (`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_adicConstant_of_iso`,
`AlgebraicGeometry.WeilSheaf.exists_linearEquiv_cohomology_adicConstant_baseChangeField`).

The identification `θ : X ×_{k₀} k̄ ≅ X' ×_{k₀'} k̄'` of the geometric fibers
(`AlgebraicGeometry.Scheme.Hom.geometricFiberBaseChangeIso`) carries the `r`-th power of the
geometric Galois Frobenius of `X` to that of `X'`. Transport along `θ`
(`AlgebraicGeometry.ProEtaleWeilSheaf.transport`) sends the constant Weil sheaf on `X` to that on
`X'` and commutes with the pushforwards to the base points, hence with their derived functors;
on global sections, the Frobenius of a transported Weil sheaf is the `r`-th power of the original
one.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

noncomputable section

namespace AlgebraicGeometry

open ProEtale

namespace ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]

lemma forget_map_frobeniusPowIso_zero_hom (K : ProEtaleWeilSheaf k₀ l Y)
    (h : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv = 𝟙 _) :
    (AdicSheaf.forget _).map (K.frobeniusPowIso 0).hom =
      (lowerStarCongr _ h).hom.app K.carrier.X ≫ (lowerStarId _ _).hom.app K.carrier.X := by
  rw [frobeniusPowIso_zero K h, Iso.trans_hom, Functor.map_comp]
  rfl

lemma forget_map_frobeniusPowIso_succ_hom (K : ProEtaleWeilSheaf k₀ l Y) (m : ℕ)
    (h : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).inv =
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv ≫
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv) :
    (AdicSheaf.forget _).map (K.frobeniusPowIso (m + 1)).hom =
      (lowerStarCongr _ h).hom.app K.carrier.X ≫
        (lowerStarComp _ _ _).inv.app K.carrier.X ≫
        ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
          ((AdicSheaf.forget _).map (K.frobeniusPowIso m).hom) ≫
        (AdicSheaf.forget _).map K.str.hom := by
  rw [frobeniusPowIso_succ K m h]
  simp only [Iso.trans_hom, Functor.map_comp]
  rfl

/-- The endomorphism of the global sections defined by the iterated Weil structure `φ_m` is the
`m`-th power of the Frobenius. -/
theorem globalSectionsStr_frobeniusPowIso (K : ProEtaleWeilSheaf k₀ l Y) (m : ℕ) :
    globalSectionsStr ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv
        ((AdicSheaf.forget _).map (K.frobeniusPowIso m).hom) =
      @HPow.hPow (End ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj K.carrier.X)) ℕ _ _
        (globalSectionsStr (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv
          ((AdicSheaf.forget _).map K.str.hom)) m := by
  induction m with
  | zero =>
    have h : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv = 𝟙 _ := by
      rw [pow_zero]; rfl
    rw [forget_map_frobeniusPowIso_zero_hom K h, globalSectionsStr_id, pow_zero]
    rfl
  | succ m ih =>
    have h : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + 1)).inv =
        ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv ≫
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv := by
      rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]
    rw [forget_map_frobeniusPowIso_succ_hom K m h, globalSectionsStr_comp, ih, pow_succ',
      End.mul_def]

end ProEtaleWeilSheaf

end AlgebraicGeometry
