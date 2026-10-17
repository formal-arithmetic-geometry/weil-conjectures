/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.Abhyankar
public import WeilConjectures.RingTheory.Etale.TraitSection.KummerFibre
public import WeilConjectures.RingTheory.Etale.TraitSection.KummerLocalization
public import WeilConjectures.RingTheory.Etale.TraitSection.Reduction

/-!
# Abhyankar's lemma at the generic points of the closed fibre

Let `A` be a discrete valuation ring with uniformizer `ϖ`, `B` a smooth `A`-algebra, `B_K` its
localization at the nonzero elements of `A` and `L` a finite étale `B_K`-algebra which is Galois
with group `G`, `n = |G|` invertible in `A`. Let `A₂ = A[t] ⧸ (tⁿ - ϖ)` and `B₂ = B ⊗[A] A₂`.
At a minimal prime `Q` of `tB₂`, the integral closure of `B₂` in `B₂ ⊗[B] L` is finite étale
(`Algebra.TraitSection.etale_finite_localization_integralClosure_kummer`): the local ring `O` of
`B` at `Q ∩ B` is a discrete valuation ring with uniformizer `ϖ`
(`Algebra.Smooth.isDiscreteValuationRing_localization_of_mem_minimalPrimes`), and Abhyankar's
lemma (`IsDiscreteValuationRing.etale_integralClosure_adjoinRoot`) applies to the Galois algebra
`O ⊗[B] L` over the fraction field `O ⊗[B] B_K` of `O`
(`Algebra.TraitSection.etale_finite_integralClosure_kummer_of_mem_minimalPrimes`).

This is used in the trait case of blueprint `sbc-thm-spreading-finite-etale-galois`
([Stacks 0EYJ]).
-/

@[expose] public section

universe u

open Polynomial IsLocalRing TensorProduct

namespace Algebra.TraitSection


variable {A B Bk L : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [Algebra A B] [Algebra.Smooth A B]
  [CommRing Bk] [Algebra B Bk]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) Bk]
  [CommRing L] [Algebra Bk L] [Algebra B L] [IsScalarTower B Bk L]
  [Module.Finite Bk L] [Algebra.Etale Bk L]

set_option maxHeartbeats 1600000 in
-- The fraction field `O ⊗[B] B_K` and the cover `O ⊗[B] L` make elaboration slow.
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
include Bk in
/-- **Abhyankar's lemma at a generic point of the closed fibre.** Let `O = B_𝔮` for a minimal
prime `𝔮` of `ϖB`. Then the integral closure of `O₂ = O[t] ⧸ (tⁿ - ϖ)` in `O₂ ⊗[O] (O ⊗[B] L)`
is finite étale over `O₂`. -/
theorem etale_finite_integralClosure_kummer_of_mem_minimalPrimes (G : Type*) [Group G]
    [Finite G] [MulSemiringAction G L] [SMulCommClass G Bk L]
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → x ∈ Set.range (algebraMap Bk L))
    (hrank : ∀ p, Module.rankAtStalk (R := Bk) L p = Nat.card G)
    (hG : IsUnit (Nat.card G : A)) {ϖ : A} (hϖ : Irreducible ϖ) (𝔮 : Ideal B) [𝔮.IsPrime]
    (h𝔮 : 𝔮 ∈ ((maximalIdeal A).map (algebraMap A B)).minimalPrimes) :
    Algebra.Etale (AdjoinRoot (X ^ Nat.card G - C (algebraMap A (Localization.AtPrime 𝔮) ϖ)))
        (integralClosure (AdjoinRoot (X ^ Nat.card G - C (algebraMap A (Localization.AtPrime 𝔮) ϖ)))
          (AdjoinRoot (X ^ Nat.card G - C (algebraMap A (Localization.AtPrime 𝔮) ϖ)) ⊗[
            Localization.AtPrime 𝔮] (Localization.AtPrime 𝔮 ⊗[B] L))) ∧
      Module.Finite (AdjoinRoot (X ^ Nat.card G - C (algebraMap A (Localization.AtPrime 𝔮) ϖ)))
        (integralClosure (AdjoinRoot (X ^ Nat.card G - C (algebraMap A (Localization.AtPrime 𝔮) ϖ)))
          (AdjoinRoot (X ^ Nat.card G - C (algebraMap A (Localization.AtPrime 𝔮) ϖ)) ⊗[
            Localization.AtPrime 𝔮] (Localization.AtPrime 𝔮 ⊗[B] L))) := by
  let O := Localization.AtPrime 𝔮
  obtain ⟨_, _, hϖO⟩ :=
    Algebra.Smooth.isDiscreteValuationRing_localization_of_mem_minimalPrimes hϖ 𝔮 h𝔮
  let F := O ⊗[B] Bk
  let LF := O ⊗[B] L
  have : Module.Flat A O := Module.Flat.trans A B O
  have hinj (r : A) (hr : r ≠ 0) : algebraMap A O r ≠ 0 := by
    intro h
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := O)
      (mem_nonZeroDivisors_of_ne_zero hr)
    refine one_ne_zero (hreg (?_ : r • (1 : O) = r • 0))
    rw [Algebra.smul_def, h, smul_zero, zero_mul]
  have : IsFractionRing O F := by
    refine IsLocalization.of_le_of_exists_dvd
      (Algebra.algebraMapSubmonoid O (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))) _
      ?_ ?_
    · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      rw [← IsScalarTower.algebraMap_apply]
      exact mem_nonZeroDivisors_of_ne_zero (hinj r (nonZeroDivisors.ne_zero hr))
    · intro x hx
      obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (nonZeroDivisors.ne_zero hx) hϖO
      refine ⟨algebraMap A O (ϖ ^ m), ⟨_, ⟨ϖ ^ m,
        pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) m, rfl⟩,
        (IsScalarTower.algebraMap_apply A B O _).symm⟩, ?_⟩
      rw [map_pow]
      exact Units.mul_left_dvd.2 dvd_rfl
  let : Field F := IsFractionRing.toField O
  let : Algebra F LF := (coverMap (B := B) (B₁ := O) (Bk := Bk) (L := L)).toRingHom.toAlgebra
  have : IsScalarTower O F LF := .of_algebraMap_eq fun x ↦
    ((coverMap (B := B) (B₁ := O) (Bk := Bk) (L := L)).commutes x).symm
  obtain ⟨hE, hFin, hrk⟩ := etale_finite_cover (B := B) (B₁ := O) (Bk := Bk) (L := L)
  have : Algebra.Etale F LF := hE
  -- the Galois action on `O ⊗[B] L`
  have : SMulCommClass G B L := ⟨fun g b x ↦ by
    rw [IsScalarTower.algebraMap_smul (A := Bk) b x |>.symm, smul_comm g]
    exact (IsScalarTower.algebraMap_smul (A := Bk) b (g • x))⟩
  let := rightTensorAction (B := B) (B₁ := O) (L := L) G
  have hfixι (g : G) (k : F) : g • algebraMap F LF k = algebraMap F LF k := by
    induction k using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]
    | add a b ha hb => rw [map_add, smul_add, ha, hb]
    | tmul b c =>
      change b ⊗ₜ[B] (g • algebraMap Bk L c) = b ⊗ₜ[B] algebraMap Bk L c
      rw [smul_algebraMap]
  have : SMulCommClass G F LF := ⟨fun g k x ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfixι]⟩
  have hfixF (x : LF) (hx : ∀ g : G, g • x = x) : x ∈ Set.range (algebraMap F LF) :=
    mem_range_of_forall_smul_eq (Bk := Bk) G hfix x hx
  have hrankF : Module.finrank F LF = Nat.card G := by
    have h := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := F) (M := LF))
      ⟨⊥, Ideal.isPrime_bot⟩
    rw [Pi.natCast_apply, Nat.cast_id] at h
    rw [← h]
    exact hrk _ hrank _
  have hn : IsUnit ((Nat.card G : ℕ) : O) := by simpa using hG.map (algebraMap A O)
  exact IsDiscreteValuationRing.etale_integralClosure_adjoinRoot (O := O) (F := F) (L := LF) G
    hrankF hfixF dvd_rfl hn hϖO _ (AdjoinRoot.isAdjoinRoot _)

set_option maxHeartbeats 1600000 in
-- The base change `B₂ = B ⊗[A] A₂` and its localizations make elaboration slow.
include Bk in
/-- **Abhyankar's lemma at the generic points of the closed fibre of `B₂ = B ⊗[A] A₂`**,
`A₂ = A[t] ⧸ (tⁿ - ϖ)`: at a minimal prime `Q` of `tB₂`, the integral closure of `B₂` in
`B₂ ⊗[B] L` is finite étale. -/
theorem etale_finite_localization_integralClosure_kummer (G : Type*) [Group G]
    [Finite G] [MulSemiringAction G L] [SMulCommClass G Bk L]
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → x ∈ Set.range (algebraMap Bk L))
    (hrank : ∀ p, Module.rankAtStalk (R := Bk) L p = Nat.card G)
    (hG : IsUnit (Nat.card G : A)) {ϖ : A} (hϖ : Irreducible ϖ)
    (Q : Ideal (B ⊗[A] AdjoinRoot (X ^ Nat.card G - C ϖ))) [Q.IsPrime]
    (hQ : Q ∈ (Ideal.span {(1 : B) ⊗ₜ[A] AdjoinRoot.root (X ^ Nat.card G - C ϖ)}).minimalPrimes) :
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[B ⊗[A] AdjoinRoot
        (X ^ Nat.card G - C ϖ)] integralClosure (B ⊗[A] AdjoinRoot (X ^ Nat.card G - C ϖ))
          (kummerCover A B L (Nat.card G) ϖ)) ∧
      Module.Finite (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[B ⊗[A] AdjoinRoot
        (X ^ Nat.card G - C ϖ)] integralClosure (B ⊗[A] AdjoinRoot (X ^ Nat.card G - C ϖ))
          (kummerCover A B L (Nat.card G) ϖ)) := by
  have hn0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  let A₂ := AdjoinRoot (X ^ Nat.card G - C ϖ)
  let B₂ := B ⊗[A] A₂
  let T₂ := integralClosure B₂ (kummerCover A B L (Nat.card G) ϖ)
  -- the image of `ϖ` in `B₂` is `tⁿ`
  have hϖt : algebraMap B B₂ (algebraMap A B ϖ) =
      ((1 : B) ⊗ₜ[A] AdjoinRoot.root (X ^ Nat.card G - C ϖ)) ^ Nat.card G := by
    have hroot : AdjoinRoot.root (X ^ Nat.card G - C ϖ) ^ Nat.card G = algebraMap A A₂ ϖ := by
      have h := AdjoinRoot.mk_self (f := X ^ Nat.card G - C ϖ)
      rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
      exact h
    rw [Algebra.TensorProduct.tmul_pow, one_pow, hroot, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  -- the contraction `𝔮` of `Q` is a minimal prime of `ϖB`
  have : Module.Free A A₂ := .of_basis (AdjoinRoot.powerBasis' (monic_X_pow_sub_C ϖ hn0)).basis
  have h𝔮 : Q.comap (algebraMap B B₂) ∈ ((maximalIdeal A).map (algebraMap A B)).minimalPrimes := by
    refine Ideal.comap_mem_minimalPrimes_of_le_radical ?_ ?_ hQ
    · rw [hϖ.maximalIdeal_eq, Ideal.map_span, Ideal.map_span, Set.image_singleton,
        Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hϖt,
        Ideal.mem_span_singleton]
      exact dvd_pow_self _ hn0
    · rw [hϖ.maximalIdeal_eq, Ideal.map_span, Ideal.map_span, Set.image_singleton,
        Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hϖt]
      exact ⟨Nat.card G, Ideal.mem_span_singleton_self _⟩
  obtain ⟨hE, hF⟩ := etale_finite_integralClosure_kummer_of_mem_minimalPrimes (Bk := Bk) G hfix
    hrank hG hϖ _ h𝔮
  let O := Localization.AtPrime (Q.comap (algebraMap B B₂))
  let O₂ := AdjoinRoot (X ^ Nat.card G - C (algebraMap A O ϖ))
  let := AdjoinRoot.tensorXPowSubCAlgebra (B := B) (T := O) (Nat.card G) ϖ
  have := AdjoinRoot.isScalarTower_tensorXPowSubCAlgebra (B := B) (T := O) (Nat.card G) ϖ
  have := AdjoinRoot.isLocalization_tensorXPowSubC (B := B) (T := O) (Nat.card G) ϖ
    (Q.comap (algebraMap B B₂)).primeCompl
  let e := TensorProduct.integralClosureTensorEquivOfIsLocalization (B := B) (B₂ := B₂) (T := O)
    (D := O₂) (Q.comap (algebraMap B B₂)).primeCompl L
  have : Algebra.Etale O₂ (O₂ ⊗[B₂] T₂) := .of_equiv e.symm
  have : Module.Finite O₂ (O₂ ⊗[B₂] T₂) := .equiv e.symm.toLinearEquiv
  -- `(B₂)_Q` is a localization of `O₂`, the localization of `B₂` at `B ∖ 𝔮`
  have hunit (s : Algebra.algebraMapSubmonoid B₂ (Q.comap (algebraMap B B₂)).primeCompl) :
      IsUnit (algebraMap B₂ (Localization.AtPrime Q) s) := by
    obtain ⟨_, ⟨b, hb, rfl⟩⟩ := s
    exact IsLocalization.map_units (Localization.AtPrime Q) (⟨_, hb⟩ : Q.primeCompl)
  let : Algebra O₂ (Localization.AtPrime Q) := (IsLocalization.lift
    (M := Algebra.algebraMapSubmonoid B₂ (Q.comap (algebraMap B B₂)).primeCompl) (S := O₂)
    hunit).toAlgebra
  have : IsScalarTower B₂ O₂ (Localization.AtPrime Q) := .of_algebraMap_eq fun b ↦
    (IsLocalization.lift_eq
      (M := Algebra.algebraMapSubmonoid B₂ (Q.comap (algebraMap B B₂)).primeCompl) (S := O₂)
      hunit b).symm
  let e' := Algebra.TensorProduct.cancelBaseChange B₂ O₂ (Localization.AtPrime Q)
    (Localization.AtPrime Q) T₂
  exact ⟨.of_equiv e', .equiv e'.toLinearEquiv⟩

end Algebra.TraitSection
