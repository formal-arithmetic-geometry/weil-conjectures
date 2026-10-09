/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Unramified extensions of discrete valuation rings

Let `R ⟶ O` be a homomorphism of discrete valuation rings mapping the maximal ideal of `R` onto
that of `O`, so that a uniformiser of `R` stays a uniformiser of `O`. Then the base change
`O ⊗[R] K` of the fraction field `K` of `R` is the fraction field of `O`
(`IsDiscreteValuationRing.isFractionRing_tensorProduct`): inverting a uniformiser of `O` already
inverts every nonzero element.

We also show that if `B` is a flat algebra over a discrete valuation ring `R` with uniformiser
`ϖ` whose special fibre `B ⧸ ϖB` is reduced, then every idempotent of `B[1/ϖ]` comes from `B`
(`IsDiscreteValuationRing.exists_eq_algebraMap_of_isIdempotentElem`, the algebraic core of
Stacks 055J).
-/

@[expose] public section

open IsLocalRing TensorProduct

namespace IsDiscreteValuationRing

variable {R O : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O]
  [IsDomain O] [IsDiscreteValuationRing O] [Algebra R O]

/-- Under a homomorphism of discrete valuation rings mapping the maximal ideal onto the maximal
ideal, a uniformiser maps to a uniformiser. -/
lemma irreducible_algebraMap_of_map_maximalIdeal
    (hm : (maximalIdeal R).map (algebraMap R O) = maximalIdeal O) {ϖ : R} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap R O ϖ) := by
  rw [irreducible_iff_uniformizer, ← hm, (irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
    Set.image_singleton]

/-- A homomorphism of discrete valuation rings mapping the maximal ideal onto the maximal ideal
is injective. -/
lemma algebraMap_injective_of_map_maximalIdeal
    (hm : (maximalIdeal R).map (algebraMap R O) = maximalIdeal O) :
    Function.Injective (algebraMap R O) := by
  refine (injective_iff_map_eq_zero _).2 fun r hr ↦ ?_
  by_contra h
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible h hϖ
  have hϖ' := irreducible_algebraMap_of_map_maximalIdeal hm hϖ
  rw [map_mul, map_pow] at hr
  exact (mul_ne_zero ((u.isUnit.map _).ne_zero) (pow_ne_zero n hϖ'.ne_zero)) hr

/-- **Base change of the fraction field along an unramified extension.** Let `R ⟶ O` be a
homomorphism of discrete valuation rings with `𝔪_R O = 𝔪_O`, and `K` a fraction field of `R`.
Then `O ⊗[R] K` is a fraction field of `O`. -/
lemma isFractionRing_tensorProduct
    (hm : (maximalIdeal R).map (algebraMap R O) = maximalIdeal O) (K : Type*) [CommRing K]
    [Algebra R K] [IsFractionRing R K] : IsFractionRing O (O ⊗[R] K) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors R)) (O ⊗[R] K) :=
    inferInstance
  refine IsLocalization.of_le_of_exists_dvd
    (Algebra.algebraMapSubmonoid O (nonZeroDivisors R)) _ ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h ↦ ?_
    exact nonZeroDivisors.ne_zero hr ((algebraMap_injective_of_map_maximalIdeal hm)
      (h.trans (map_zero _).symm))
  · intro a ha
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    have hϖ' := irreducible_algebraMap_of_map_maximalIdeal hm hϖ
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ'
    refine ⟨algebraMap R O (ϖ ^ n), ⟨ϖ ^ n, mem_nonZeroDivisors_of_ne_zero
      (pow_ne_zero n hϖ.ne_zero), rfl⟩, ?_⟩
    rw [map_pow]
    exact ⟨↑u⁻¹, by rw [mul_comm (u : O), mul_assoc, Units.mul_inv, mul_one]⟩

omit [IsDiscreteValuationRing R] in
/-- Let `R` be a discrete valuation ring with uniformiser `ϖ` and `B` a flat `R`-algebra whose
special fibre `B ⧸ ϖB` is reduced. Then every idempotent of `B[1/ϖ]` comes from `B`.

The proof only uses that `R` is a domain and `ϖ ≠ 0`. -/
theorem exists_eq_algebraMap_of_isIdempotentElem {B : Type*} [CommRing B] [Algebra R B]
    [Module.Flat R B] {ϖ : R} (hϖ : Irreducible ϖ)
    (hred : IsReduced (B ⧸ Ideal.span {algebraMap R B ϖ}))
    {e : Localization.Away (algebraMap R B ϖ)} (he : IsIdempotentElem e) :
    ∃ b : B, algebraMap B _ b = e := by
  have hcancel (m : ℕ) (x y : B) (h : algebraMap R B ϖ ^ m * x = algebraMap R B ϖ ^ m * y) :
      x = y := by
    refine ((Module.Flat.isSMulRegular_of_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)).pow m) ?_
    simpa [Algebra.smul_def] using h
  have hinj (x y : B) (h : algebraMap B (Localization.Away (algebraMap R B ϖ)) x =
      algebraMap B _ y) : x = y := by
    obtain ⟨⟨_, m, rfl⟩, hc⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R B ϖ)) _).1 h
    exact hcancel m x y hc
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj (algebraMap R B ϖ) e
  induction n generalizing b with
  | zero => exact ⟨b, by simpa using hb.symm⟩
  | succ n ih =>
    have hsq : b * b = algebraMap R B ϖ ^ (n + 1) * b := by
      refine hinj _ _ ?_
      rw [map_mul, map_mul, map_pow, ← hb]
      linear_combination (algebraMap B (Localization.Away (algebraMap R B ϖ))
        (algebraMap R B ϖ) ^ (n + 1)) ^ 2 * he.eq
    have hb0 : Ideal.Quotient.mk (Ideal.span {algebraMap R B ϖ}) b = 0 := by
      refine IsReduced.eq_zero _ ⟨2, ?_⟩
      rw [pow_two, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hsq, pow_succ, mul_assoc]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hb0)
    refine ih c ((IsLocalization.Away.algebraMap_isUnit (algebraMap R B ϖ)).mul_left_inj.1 ?_)
    rw [mul_assoc, ← pow_succ, hb, map_mul]

section Roots

variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

/-- In a discrete valuation ring `S` with uniformiser `ϖ`, if `ϖ ^ a` is an `N`-th power in
`S[1/ϖ]`, then `N ∣ a`: the valuation of an `N`-th power is divisible by `N`. -/
theorem dvd_of_pow_eq_pow_away {ϖ : S} (hϖ : Irreducible ϖ) {N a : ℕ} (hN : N ≠ 0)
    {t : Localization.Away ϖ} (ht : t ^ N = algebraMap S _ ϖ ^ a) : N ∣ a := by
  obtain ⟨k, x, hx⟩ := IsLocalization.Away.surj ϖ t
  have hinj : Function.Injective (algebraMap S (Localization.Away ϖ)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero)
  have hxN : x ^ N = ϖ ^ (a + k * N) := hinj (by
    rw [map_pow, ← hx, mul_pow, ht, map_pow, pow_add, ← pow_mul, mul_comm k N, pow_mul])
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hxN
    exact pow_ne_zero _ hϖ.ne_zero hxN.symm
  obtain ⟨j, u, rfl⟩ := eq_unit_mul_pow_irreducible hx0 hϖ
  have h : ((u ^ N : Sˣ) : S) * ϖ ^ (j * N) = ((1 : Sˣ) : S) * ϖ ^ (a + k * N) := by
    rw [Units.val_pow_eq_pow_val, pow_mul, ← mul_pow, hxN, Units.val_one, one_mul]
  have hjk := unit_mul_pow_congr_pow hϖ hϖ _ _ _ _ h
  exact (Nat.dvd_add_left (dvd_mul_left N k)).1 (hjk ▸ dvd_mul_left N j)

end Roots

end IsDiscreteValuationRing
