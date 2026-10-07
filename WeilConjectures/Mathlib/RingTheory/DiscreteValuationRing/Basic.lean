/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Unramified extensions of discrete valuation rings

Let `R ⟶ O` be a homomorphism of discrete valuation rings mapping the maximal ideal of `R` onto
that of `O`, so that a uniformiser of `R` stays a uniformiser of `O`. Then the base change
`O ⊗[R] K` of the fraction field `K` of `R` is the fraction field of `O`
(`IsDiscreteValuationRing.isFractionRing_tensorProduct`): inverting a uniformiser of `O` already
inverts every nonzero element.
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

end IsDiscreteValuationRing
