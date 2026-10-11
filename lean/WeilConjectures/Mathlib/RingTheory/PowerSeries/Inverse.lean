/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.LinearCombination

/-!
# Congruences of power series modulo powers of `X`

Finite products of power series congruent to `1` modulo `X ^ n` are congruent to `1` modulo
`X ^ n`, and over a field congruence modulo `X ^ n` is preserved by inversion.

## Main statements

- `PowerSeries.X_pow_dvd_prod_sub_one`
- `PowerSeries.X_pow_dvd_prod_sub_prod_of_subset`
- `PowerSeries.X_pow_dvd_inv_sub_inv`
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- A finite product of power series congruent to `1` modulo `X ^ n` is congruent to `1` modulo
`X ^ n`. -/
theorem X_pow_dvd_prod_sub_one {J : Type*} (s : Finset J) (f : J → R⟦X⟧) (n : ℕ)
    (hf : ∀ j ∈ s, X ^ n ∣ f j - 1) : X ^ n ∣ ∏ j ∈ s, f j - 1 := by
  simp_rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hf ⊢
  rw [map_prod]
  exact Finset.prod_eq_one hf

/-- Two finite products agree modulo `X ^ n` if the second one only adds factors congruent to
`1` modulo `X ^ n`. -/
theorem X_pow_dvd_prod_sub_prod_of_subset {J : Type*} {s t : Finset J}
    (hst : s ⊆ t) (f : J → R⟦X⟧) (n : ℕ) (hf : ∀ j ∈ t, j ∉ s → X ^ n ∣ f j - 1) :
    X ^ n ∣ ∏ j ∈ t, f j - ∏ j ∈ s, f j := by
  classical
  rw [← Finset.prod_sdiff hst, ← sub_one_mul]
  exact Dvd.dvd.mul_right (X_pow_dvd_prod_sub_one _ f n fun j hj ↦
    hf j (Finset.sdiff_subset hj) (Finset.mem_sdiff.1 hj).2) _

/-- Over a field, congruence modulo `X ^ n` of two power series with nonzero constant term is
preserved by inversion: `f⁻¹ - g⁻¹ = f⁻¹ g⁻¹ (g - f)`. -/
theorem X_pow_dvd_inv_sub_inv {k : Type*} [Field k] {f g : k⟦X⟧} {n : ℕ}
    (hf : constantCoeff f ≠ 0) (hg : constantCoeff g ≠ 0) (h : X ^ n ∣ f - g) :
    X ^ n ∣ f⁻¹ - g⁻¹ := by
  have h₁ := PowerSeries.inv_mul_cancel _ hf
  have h₂ := PowerSeries.inv_mul_cancel _ hg
  have : f⁻¹ - g⁻¹ = -(f⁻¹ * g⁻¹ * (f - g)) := by
    linear_combination g⁻¹ * h₁ - f⁻¹ * h₂
  rw [this, dvd_neg]
  exact Dvd.dvd.mul_left h _

end PowerSeries
