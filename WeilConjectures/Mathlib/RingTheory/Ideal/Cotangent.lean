/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# A criterion for linear independence in the cotangent space

For a local ring `A` with maximal ideal `𝔪` and residue field `κ`, a finite family
`f : σ → 𝔪` has linearly independent classes in the cotangent space `𝔪 ⧸ 𝔪 ^ 2` as soon as
every relation `∑ aᵢ fᵢ ∈ 𝔪 ^ 2` has all its coefficients in `𝔪`.

## Main results

* `IsLocalRing.linearIndependent_toCotangent`: the criterion above.
-/

@[expose] public section

open IsLocalRing

namespace IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- A finite family of elements of the maximal ideal of a local ring is linearly independent
in the cotangent space as soon as any relation `∑ aᵢ fᵢ ∈ 𝔪 ^ 2` forces all `aᵢ ∈ 𝔪`. -/
theorem linearIndependent_toCotangent {σ : Type*} [Fintype σ] (f : σ → A)
    (hmem : ∀ i, f i ∈ maximalIdeal A)
    (H : ∀ a : σ → A, (∑ i, a i * f i) ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) :
    LinearIndependent (ResidueField A)
      (fun i ↦ (maximalIdeal A).toCotangent ⟨f i, hmem i⟩) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (I := maximalIdeal A) (g i)
  have hsum : (maximalIdeal A).toCotangent ⟨∑ i, a i * f i, Ideal.sum_mem _
      (fun i _ ↦ Ideal.mul_mem_left _ _ (hmem i))⟩ = 0 := by
    rw [← hg]
    rw [show (⟨∑ i, a i * f i, _⟩ : maximalIdeal A) = ∑ i, a i • (⟨f i, hmem i⟩ : maximalIdeal A) by
      ext; simp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, ← ha i]
    exact (algebraMap_smul (ResidueField A) (a i) _).symm
  rw [Ideal.toCotangent_eq_zero] at hsum
  have h0 : (Ideal.Quotient.mk (maximalIdeal A)) (a i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (H a hsum i)
  rw [← ha i]
  exact h0

end IsLocalRing
