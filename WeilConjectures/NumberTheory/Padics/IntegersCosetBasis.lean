/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.NumberTheory.Padics.CoefficientExtension

/-!
# Uniformizer cosets form a neighbourhood basis

In the ring of integers of a finite extension of `ℚ_[l]`, the cosets of the powers of the
uniformizer form a neighbourhood basis.
-/

@[expose] public section

open scoped Topology

universe u

namespace Padic

/-- The positive uniformizer-power cosets form a neighbourhood basis in the ring of integers.
-/
theorem coefficientExtension_integers_coset_basis (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    letI := spectralNorm.normedField (Padic l) E
    ∀ x : coefficientExtensionIntegers l E,
      (𝓝 x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
        {y | Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)) y =
          Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)) x}) := by
  let : NormedField E := spectralNorm.normedField (Padic l) E
  let R := coefficientExtensionIntegers l E
  let π := coefficientExtensionUniformizer l E
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  have hR : ∀ z : E, z ∈ R ↔ ‖z‖ ≤ 1 := h.1
  have hgen : Ideal.span ({π} : Set R) = coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hπ0 : π ≠ 0 := by
    intro he
    have hz := hgen
    rw [he, Ideal.span_singleton_zero] at hz
    exact h.2.2.2.2.2.2.2.2.2.1 hz.symm
  have hπE : (π : E) ≠ 0 := by
    intro he
    exact hπ0 (Subtype.ext he)
  have hr0 : 0 < ‖(π : E)‖ := norm_pos_iff.mpr hπE
  have hr1 : ‖(π : E)‖ < 1 := by
    apply (h.2.1 π).mp
    change π ∈ coefficientExtensionMaximalIdeal l E
    rw [← hgen]
    exact Ideal.subset_span (Set.mem_singleton π)
  have hmem (n : ℕ) (z : R) :
      z ∈ coefficientExtensionIdeal l E n ↔ ‖(z : E)‖ ≤ ‖(π : E)‖ ^ n := by
    change z ∈ Ideal.span ({π} : Set R) ^ n ↔ _
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      change ‖(y : E) * (π : E) ^ n‖ ≤ _
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (by positivity) ((hR _).mp y.property)
    · intro hz
      have hy : (z : E) / (π : E) ^ n ∈ R := by
        rw [hR, norm_div, norm_pow, div_le_one (pow_pos hr0 n)]
        exact hz
      refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
      change (z : E) / (π : E) ^ n * (π : E) ^ n = (z : E)
      exact div_mul_cancel₀ _ (pow_ne_zero _ hπE)
  intro x
  have he (n : ℕ) :
      {y : R | Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)) y =
        Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)) x} =
        Metric.closedBall x (‖(π : E)‖ ^ (n + 1)) := by
    ext y
    rw [Set.mem_ofPred_eq, Ideal.Quotient.eq, hmem]
    change ‖(y : E) - (x : E)‖ ≤ _ ↔ _
    rfl
  have hb : (𝓝 x).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ Metric.closedBall x (‖(π : E)‖ ^ (n + 1))) := by
    apply Metric.nhds_basis_closedBall.to_hasBasis
    · intro ε hε
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hr1
      refine ⟨n, trivial, Metric.closedBall_subset_closedBall ?_⟩
      exact (pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_succ n)).trans hn.le
    · intro n _
      exact ⟨_, pow_pos hr0 (n + 1), Set.Subset.rfl⟩
  convert hb using 1
  funext n
  exact he n

end Padic
