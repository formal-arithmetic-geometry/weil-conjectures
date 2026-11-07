/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Expand
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.PiTopology
public import WeilConjectures.ZetaLinearAlgebra.CharpolyRevExpand
public import WeilConjectures.ZetaLinearAlgebra.TraceDatum

/-!
# Euler products of alternating determinants

For a finite graded family `(W i, F i)` of endomorphisms of finite dimensional vector spaces
and `e ≥ 1`, the alternating determinant `Δ_e = ∏_i det (1 - T ^ e F i)^{(-1)^i}`
(`LinearMap.alternatingCharpolyRevProd`) is the expansion `T ↦ T ^ e` of `Δ_1`, has constant
coefficient `1`, and the logarithmic derivative of `Δ_e⁻¹` is the generating series

`∑_{e ∣ m} e (∑_i (-1)^i tr (F_i^{m / e})) T^m`.

Comparing logarithmic derivatives, a trace identity

`∑_i (-1)^i tr (A_i^m) = ∑_{j, e_j ∣ m} e_j ∑_i (-1)^i tr (B_{j,i}^{m / e_j})`, `m ≥ 1`,

between a family `A` and families `B_j` indexed by a set `J` with finitely many `j` of each
degree `e_j` gives the Euler product `∏_j Δ_{e_j}(B_j)⁻¹ = Δ_1(A)⁻¹`, the product being
coefficientwise locally finite.

## Main statements

- `LinearMap.X_mul_derivative_inv_alternatingCharpolyRevProd`: the logarithmic derivative of
  `Δ_e⁻¹`.
- `LinearMap.hasProd_inv_alternatingCharpolyRevProd_of_sum_trace_eq`: the Euler product.
-/

@[expose] public section

open PowerSeries

namespace LinearMap

variable {K : Type*} [Field K] {W : ℤ → Type*} [∀ i, AddCommGroup (W i)]
  [∀ i, Module K (W i)] [∀ i, FiniteDimensional K (W i)]


/-- The alternating determinant `∏_i det (1 - T ^ e F i)^{(-1)^i}`, `e ≠ 0`, has constant
coefficient `1`. -/
theorem constantCoeff_alternatingCharpolyRevProd (s : Finset ℤ) (F : ∀ i, Module.End K (W i))
    {e : ℕ} (he : e ≠ 0) : constantCoeff (alternatingCharpolyRevProd s F e) = 1 := by
  rw [alternatingCharpolyRevProd, map_prod]
  refine Finset.prod_eq_one fun i _ ↦ ?_
  have h : constantCoeff (((F i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) :
      K⟦X⟧) = 1 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
      Polynomial.eval_pow, Polynomial.eval_X, zero_pow he, eval_charpolyRev]
  split_ifs
  · exact h
  · rw [constantCoeff_inv, h, inv_one]


/-- The logarithmic derivative of the inverse `∏_i det (1 - T ^ e F i)^{(-1)^{i+1}}` of an
alternating determinant, `e ≠ 0`, is the generating series
`∑_{e ∣ m} e (∑_i (-1)^i tr (F_i^{m / e})) T^m` of the alternating traces. -/
theorem X_mul_derivative_inv_alternatingCharpolyRevProd (s : Finset ℤ)
    (F : ∀ i, Module.End K (W i)) {e : ℕ} (he : e ≠ 0) :
    X * derivative (R := K) (alternatingCharpolyRevProd s F e)⁻¹ =
      (PowerSeries.mk fun m ↦ if m ≠ 0 ∧ e ∣ m then
        (e : K) * ∑ i ∈ s, (i.negOnePow : ℤ) • trace K (W i) (F i ^ (m / e)) else 0) *
        (alternatingCharpolyRevProd s F e)⁻¹ := by
  set B : ℤ → K⟦X⟧ := fun i ↦ PowerSeries.mk fun m ↦
    if m ≠ 0 ∧ e ∣ m then (e : K) * trace K (W i) (F i ^ (m / e)) else 0 with hB
  have hP (i : ℤ) : X * derivative (R := K) (((F i).charpolyRev.comp (Polynomial.X ^ e) :
      Polynomial K) : K⟦X⟧) = -B i * (((F i).charpolyRev.comp (Polynomial.X ^ e) :
      Polynomial K) : K⟦X⟧) := by
    rw [← Polynomial.expand_eq_comp_X_pow, coe_expand e he]
    exact X_mul_derivative_expand_charpolyRev (F i) e he
  have hP0 (i : ℤ) : constantCoeff (((F i).charpolyRev.comp (Polynomial.X ^ e) :
      Polynomial K) : K⟦X⟧) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
      Polynomial.eval_pow, Polynomial.eval_X, zero_pow he, eval_charpolyRev]
    exact one_ne_zero
  have hfac : ∀ i ∈ s, X * derivative (R := K) (if Even i then
      (((F i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧) else
      (((F i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧)⁻¹) =
      (-((i.negOnePow : ℤ) • B i)) * (if Even i then
      (((F i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧) else
      (((F i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧)⁻¹) := by
    intro i _
    split_ifs with h
    · rw [Int.negOnePow_even _ h, Units.val_one, one_smul]
      exact hP i
    · rw [Int.negOnePow_odd _ (Int.not_even_iff_odd.1 h), Units.val_neg, Units.val_one,
        neg_smul, one_smul, neg_neg, X_mul_derivative_inv (hP i) (hP0 i), neg_neg]
  have h0 := constantCoeff_alternatingCharpolyRevProd s F he
  rw [alternatingCharpolyRevProd] at h0 ⊢
  rw [X_mul_derivative_inv (PowerSeries.X_mul_derivative_prod s hfac)
    (by rw [h0]; exact one_ne_zero), Finset.sum_neg_distrib, neg_neg]
  congr 1
  ext m
  rw [map_sum, PowerSeries.coeff_mk]
  simp only [hB, coeff_smul, PowerSeries.coeff_mk]
  split_ifs
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_smul_comm]
  · simp


end LinearMap
