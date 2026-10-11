/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EulerProduct

/-!
# The zeta function counts effective zero-cycles

The `n`-th coefficient of an Euler product `∏ᵢ (1 - T^{dᵢ})⁻¹` with all `dᵢ ≥ 1` is the number
of finitely supported families `(mᵢ)` of natural numbers with `∑ mᵢ dᵢ = n`. For the zeta
function of a scheme of finite type over a finite field this says that `Z_n` is the number of
effective zero-cycles of degree `n`.

## Main statements

- `PowerSeries.coeff_tprod_inv_one_sub_X_pow_eq_natCard`: the coefficients of an Euler product.
-/

@[expose] public section

open scoped PowerSeries.WithPiTopology

namespace PowerSeries

variable {ι : Type*} {d : ι → ℕ}

/-- **Coefficients of an Euler product.** If `dᵢ ≥ 1` for all `i` and only finitely many `dᵢ`
are at most any given bound, the `n`-th coefficient of `∏ᵢ (1 - T^{dᵢ})⁻¹` is the number of
finitely supported `m : ι →₀ ℕ` with `∑ᵢ mᵢ dᵢ = n`. -/
theorem coeff_tprod_inv_one_sub_X_pow_eq_natCard (hd : ∀ i, d i ≠ 0)
    (hfin : ∀ n, {i | d i ≤ n}.Finite) (n : ℕ) :
    coeff n (∏' i, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) =
      Nat.card {m : ι →₀ ℕ // (m.sum fun i k ↦ k * d i) = n} := by
  classical
  set T : Finset ι := (hfin n).toFinset with hT_def
  have hT : ∀ i, d i ≤ n → i ∈ T := fun i hi ↦ by simpa [hT_def] using hi
  rw [coeff_tprod_inv_one_sub_X_pow hd hfin n hT, coeff_prod]
  simp only [inv_one_sub_X_pow_eq_mk (hd _), coeff_mk]
  rw [Finset.sum_congr rfl fun l _ ↦ Finset.prod_boole, Finset.sum_boole]
  congr 1
  -- the families `m` correspond to the `l = m d` in the antidiagonal divisible by `d`
  -- the support of an admissible `m` lies in `T`
  have hsupp (m : ι →₀ ℕ) (hm : (m.sum fun i k ↦ k * d i) = n) : m.support ⊆ T := by
    intro i hi
    refine hT i ?_
    have hle : m i * d i ≤ m.sum fun i k ↦ k * d i :=
      Finset.single_le_sum (f := fun i ↦ m i * d i) (fun _ _ ↦ Nat.zero_le _) hi
    have : 1 ≤ m i := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi)
    nlinarith
  let toL (m : ι →₀ ℕ) : ι →₀ ℕ :=
    Finsupp.ofSupportFinite (fun i ↦ m i * d i) (m.finite_support.subset fun i hi ↦ by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hi
      exact hi.1)
  let toM (l : ι →₀ ℕ) : ι →₀ ℕ :=
    Finsupp.ofSupportFinite (fun i ↦ l i / d i) (l.finite_support.subset fun i hi ↦ by
      simp only [Function.mem_support, ne_eq] at hi ⊢
      intro h
      exact hi (by rw [h, Nat.zero_div]))
  have htoL (m : ι →₀ ℕ) (i : ι) : toL m i = m i * d i := rfl
  have htoM (l : ι →₀ ℕ) (i : ι) : toM l i = l i / d i := rfl
  have hsumT (m : ι →₀ ℕ) (hm : m.support ⊆ T) :
      (m.sum fun i k ↦ k * d i) = ∑ i ∈ T, toL m i := by
    rw [Finsupp.sum, Finset.sum_subset hm fun i _ hi ↦ by
      rw [Finsupp.notMem_support_iff.1 hi, zero_mul]]
    rfl
  refine (Nat.card_eq_finsetCard _).symm.trans (Nat.card_congr ?_)
  exact
    { toFun l := ⟨toM l.1, by
        obtain ⟨hl, hdvd⟩ := Finset.mem_filter.1 l.2
        rw [Finset.mem_finsuppAntidiag] at hl
        have hlm : toL (toM l.1) = l.1 := by
          ext i
          rw [htoL, htoM]
          by_cases hi : i ∈ T
          · exact Nat.div_mul_cancel (hdvd i hi)
          · rw [Finsupp.notMem_support_iff.1 fun h ↦ hi (hl.2 h), Nat.zero_div, zero_mul]
        have hsub : (toM l.1).support ⊆ T := fun i hi ↦ by
          by_contra hiT
          apply Finsupp.mem_support_iff.1 hi
          rw [htoM, Finsupp.notMem_support_iff.1 fun h ↦ hiT (hl.2 h), Nat.zero_div]
        rw [hsumT _ hsub, hlm, hl.1]⟩
      invFun m := ⟨toL m.1, by
        have hsub := hsupp m.1 m.2
        refine Finset.mem_filter.2 ⟨Finset.mem_finsuppAntidiag.2 ⟨?_, fun i hi ↦ ?_⟩,
          fun i _ ↦ ⟨m.1 i, by rw [htoL, mul_comm]⟩⟩
        · rw [← hsumT _ hsub, m.2]
        · refine hsub (Finsupp.mem_support_iff.2 fun h ↦ ?_)
          apply Finsupp.mem_support_iff.1 hi
          rw [htoL, h, zero_mul]⟩
      left_inv l := by
        obtain ⟨hl, hdvd⟩ := Finset.mem_filter.1 l.2
        rw [Finset.mem_finsuppAntidiag] at hl
        refine Subtype.ext (Finsupp.ext fun i ↦ ?_)
        change toL (toM l.1) i = l.1 i
        rw [htoL, htoM]
        by_cases hi : i ∈ T
        · exact Nat.div_mul_cancel (hdvd i hi)
        · rw [Finsupp.notMem_support_iff.1 fun h ↦ hi (hl.2 h), Nat.zero_div, zero_mul]
      right_inv m := by
        refine Subtype.ext (Finsupp.ext fun i ↦ ?_)
        change toM (toL m.1) i = m.1 i
        rw [htoM, htoL, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (hd i))] }

end PowerSeries
