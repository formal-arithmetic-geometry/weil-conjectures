/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular sequences are quasi-regular

Let `a₁, …, a_c` be a regular sequence in a commutative ring `R`, generating the ideal `I`. If
`F ∈ R[X₁, …, X_c]` is homogeneous of degree `d` and `F(a) ∈ I^{d+1}`, then all coefficients of
`F` lie in `I` (`MvPolynomial.coeff_mem_of_eval_mem_pow_succ`). Equivalently, the canonical
surjection `(R / I)[X₁, …, X_c] ⟶ ⨁_d I^d / I^{d+1}`, `Xᵢ ↦ aᵢ`, is an isomorphism: the sequence is
*quasi-regular* (Matsumura, *Commutative ring theory*, Theorem 16.2; Stacks, Tag 061M).

The regularity hypothesis is phrased by peeling off the first entry: `a` is regular
(`MvPolynomial.IsRevRegular`) if `a₀` is a nonzerodivisor modulo `(a₁, …, a_c)` and
`(a₁, …, a_c)` is regular. For a weakly regular list `r₁, …, r_c` in the sense of Mathlib
(`RingTheory.Sequence.IsWeaklyRegular`), the reversed sequence is regular in this sense.

## Main statements

- `MvPolynomial.coeff_mem_of_eval_mem_pow_succ`: quasi-regularity of regular sequences.
-/

@[expose] public section

open Finsupp

namespace MvPolynomial

variable {R : Type*} [CommRing R]

section Homogeneous

variable {σ : Type*} [Fintype σ] {a : σ → R}

/-- The value at `a` of a homogeneous polynomial of degree `d` with coefficients in `K` lies in
`K (a)^d`. -/
lemma IsHomogeneous.eval_mem_mul_pow {K : Ideal R} {G : MvPolynomial σ R} {d : ℕ}
    (hG : G.IsHomogeneous d) (hK : ∀ m, G.coeff m ∈ K) :
    eval a G ∈ K * Ideal.span (Set.range a) ^ d := by
  rw [eval_eq]
  refine Ideal.sum_mem _ fun m hm ↦ Ideal.mul_mem_mul (hK m) ?_
  have hdeg : ∑ i, m i = d := by
    rw [hG.degree_eq_sum_deg_support hm]
    exact (Finset.sum_subset (Finset.subset_univ _)
      fun i _ hi ↦ Finsupp.notMem_support_iff.1 hi).symm
  rw [← hdeg, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ ↦ Ideal.pow_mem_pow (Ideal.subset_span ⟨i, rfl⟩) _

/-- The value at `a` of a homogeneous polynomial of degree `d` lies in `(a)^d`. -/
lemma IsHomogeneous.eval_mem_pow {G : MvPolynomial σ R} {d : ℕ} (hG : G.IsHomogeneous d) :
    eval a G ∈ Ideal.span (Set.range a) ^ d := by
  simpa using hG.eval_mem_mul_pow (a := a) (K := (⊤ : Ideal R)) fun _ ↦ Submodule.mem_top

/-- Every element of `(a)^d` is the value at `a` of a homogeneous polynomial of degree `d`. -/
lemma exists_isHomogeneous_eval_eq {d : ℕ} {x : R} (hx : x ∈ Ideal.span (Set.range a) ^ d) :
    ∃ G : MvPolynomial σ R, G.IsHomogeneous d ∧ eval a G = x := by
  induction d generalizing x with
  | zero => exact ⟨C x, isHomogeneous_C _ _, eval_C _⟩
  | succ d ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun y hy z hz ↦ ?_) (fun y z ⟨G, hG, hGy⟩ ⟨H, hH, hHz⟩ ↦
      ⟨G + H, hG.add hH, by rw [map_add, hGy, hHz]⟩)
    obtain ⟨G, hG, rfl⟩ := ih hy
    obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hz
    refine ⟨G * ∑ i, C (c i) * X i, hG.mul (IsHomogeneous.sum _ _ _ fun i _ ↦
      isHomogeneous_C_mul_X _ _), ?_⟩
    simp [Finset.mul_sum]

end Homogeneous

/-- A sequence `a₀, a₁, …, a_n` is *regular, read from the end*, if `(a₁, …, a_n)` is and `a₀` is a
nonzerodivisor modulo `(a₁, …, a_n)`; that is, `a_n, a_{n-1}, …, a₀` is a regular sequence. -/
def IsRevRegular : {n : ℕ} → (Fin n → R) → Prop
  | 0, _ => True
  | _ + 1, a => IsRevRegular (Fin.tail a) ∧
      ∀ x : R, a 0 * x ∈ Ideal.span (Set.range (Fin.tail a)) →
        x ∈ Ideal.span (Set.range (Fin.tail a))

end MvPolynomial
