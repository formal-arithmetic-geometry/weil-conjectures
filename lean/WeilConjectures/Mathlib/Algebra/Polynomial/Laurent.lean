/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Complements on Laurent polynomials

## Main results

- `LaurentPolynomial.coeff_toLaurent_natCast`, `LaurentPolynomial.coeff_toLaurent_of_neg`: the
  coefficients of the Laurent polynomial attached to a polynomial.
- `LaurentPolynomial.coeff_T_mul`: multiplication by `T d` shifts the coefficients by `d`.
-/

@[expose] public section

open Polynomial

namespace LaurentPolynomial

variable {R : Type*} [Semiring R]

@[simp]
lemma coeff_toLaurent_natCast (p : R[X]) (j : ℕ) : (toLaurent p).coeff j = p.coeff j := by
  rw [coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ j

lemma coeff_toLaurent_of_neg (p : R[X]) {j : ℤ} (hj : j < 0) : (toLaurent p).coeff j = 0 := by
  rw [coeff_toLaurent]
  exact Finsupp.mapDomain_of_notMem_range _ _ fun ⟨i, hi⟩ ↦ by
    simp only [Nat.castEmbedding_apply] at hi
    omega

@[simp]
lemma coeff_T_mul (d j : ℤ) (f : R[T;T⁻¹]) : (T d * f).coeff j = f.coeff (j - d) := by
  rw [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, neg_add_eq_sub]

end LaurentPolynomial
