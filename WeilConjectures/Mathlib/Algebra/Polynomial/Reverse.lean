/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Complements on the reversal of a polynomial

## Main results

- `Polynomial.reverse_reverse` — reversal is an involution on polynomials with nonzero constant
  coefficient.
- `Polynomial.reverse_map` — reversal commutes with the coefficient map along an injective ring
  homomorphism.
-/

@[expose] public section

namespace Polynomial

variable {R S : Type*} [Semiring R] [Semiring S]

/-- Reversing twice is the identity on polynomials with vanishing trailing degree, i.e. on
polynomials with nonzero constant coefficient. -/
theorem reverse_reverse {p : R[X]} (hp : p.natTrailingDegree = 0) : p.reverse.reverse = p := by
  have h : p.reverse.natDegree = p.natDegree := by rw [reverse_natDegree, hp, Nat.sub_zero]
  change reflect p.reverse.natDegree p.reverse = p
  rw [h]
  exact reflect_reflect

/-- Reversal commutes with the coefficient map along an injective ring homomorphism. -/
theorem reverse_map {f : R →+* S} (hf : Function.Injective f) (p : R[X]) :
    (p.map f).reverse = p.reverse.map f := by
  simp only [reverse, reflect_map, natDegree_map_eq_of_injective hf]

end Polynomial
