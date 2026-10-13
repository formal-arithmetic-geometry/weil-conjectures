/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable

/-!
# Reduced quotient by a separable polynomial

Source: Stacks Project, Algebra, proof of Lemma Tag 030U, first paragraph,
line 10182 (blueprint: lem-weil-pbc-separable-polynomial-quotient-reduced).
-/

@[expose] public section

universe u

open Polynomial

namespace Polynomial

/-- If `Q` is separable over a field, every power divisible by `Q` is already
  divisible by `Q`; equivalently, the quotient by `(Q)` is reduced.
Source: Stacks Project, Algebra, proof of Lemma Tag 030U, first paragraph,
line 10182 (blueprint: lem-weil-pbc-separable-polynomial-quotient-reduced).

Proof (to be supplied):
1. The Bezout identity for `Q` and `Q.derivative` from
   `def-pc-separable-polynomial` implies that `Q` is squarefree. If `H ^ 2`
   divides `Q`, write `Q = H ^ 2 * W`. The derivative product rule gives
   `Q.derivative = 2 * H * H.derivative * W + H ^ 2 * W.derivative`.
   Thus `H` divides both `Q` and its derivative, and hence their Bezout
   combination `1`; therefore `H` is a unit. This is the square-divisor
   condition in `lem-weil-pbc-squarefree-polynomial-divides-power`.
   Nonzero constants satisfy this condition; `Q = 0` is excluded by Bezout.
2. For `m ≥ 1`, membership of `g ^ m` in the principal ideal means
   `Q ∣ g ^ m`. Apply `lem-weil-pbc-squarefree-polynomial-divides-power`
   (`Squarefree.dvd_pow_iff_dvd`) to deduce `Q ∣ g`, equivalently membership
   of `g` in the ideal. A nilpotent quotient class represented by `g` has
   some positive power zero, so this implication makes its representative
   lie in the ideal and its class zero. Hence the quotient is reduced.
-/
theorem isReduced_quotient_of_separable
    (E : Type u) [Field E] (Q : E[X]) (hQ : Q.Separable) :
    ∀ (g : E[X]) (m : ℕ), 1 ≤ m →
      g ^ m ∈ Ideal.span ({Q} : Set E[X]) →
        g ∈ Ideal.span ({Q} : Set E[X]) := by
  sorry

end Polynomial
