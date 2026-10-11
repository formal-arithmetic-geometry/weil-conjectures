/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Roots of polynomials with p-th-power coefficients

Source: Stacks Project, Fields, Lemma Tag 031V, part (2)
(blueprint: lem-weil-pbc-separable-root-pth-power).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Polynomial

/-- A root in a separable algebraic extension of a nonzero polynomial with distinct roots
and p-th-power coefficients is itself a p-th power.
Source: Stacks Project, Fields, Tag 031V (2)
(blueprint: lem-weil-pbc-separable-root-pth-power).

Proof:
1. The absence of repeated roots makes P coprime to its derivative: a nonconstant common
   divisor would have a root in AlgebraicClosure E and give a repeated root of P.
2. A Bezout identity transports this absence of repeated roots to an algebraic closure
   of L (def-weil-algebraic-closure, def-pc-separable-polynomial).
3. Choose p-th roots of the coefficients to form Q. Coefficientwise Frobenius maps Q to P
   and satisfies Q(gamma)^p = P(gamma^p) (def-weil-ring-frobenius).
4. A repeated root of Q would, under Frobenius, give a repeated root of P.
5. In the closure of L choose gamma with gamma^p = alpha. Then Q(gamma) = 0 and
   X^p - alpha = (X - gamma)^p.
6. If alpha were not a p-th power in L, lem-weil-pbc-x-pow-p-minus-t-irreducible makes
   X^p - alpha irreducible. Its common root with Q forces it to divide Q, giving a
   repeated root since p is at least two, a contradiction. -/
theorem exists_pow_eq_of_distinct_roots_coeff_pow
    {E : Type u} {L : Type v} [Field E] [Field L] [Algebra E L]
    (p : ℕ) [Fact p.Prime] [CharP E p] [Algebra.IsSeparable E L]
    (α : L) (P : E[X]) (hroot : aeval α P = 0) (hne : P ≠ 0)
    (hdistinct : ∀ ρ : AlgebraicClosure E,
      ¬ (X - C ρ) ^ 2 ∣ P.map (algebraMap E (AlgebraicClosure E)))
    (hcoeff : ∀ n : ℕ, ∃ b : E, P.coeff n = b ^ p) :
    ∃ α' : L, α = α' ^ p := by
  sorry

end Polynomial
