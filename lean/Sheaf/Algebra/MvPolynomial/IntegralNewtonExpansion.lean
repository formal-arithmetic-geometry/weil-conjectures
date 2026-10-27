/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.Binomial
import Sheaf.LinearAlgebra.TriangularChangeOfBasis

/-! # Integral Newton expansion in finitely many variables

Source: Stacks Project, Algebra, Tag 00JX, `definition-numerical-polynomial` and the
following paragraph, with the multivariate extension in the DAG proof
(blueprint: lem-sfb-integral-newton-expansion).

The binomial factors and forward differences are Mathlib's `Ring.choose` and `fwdDiff`.
The auxiliary declarations only assemble the indices, products, sums and iterates
appearing in this statement.
-/

@[expose] public section

namespace MvPolynomial

/-- Multi-indices of weight at most `D`, represented in a finite box. Each coordinate
of such a natural multi-index is at most `D`, so this representation omits none.
Source: Tag 00JX, multivariate extension, bounded expansion indices
(blueprint: lem-sfb-integral-newton-expansion). -/
abbrev NewtonIndex (r D : ℕ) :=
  {b : Fin r → Fin (D + 1) // ∑ i : Fin r, (b i).val ≤ D}

/-- The product binomial polynomial `B_b = ∏ i, binom(X_i,b_i)`.
Mathlib's binomial operation is the falling product divided by the factorial in
this rational algebra, including the empty product at order zero.
Source: Tag 00JX, multivariate extension, binomial products
(blueprint: lem-sfb-integral-newton-expansion). -/
noncomputable def newtonBinomial {r : ℕ} (b : Fin r → ℕ) : MvPolynomial (Fin r) ℚ :=
  ∏ i : Fin r, Ring.choose (X i : MvPolynomial (Fin r) ℚ) (b i)

/-- The finite expansion with coefficients indexed by all multi-indices of weight
at most `D`. The coordinate bounds in `NewtonIndex` just make the finite sum explicit.
Source: Tag 00JX, multivariate extension, bounded binomial expansion
(blueprint: lem-sfb-integral-newton-expansion). -/
noncomputable def newtonExpansion (r D : ℕ) (c : NewtonIndex r D → ℚ) :
    MvPolynomial (Fin r) ℚ :=
  ∑ b : NewtonIndex r D, c b • newtonBinomial (fun i ↦ (b.val i).val)

/-- The iterated coordinate forward difference evaluated at zero. The right fold
applies `Δ_0^b₀ (Δ_1^b₁ (... P ...))`, matching the displayed operator order.
`Pi.single i 1` is the unit displacement in coordinate `i`; the starting function is
polynomial evaluation, so these are precisely the evaluations of the polynomial
coordinate differences. When `r = 0`, the fold is the identity.
Source: Tag 00JX, multivariate extension, forward-difference coefficient formula
(blueprint: lem-sfb-integral-newton-expansion). -/
noncomputable def newtonCoefficient {r : ℕ} (P : MvPolynomial (Fin r) ℚ)
    (b : Fin r → ℕ) : ℚ :=
  ((List.finRange r).foldr
    (fun i f ↦ (fwdDiff (Pi.single i (1 : ℚ)))^[b i] f)
    (fun x : Fin r → ℚ ↦ eval x P)) 0

/-- Existence and uniqueness of the bounded Newton expansion, its difference formula,
and both integral-value implications, together with the integral expansion of every
affine binomial polynomial. The final assertion allows negative `s` and `u_i`.
For `r = 0` the index set is a singleton, every binomial product is `1`, and these
clauses say that a rational constant is integer-valued exactly when it is an integer.
Source: Stacks Project, Algebra, Tag 00JX, `definition-numerical-polynomial` and the
following paragraph; multivariate extension in the DAG proof
(blueprint: lem-sfb-integral-newton-expansion).

Proof:
1. In the span of monomials of total degree at most `D`, order the indices by weight.
   Each binomial product has leading monomial `X^b / ∏ i, b_i!` and only lower-weight
   remaining terms. The triangular change-of-basis theorem
   `lem-weil-pbc-triangular-change-of-basis` gives a basis, hence unique coefficients.
2. Factoring the falling products proves `Δ binom(X,j) = binom(X,j-1)` for positive
   `j`; the difference of the order-zero factor is zero. At zero, only order zero
   has value one; all positive orders have value zero.
3. Coordinate translations commute, so their differences commute and are rational
   linear. Apply the indicated iterated differences to the expansion and evaluate
   at zero. Only the matching binomial product survives, giving its coefficient.
4. Differences preserve integer values on the natural grid because both evaluated
   points stay in that grid. Induction on the number of differences makes every
   coefficient an integer by step 3.
5. The integer falling-factorial divisibility lemma
   `lem-sfb-integer-falling-factorial-divisibility`, given by Mathlib's
   `Ring.descPochhammer_eq_factorial_smul_choose`, says that binomial factors are
   integral at every integer, including negative ones. Products and integer linear
   combinations are therefore integer-valued on the full integer grid.
6. An affine binomial of order `t` has degree at most `t`, and its affine argument
   is integral at each natural tuple even with negative affine coefficients.
   Falling-factorial divisibility and steps 1 and 4 give its integral expansion.
7. With no variables the empty tuple is the only index, its weight is zero and its
   product is one. This gives the constant assertion. Degree zero also gives only
   constants; the zero polynomial has zero coefficients, and order zero gives one.
-/
theorem integral_newton_expansion (r D : ℕ) (P : MvPolynomial (Fin r) ℚ)
    (hP : P.totalDegree ≤ D) :
    (∃! c : NewtonIndex r D → ℚ, P = newtonExpansion r D c) ∧
    (∀ c : NewtonIndex r D → ℚ, P = newtonExpansion r D c →
      (∀ b : NewtonIndex r D,
        c b = newtonCoefficient P (fun i ↦ (b.val i).val)) ∧
      ((∀ n : Fin r → ℕ, ∃ z : ℤ, eval (fun i ↦ (n i : ℚ)) P = (z : ℚ)) →
        ∀ b : NewtonIndex r D, ∃ z : ℤ, c b = (z : ℚ)) ∧
      ((∀ b : NewtonIndex r D, ∃ z : ℤ, c b = (z : ℚ)) →
        ∀ n : Fin r → ℤ, ∃ z : ℤ, eval (fun i ↦ (n i : ℚ)) P = (z : ℚ))) ∧
    (∀ (s : ℤ) (u : Fin r → ℤ) (t : ℕ), ∃ c : NewtonIndex r t → ℤ,
      Ring.choose (C (s : ℚ) + ∑ i : Fin r, C (u i : ℚ) * X i) t =
        newtonExpansion r t (fun b ↦ (c b : ℚ))) := by
  sorry

end MvPolynomial
