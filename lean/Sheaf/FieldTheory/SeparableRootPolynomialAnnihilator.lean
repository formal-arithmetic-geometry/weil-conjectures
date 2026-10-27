/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.Separable

/-!
# Polynomial annihilators from a separable root

Source: Stacks Project, Tag 0C2X, lemma-separable-algebraic-diagonal,
finite primitive-element calculation and general algebraic-union paragraph
(blueprint: lem-trf-separable-root-polynomial-annihilator).

`Polynomial.rootDividedDifference` is the explicit finite coefficient sum in the node.
`Polynomial.separable_root_polynomial_annihilator` states its factorization, derivative,
and annihilation identities, allowing the zero target ring.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Polynomial

/-- The coefficient formula for the divided difference at `α`:
sum over coefficients `c_j` of `c_j * ∑ h < j, X^(j-1-h) * α^h`.
The outer sum uses the finite coefficient support; the `j = 0` inner sum is empty.
Source: Stacks Project, Tag 0C2X, complementary-factor calculation, expanded coefficientwise
(blueprint: lem-trf-separable-root-polynomial-annihilator). -/
noncomputable def rootDividedDifference {L : Type u} [Field L] (G : L[X]) (α : L) : L[X] :=
  G.sum fun j c ↦ C c * ∑ h ∈ Finset.range j, X ^ (j - 1 - h) * C (α ^ h)

/-- The explicit divided differences factor every polynomial after subtracting its value,
evaluate to its derivative, and give annihilators at roots of a separable polynomial.
Source: Stacks Project, Tag 0C2X, lemma-separable-algebraic-diagonal, finite
primitive-element calculation and general algebraic-union paragraph
(blueprint: lem-trf-separable-root-polynomial-annihilator).

Proof:
1. For each `j ≥ 1`, multiply the inner sum by `X - C α`. Consecutive terms cancel,
   leaving `X^j - C (α^j)`. Sum with the coefficients of `G`; the constant term
   contributes zero. This proves the polynomial identity, using the coefficient
   convolution multiplication of def-weil-polynomial-ring.
2. Evaluate the inner sum at `α`. Each of its `j` terms is `α^(j-1)`, so the sum
   is `j * α^(j-1)`. Summing gives the formal derivative formula of
   def-pc-separable-polynomial. This works in every characteristic, including `α = 0`.
3. Apply these identities to `P` and use `P(α) = 0`. Separability gives polynomials
   `U,V` with `U*P + V*P.derivative = 1`. Evaluation at `α` yields
   `V(α)*P.derivative(α) = 1`, so the derivative is nonzero since `L` is a field
   (def-pc-separable-polynomial and def-weil-field).
4. Apply the factorization to `F`. Evaluation via the unital map `ι` preserves
   multiplication by the convolution formula of def-weil-polynomial-ring.
   Commutativity in `R` therefore gives
   `Q(t)*F(t) = Q(t)*(t-ι(α))*H(t) = P(t)*H(t) = 0`.
   If `F = 0`, its coefficient sum gives `H = 0`. Neither cancellation nor
   nontriviality of `R` is used. -/
theorem separable_root_polynomial_annihilator
    (L : Type u) [Field L] (R : Type v) [CommRing R]
    (ι : L →+* R) (α : L) (P : L[X]) (hP : P.eval α = 0) (hsep : P.Separable) :
    (∀ G : L[X],
      G - C (G.eval α) = (X - C α) * rootDividedDifference G α ∧
        (rootDividedDifference G α).eval α = G.derivative.eval α) ∧
    P = (X - C α) * rootDividedDifference P α ∧
    (rootDividedDifference P α).eval α = P.derivative.eval α ∧
    P.derivative.eval α ≠ 0 ∧
    ∀ (t : R), P.eval₂ ι t = 0 → ∀ (F : L[X]), F.eval α = 0 →
      F = (X - C α) * rootDividedDifference F α ∧
      (rootDividedDifference P α).eval₂ ι t * F.eval₂ ι t =
        P.eval₂ ι t * (rootDividedDifference F α).eval₂ ι t ∧
      P.eval₂ ι t * (rootDividedDifference F α).eval₂ ι t = 0 := by
  sorry

end Polynomial
