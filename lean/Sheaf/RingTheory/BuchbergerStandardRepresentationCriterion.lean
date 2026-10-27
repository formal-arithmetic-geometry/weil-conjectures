/-
Copyright (c) 2026 The Weil conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil conjectures contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.Ideal.Span

/-!
# Buchberger's criterion from strict standard representations

Source: Yankı Lekili, Commutative Algebra, Lecture 7, Theorem 4.11 and Lemma 4.12;
the DAG supplies the arbitrary-family, strict-standard-representation formulation
(blueprint: lem-sfb-buchberger-standard-representation-criterion).

The coefficients of each representation are finitely supported even when the generating
set is infinite. For monic inputs, `MonomialOrder.sPolynomial_def` identifies Mathlib's
S-polynomial with the difference of the two monomial multiples specified in the source.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MonomialOrder

/-- Buchberger's criterion for an arbitrary set of nonzero monic polynomials, assuming
strict standard representations of all its S-polynomials.

Source: Yankı Lekili, Commutative Algebra, Lecture 7, Theorem 4.11 (converse), using
Lemma 4.12; the DAG supplies the finite-support adaptation to arbitrary generating sets
(blueprint: lem-sfb-buchberger-standard-representation-criterion).

Proof plan:
1. Finite polynomial combinations of members of `B` form exactly `Ideal.span B`.
   Expand their coefficients into monomials, obtaining a finite expression for a nonzero
   `f` as a sum of nonzero scalar-monomial multiples of generators. If `B` is empty,
   its ideal is zero, so there is no such `f`.
2. For each expression, take the largest leading exponent of its summands. Choose an
   expression with least such maximum `δ`, using the well-order. A summand indexed by
   `i` has leading exponent `αᵢ + m.degree bᵢ` and leading coefficient `cᵢ`, by monicity.
3. If `m.degree f = δ`, any summand attaining `δ` supplies the desired coordinatewise
   divisibility. Otherwise `m.degree f` is strictly below `δ`, and the coefficients of
   the summands attaining `δ` sum to zero. Let `T` be their finite index set and fix `j ∈ T`.
4. Put `λᵢ = m.degree bᵢ ⊔ m.degree bⱼ`. Both leading exponents are coordinatewise at
   most `δ`, so `λᵢ ≤ δ`. Direct expansion gives
   `x^(δ-λᵢ) P(bᵢ,bⱼ) = x^αᵢ bᵢ - x^αⱼ bⱼ`.
   Hence the sum of the top summands equals
   `∑ i ∈ T \ {j}, cᵢ x^(δ-λᵢ) P(bᵢ,bⱼ)`, since their scalar coefficients sum to zero.
5. Substitute the assumed finitely supported representations of these S-polynomials.
   By `MonomialOrder.degree_mul` and `MonomialOrder.leadingCoeff_mul`
   (blueprint: lem-sfb-monomial-order-leading-product), each monomial `β` in a nonzero
   coefficient satisfies `β + m.degree u ≺ λᵢ`. Translating by `δ - λᵢ` preserves
   strict order and gives `δ - λᵢ + β + m.degree u ≺ δ`.
6. Expand the substituted coefficients into monomials and discard zero scalar terms.
   Together with the unchanged summands outside `T`, this gives a finite expression
   for `f` whose largest leading exponent is strictly below `δ`. Its index set is
   nonempty since `f ≠ 0`, contradicting minimality. Thus step 3 gives the conclusion.
-/
theorem buchberger_standard_representation_criterion
    {k : Type u} [Field k] {r : ℕ} (hr : 1 ≤ r) (m : MonomialOrder (Fin r))
    (B : Set (MvPolynomial (Fin r) k))
    (hB : ∀ b ∈ B, b ≠ 0 ∧ m.Monic b)
    (hS : ∀ b ∈ B, ∀ c ∈ B,
      ∃ q : B →₀ MvPolynomial (Fin r) k,
        m.sPolynomial b c = q.sum (fun u a ↦ a * (u : MvPolynomial (Fin r) k)) ∧
        ∀ u : B, q u * (u : MvPolynomial (Fin r) k) ≠ 0 →
          m.toSyn (m.degree (q u * (u : MvPolynomial (Fin r) k))) <
            m.toSyn (m.degree b ⊔ m.degree c))
    (f : MvPolynomial (Fin r) k) (hf : f ∈ Ideal.span B) (hf0 : f ≠ 0) :
    ∃ b ∈ B, ∀ a : Fin r, m.degree b a ≤ m.degree f a := by
  sorry

end MonomialOrder
