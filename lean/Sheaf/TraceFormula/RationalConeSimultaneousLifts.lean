/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Algebra.Order.Field.Rat

/-! # Simultaneous integral lifts in a rational cone

Source: Illusie--Laszlo--Orgogozo, `travaux-de-gabber_arXiv-1207.3648.pdf`,
Expose VIII, 3.1.17 (printed p. 101) and Remark 3.1.29 (printed p. 103);
context only; the argument below is the node's agent-written elementary expansion
(blueprint: lem-trf-rational-cone-simultaneous-lifts).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace PointedCone

/-- A finite family in a rational cone has simultaneous integral lifts, and opposite
cone elements admit lifts summing to zero.

Source: Illusie--Laszlo--Orgogozo, `travaux-de-gabber_arXiv-1207.3648.pdf`,
Expose VIII, 3.1.17 (printed p. 101) and Remark 3.1.29 (printed p. 103);
these places supply saturation and fan context, not this precise assertion. The
finite numerator--denominator argument is the node's agent-written five-step proof.
(blueprint: lem-trf-rational-cone-simultaneous-lifts)

Proof:
1. For each member of a finite family choose a finite expression in the defining
   rational cone, write every nonnegative rational coefficient as a numerator over
   a positive denominator, and collect the finitely many denominators.
2. Set N to the product of all positive denominators d, with empty product 1.
   For a coefficient u/d, let D be the product of the other denominators. Then
   N = d*D and N*(u/d) = u*D is a nonnegative integer, simultaneously for all terms.
3. Replace each finite expression by the corresponding repeated-addition sum in `P`.
   Closure of `P` under addition and the assumption `0 ∈ P` put each sum in `P`, and
   additivity of `i` gives the simultaneous lift identities. The empty family and
   empty expressions use the empty sum and `N = 1`.
4. Applying the lift assertion to the singleton family `i g` and using injectivity
   proves `i g ∈ C ↔ ∃ n ≥ 1, n • g ∈ P`; the reverse implication is the one-term
   expression with coefficient `1/n`.
5. Apply the lift assertion to the two-element family `(x, -x)`. Injectivity applied
   to i(a+b) = Nx + N(-x) = 0 = i(0) gives `a + b = 0`.
-/
theorem simultaneous_integral_lifts
    {G : Type u} [AddCommGroup G]
    {V : Type v} [AddCommGroup V] [Module ℚ V]
    (i : G →+ V) (hi : Function.Injective i) (P : Set G)
    (h0 : (0 : G) ∈ P)
    (hadd : ∀ {a b : G}, a ∈ P → b ∈ P → a + b ∈ P) :
    (∀ (T : Type w) [Fintype T] (x : T → V),
      (∀ t, x t ∈ hull ℚ (i '' P)) →
        ∃ N : ℕ, 1 ≤ N ∧ (IsEmpty T → N = 1) ∧ ∃ a : T → G,
          ∀ t, a t ∈ P ∧ i (a t) = (N : ℚ) • x t) ∧
      (∀ g : G, i g ∈ hull ℚ (i '' P) ↔
        ∃ n : ℕ, 1 ≤ n ∧ n • g ∈ P) ∧
      (∀ x : V, x ∈ hull ℚ (i '' P) → -x ∈ hull ℚ (i '' P) →
        ∃ N : ℕ, 1 ≤ N ∧ ∃ a b : G,
          a ∈ P ∧ b ∈ P ∧ i a = (N : ℚ) • x ∧
            i b = (N : ℚ) • (-x) ∧ a + b = 0) := by
  sorry

end PointedCone
