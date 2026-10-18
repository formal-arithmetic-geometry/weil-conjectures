/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Order.UpperLower.Basic

/-!
# Ideals of a valuation ring and its value group

Source: Stacks Project, `algebra.tex`, Tags 00IE and 00IH,
`definition-value-group` and `lemma-ideals-valuation-ring`
(blueprint: lem-trf-valuation-ring-ideal-correspondence).

Mathlib's `A.ValueGroup` is the quotient of `K` by multiplication by `Aˣ`, including
zero, with the multiplicative valuation order. Its units discard the zero class.
Thus `Additive (OrderDual A.ValueGroupˣ)` is exactly the Stacks additive value group
`Kˣ/Aˣ`, with `[x] ≤ [y]` precisely when `y/x ∈ A`. In particular its zero is the
class of `1`, not the discarded class of the field element `0`.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

namespace ValuationSubring

/-- The canonical inclusion-preserving correspondence between ideals of a valuation ring
and upward-closed subsets of the nonnegative cone of its additive value group preserves
and reflects primality. The displayed value-set formula specifies the correspondence.

Source: Stacks Project, `algebra.tex`, Tags 00IE and 00IH,
`definition-value-group` and `lemma-ideals-valuation-ring`
(blueprint: lem-trf-valuation-ring-ideal-correspondence).

Proof:
1. Send an ideal `J` to the classes of its nonzero elements. Multiplication by a unit
   of `A` preserves membership in `J`, so this is well defined. Every such class is
   nonnegative. If `[a] ≤ [b]`, then `b/a ∈ A`, so `a ∈ J` implies `b ∈ J`.
2. Send an upward-closed nonnegative set `I` to zero together with the nonzero elements
   of `A` whose classes lie in `I`. Multiplication by `A` preserves this set. For
   addition, totality lets us suppose `b/a ∈ A`; then `a+b = a(1+b/a)` shows
   `[a+b] ≥ [a]` when the sum is nonzero. Zero and zero summands are immediate.
3. These constructions are inverse: each nonnegative class has a representative in
   `A`, and membership is invariant under units. Both maps preserve inclusion, giving
   the order isomorphism. The forward map has exactly the displayed carrier formula.
4. A proper prime ideal contains no units, so its value set excludes the zero class.
   The identity `[ab] = [a]+[b]` proves primality of its value set. Conversely, a prime
   value set gives a proper ring ideal since it excludes `[1]`. If `ab` belongs to
   this ideal, either `ab=0`, when the domain property applies, or primality of the
   value set puts `[a]` or `[b]` in the set. Thus ring primality is equivalent to
   the displayed positive-cone primality condition. -/
theorem exists_ideal_orderEquiv_valueGroup
    {K : Type u} [Field K] (A : ValuationSubring K) :
    ∃ e : Ideal A ≃o
        {I : Set (Additive (OrderDual A.ValueGroupˣ)) // I ⊆ Set.Ici 0 ∧ IsUpperSet I},
      (∀ (J : Ideal A) (x : Kˣ),
        Additive.ofMul (OrderDual.toDual
            (Units.map A.valuation.toMonoidWithZeroHom.toMonoidHom x)) ∈ (e J).1 ↔
          ∃ a : A, a ∈ J ∧ (a : K) = (x : K)) ∧
      (∀ J : Ideal A, J.IsPrime ↔
        0 ∉ (e J).1 ∧
          ∀ γ δ : Additive (OrderDual A.ValueGroupˣ),
            0 ≤ γ → 0 ≤ δ → γ + δ ∈ (e J).1 → γ ∈ (e J).1 ∨ δ ∈ (e J).1) := by
  sorry

end ValuationSubring
