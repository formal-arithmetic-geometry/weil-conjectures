/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Data.NNReal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!
# A real absolute value for a height-one valuation ring

Source: Temkin, Stable modification of relative curves, Section 2.1, printed pp. 6–7,
and the height-one bridge used in Theorem 3.5.5, Step 3
(blueprint: lem-trf-height-one-real-absolute-value).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

open scoped NNReal

namespace ValuationRing

/-- A nonfield valuation subring with no intermediate prime ideal is the unit ball of a
nontrivial nonarchimedean real absolute value. A `Valuation F ℝ≥0` includes multiplicativity,
preservation of zero and one, and the strong triangle inequality; over the field `F`, its
zero fiber is exactly `{0}` by `Valuation.zero_iff`.

Source: Temkin, Stable modification of relative curves, Section 2.1, printed pp. 6–7,
and Theorem 3.5.5, Step 3 (blueprint: lem-trf-height-one-real-absolute-value).

Proof: Form the ordered value group of the valuation ring in its fraction field. Its convex
subgroups correspond, in reverse order, to the prime ideals of the valuation ring. Thus the
two-prime hypothesis leaves only the trivial and whole convex subgroups. This ordered group
is Archimedean: otherwise the subgroup of elements bounded between integral powers of a fixed
positive element would be nontrivial and proper. The Archimedean embedding theorem embeds
its additive version into the additive reals; exponentiating gives an order-preserving
multiplicative embedding into the positive reals. Extend by zero and compose with the
canonical valuation of `F`. This gives the stated real-valued valuation. Order preservation
identifies its closed unit ball with `V` and its open unit ball with the maximal ideal.
Finally, since `V` is not a field, its maximal ideal contains a nonzero element; its value
is strictly between zero and one, proving nontriviality. -/
theorem exists_real_valuation_of_height_one
    (F : Type u) [Field F] (V : Subring F) [ValuationRing V] [IsFractionRing V F]
    (hnotfield : ¬ IsField V)
    (hheight : ∀ p : Ideal V, p.IsPrime → p = ⊥ ∨ p = IsLocalRing.maximalIdeal V) :
    ∃ v : Valuation F ℝ≥0,
      (∀ x : F, x ∈ V ↔ v x ≤ 1) ∧
      (∀ x : V, x ∈ IsLocalRing.maximalIdeal V ↔ v (x : F) < 1) ∧
      ∃ x : F, x ≠ 0 ∧ v x ≠ 1 := by
  sorry

end ValuationRing
