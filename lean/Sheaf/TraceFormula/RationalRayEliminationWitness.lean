/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Bounds.Defs

/-!
# A rational witness for one-variable signed inequalities

Source: the agent-written auxiliary assertion extracted from
`lem-trf-rational-cone-dual-finite`, old proof steps 5--6. ILO, Travaux de Gabber,
Exposé VIII, Remark 3.1.29, printed p. 103, provides toric context only.
(blueprint: lem-trf-rational-ray-elimination-witness)
-/

@[expose] public section

universe u

namespace Weil

/-- The greatest of zero and the negative-slope ratios solves the signed rational inequalities.
Source: the agent-written auxiliary assertion extracted from
`lem-trf-rational-cone-dual-finite`, old proof steps 5--6; ILO, Travaux de Gabber,
Exposé VIII, Remark 3.1.29, printed p. 103, supplies context only.
(blueprint: lem-trf-rational-ray-elimination-witness)

Proof:
1. Enumerate the negative indices, allowing the empty list. Start at zero and successively
   take the maximum with each ratio. Induction shows that the result belongs to the finite
   set consisting of zero and these ratios and bounds all its members above. This constructs
   its greatest member T, which is nonnegative and bounds each negative-slope ratio.
2. For positive i and negative j, the difference b i / a i - b j / a j equals
   (a i * b j - a j * b i) / (a i * (-a j)). Its numerator is nonnegative by the
   mixed hypothesis and its denominator is positive. Also b i / a i is nonnegative.
3. Consequently every member of the finite set is at most each positive-slope ratio.
   Since T belongs to the set, T satisfies all these upper bounds. This is vacuous if
   there are no positive indices; no positive index is chosen globally.
4. For positive slopes multiply the upper bound by the positive slope; for negative
   slopes multiply the lower bound by the negative slope, reversing its inequality.
   At zero slopes the residual is the assumed nonnegative constant. Thus every residual
   is nonnegative. If there are no negative indices the set is the singleton zero,
   so its greatest member is zero. This includes the empty index type.
-/
theorem rationalRayEliminationWitness {I : Type u} [Finite I] (a b : I → ℚ)
    (hzero : ∀ h : I, a h = 0 → 0 ≤ b h)
    (hpos : ∀ i : I, 0 < a i → 0 ≤ b i)
    (hmixed : ∀ i j : I, 0 < a i → a j < 0 → 0 ≤ a i * b j - a j * b i) :
    (insert 0 ((fun j : I ↦ b j / a j) '' {j : I | a j < 0})).Finite ∧
    (insert 0 ((fun j : I ↦ b j / a j) '' {j : I | a j < 0})).Nonempty ∧
    ∃ T : ℚ,
      IsGreatest (insert 0 ((fun j : I ↦ b j / a j) '' {j : I | a j < 0})) T ∧
      0 ≤ T ∧
      (∀ j : I, a j < 0 → b j / a j ≤ T) ∧
      (∀ i : I, 0 < a i → T ≤ b i / a i) ∧
      (∀ i : I, 0 ≤ b i - T * a i) ∧
      ({j : I | a j < 0} = ∅ → T = 0) := by
  sorry

end Weil
