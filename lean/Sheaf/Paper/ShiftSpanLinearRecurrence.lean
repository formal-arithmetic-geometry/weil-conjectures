/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import WeilConjectures.ZetaLinearAlgebra.ShiftSpan
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# A bounded linear recurrence from a finite-dimensional shift span

Source: the Weil conjectures blueprint, `sec-zeta-weil/sk-prop-criterion`, proof of
`prop-weil-rationality-criterion`, second paragraph
(blueprint: lem-weil-shift-span-linear-recurrence).
-/

@[expose] public section

universe u

/-- A sequence over a field with finite-dimensional shift span has a linear recurrence
from index zero, of positive order at most the maximum of the shift-span dimension and one.
The first equality is the relation among shifted sequences; `IsSolution` records its
coordinatewise form, with negated coefficients to match Mathlib's recurrence convention.

Source: the Weil conjectures blueprint, `sec-zeta-weil/sk-prop-criterion`, proof of
`prop-weil-rationality-criterion`, second paragraph
(blueprint: lem-weil-shift-span-linear-recurrence).

Proof plan: write `D` for the dimension. If `D = 0`, every shift is zero, so take `d = 1`
and `a₀ = 0`. Otherwise some shift is nonzero, hence the original sequence is nonzero.
The `D + 1` initial shifts are dependent by the independent-family dimension bound
(`lem-weil-independent-family-card-le-dimension`). Choose the least dependent index
`d ≥ 1`; then `d ≤ D` and the preceding `d` shifts are independent (for `d = 1`, use
that the original sequence is nonzero). A nontrivial dependence has nonzero coefficient
on the last shift, since otherwise it contradicts that independence. Divide by this
coefficient to obtain the displayed relation. Evaluating at each coordinate gives the
recurrence from index zero (`def-weil-eventual-linear-recurrence`). -/
theorem exists_linearRecurrence_of_finiteDimensional_shiftSpan
    {K : Type u} [Field K] (c : ℕ → K) [FiniteDimensional K (shiftSpan K c)] :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ max (Module.finrank K (shiftSpan K c)) 1 ∧
      ∃ a : Fin d → K,
        (fun s : ℕ ↦ c (d + s)) +
          (∑ i : Fin d, a i • (fun s : ℕ ↦ c ((i : ℕ) + s))) = 0 ∧
        (LinearRecurrence.mk d (fun i ↦ -a i)).IsSolution c := by
  sorry
