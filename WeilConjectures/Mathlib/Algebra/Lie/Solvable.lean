/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Solvable

/-!
# Solvability from the derived algebra

A Lie algebra whose derived algebra `⁅L, L⁆` is solvable is itself solvable.
-/

@[expose] public section

namespace LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A Lie algebra whose derived algebra `⁅L, L⁆` is solvable is solvable. -/
theorem isSolvable_of_isSolvable_derivedSeries_one [IsSolvable (derivedSeries R L 1)] :
    IsSolvable L := by
  obtain ⟨n, hn⟩ := IsSolvable.solvable R (derivedSeries R L 1)
  rw [LieIdeal.derivedSeries_eq_bot_iff, derivedSeries_def, ← derivedSeriesOfIdeal_add] at hn
  exact IsSolvable.mk (R := R) (k := n + 1) (by rwa [derivedSeries_def])

end LieAlgebra
