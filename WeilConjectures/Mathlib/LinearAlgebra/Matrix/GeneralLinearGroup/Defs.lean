/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible matrices of size at most one

Invertible matrices indexed by a subsingleton type commute.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

/-- Invertible matrices of size at most one commute. -/
theorem mul_comm_of_subsingleton {n R : Type*} [Fintype n] [DecidableEq n] [Subsingleton n]
    [CommRing R] (g h : GL n R) : g * h = h * g := by
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  obtain rfl := Subsingleton.elim l i
  obtain rfl := Subsingleton.elim j l
  exact mul_comm _ _

end Matrix.GeneralLinearGroup
