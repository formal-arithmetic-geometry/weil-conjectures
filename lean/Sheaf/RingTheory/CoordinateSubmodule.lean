/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-!
# Coordinate submodules of direct sums

Source: Stacks Project, Algebra, Tag 058X, theorem-kaplansky-direct-sum,
proof lines 20511–20552 (blueprint: def-trf-coordinate-submodule).
-/

@[expose] public section

universe u v w

open DirectSum

namespace DirectSum

set_option autoImplicit false in
/-- The submodule of a direct sum whose coordinates outside `A` vanish.

Source: Stacks Project, Algebra, Tag 058X, theorem-kaplansky-direct-sum,
proof lines 20511–20552 (blueprint: def-trf-coordinate-submodule).
-/
noncomputable def coordinateSubmodule
    (R : Type u) [CommRing R] (J : Type v) (N : J → Type w)
    [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)] (A : Set J) :
    Submodule R (⨁ j, N j) := by
  classical
  exact
    { carrier := {x | ∀ j, j ∉ A → x j = 0}
      zero_mem' := by
        intro j hj
        simp
      add_mem' := by
        intro x y hx hy j hj
        rw [DirectSum.add_apply, hx j hj, hy j hj, add_zero]
      smul_mem' := by
        intro r x hx j hj
        rw [DirectSum.smul_apply, hx j hj, smul_zero] }

end DirectSum
