/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Complements on subrings

* `Subring.inv_mem_of_isUnit`: if an element of a subring of a division ring is a unit of
  that subring, then its inverse in the ambient ring already lies in the subring.
-/

@[expose] public section

namespace Subring

variable {K : Type*} [DivisionRing K] (S : Subring K)

/-- The inverse of an element of a subring of a division ring which is a unit of the
subring belongs to the subring. -/
theorem inv_mem_of_isUnit {x : K} (hx : x ∈ S) (hu : IsUnit (⟨x, hx⟩ : S)) : x⁻¹ ∈ S := by
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
  have hxy : x * (y : K) = 1 := congrArg Subtype.val hy
  rw [inv_eq_of_mul_eq_one_right hxy]
  exact y.2

end Subring
