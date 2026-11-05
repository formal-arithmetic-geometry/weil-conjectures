/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# The decomposition group normalises the inertia group
-/

@[expose] public section

open scoped Pointwise

namespace Ideal

variable {M R : Type*} [Group M] [Ring R] [MulSemiringAction M R] {P : Ideal R}

end Ideal
