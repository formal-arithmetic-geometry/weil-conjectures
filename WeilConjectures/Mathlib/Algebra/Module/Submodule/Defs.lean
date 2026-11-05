/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# Subsets underlying submodules

## Main statements

- `Submodule.exists_coe_eq_iff`: a subset of a module is the carrier of a submodule if and only
  if it contains `0` and is closed under addition and scalar multiplication.
-/

@[expose] public section

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

end Submodule
