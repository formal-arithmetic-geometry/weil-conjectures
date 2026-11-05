/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Equivariant maps out of free actions lift along surjections

Let a group `H` act freely on a type `Y`. An `H`-equivariant map `s : Y → N` lifts along any
surjective `H`-equivariant map `π : M → N`: choose a representative of every orbit of `Y` and a
lift of its image, and extend equivariantly, which is well defined as the action is free.

## Main statements

- `MulAction.exists_equivariant_lift_of_free`.
-/

@[expose] public section

namespace MulAction

end MulAction
