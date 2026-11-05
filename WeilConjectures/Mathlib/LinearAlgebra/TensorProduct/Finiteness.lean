/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Expanding tensors along a linearly independent family

Over a field `k`, finitely many tensors `t a ∈ A a ⊗[k] K` can be written simultaneously as
`t a = ∑ q, F a q ⊗ₜ β q` for one linearly independent family `β` of `K`: take for `β` a basis of
the span of the right factors of chosen expansions of the `t a`.

## Main statements

- `TensorProduct.exists_linearIndependent_forall_eq_sum_tmul`: the simultaneous expansion.
-/

@[expose] public section

open TensorProduct

namespace TensorProduct

variable {k K : Type*} [Field k] [AddCommGroup K] [Module k K]

end TensorProduct
