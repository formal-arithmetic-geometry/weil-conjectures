/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# Simple extensions and `p`-th powers

Auxiliary facts on simple field extensions in characteristic `p`:

- `IntermediateField.exists_mul_aeval_eq_aeval_of_mem_adjoin_simple`: an element of `k⟮x⟯` times a
  nonzero polynomial in `x` is a polynomial in `x`.
- `IntermediateField.pow_ne_of_mem_adjoin_simple`: if `x` is transcendental over `k`, then `x` is
  not a `p`-th power in `k⟮x⟯` for `p > 1`.
- `IsSeparable.mem_bot_of_pow_mem`: a separable element whose `q`-th power lies in the base field
  lies in the base field.
- `minpoly_eq_X_pow_sub_C_of_notMem_bot`: if `z ^ p = a` lies in the base field but `z` does not,
  then the minimal polynomial of `z` is `X ^ p - a`.
-/

@[expose] public section

open Polynomial IntermediateField

variable {k Q : Type*} [Field k] [Field Q] [Algebra k Q]

namespace IntermediateField

end IntermediateField

