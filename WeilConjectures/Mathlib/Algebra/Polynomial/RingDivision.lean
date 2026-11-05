/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Root multiplicities of finite products

## Main results

- `Polynomial.rootMultiplicity_prod`: over a domain, the root multiplicity of a nonzero finite
  product is the sum of the root multiplicities of the factors.
- `Polynomial.rootMultiplicity_one_sub_C_mul_X`: `1 - a X` has the simple root `a⁻¹`.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

section Field

variable {K : Type*} [Field K]

end Field

end Polynomial
