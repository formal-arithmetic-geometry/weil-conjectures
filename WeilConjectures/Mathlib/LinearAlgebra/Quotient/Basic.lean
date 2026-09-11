/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Composing a map out of a quotient module with a linear map

We record that postcomposing `Submodule.liftQ` with a linear map is again a `Submodule.liftQ`,
through the map `Submodule.factor` between the quotients.
-/

@[expose] public section

namespace Submodule

variable {R M N N' : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N'] {p p' : Submodule R M}

/-- Postcomposing `Submodule.liftQ` with a linear map `k` is the `Submodule.liftQ` of the
composite, read through `Submodule.factor`. -/
theorem comp_liftQ (hpp' : p ≤ p') {L : M →ₗ[R] N} (hL : p ≤ LinearMap.ker L) (k : N →ₗ[R] N')
    {L' : M →ₗ[R] N'} (hL' : p' ≤ LinearMap.ker L') (hk : k.comp L = L') :
    k.comp (p.liftQ L hL) = (p'.liftQ L' hL').comp (factor hpp') := by
  ext y
  simpa using congr($hk y)

end Submodule
