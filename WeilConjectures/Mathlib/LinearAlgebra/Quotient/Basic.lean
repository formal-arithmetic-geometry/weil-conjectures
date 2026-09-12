/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Composing a map out of a quotient module with a linear map

We record two compatibilities of `Submodule.liftQ` with composition: postcomposing
`Submodule.liftQ` with a linear map is again a `Submodule.liftQ`, and precomposing it with
`Submodule.factor` is the `Submodule.liftQ` over the smaller submodule.
-/

@[expose] public section

namespace Submodule

variable {R R₂ R₃ M M₂ M₃ : Type*} [Ring R] [Ring R₂] [Ring R₃] [AddCommGroup M] [Module R M]
  [AddCommGroup M₂] [Module R₂ M₂] [AddCommGroup M₃] [Module R₃ M₃] {τ₁₂ : R →+* R₂}
  {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃} [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃] {p p' : Submodule R M}

/-- Postcomposing `Submodule.liftQ` with a linear map is the `Submodule.liftQ` of the
composite. -/
theorem comp_liftQ (L : M →ₛₗ[τ₁₂] M₂) (hL : p ≤ LinearMap.ker L) (k : M₂ →ₛₗ[τ₂₃] M₃) :
    k.comp (p.liftQ L hL) =
      p.liftQ (k.comp L) (hL.trans (LinearMap.ker_le_ker_comp L k)) := by
  ext y
  rfl

/-- Precomposing `Submodule.liftQ` over `p'` with the map `M ⧸ p ⟶ M ⧸ p'` of
`Submodule.factor` is `Submodule.liftQ` over `p`. -/
theorem liftQ_comp_factor (hpp' : p ≤ p') (L : M →ₛₗ[τ₁₂] M₂) (hL : p' ≤ LinearMap.ker L) :
    (p'.liftQ L hL).comp (factor hpp') = p.liftQ L (hpp'.trans hL) := by
  ext y
  rfl

end Submodule
