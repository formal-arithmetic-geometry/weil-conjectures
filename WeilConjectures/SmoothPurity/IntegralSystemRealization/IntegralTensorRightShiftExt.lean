/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralTensorShiftProperties

/-! # Extensionality of normalized completed right shifts

## References

* Stacks Project, Tags 011G, 014E, 06YU and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Equality of completed right-slot comparisons with the same representative normalization. -/
theorem integralTensorRightShift_ext (W : Scheme.{u}) (r : ℤ)
    (σ τ : completedTensorShiftSecond (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r)
    (hσ : integralCompletedTensorRightShiftProperty l E W r σ)
    (hτ : integralCompletedTensorRightShiftProperty l E W r τ) : σ = τ := by sorry

end WeilConjectures.IntegralSystemRealization
