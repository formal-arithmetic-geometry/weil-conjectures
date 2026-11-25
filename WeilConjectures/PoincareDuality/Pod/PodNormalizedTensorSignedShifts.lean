/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCompletionUnitTensor
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorSignedShifts

/-! # Signed tensor shifts for arbitrary normalized reindexing data

## References

* Stacks Project, Tags 011G, 07A4, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The signed completed tensor shift square for every representative-normalized datum. -/
theorem podNormalized_tensor_signed_shifts
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g A)
    (hA : PodCompletionReindex.Laws l E g A)
    (hT : PodCompletedTensorReindex.Laws l E g A T) :
    ∃ (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X),
      PodReindexSignedShifts l E g A T SY SX := by
  exact podReindexingTensorSignedShifts l E g A hA T hT

end WeilConjectures
