/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.RingTheory.CompletionDimensionEquality
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Dimension of the completion of a Noetherian local ring

The completion of a Noetherian local ring at its maximal ideal has the same finite Krull
dimension.

## Implementation details

The equality comes from `RingTheory.completion_dimension_eq`, which applies the flat height
formula to the faithfully flat map to the completion, whose closed fibre is the residue field.
Finiteness is Mathlib's `ringKrullDim_lt_top`.

## References

* [Stacks, Tag 07NV], alternative proof via [Stacks, Tag 00ON]
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory

/-- The maximal-ideal completion of a Noetherian local ring has the same finite Krull
dimension. -/
theorem completion_dimension (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) = ringKrullDim A ∧
      ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) < ⊤ ∧
      ringKrullDim A < ⊤ := by
  have hA : ringKrullDim A < ⊤ := ringKrullDim_lt_top
  have heq := completion_dimension_eq A
  have hB : ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) < ⊤ :=
    heq ▸ hA
  exact ⟨heq, hB, hA⟩

end RingTheory
