/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Completion of a discrete valuation ring

The maximal-ideal-adic completion of a discrete valuation ring is a discrete valuation ring.

## Implementation details

A discrete valuation ring is a regular local ring of dimension one. Its completion is regular
local of the same dimension, hence a discrete valuation ring.

## References

* [Stacks, Tag 0AP1], forward direction
* [Stacks, Tag 00PD], part (4)
-/

@[expose] public section

universe u

namespace AdicCompletion

/-- The maximal-ideal-adic completion of a discrete valuation ring is a domain and again a
discrete valuation ring. -/
theorem isDiscreteValuationRing
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    ∃ _ : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A),
      IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  have : IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    (isRegularLocalRing_iff A).mp inferInstance
  refine ⟨inferInstance, IsRegularLocalRing.isDiscreteValuationRing _ ?_⟩
  exact (RingTheory.completion_dimension A).1.trans
    (IsDiscreteValuationRing.ringKrullDim_eq_one A)

end AdicCompletion
