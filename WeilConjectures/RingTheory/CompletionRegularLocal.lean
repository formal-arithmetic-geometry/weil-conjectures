/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionDimension

/-!
# Regularity and completion of Noetherian local rings

A Noetherian local ring is regular if and only if its completion is.

## Implementation details

Both sides are rewritten with `isRegularLocalRing_iff`; the completion has the same number of
generators of the maximal ideal (`AdicCompletion.spanFinrank_maximalIdeal_eq`) and the same
dimension.

## References

* [Stacks, Tag 07NY]
-/

@[expose] public section


universe u

namespace AdicCompletion

/-- A Noetherian local ring is regular if and only if its maximal-ideal-adic completion
is regular. -/
theorem isRegularLocalRing_iff (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    IsRegularLocalRing A ↔ IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  set_option linter.style.haveILetI false in
    letI : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    AdicCompletion.isNoetherianRing _
  rw [_root_.isRegularLocalRing_iff, _root_.isRegularLocalRing_iff]
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq]
  rw [RingTheory.completion_dimension A |>.1]

end AdicCompletion
