/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import all WeilConjectures.SixFunctors.Open.OpenQuotientKoszulCompleteness
import all WeilConjectures.SixFunctors.Open.OpenDvrIntrinsicOpenTransport
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenDvrRingedIdentification
import all WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedDirectImagePreservesCompleteness
import all WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence

/-! # Completeness of the normalized limit after quasi-compact open extension

This is the completeness part of the open reduction and reconstruction argument.

## References

* [Stacks, Tag 0941]
* [Stacks, Tag 09BP]
* [Stacks, Tag 0A0E]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ringed open extension of a normalized coefficient limit is complete. -/
theorem integralOpenLimitComplete (o : Operations l E)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] [QuasiCompact j]
    (N : System l E U) (hN : Good l E U N)
    (hJ : Good l E V ((Operations.shriek l E o j).obj N)) :
    IntegralOnSlice.IsComplete l E V none
      ((ringedOpen l E j).obj ((coefficientSequenceLimit l E U).obj N)) := by
  have _ := hJ
  have hcomplete :=
    ((purNormalizedReconstructionOfScheme l E U (calculus l E U)).1 N hN.1).1
  obtain ⟨O⟩ := dvrOpenModel_exists l E j
  have hext := dvrOpen_complete l E j O _ hcomplete
  obtain ⟨e⟩ := openDvr_ringed_identification l E j O
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  have hne : p ≠ l := by omega
  exact (complete_iff_local p l hne E V _).mpr
    (integralLocallyComplete_iso l E V _ (e.app _)
      ((complete_iff_local p l hne E V _).mp hext))

end WeilConjectures.IntegralSystemRealization
