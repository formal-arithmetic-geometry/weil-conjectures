/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenReductionIso
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenLimitComplete

/-! # Canonical integral model construction steps

We show that open reduction and the output reconstruction unit are invertible at a good
total limit.

## Implementation details

These arguments concern the completed coefficient sheaves and their projections; they do not
require `l` to be invertible on the scheme or a finite-field base.

## References

* [Stacks, Tag 03DI], [Stacks, Tag 0941], [Stacks, Tag 07A7], [Stacks, Tag 09BP],
  [Stacks, Tag 0A0E]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Open reduction and the output reconstruction unit at a good total limit.
Only invertibility of these specified maps is asserted; the realization isomorphism
and its counit/unit normalization are not part of this statement. -/
theorem integralOpenReductionNormalizedLimit (o : Operations l E)
    (m : RealizationModel l E o) {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] [QuasiCompact j] (N : System l E U)
    (hN : Good l E U N)
    (hJ : Good l E V ((Operations.shriek l E o j).obj N)) :
    IsIso ((calculus l E V).adjunction.unit.app
      ((ringedOpen l E j).obj ((coefficientSequenceLimit l E U).obj N))) ∧
      IsIso ((m.openReduction l E j).app ((coefficientSequenceLimit l E U).obj N)) := by
  refine ⟨?_, ?_⟩
  · have hcomplete := integralOpenLimitComplete l E o j N hN hJ
    exact (purNormalizedReconstructionOfScheme l E V (calculus l E V)).2 _ hcomplete
  · exact integralOpenReductionIso l E o m j _

end WeilConjectures.IntegralSystemRealization
