/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
public import WeilConjectures.SmoothPurity.OpenCompletedRestriction.OpenCompletedRestrictionIdentification
import WeilConjectures.SixFunctors.Supporting.OrdinaryIntegralNestedOpenRestriction
import WeilConjectures.SixFunctors.Clopen.ClopenIntegralCompletionRestriction
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion

/-!
# Ordinary restriction of a completed chart to a smaller clopen

We show that, on nested clopens `A ≤ U`, the completed chart of a complete complex restricts
to its ordinary restriction to `A`.

## Implementation details

The restriction functor is the existing normalized open restriction, with its exactness
instances. There is no boundedness, projectivity, constructibility or affineness hypothesis,
and all constructions allow empty clopens and the zero coefficient module.

## References

* [Stacks, Tag 03D8]
* [Stacks, Tag 06YY]
* [Stacks, Tag 08TC]
* [Stacks, Tag 09C3]
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.ordinaryIntegralDerivedPull WeilConjectures.integralDerivedPullback

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- On nested clopens, exact unit-preserving module restriction identifies the
completed chart of a complete complex with its ordinary restriction to the smaller open. -/
theorem clopen_completed_restriction_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W V : Scheme.{u}) (f : V ⟶ W) (U A : V.Opens)
    (_hU : IsClosed (U : Set V)) (_hA : IsClosed (A : Set V)) (hAU : A ≤ U)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W))
    (_hK : IntegralOnSlice.IsComplete l E V none ((ordinaryIntegralDerivedPull l E f).obj K)) :
    Nonempty ((ordinaryIntegralDerivedPull l E (A.ι ≫ f)).obj K ≅
      (OpenCompletedRestriction.derivedRestriction l E (V.homOfLE hAU)).obj
        ((integralDerivedPullback l E U.ι).obj
          ((ordinaryIntegralDerivedPull l E f).obj K))) := by
  obtain ⟨ordinary⟩ := ordinaryIntegralNestedOpenRestriction l E W V f U A hAU
  obtain ⟨completed⟩ := clopenIntegralCompletionRestriction l E V U _hU
  let M := (ordinaryIntegralDerivedPull l E f).obj K
  have hu : IsIso ((IntegralOnSlice.completionUnit l E V none).app M) :=
    (IntegralOnSlice.canonicalCompletionUnitCriterion l E V M).mpr _hK
  let rU := OpenCompletedRestriction.derivedRestriction l E U.ι
  let rA := OpenCompletedRestriction.derivedRestriction l E (V.homOfLE hAU)
  let unitIso := asIso ((IntegralOnSlice.completionUnit l E V none).app M)
  exact ⟨ordinary.app K ≪≫
    rA.mapIso (rU.mapIso unitIso ≪≫ completed.app M)⟩

end WeilConjectures
