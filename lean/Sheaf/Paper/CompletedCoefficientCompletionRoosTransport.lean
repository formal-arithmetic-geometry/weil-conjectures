/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.PbcCompletedPullbackActual
public import Sheaf.Paper.SfDerivedComplete

/-! # The normalized completion Roos triangle under coefficient transport

Source: Stacks Tags 099M, 099N and 06YY; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-pur-completed-coefficient-completion-roos-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Transport of the completion reflector, retaining its unit and the canonical
intrinsic reduction maps. This compares completion objects before imposing any
completeness, boundedness or constructibility condition on the input.

Source: Stacks Tags 099M, 099N and 06YY; Bhatt--Scholze, Definition 3.5.2.
(blueprint: lem-pur-completed-coefficient-completion-roos-transport).

Proof: the equation on the coefficient isomorphism identifies its finite projections
with the already normalized integralDetailedLevelComparison. At each positive level,
the tensor/restriction adjunction therefore identifies reduction after inverse scalar
restriction with sfDerivedReductionRestricted. On flat K-flat representatives these
maps send a pure tensor to the same tensor with its coefficient transported. The
transition squares and augmentation squares follow on these tensors and descend by
the universal derived tensor counits. Thus this is an isomorphism of the augmented
reduction sequences, including their canonical units, rather than only levelwise
isomorphisms of their objects.

Apply completedKoszulQuotientComparison and completedKoszulReductionRoosTriangle to
an intrinsic completed-coefficient representative. The Koszul reflector and the
actual complete-subcategory reflector represent the same adjunction, so their unique
unit-compatible comparison identifies the first vertex with pbcActualCompletion K.
Exact restriction along the inverse ring isomorphism preserves products and
triangles. Transport the resulting Roos triangle through the preceding sequence
isomorphism. Its coordinate unit equations give the displayed product unit equation
by product extensionality. All comparisons use the positive quotient levels; the
argument also applies to the zero object, the empty scheme and residue level one. -/
theorem completedCoefficientCompletionRoosTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (c : pbcAdicCompletion W (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E W)
    (_hc : (adicLisseForget W).mapIso c = integralDetailedCoefficientComparison W l E)
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    ∃ hp : HasProduct (fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj
        ((pbcDerivedRestrict c.inv).obj K)),
      letI := hp
      ∃ (p : (pbcDerivedRestrict c.inv).obj
          ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K) ⟶
          ∏ᶜ fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj
            ((pbcDerivedRestrict c.inv).obj K))
        (δ : (∏ᶜ fun n : ℕ ↦ (sfDerivedReductionRestricted l E W n).obj
            ((pbcDerivedRestrict c.inv).obj K)) ⟶
          ((pbcDerivedRestrict c.inv).obj
            ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K))⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle
          (fun n ↦ (sfDerivedReductionTransition l E W n).app
            ((pbcDerivedRestrict c.inv).obj K))
          ((pbcDerivedRestrict c.inv).obj
            ((pbcActualCompletion (pbcIntegralDatum l E) W).obj K)) p δ ∧
        (pbcDerivedRestrict c.inv).map
            ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K) ≫ p =
          Pi.lift (fun n ↦ (sfDerivedReductionUnit l E W n).app
            ((pbcDerivedRestrict c.inv).obj K)) := by
  sorry

end WeilConjectures
