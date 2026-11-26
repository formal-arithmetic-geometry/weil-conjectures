/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensor

/-! # Field-tower coherence of the explicit integral comparison

For a tower of coefficient fields, the explicit integral comparisons compose, through the
integral scalar associator, to the direct comparison.

## Implementation details

The associator is passed as an argument `assoc` together with its defining equation `hassoc`
(the defining equation `integralTensorAssociator_eq` of `integralTensorAssociator`, which lives
in a module importing this one). By the completed scalar associator formula, the integral
associator `sfIntegralScalarComp` is the ordinary derived balancing associator conjugated by the
three completion comparisons; naturality cancels these, and what remains is associativity of
the balanced derived tensor with the native ring, checked on ordinary tensor units and K-flat
complexes and descended along the universal derived counit.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Propositions 3.5.1 and 6.8.14(2),
  Remark 6.8.15
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]

/-- For a tower `E ≤ L ≤ M`, the explicit integral comparisons compose, through the
integral scalar associator `assoc`, to the direct comparison. Here `hassoc` identifies
`assoc` with `sfIntegralScalarComp` followed by equality transport along the
field-inclusion composition law. -/
theorem integralTensorComparison_tower (C : CoefficientSystem l X)
    (assoc : ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M),
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) X ⋙
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l (PadicAlgCl l) L) (Coefficient.{u} l (PadicAlgCl l) M)
        (coefficientInclusion l (PadicAlgCl l) L M k) X ≅
      sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) M)
        (coefficientInclusion l (PadicAlgCl l) E M (h.trans k)) X)
    (hassoc : ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M),
      assoc h k =
        sfIntegralScalarComp l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L)
          (coefficientInclusion l (PadicAlgCl l) E L h) X
          0 (Fact.out : l.Prime).ne_zero (Coefficient.{u} l (PadicAlgCl l) M)
          (coefficientInclusion l (PadicAlgCl l) L M k) ≪≫
        eqToIso (congrArg
          (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) M) i X)
          ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l
            (PadicAlgCl l)).2 E L M h k))) :
    ∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      (integralTensorComparison l X C h).app K ≫
        (integralTensorComparison l X C k).app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition
            l (PadicAlgCl l) X E L h).obj K) ≫
        (integralTensor l X C M).map ((assoc h k).hom.app K) =
      (integralTensorComparison l X C (h.trans k)).app K := by
  sorry

end WeilConjectures.LocallyFiniteAdicRealization
