/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensor
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensorShiftCoherence
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicIntegralTensorTowerCoherence

/-! # Coherence before rational localization

The integral tensor comparison maps commute with shifts and are compatible with towers of
coefficient fields, before rational localization.

## Implementation details

The ordinary tensor comparison and its quotient-completion chain map commute with the
degreewise shift; the universal derived counits lift these squares. For a tower
`E ⊆ L ⊆ M`, the integral associator is rewritten as the conjugate of ordinary derived
balancing by the three completion comparisons; the remaining equality is associativity of the
balanced derived tensor with the native ring, checked on ordinary tensor units and on K-flat
complexes and descended along the universal derived counit. The defining equation of
`integralTensorAssociator` is exposed as a separate lemma so that component proofs do not
normalize large scalar-extension functors.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Propositions 3.5.1 and 6.8.14(2),
  Remark 6.8.15
* Stacks Project, Tag 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The integral scalar associator with the literal field-inclusion transport. -/
@[irreducible] def integralTensorAssociator
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :=
  sfIntegralScalarComp l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) X
    0 (Fact.out : l.Prime).ne_zero (Coefficient.{u} l Ω M)
    (coefficientInclusion l Ω L M k) ≪≫
    eqToIso (congrArg
      (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω M) i X)
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2
        E L M h k))

/-- The defining equation of `integralTensorAssociator`. -/
theorem integralTensorAssociator_eq
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {E L M : Index l Ω} (h : E ≤ L) (k : L ≤ M) :
    integralTensorAssociator l X Ω h k =
  sfIntegralScalarComp l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) X
    0 (Fact.out : l.Prime).ne_zero (Coefficient.{u} l Ω M)
    (coefficientInclusion l Ω L M k) ≪≫
    eqToIso (congrArg
      (fun i ↦ sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω M) i X)
      ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2
        E L M h k)) := by
  unfold integralTensorAssociator
  rfl

variable [IsCommMonObj (abRing l X)] [(sections l X).Additive]
  [PreservesFiniteLimits (sections l X)] [PreservesFiniteColimits (sections l X)]

/-- The explicit inverse-balancing and completion maps commute with shifts and are compatible
with the integral associators of field towers `E ⊆ L ⊆ M`. -/
theorem integralTensorComparison_coherent (C : CoefficientSystem l X) :
    (∀ {E L : Index l (PadicAlgCl l)} (h : E ≤ L),
      NatTrans.CommShift (integralTensorComparison l X C h) ℤ) ∧
    (∀ {E L M : Index l (PadicAlgCl l)} (h : E ≤ L) (k : L ≤ M)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
      (integralTensorComparison l X C h).app K ≫
        (integralTensorComparison l X C k).app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition
            l (PadicAlgCl l) X E L h).obj K) ≫
        (integralTensor l X C M).map ((integralTensorAssociator l X (PadicAlgCl l) h k).hom.app K) =
      (integralTensorComparison l X C (h.trans k)).app K) := by
  exact ⟨integralTensorComparison_shift l X C,
    integralTensorComparison_tower l X C
      (fun h k ↦ integralTensorAssociator l X (PadicAlgCl l) h k)
      (fun h k ↦ integralTensorAssociator_eq l X (PadicAlgCl l) h k)⟩

end WeilConjectures.LocallyFiniteAdicRealization
