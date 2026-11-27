/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemScalarFiniteEvaluation
import all WeilConjectures.SixFunctors.FrobeniusExchange.SystemScalarPullbackGeneralMate
import all WeilConjectures.SixFunctors.FrobeniusExchange.SystemOpenScalarPullbackMate
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemOpenScalarEvaluationCore
import WeilConjectures.Tactic.ExactByKernel

/-! # The scalar/pullback compatibility square used by proper evaluation

## Implementation details

This square is stated separately so that the mate calculation in
`systemDirectScalar_finiteEvaluation` is a formal consequence of
`SemilinearSections.evaluation_mate`. It is proved from the ordinary cube of right-adjoint
squares (direct image, restriction of scalars and finite evaluation), which commutes since
every comparison is the identity on sections: its left mates are localized with
`Functor.derivedCube_of_isDerivedSquareOf` and assembled by `scalarPullback_evaluation_cube`.

## References

* W. Zheng, Construction 4.1 and Lemma 4.10
* Stacks Project, Tags 06YY, 07A6 and 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open AlgebraicGeometry.Scheme.FiniteCompactScalar
open WeilConjectures.SemilinearSections

/-- The evaluated scalar/pullback cube required by the mate-pasting proof of the proper
scalar evaluation formula: the specified double mate of the normalized direct-image
restriction comparison agrees with the finite tensor/pullback square. -/
theorem systemProperScalarEvaluation_compatibility
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    let levelE := (sfIntrinsicConstantModuleAdjunction f
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryRightDerivedAdjunction
    let levelL := (sfIntrinsicConstantModuleAdjunction f
      (Padic.coefficientExtensionRing l L (n + 1))).mapDerivedCategoryRightDerivedAdjunction
    let φ := integralScalarQuotientMap l E L ι n
    let scalarMate := ((mateEquiv
      (pbcDerivedScalarAdjunction (scalarRingMap φ X))
      (pbcDerivedScalarAdjunction (scalarRingMap φ Y))).symm
      (TwoSquare.mk _ _ _ _ (sfDerivedImageRestriction f φ).hom))
    let a := (mateEquiv levelE levelL).symm scalarMate
    ∀ A : coefficientSequenceDerived l E Y,
      (coefficientSequenceDerivedEvaluation l L X n).map
          ((integralComparisonSystemScalarPullback l E L ι f).inv.app A) ≫
        (systemScalarFiniteEvaluation l E L ι X n).hom.app
          ((integralComparisonDerivedSequencePullback l E f).obj A) ≫
        (pbcDerivedExtend
            (scalarRingMap (integralScalarQuotientMap l E L ι n) X)).map
          ((systemPullEvaluation l E f n).inv.app A) =
      (systemPullEvaluation l L f n).inv.app
          ((integralComparisonDerivedSequenceScalar l E L ι Y).obj A) ≫
        (sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l L (n + 1)) f).map
          ((systemScalarFiniteEvaluation l E L ι Y n).hom.app A) ≫
        a.app ((coefficientSequenceDerivedEvaluation l E Y n).obj A) := by
  intro levelE levelL φ scalarMate a A
  have := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
  obtain ⟨ρX, hρX, hβX⟩ := systemScalarFiniteEvaluation_inv_eq_mate l E L ι X n
  obtain ⟨ρY, hρY, hβY⟩ := systemScalarFiniteEvaluation_inv_eq_mate l E L ι Y n
  obtain ⟨ρX₀, hρX₀, hΔX⟩ := systemRestrictionEvaluation_isDerivedSquareOf l E L ι X n ρX hρX
  obtain ⟨ρY₀, hρY₀, hΔY⟩ := systemRestrictionEvaluation_isDerivedSquareOf l E L ι Y n ρY hρY
  obtain ⟨Qd, hQd⟩ := Functor.exists_isDerivedSquareOf (sequenceRestrictionPullbackInv l E L ι f)
  -- the two presentations of the evaluated direct image are compared by the kernel
  have hord := ordinaryDirectRestrictionEvaluation_cube l E L ι f n
    (eqToIso (systemDirectEvaluationOrdinary_eq l E f n)).hom (fun M U y ↦ by
      exact_by_kernel eqToIso_hom_app_val_app_heq l E (systemDirectEvaluationOrdinary_eq l E f n)
        M U y)
    (eqToIso (systemDirectEvaluationOrdinary_eq l L f n)).hom (fun M U y ↦ by
      exact_by_kernel eqToIso_hom_app_val_app_heq l L (systemDirectEvaluationOrdinary_eq l L f n)
        M U y)
    ρY₀ hρY₀ ρX₀ hρX₀
  have hcube₀ := leftMate_cube_of_rightCube
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l L f))
    (sfIntrinsicConstantModuleAdjunction f (Padic.coefficientExtensionRing l E (n + 1)))
    (sfIntrinsicConstantModuleAdjunction f (Padic.coefficientExtensionRing l L (n + 1)))
    (eqToIso (systemDirectEvaluationOrdinary_eq l E f n)).hom
    (eqToIso (systemDirectEvaluationOrdinary_eq l L f n)).hom
    (sequenceScalarPullbackRight l E L ι f).inv
    (proEtaleCoefficientDirectImageComparison f φ).hom ρY₀ ρX₀ (by exact_by_kernel hord)
  have := sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1)) f
  have := sfIntrinsicPullback_preservesFiniteLimits (Padic.coefficientExtensionRing l E (n + 1)) f
  have := sfIntrinsicPullback_preservesFiniteColimits (Padic.coefficientExtensionRing l E (n + 1)) f
  have := sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l L (n + 1)) f
  have := sfIntrinsicPullback_preservesFiniteLimits (Padic.coefficientExtensionRing l L (n + 1)) f
  have := sfIntrinsicPullback_preservesFiniteColimits (Padic.coefficientExtensionRing l L (n + 1)) f
  have := coefficientSequenceEvaluation_additiveInstance l E X n
  have := coefficientSequenceEvaluation_additiveInstance l E Y n
  have := coefficientSequenceEvaluation_additiveInstance l L X n
  have := coefficientSequenceEvaluation_additiveInstance l L Y n
  have := coefficientSequenceEvaluation_limits l E X n
  have := coefficientSequenceEvaluation_limits l E Y n
  have := coefficientSequenceEvaluation_limits l L X n
  have := coefficientSequenceEvaluation_limits l L Y n
  have := coefficientSequenceEvaluation_colimits l E X n
  have := coefficientSequenceEvaluation_colimits l E Y n
  have := coefficientSequenceEvaluation_colimits l L X n
  have := coefficientSequenceEvaluation_colimits l L Y n
  have hΔE : Functor.IsDerivedSquareOf (systemPullEvaluationOrdinaryInv l E f n)
      (systemPullEvaluation l E f n).hom := by
    exact_by_kernel Functor.isDerivedSquareOf_mapDerivedCategorySquareIso
      (@asIso _ _ _ _ (systemPullEvaluationOrdinaryInv l E f n)
        (systemPullEvaluationOrdinaryInv_isIso l E f n))
  have hΔL : Functor.IsDerivedSquareOf (systemPullEvaluationOrdinaryInv l L f n)
      (systemPullEvaluation l L f n).hom := by
    exact_by_kernel Functor.isDerivedSquareOf_mapDerivedCategorySquareIso
      (@asIso _ _ _ _ (systemPullEvaluationOrdinaryInv l L f n)
        (systemPullEvaluationOrdinaryInv_isIso l L f n))
  have hcube := Functor.derivedCube_of_isDerivedSquareOf
    (δE := systemPullEvaluationOrdinaryInv l E f n) (δL := systemPullEvaluationOrdinaryInv l L f n)
    (Q := sequenceRestrictionPullbackInv l E L ι f) (by exact_by_kernel hcube₀) hΔE hΔL hQd
    (sfDerivedImageRestriction_inverseMate_isDerivedSquareOf φ f) hΔY hΔX
  exact scalarPullback_evaluation_cube levelE levelL
    (finiteEvaluationSystemScalarAdjunction l E L ι Y)
    (finiteEvaluationSystemScalarAdjunction l E L ι X)
    (pbcDerivedScalarAdjunction (scalarRingMap φ Y))
    (pbcDerivedScalarAdjunction (scalarRingMap φ X))
    (coefficientSequenceDerivedEvaluation l E Y n) (coefficientSequenceDerivedEvaluation l L Y n)
    (coefficientSequenceDerivedEvaluation l E X n) (coefficientSequenceDerivedEvaluation l L X n)
    (integralComparisonSystemScalarPullback l E L ι f) Qd
    (systemScalarPullback_hom_eq_finiteMate_general l E L ι f Qd hQd)
    (systemScalarFiniteEvaluation l E L ι X n) ρX hβX
    (systemScalarFiniteEvaluation l E L ι Y n) ρY hβY
    (systemPullEvaluation l E f n) (systemPullEvaluation l L f n)
    (sfDerivedImageRestriction f φ) hcube a rfl A

end WeilConjectures.FrobeniusExchange
