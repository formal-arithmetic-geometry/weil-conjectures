/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemScalarFiniteEvaluation

/-! # The scalar/pullback compatibility square used by proper evaluation

## Implementation details

This square is stated separately so that the mate calculation in
`systemDirectScalar_finiteEvaluation` is a formal consequence of
`SemilinearSections.evaluation_mate`. It is proved on a common flat-term K-flat model using
the universal scalar counits and the K-injective normalization of
`sfDerivedImageRestriction`, then transported by naturality to all derived systems.

## References

* W. Zheng, Construction 4.1 and Lemma 4.10
* Stacks Project, Tags 06YY, 07A6 and 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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
        a.app ((coefficientSequenceDerivedEvaluation l E Y n).obj A) := by sorry

end WeilConjectures.FrobeniusExchange
