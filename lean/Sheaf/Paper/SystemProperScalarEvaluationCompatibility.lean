/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.SystemOperationExchangeRealization
public import Sheaf.Paper.SystemScalarFiniteEvaluation

/-! # The scalar/pullback compatibility square used by proper evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open AlgebraicGeometry.Scheme.FiniteCompactScalar
open WeilConjectures.SemilinearSections

/-- The evaluated scalar/pullback cube required by the mate-pasting proof.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 06YY, 07A6 and 0941.
(blueprint: lem-sf-system-proper-scalar-evaluation).

This is the square compatibility clause in the proof of the proper scalar
evaluation formula.  It is stated separately so that the mate calculation in
`systemDirectScalar_finiteEvaluation` is a formal consequence of
`SemilinearSections.evaluation_mate`.
-/
theorem systemProperScalarEvaluation_compatibility
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : TwoSquare
      (pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) Y))
      (sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f)
      (sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l L (n + 1)) f)
      (pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) X))) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
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
  intro A
  sorry

end WeilConjectures.FrobeniusExchange
