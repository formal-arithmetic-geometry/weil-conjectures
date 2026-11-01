/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemScalarFiniteEvaluation

/-! # Inverse-mate reduction for open scalar evaluation

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- The inverse open scalar mate evaluates to the finite open scalar transpose.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 07A6
(blueprint: lem-sf-system-open-scalar-evaluation).

This is the inverse-mate square used to prove the forward evaluation theorem. It is
strictly below that theorem: the forward open scalar mate is absent, and the equation
is before cancellation of its inverse component. The proof is the sectionwise balanced
 tensor calculation on the open, followed by the unit and counit equations of the
specified open adjunctions and the normalized scalar evaluation maps. Localization
preserves these equations for arbitrary unbounded systems. -/
theorem systemOpenScalarInv_finiteEvaluation_core
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) (N : coefficientSequenceDerived l E X) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    let uE :=
      letI := systemOpenEvaluationInv_isIso l E j n
      (asIso (systemOpenEvaluationInv l E j n)).symm
    let uL :=
      letI := systemOpenEvaluationInv_isIso l L j n
      (asIso (systemOpenEvaluationInv l L j n)).symm
    let a :=
      ((mateEquiv (pbcDerivedScalarAdjunction
          (scalarRingMap (integralScalarQuotientMap l E L ι n) X))
        (pbcDerivedScalarAdjunction
          (scalarRingMap (integralScalarQuotientMap l E L ι n) Z))).symm
        (TwoSquare.mk _ _ _ _
          ((Functor.mapDerivedCategorySquareIso
            (sfOpenRestriction j (integralScalarQuotientMap l E L ι n))).hom))).natTrans
    (uL.hom.app ((integralComparisonDerivedSequenceScalar l E L ι X).obj N)) ≫
        (sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l L (n + 1))).mapDerivedCategory.map
            ((systemScalarFiniteEvaluation l E L ι X n).hom.app N) =
      (coefficientSequenceDerivedEvaluation l L Z n).map
          ((systemOpenScalarInv l E L ι j).app N) ≫
        (systemScalarFiniteEvaluation l E L ι Z n).hom.app
          ((systemDerivedOpen l E j).obj N) ≫
        (pbcDerivedExtend
          (scalarRingMap (integralScalarQuotientMap l E L ι n) Z)).map
          (uE.hom.app N) ≫
        a.app ((coefficientSequenceDerivedEvaluation l E X n).obj N) := by
  sorry

end WeilConjectures.FrobeniusExchange
