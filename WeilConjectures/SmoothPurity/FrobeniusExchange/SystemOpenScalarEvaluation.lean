/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemScalarFiniteEvaluation
import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemOpenScalarEvaluationCore

/-! # Evaluation of the open scalar mate

Evaluation takes the open system scalar mate to the finite scalar transpose of the open
restriction comparison.

## Implementation details

The inverse mate is evaluated first (see the core file); inverting the specified open
evaluation mates and the system open scalar mate gives the forward equation, which is then
transposed under the finite scalar adjunction.

## References

* W. Zheng, Construction 4.1 and Lemma 4.10
* Stacks Project, Tags 03DI, 06YY and 07A6
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- The finite scalar transpose of the specified open restriction comparison. -/
def finiteOpenScalar
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory ⋙
        pbcDerivedExtend (scalarRingMap φ Z) ⟶
      pbcDerivedExtend (scalarRingMap φ X) ⋙ (sfIntrinsicExtensionByZero j B).mapDerivedCategory :=
  ((mateEquiv (pbcDerivedScalarAdjunction (scalarRingMap φ X))
    (pbcDerivedScalarAdjunction (scalarRingMap φ Z))).symm
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ)).hom))

/-- Evaluation of open extension, inverse to the specified open-adjunction mate. -/
def systemOpenFiniteEvaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    systemDerivedOpen l E j ⋙ coefficientSequenceDerivedEvaluation l E Z n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙
        (sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory :=
  letI := systemOpenEvaluationInv_isIso l E j n
  (asIso (systemOpenEvaluationInv l E j n)).symm

/-- Evaluation takes the forward open system scalar map to the finite scalar transpose. -/
theorem systemOpenScalar_finiteEvaluation
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) (N : coefficientSequenceDerived l E X) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    (coefficientSequenceDerivedEvaluation l L Z n).map
          ((systemOpenScalar l E L ι j).hom.app N) ≫
        (systemOpenFiniteEvaluation l L j n).hom.app
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj N) ≫
        (sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l L (n + 1))).mapDerivedCategory.map
            ((systemScalarFiniteEvaluation l E L ι X n).hom.app N) =
      (systemScalarFiniteEvaluation l E L ι Z n).hom.app ((systemDerivedOpen l E j).obj N) ≫
        (pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) Z)).map
          ((systemOpenFiniteEvaluation l E j n).hom.app N) ≫
        (finiteOpenScalar (integralScalarQuotientMap l E L ι n) j).app
          ((coefficientSequenceDerivedEvaluation l E X n).obj N) := by
  let _ := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let _ := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
  have : IsIso (systemOpenScalarInv l E L ι j) :=
    systemOpenScalarInv_isIso l E L ι j
  have h := systemOpenScalarInv_finiteEvaluation_core l E L ι j n N
  dsimp only [systemOpenFiniteEvaluation, finiteOpenScalar] at h ⊢
  rw [h]
  rw [show (systemOpenScalar l E L ι j).hom.app N =
      (asIso (systemOpenScalarInv l E L ι j)).inv.app N by rfl]
  rw [show (systemOpenScalarInv l E L ι j).app N =
      (asIso (systemOpenScalarInv l E L ι j)).hom.app N by rfl]
  rw [← Category.assoc]
  rw [← (coefficientSequenceDerivedEvaluation l L Z n).map_comp]
  rw [Iso.inv_hom_id_app]
  rw [(coefficientSequenceDerivedEvaluation l L Z n).map_id, Category.id_comp]

end WeilConjectures.FrobeniusExchange
