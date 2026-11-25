/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReindexingReductionTensorData
import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReductionReindexUnaryModelAux2

/-! # The unary strict reduction/reindexing model

The whole-system reduction mate has an ordinary quotient representative.

## Implementation details

The system localization factor uses the same equality transport as the system
tensor comparison; it is a specified natural isomorphism, not a chosen witness.

## References

* Stacks Project, Tags 03EL, 07A4, 07A6, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReductionRepresentatives
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option quotPrecheck false in
set_option hygiene false in
local notation "R[" W "]" =>
  (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "I[" g "]" =>
  (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "F[" g "]" => podReindexingComplexFunctor l E g none
/-- The whole-system reduction mate has an ordinary quotient representative. -/
theorem unary_model {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : PodCompletionReindex l E g) (hA : PodCompletionReindex.Laws l E g A)
    (h : podReindexingDerivedFunctor l E g none = podOrdinaryReindex l E g)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    ∃ (hFP : integralOperationsGoodComplex l E X ((F[g]).obj P.obj))
      (β : (I[g]).obj ((R[Y]).obj P.obj) ≅ (R[X]).obj ((F[g]).obj P.obj)),
      Generators l E g P.obj β ∧
      (integralComparisonDerivedSequencePullback l E g).map
          ((pullbackTensorReductionModel l E Y).hom.app P) ≫
        (systemFactor l E g).hom.app
          ((R[Y]).obj P.obj) ≫ (systemQ l E X).map β.hom =
      A.reduction.hom.app ((podReindexingQ l E Y none).obj P.obj) ≫
        (podReindexCalculus l E X).reduction.map ((factor l E g h).hom.app P.obj) ≫
        (pullbackTensorReductionModel l E X).hom.app ⟨(F[g]).obj P.obj, hFP⟩ :=
  unary_model_core l E g A hA h P

end WeilConjectures.PodReductionRepresentatives
