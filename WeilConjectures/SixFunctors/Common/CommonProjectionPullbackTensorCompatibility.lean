/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Common.CommonProjectionTensorComparison
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackTensorComponent
import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackTensorRepresentative
import all Mathlib.Logic.Small.Defs

/-! # Compatibility of finite-stage inclusion with tensor and pullback

We show that finite-stage inclusion preserves the canonical tensor/pullback comparison.

## Implementation details

For two inputs included from `E`, the common-stage comparison is evaluated at the coefficient
stage `E`, where its representative is `pullbackTensorAtCommonStage`. The inclusion
tensorators are expanded using `commonInclusionTensorModel`, and naturality of the transitions
cancels the transition maps on both sides. Equality in the common-stage Hom group follows by
applying `ofHom` at `E`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option Elab.async false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.style.haveILetI false

universe u v w v' w'
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  StageSystem.instCategoryPairCategory Functor.category
attribute [local irreducible] StageSystem.PairCategory.categoryStruct
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  commonStageDerivedPullback commonStageDerivedTensor

theorem projectionTensorComparisonCompatible_of_representative_formula
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (Q : SixFunctorCompactifiedSquare D)
    [hZ : ∀ x : Q.Z.obj.left, Invertible (C.l : Q.Z.obj.left.residueField x)]
    [hY : ∀ x : Q.Y.obj.left, Invertible (C.l : Q.Y.obj.left.residueField x)]
    (hrep : ∀
      (M N : sfRationalConstructibleCategory C.l
        (AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar E) Q.Y.obj.left)
      (L : AlgebraicallyClosedCoefficients.Index C.l C.Qbar)
      (h : (commonStageTensorObject C.l C.Qbar Q.Y.obj.left
        ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Q.Y.obj.left) E).obj M)
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (Y := Q.Y.obj.left) E).obj N)).stage ≤ L),
      HEq (canonicalCommonStagePullbackTensor C.l C.Qbar
        Q.p.hom.left
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (Y := Q.Y.obj.left) E).obj M)
        ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Q.Y.obj.left) E).obj N)).hom
        (ofHom (commonStagePullbackObject C.l C.Qbar Q.p.hom.left
          (commonStageTensorObject C.l C.Qbar Q.Y.obj.left
            ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Q.Y.obj.left) E).obj M)
            ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Q.Y.obj.left) E).obj N)))
          (commonStageTensorObject C.l C.Qbar Q.Z.obj.left
            (commonStagePullbackObject C.l C.Qbar Q.p.hom.left
              ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Q.Y.obj.left) E).obj M))
            (commonStagePullbackObject C.l C.Qbar Q.p.hom.left
              ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Q.Y.obj.left) E).obj N)))
          L h h (pullbackTensorAtCommonStage C.l C.Qbar Q.p.hom.left
            ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Q.Y.obj.left) E).obj M)
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (Y := Q.Y.obj.left) E).obj N) L h).hom)) :
    projectionTensorComparisonCompatible
      (S := (H.coefficientStages E).rational) (S' := H.commonStage)
      (T := (H.coefficientStages E).rationalTensor) (T' := H.commonStageTensor)
      (H.commonStageComparison E) (commonProjectionTensorComparison H E)
      ((H.coefficientStages E).rationalExchange Q) (H.commonStageExchange Q) := by
  unfold projectionTensorComparisonCompatible Adjunction.ComparisonCompatible
  intro M N
  have hr := @hrep M N E (by
    change E.val ⊔ E.val ≤ E.val
    exact sup_le le_rfl le_rfl)
  exact @projectionTensorComparisonCompatible_component_of_representative_formula
    D C H E Q hZ hY M N hr

/-- Finite-stage inclusion preserves the canonical tensor/pullback comparison.
This is a square for pullback and tensor alone; no support functor, direct image,
projection mate, or adjunction counit occurs in the square. -/
theorem commonProjectionPullbackTensorCompatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C) (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (Q : SixFunctorCompactifiedSquare D) :
    projectionTensorComparisonCompatible
      (S := (H.coefficientStages E).rational) (S' := H.commonStage)
      (T := (H.coefficientStages E).rationalTensor) (T' := H.commonStageTensor)
      (H.commonStageComparison E) (commonProjectionTensorComparison H E)
      ((H.coefficientStages E).rationalExchange Q) (H.commonStageExchange Q) := by
  letI : ∀ x : Q.Z.obj.left, Invertible (C.l : Q.Z.obj.left.residueField x) :=
    fun x ↦ (sixFunctorSpace_coefficient_invertible C Q.Z x).some
  letI : ∀ x : Q.Y.obj.left, Invertible (C.l : Q.Y.obj.left.residueField x) :=
    fun x ↦ (sixFunctorSpace_coefficient_invertible C Q.Y x).some
  refine projectionTensorComparisonCompatible_of_representative_formula H E Q ?_
  intro M N L h
  exact canonicalCommonStagePullbackTensor_formula C.Qbar Q.p.hom.left
    ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Q.Y.obj.left) E).obj M)
    ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Q.Y.obj.left) E).obj N) L h

end WeilConjectures
