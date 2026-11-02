/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
import all WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints

import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels

/-! # Common-stage normalized tensor associator

The common-stage associator and braiding constraints, using the finite
normalized constraints and the directed-stage representative calculation.
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.privateModule false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v r

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Preserve the cached additive-group data while comparing stage Hom types.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

-- Match the category-wrapper proof context used by DerivedPullbackTensorHom.
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  integralCoefficientLinear integralScalarConstant sfIntegralCoefficientLinear
  sfIntegralConstructibleLinear
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence
  commonStageTensorComparison commonStagePullbackComparison
  operationStageTransitionIso commonStageDerivedTensor commonStageDerivedPullback

section HigherCoherence
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

/-- The left nested tensor expressed at an arbitrary common finite stage.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonLeft (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W
      (commonStageTensorObject l Ω W M N) P).stage ≤ L) :=
  commonStageTensorComparison l Ω W (commonStageTensorObject l Ω W M N) P L h ≪≫
    ((@rationalDerivedTensor l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
      hW)).mapIso
      (Iso.prod (commonStageTensorComparison l Ω W M N L (((Padic.finiteCoefficientFields_properties
        l Ω).1 (commonStageTensorObject l Ω W M N).stage P.stage).1.trans h)) (Iso.refl _))

/-- The right nested tensor expressed at an arbitrary common finite stage.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonRight (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W M
      (commonStageTensorObject l Ω W N P)).stage ≤ L) :=
  commonStageTensorComparison l Ω W M (commonStageTensorObject l Ω W N P) L h ≪≫
    ((@rationalDerivedTensor l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
      hW)).mapIso
      (Iso.prod (Iso.refl _) (commonStageTensorComparison l Ω W N P L
        (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage (commonStageTensorObject l Ω W N
        P).stage).2.trans h)))

attribute [local irreducible] pullbackTensorCommonLeft pullbackTensorCommonRight

/-- Existence half of the normalized constraint; uniqueness is proved by the parent theorem.
Source: Stacks 06YS, 07A4, 0941.
(blueprint: lem-pur-derived-pullback-tensor-constraints-common-associator-existence). -/
theorem pullbackTensorCommonAssociator_exists (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃ e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (((@commonStageDerivedTensor l _ Ω _ _
      _ W hW)).obj (M,N),P) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,((@commonStageDerivedTensor l _ Ω _ _ _
        W hW)).obj (N,P)),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P).stage ≤ L) (hT :
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P)
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)) L hS hT
          (((@pullbackTensorCommonLeft l _ Ω _ _ _ W hW) M N P L hS).hom ≫
            ((@pullbackTensorRationalAssociator l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (N.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (P.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).2.trans hS))).hom ≫
            ((@pullbackTensorCommonRight l _ Ω _ _ _ W hW) M N P L hT).inv)) := by
  sorry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The common-stage associator has its prescribed representative at every larger field.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Conjugate the rational associator
by the
  displayed transition/tensor comparisons. Their scalar-extension cocycles show independence of
  enlargement. The inverse formula gives an inverse class. Directedness supplies common stages, and
  a representative determines its colimit hom class uniquely. -/
theorem pullbackTensorCommonAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (((@commonStageDerivedTensor l _ Ω _ _
      _ W hW)).obj (M,N),P) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,((@commonStageDerivedTensor l _ Ω _ _ _
        W hW)).obj (N,P)),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P).stage ≤ L) (hT :
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P)
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)) L hS hT
          (((@pullbackTensorCommonLeft l _ Ω _ _ _ W hW) M N P L hS).hom ≫
            ((@pullbackTensorRationalAssociator l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (N.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (P.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).2.trans hS))).hom ≫
            ((@pullbackTensorCommonRight l _ Ω _ _ _ W hW) M N P L hT).inv)) := by
  obtain ⟨e, he⟩ := pullbackTensorCommonAssociator_exists l Ω W M N P
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  let S := commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P
  let T := commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)
  let L := Padic.finiteCoefficientCompositum l Ω S.stage T.stage
  let hS := ((Padic.finiteCoefficientFields_properties l Ω).1 S.stage T.stage).1
  let hT := ((Padic.finiteCoefficientFields_properties l Ω).1 S.stage T.stage).2
  exact eq_of_heq ((hd L hS hT).trans (he L hS hT).symm)

/-- The stage-independent rational associator class.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonAssociator_existsUnique l _ Ω _ _ _ W hW) M N P).exists.choose

attribute [local irreducible] pullbackTensorCommonAssociator

end HigherCoherence

end WeilConjectures
