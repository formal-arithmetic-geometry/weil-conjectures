/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorConstruction
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorKFlatNormalization
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationQuotient
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorEvaluationFactors

/-! # The total diagonal through exact-functor factorizations

Source: Stacks Tags 07A4, 0941 and 03D2.
(blueprint: lem-pur-completed-pullback-tensor-evaluation-diagonal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  sfIntrinsicPullback coefficientSequenceEvaluation
  pullbackTensorSequenceInverse pullbackTensorSystemComparison
  pullbackTensorInverseEvaluationComplex finitePullbackTensorConstruction
  coefficientTotalTensor DerivedCategory.Q DerivedCategory instCategoryDerivedCategory
  CochainComplex.IsKFlatIndependentCoefficients
  CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorCalculus pullbackTensorSequenceDerived
  finiteIntrinsicDerivedTensor finiteIntrinsicClosed

private theorem diagonal_paste
    {D : Type*} [Category* D]
    {A0 A1 A2 A3 A4 B0 B1 B2 C0 C1 Z : D}
    (e : A0 ⟶ A1) (ga : A1 ⟶ A2) (gv : A2 ⟶ A3)
    (delta0 : A2 ⟶ C0) (delta1 : A3 ⟶ A4) (qgv : C0 ⟶ A4) (qk : A4 ⟶ Z)
    (wa : A0 ⟶ B0) (wb : B0 ⟶ B1) (gamma0 : B0 ⟶ C1) (gamma1 : B1 ⟶ B2)
    (qd : C1 ⟶ C0) (qwb : C1 ⟶ B2) (qw : B2 ⟶ Z)
    (he : e ≫ ga ≫ delta0 = wa ≫ gamma0 ≫ qd)
    (hv : gv ≫ delta1 = delta0 ≫ qgv)
    (hw : wb ≫ gamma1 = gamma0 ≫ qwb)
    (hc : qd ≫ qgv ≫ qk = qwb ≫ qw) :
    e ≫ ga ≫ gv ≫ delta1 ≫ qk = wa ≫ wb ≫ gamma1 ≫ qw := by
  rw [reassoc_of% hv, reassoc_of% he, hc, ← reassoc_of% hw]

attribute [local instance] sfIntrinsicPullback_additive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures
