/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

import WeilConjectures.SmoothPurity.Rational.RationalPullbackStageCoherence
import WeilConjectures.SmoothPurity.Supporting.Tensor.MixedTensorStageComponent
import WeilConjectures.SmoothPurity.Common.CommonStagePullbackEndpoint
import WeilConjectures.SmoothPurity.Common.CommonStageTensorEndpoint
import WeilConjectures.SmoothPurity.Supporting.Tensor.RestrictionTensorNormalizedSquare
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all Mathlib.Logic.Small.Defs

/-! # Stage transport of restriction tensor representatives

Source: lemma-section-normal-bundle--1, common-stage subargument, steps 3--5
(blueprint: lem-pur-restriction-tensor-representative-transport).

The stage-level transport identity used by the quotient representative theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField

universe u v
open CategoryTheory AlgebraicGeometry
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
open WeilConjectures.AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory Stage transition
  WeilConjectures.commonStagePullbackObject WeilConjectures.commonStageTensorObject

set_option allowUnsafeReducibility true in
attribute [local reducible] stageSystem

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5

namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  ScalarLocalization.category ScalarLocalization.composition
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue sfRationalScalarComp
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.normalizedAssociator
  AlgebraicallyClosedCoefficients.coefficientInclusion
  ObjectProperty.FullSubcategory.category sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup
  Preadditive.fullSubcategory Linear.fullSubcategory sfIntegralConstructibleLinear

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  sfRationalScalarExtension commonStageDerivedPullback commonStageDerivedTensor
  rationalPullbackScalarComparison rationalTensorScalarComparison
  commonStagePullbackComparison commonStageTensorComparison operationStageTransitionIso

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A stage transport equality gives equality of the corresponding pair-category
representatives. -/
theorem pairRepresentative_eq_of_stage_transport
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category* (C i)]
    (S : StageSystem C) {A B : S.PairCategory} {H L : I}
    (hA : A.stage ≤ H) (hB : B.stage ≤ H) (h : H ≤ L)
    (u : A.toStage hA ⟶ B.toStage hB)
    (v : A.toStage (hA.trans h) ⟶ B.toStage (hB.trans h))
    (hv : v = S.tr h u) :
    StageSystem.PairCategory.mkHom H hA hB u =
      StageSystem.PairCategory.mkHom L (hA.trans h) (hB.trans h) v := by
  rw [hv]
  exact (StageSystem.PairCategory.mkHom_tr h u).symm

set_option maxHeartbeats 400000 in
-- The categorical component calculation checks several equivalent coefficient-category instances.
/--
At the level of the finite coefficient stage, the mixed scalar square and the
naturality of the tensor comparison identify the representative at an extension
with the stage-system transport of the representative at the original stage.
This is the component calculation: expand the two endpoint comparisons, use the
mixed square to move the pullback comparison through the tensor comparison, and
cancel inverse comparison isomorphisms.  The coefficient tower equations identify
the remaining comparisons with the direct ones, while the scalar associator
cocycle and naturality of `mu` identify the outer conjugates.  Different stages
are retained as transition maps; no literal equality of coefficient fields is
used. -/
theorem restrictionTensorRepresentativeStageTransport
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    let R := fun E : Index l Ω ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f
    let T := fun (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (E : Index l Ω) ↦ rationalDerivedTensor l (Coefficient.{u} l Ω E) W
    let b := fun (E L : Index l Ω) (h : E ≤ L) ↦
      rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f
    let theta := fun (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (E L : Index l Ω) (h : E ≤ L) ↦
      rationalTensorScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) W
    let S := fun A B : Pair l Ω X ↦
      commonStagePullbackObject l Ω f (commonStageTensorObject l Ω X A B)
    let U := fun A B : Pair l Ω X ↦ commonStageTensorObject l Ω Y
      (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B)
    let a := fun (A B : Pair l Ω X) (L : Index l Ω) (h : (S A B).stage ≤ L) ↦
      commonStagePullbackComparison l Ω f (commonStageTensorObject l Ω X A B) L h ≪≫
        (R L).mapIso (commonStageTensorComparison l Ω X A B L h)
    let z := fun (A B : Pair l Ω X) (L : Index l Ω) (h : (U A B).stage ≤ L) ↦
      commonStageTensorComparison l Ω Y
        (commonStagePullbackObject l Ω f A) (commonStagePullbackObject l Ω f B) L h ≪≫
      (T Y L).mapIso (Iso.prod
        (commonStagePullbackComparison l Ω f A L
          (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans h))
        (commonStagePullbackComparison l Ω f B L
          (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans h)))
    ∀ (mu : ∀ E : Index l Ω, T X E ⋙ R E ≅ (R E).prod (R E) ⋙ T Y E),
      (∀ (E L : Index l Ω) (h : E ≤ L) (M N : Stage l Ω X E),
        (transition l Ω Y E L h).map ((mu E).hom.app (M, N)) ≫
          (theta Y E L h).hom.app ((R E).obj M, (R E).obj N) ≫
          (T Y L).map (Prod.mkHom ((b E L h).hom.app M) ((b E L h).hom.app N)) =
        (b E L h).hom.app ((T X E).obj (M, N)) ≫
          (R L).map ((theta X E L h).hom.app (M, N)) ≫
          (mu L).hom.app ((transition l Ω X E L h).obj M,
            (transition l Ω X E L h).obj N)) →
      ∀ (A B : Pair l Ω X) (L : Index l Ω) (h : (S A B).stage ≤ L),
        let H := (S A B).stage
        let c := fun (K : Index l Ω) (hK : H ≤ K) ↦
          (a A B K hK).hom ≫
            (mu K).hom.app
              (A.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                A.stage B.stage).1.trans hK),
               B.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                A.stage B.stage).2.trans hK)) ≫ (z A B K hK).inv
        c L h = (stageSystem l Ω Y).tr h (c H le_rfl) := by
  intro R T b theta S U a z mu mixed A B L h H c
  let SX := stageSystem l Ω X
  let SY := stageSystem l Ω Y
  let p := fun {E K : Index l Ω} (h : E ≤ K) ↦
    rationalPullbackStageComparison l Ω f h
  let t := fun (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    {E K : Index l Ω} (h : E ≤ K) ↦ rationalTensorStageComparison l Ω W h
  let hA := ((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1
  let hB := ((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2
  let PA := commonStagePullbackObject l Ω f A
  let PB := commonStagePullbackObject l Ω f B
  let d := (mu H).hom.app (A.toStage hA, B.toStage hB) ≫
    (T Y H).map (Prod.mkHom
      (commonStagePullbackComparison l Ω f A H hA).inv
      (commonStagePullbackComparison l Ω f B H hB).inv)
  have square (E K : Index l Ω) (k : E ≤ K) :=
    restrictionTensorNormalizedSquare l Ω f mu mixed E K k
  have hc (K : Index l Ω) (k : H ≤ K) : c K k = (SY.T k).map d := by
    have hm := mixedTensorStageComponent SX SY R (T X) (T Y) p
      (rationalPullbackStageComparison_coherent l Ω f) (t X) (t Y) mu
      (fun {_ _} k ↦ square _ _ k) A B
      (fun K k ↦ commonStagePullbackComparison l Ω f A K k)
      (fun K k ↦ commonStagePullbackComparison l Ω f B K k)
      (fun K k ↦ (commonStagePullback_endpoint l Ω f A K k).symm)
      (fun K k ↦ (commonStagePullback_endpoint l Ω f B K k).symm)
      H K hA hB k
    let aK := (p k).app ((T X H).obj (A.toStage hA, B.toStage hB)) ≪≫
      (R K).mapIso ((t X k).app (A.toStage hA, B.toStage hB) ≪≫
        (T X K).mapIso (Iso.prod ((SX.assoc hA k).app A.obj)
          ((SX.assoc hB k).app B.obj)))
    let zK := ((t Y k).app (PA.toStage hA, PB.toStage hB) ≪≫
      (T Y K).mapIso (Iso.prod ((SY.assoc hA k).app PA.obj)
        ((SY.assoc hB k).app PB.obj))) ≪≫
      (T Y K).mapIso (Iso.prod
        (commonStagePullbackComparison l Ω f A K (hA.trans k))
        (commonStagePullbackComparison l Ω f B K (hB.trans k)))
    have ha : a A B K k = aK :=
      congrArg₂ (fun i j ↦ i ≪≫ (R K).mapIso j)
        (commonStagePullback_endpoint l Ω f (commonStageTensorObject l Ω X A B) K k).symm
        (commonStageTensor_endpoint l Ω X A B K k).symm
    have hz : z A B K k = zK :=
      congrArg (fun i ↦ i ≪≫ (T Y K).mapIso (Iso.prod
        (commonStagePullbackComparison l Ω f A K (hA.trans k))
        (commonStagePullbackComparison l Ω f B K (hB.trans k))))
        (commonStageTensor_endpoint l Ω Y PA PB K k).symm
    exact (congrArg₂ (fun (i : _ ≅ _) (j : _ ≅ _) ↦ i.hom ≫
      (mu K).hom.app (A.toStage (hA.trans k), B.toStage (hB.trans k)) ≫ j.inv)
        ha hz).trans hm
  exact (hc L h).trans ((SY.tr_map h d).symm.trans
    (congrArg (SY.tr h) (hc H le_rfl).symm))

end WeilConjectures
