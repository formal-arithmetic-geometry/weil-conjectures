/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
public import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

/-! The representative specification of the prescribed common-stage tensor. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u v w u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] WeilConjectures.CoefQbarTensor
private theorem chosen_tensor_eq
    {I : Type w} [Preorder I] [IsDirectedOrder I]
    {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
    (S : StageSystem C) (U : BilinearCoefficientDescent.Family S S S)
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (c : ∀ (P Q : S.PairCategory) (L : I) (h : join P.stage Q.stage ≤ L),
      (S.T h).obj (BilinearCoefficientDescent.output U join left right (P, Q)).obj ≅
        (U.U L).obj (P.toStage ((left _ _).trans h), Q.toStage ((right _ _).trans h)))
    (hc : ∀ P Q L h,
      BilinearCoefficientDescent.endpoint U join left right (P, Q) h = c P Q L h) :
    (WeilConjectures.tensorDescent_with_components S U join left right c hc).exists.choose =
      BilinearCoefficientDescent.explicitDescent U join left right := by
  apply (WeilConjectures.tensorDescent_with_components S U join left right c hc).unique
    (WeilConjectures.tensorDescent_with_components S U join left right c hc).exists.choose_spec
  refine ⟨fun P Q ↦ rfl, fun P Q P' Q' L h h' a b ↦ ?_⟩
  simpa only [hc] using
    (BilinearCoefficientDescent.explicitDescent_spec U join left right).2
      (P, Q) (P', Q') L h h' a b

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageSystem stageSystem_existsUnique)

private def tensorFamily : BilinearCoefficientDescent.Family
    (stageSystem l Ω X) (stageSystem l Ω X) (stageSystem l Ω X) := by
  letI := RationalVerdier.units D l hl X
  exact ⟨fun E ↦ rationalDerivedTensor l (Coefficient.{u} l Ω E) X,
    fun {_ _} h ↦ rationalTensorStageComparison l Ω X h,
    rationalTensorStageComparison_coherent l Ω X⟩

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  rationalDerivedTensor sfRationalScalarExtension rationalTensorScalarComparison

private def tensorModel :
    generalAlgebraicallyClosedConstructibleCategory l Ω X ×
      generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  BilinearCoefficientDescent.explicitDescent (tensorFamily D l hl Ω X)
    (Padic.finiteCoefficientCompositum l Ω)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2)

attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage tensorFamily
  BilinearCoefficientDescent.explicitDescent BilinearCoefficientDescent.output
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.uniformProd
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.pairCategory

private theorem tensor_model_eq : CoefQbarTensor D l hl Ω X = tensorModel D l hl Ω X := by
  let := RationalVerdier.units D l hl X
  unfold CoefQbarTensor tensorModel
  let S := stageSystem l Ω X
  let U := tensorFamily D l hl Ω X
  let join := Padic.finiteCoefficientCompositum l Ω
  let left := fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1
  let right := fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2
  have hc (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω X)
      (L : Index l Ω) (h : join P.stage Q.stage ≤ L) :
      BilinearCoefficientDescent.endpoint U join left right (P, Q) h =
        commonStageTensorComparison l Ω X P Q L h := by
    unfold BilinearCoefficientDescent.endpoint
    change ((rationalTensorStageComparison l Ω X h).app
      (P.toStage (left P.stage Q.stage), Q.toStage (right P.stage Q.stage)) ≪≫
      (rationalDerivedTensor l (Coefficient.{u} l Ω L) X).mapIso
        (Iso.prod ((S.assoc (left P.stage Q.stage) h).app P.obj)
          ((S.assoc (right P.stage Q.stage) h).app Q.obj))) = _
    delta rationalTensorStageComparison commonStageTensorComparison operationStageTransitionIso
    exact tensorStageComparison_endpoint
      (C := Stage l Ω X (join P.stage Q.stage)) (D := Stage l Ω X L)
      (rationalDerivedTensor l (Coefficient.{u} l Ω (join P.stage Q.stage)) X)
      (rationalDerivedTensor l (Coefficient.{u} l Ω L) X)
      (eqToIso ((stageSystem_existsUnique l Ω X).exists.choose_spec.1 _ L h))
      (rationalTensorScalarComparison l (Coefficient.{u} l Ω (join P.stage Q.stage))
        (Coefficient.{u} l Ω L) (AlgebraicallyClosedCoefficients.coefficientInclusion
          l Ω _ L h) X)
      (P.toStage (left P.stage Q.stage)) (Q.toStage (right P.stage Q.stage))
      ((S.assoc (left P.stage Q.stage) h).app P.obj)
      ((S.assoc (right P.stage Q.stage) h).app Q.obj)
  exact chosen_tensor_eq S U join left right
    (fun P Q L h ↦ commonStageTensorComparison l Ω X P Q L h) hc

/-- The prescribed tensor satisfies the explicit bilinear representative specification.
Source: blueprint def-weil-derived-pullback-tensor-hom and thm-coef-qbar-verdier,
the common-coefficient tensor used for evaluation descent.
(blueprint: lem-coef-qbar-tensor-descent-spec).
Proof: build the coherent finite tensor family from rational tensor and its tower
comparison. Its endpoint isomorphisms equal the prescribed common-stage tensor
comparisons by the component formula for whiskering and the stage associators.
The chosen functor and explicit bilinear descent therefore satisfy the same unique
representative prescription. Their equality transports the proved explicit
descent specification to the chosen tensor. All data in the family are the
prescribed rational operations; the uniqueness assertion determines the functor. -/
theorem tensor_descent_spec :
    let := RationalVerdier.units D l hl X
    let S := stageSystem l Ω X
    let U : BilinearCoefficientDescent.Family S S S :=
      ⟨fun E ↦ rationalDerivedTensor l (Coefficient.{u} l Ω E) X,
        fun {_ _} h ↦ rationalTensorStageComparison l Ω X h,
        rationalTensorStageComparison_coherent l Ω X⟩
    BilinearCoefficientDescent.IsDescent U (Padic.finiteCoefficientCompositum l Ω)
      (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
      (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2)
      (CoefQbarTensor D l hl Ω X) := by
  let := RationalVerdier.units D l hl X
  change BilinearCoefficientDescent.IsDescent (tensorFamily D l hl Ω X)
    (Padic.finiteCoefficientCompositum l Ω)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2)
    (CoefQbarTensor D l hl Ω X)
  exact (congrArg (fun F ↦ BilinearCoefficientDescent.IsDescent (tensorFamily D l hl Ω X)
    (Padic.finiteCoefficientCompositum l Ω)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
    (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2) F)
      (tensor_model_eq D l hl Ω X)).mpr
    (BilinearCoefficientDescent.explicitDescent_spec (tensorFamily D l hl Ω X)
      (Padic.finiteCoefficientCompositum l Ω)
      (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).1)
      (fun E L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 E L).2))

end WeilConjectures.CoefQbarVerdier
