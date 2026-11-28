/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCommonClosedExistence
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationABase
import WeilConjectures.PoincareDuality.Pod.PodCommonInverseTransposeTransition
import WeilConjectures.PoincareDuality.Pod.PodRationalClosedScalar
import WeilConjectures.PoincareDuality.Pod.PodRationalClosedHomNaturality
import WeilConjectures.SmoothPurity.Common.CommonStageTensorEndpoint
import WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all WeilConjectures.SmoothPurity.CommonStageInternalHom.CommonStageInternalHomCoherence
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

/-! # Stage transitions of conjugated normalized rational inverse transposition

For a family of rational closed data with the pure-tensor normalization at every finite
coefficient stage, the stage transitions carry the conjugated inverse transposition at a
finite stage to the conjugated inverse transposition at every larger finite stage.

## Main statements

* `commonStageInverseTranspose_transition`: the stage-transition equation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard

section CommonClosed
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients
open TensorProduct
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- For a family of rational closed data with the pure-tensor normalization, the stage
transitions carry the conjugated stage inverse transposition at a finite stage to the
conjugated stage inverse transposition at every larger finite stage. -/
theorem commonStageInverseTranspose_transition
    (R : ∀ F : Index l Ω, PodPartialClosed (rationalDerivedTensor l (Coefficient.{u} l Ω F) W)
      (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) W)
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) W))
    (hR : ∀ (F : Index l Ω) (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) W)
      (P : (constructibleRationalHomPairs l (Coefficient.{u} l Ω F) W).FullSubcategory)
      (f : K.obj ⟶ (constructibleIntegralHom l (Coefficient.{u} l Ω F) W).obj
        (integralPairOfRationalHomPair l (Coefficient.{u} l Ω F) W P))
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω F)))
      (q : K ⟶ (rationalDerivedInternalHom l (Coefficient.{u} l Ω F) W).obj P),
      HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω F)] f) →
      HEq (((R F).transpose K P).symm q)
        (a ⊗ₜ[Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω F)]
          ((podIntegralClosed l (Coefficient.{u} l Ω F) W).transpose K.obj
            (integralPairOfRationalHomPair l (Coefficient.{u} l Ω F) W P)).symm f))
    (L : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (P : (commonStageHomPairs l Ω W).FullSubcategory) (F F' : Index l Ω) (k : F ≤ F')
    (hL : L.stage ≤ F) (hP : (commonStageHomObject l Ω W P).stage ≤ F)
    (hT : (commonStageTensorObject l Ω W L P.obj.1.unop).stage ≤ F) (hN : P.obj.2.stage ≤ F)
    (φ : L.toStage hL ⟶ (commonStageHomObject l Ω W P).toStage hP) :
    (stageSystem l Ω W).tr k (commonStageInverseTranspose l Ω W R L P F hL hP hT hN φ) =
      commonStageInverseTranspose l Ω W R L P F' (hL.trans k) (hP.trans k) (hT.trans k)
        (hN.trans k) ((stageSystem l Ω W).tr k φ) := by
  refine inverseTranspose_transition_of_scalar (R F) (R F')
    (podRationalClosed_symm_comp_map l (Coefficient.{u} l Ω F') W (R F') (hR F'))
    ((stageSystem l Ω W).T k) (transition l Ω W F F' k) (operationStageTransitionIso l Ω W F F' k)
    (L.toStage hL) (commonStageHomPairAtStage l Ω W P F hP) _ _ (L.toStage (hL.trans k))
    (commonStageHomPairAtStage l Ω W P F' (hP.trans k)) _ _
    (rationalHomScalarPair_permitted l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω F')
      (coefficientInclusion l Ω F F' k) W (commonStageHomPairAtStage l Ω W P F hP))
    (commonStageTensorComparison l Ω W L P.obj.1.unop F hT)
    (commonStageHomComparison l Ω W P F hP)
    (commonStageTensorComparison l Ω W L P.obj.1.unop F' (hT.trans k))
    (commonStageHomComparison l Ω W P F' (hP.trans k))
    (((stageSystem l Ω W).assoc hL k).app L.obj)
    (((stageSystem l Ω W).assoc (((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).1.trans hP) k).app P.obj.1.unop.obj)
    (((stageSystem l Ω W).assoc hN k).app P.obj.2.obj)
    (((stageSystem l Ω W).assoc hT k).app (commonStageTensorObject l Ω W L P.obj.1.unop).obj)
    (((stageSystem l Ω W).assoc hP k).app (commonStageHomObject l Ω W P).obj)
    ((rationalTensorScalarComparison l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω F')
      (coefficientInclusion l Ω F F' k) W).app _)
    (rationalHomScalarComparison l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω F')
      (coefficientInclusion l Ω F F' k) W (commonStageHomPairAtStage l Ω W P F hP))
    (CommonStageInternalHom.pairStep l Ω W P F hP F' k).hom ?_ ?_ ?_ ?_ ?_ φ
  · exact (CommonStageInternalHom.inputStep l Ω W P.obj.1.unop
      (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans hP) k).hom_inv_id
  · rfl
  · intro ψ
    exact podRationalClosed_scalar_symm l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω F')
      (coefficientInclusion l Ω F F' k) W (R F) (hR F) (R F') (hR F') (L.toStage hL)
      (commonStageHomPairAtStage l Ω W P F hP) ψ
  · exact stageComparison_scalar_tower (stageSystem l Ω W)
      (fun F ↦ rationalDerivedTensor l (Coefficient.{u} l Ω F) W)
      (fun h ↦ rationalTensorStageComparison l Ω W h)
      (fun h h' X Y ↦ rationalTensorStageComparison_coherent l Ω W h h' X Y)
      ((Padic.finiteCoefficientFields_properties l Ω).1 L.stage P.obj.1.unop.stage).1
      ((Padic.finiteCoefficientFields_properties l Ω).1 L.stage P.obj.1.unop.stage).2
      hT k L.obj P.obj.1.unop.obj
      (commonStageTensorComparison l Ω W L P.obj.1.unop F hT)
      (congrArg Iso.hom (commonStageTensor_endpoint l Ω W L P.obj.1.unop F hT)).symm
      (commonStageTensorComparison l Ω W L P.obj.1.unop F' (hT.trans k))
      (congrArg Iso.hom
        (commonStageTensor_endpoint l Ω W L P.obj.1.unop F' (hT.trans k))).symm
      (transition l Ω W F F' k) (operationStageTransitionIso l Ω W F F' k)
      (rationalTensorScalarComparison l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω F')
        (coefficientInclusion l Ω F F' k) W) (fun _ _ ↦ rfl)
  · exact CommonStageInternalHom.comparison_tower l Ω W P F hP F' k

end CommonClosed

end WeilConjectures
