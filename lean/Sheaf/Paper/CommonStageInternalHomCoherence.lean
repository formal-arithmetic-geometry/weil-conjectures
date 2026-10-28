/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.Paper.CommonStageInternalHomData

/-! The missing normalized Hom comparison coherence for common-stage transport.
Source: the common-stage internal-Hom paragraph of def-weil-derived-pullback-tensor-hom.
(blueprint: lem-weil-common-stage-internal-hom-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open Opposite CategoryTheory AlgebraicGeometry

namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  rationalDerivedInternalHom sfRationalScalarExtension ScalarLocalization.category
  ObjectProperty.FullSubcategory.category StageSystem.PairCategory.mkHom
  commonStageHomComparison

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  commonStageHomObject commonStageHomPairAtStage

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (W : Scheme.{u})

namespace CommonStageInternalHom

variable (P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
  (L : Index l Ω)
  (h : (commonStageHomObject l Ω W P).stage ≤ L)
  (h' : (commonStageHomObject l Ω W Q).stage ≤ L)
  (a : (commonStageHomPairAtStage l Ω W Q L h').obj.1.unop ⟶
    (commonStageHomPairAtStage l Ω W P L h).obj.1.unop)
  (b : (commonStageHomPairAtStage l Ω W P L h).obj.2 ⟶
    (commonStageHomPairAtStage l Ω W Q L h').obj.2)

/-- The normalized Hom comparison square at one coefficient extension.
Source: the common-stage internal-Hom paragraph of def-weil-derived-pullback-tensor-hom;
lem-pur-integral-operations-scalar-extension supplies the scalar Hom tower and naturality.
(blueprint: lem-weil-common-stage-internal-hom-coherence).

Proof: expand each comparison into its operation-stage transition, normalized rational Hom
comparison, and the two recorded stage associators. The scalar Hom tower equation and its
naturality identify the middle square; functoriality of derived internal Hom cancels the
inverse first associator and forward second associator. The remaining operation-stage
transition and stage-system associators are exactly the displayed transport isomorphisms. -/
theorem commonStageHomComparison_hom_square
    (M : Index l Ω) (k : L ≤ M) :
    let cP_L := commonStageHomComparison l Ω W P L h
    let cQ_L := commonStageHomComparison l Ω W Q L h'
    let cP_M := commonStageHomComparison l Ω W P M (h.trans k)
    let cQ_M := commonStageHomComparison l Ω W Q M (h'.trans k)
    ((stageSystem l Ω W).assoc h k).inv.app
          (commonStageHomObject l Ω W P).obj ≫
      ((stageSystem l Ω W).T k).map
        (cP_L.hom ≫
          (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).map
            (ObjectProperty.homMk
              (X := commonStageHomPairAtStage l Ω W P L h)
              (Y := commonStageHomPairAtStage l Ω W Q L h') (Prod.mkHom a.op b)) ≫
          cQ_L.inv) ≫
      ((stageSystem l Ω W).assoc h' k).hom.app
          (commonStageHomObject l Ω W Q).obj =
    cP_M.hom ≫
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω M) W).map
        (ObjectProperty.homMk
          (X := commonStageHomPairAtStage l Ω W P M (h.trans k))
          (Y := commonStageHomPairAtStage l Ω W Q M (h'.trans k))
          (Prod.mkHom ((stageSystem l Ω W).tr k a).op
            ((stageSystem l Ω W).tr k b))) ≫
      cQ_M.inv := by
  sorry

end CommonStageInternalHom
end WeilConjectures
