/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Common.CommonStageInternalHomData

/-! # Literal common-stage pullback data

The common-stage pullback of an algebraically closed constructible coefficient object, and its
comparison with rational pullback at any larger coefficient stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory AlgebraicGeometry

namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionAbsoluteValue rationalDerivedPullback sfRationalScalarExtension
  operationStageTransitionIso ObjectProperty.FullSubcategory.category

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

-- Match the transported structures on the small coefficient models.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Common-stage pullback of an object `P` at stage `L` is the rational
pullback of `P` with coefficients in `L`, at the same stage `L`. -/
def commonStagePullbackObject {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  ⟨P.stage, (rationalDerivedPullback l (Coefficient.{u} l Ω P.stage) f).obj P.obj⟩

/-- The canonical pullback comparison at a larger stage `L`: the transport of
`commonStagePullbackObject f P` to `L` is isomorphic to the rational pullback of the transport of
`P` to `L`, via the stage-transition identifications. -/
def commonStagePullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : Index l Ω) (h : P.stage ≤ L) :
    (commonStagePullbackObject l Ω f P).toStage h ≅
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).obj (P.toStage h) :=
  (operationStageTransitionIso l Ω X P.stage L h).app
      (commonStagePullbackObject l Ω f P).obj ≪≫
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω P.stage)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h) f).app P.obj ≪≫
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).mapIso
      ((operationStageTransitionIso l Ω Y P.stage L h).app P.obj).symm

end WeilConjectures
