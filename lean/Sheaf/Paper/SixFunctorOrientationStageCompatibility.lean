/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.SixFunctorOrientationHigherPair

/-!
# Coherent six-functor orientations

Source: main-20261015, sec-six-functors/sk-def-sf-orientation/def-sf-orientation.md
(blueprint: def-sf-orientation-stage-compatibility).

The two comparison arrows below are counit transposes. In particular, an
orientation never supplies an arbitrary replacement for either arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  sixFunctorCoefficientRational sixFunctorCoefficientTensor
  sixFunctorCoefficientExchange


/-- Scalar compatibility in the recorded finite-field stage system, with the
actual root-normalized transition line. This is the A5 orientation equation.
Source: clause 3 (blueprint: def-sf-orientation-stage-compatibility). -/
def SfStageOrientationCompatible {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (S : SixFunctorCommonStages D C)
    {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E₀ ≤ L)
    (O : SfHigherOrientation (S.coefficientStages E₀))
    (O' : SfHigherOrientation (S.coefficientStages L)) : Prop :=
  @SfOrientationCoefficientCompatible D
    (fun X ↦ GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀)
    (fun X ↦ GeneralAlgebraicallyClosedCoefficients.stageCategory C.l C.Qbar X.obj.left E₀)
    (fun X ↦ GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left L)
    (fun X ↦ GeneralAlgebraicallyClosedCoefficients.stageCategory C.l C.Qbar X.obj.left L)
    (sixFunctorCoefficientRational D C S.coefficientStages E₀)
    (sixFunctorCoefficientRational D C S.coefficientStages L)
    (sixFunctorCoefficientTensor D C S.coefficientStages E₀)
    (sixFunctorCoefficientTensor D C S.coefficientStages L)
    (fun X d ↦ (sfRationalConstructibleLocalization C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left).obj
        (sfOrientationIntegralLineOn D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X d))
    (fun X d ↦ (sfRationalConstructibleLocalization C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left).obj
        (sfOrientationIntegralLineOn D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X d))
    O.rationalCoordinates.twists O'.rationalCoordinates.twists
    O.rationalCoordinates.exchange O'.rationalCoordinates.exchange
    O.rational O'.rational
    (fun X ↦ (GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left).T h)
    (S.coefficientTransition h) (sfOrientationStageScalarLine D C h)


end WeilConjectures
