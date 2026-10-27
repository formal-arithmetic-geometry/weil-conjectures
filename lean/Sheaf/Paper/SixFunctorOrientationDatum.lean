/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.SixFunctorOrientationStageCompatibility

/-!
# Coherent six-functor orientations

Source: main-20261015, sec-six-functors/sk-def-sf-orientation/def-sf-orientation.md
(blueprint: def-sf-orientation-geometric-family).

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


/-- Common-stage coordinates and their geometric family, compared with the
least finite coefficient field through its actual A5 functor.
Source: clause 3 (blueprint: def-sf-orientation-geometric-family). -/
structure SfOrientationCommonFamily {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (S : SixFunctorCommonStages D C)
    (coefficients : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      SfHigherOrientation (S.coefficientStages E₀)) where
  commonCoordinates : @SfOrientationImageCoordinates D
    (fun X ↦ GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left
      (Padic.finiteCoefficientBase C.l C.Qbar))
    (fun X ↦ GeneralAlgebraicallyClosedCoefficients.stageCategory C.l C.Qbar X.obj.left
      (Padic.finiteCoefficientBase C.l C.Qbar))
    (fun X ↦ generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
    (fun _ ↦ inferInstance)
    (sixFunctorCoefficientRational D C S.coefficientStages
      (Padic.finiteCoefficientBase C.l C.Qbar)) S.commonStage
    (sixFunctorCoefficientTensor D C S.coefficientStages
      (Padic.finiteCoefficientBase C.l C.Qbar)) S.commonStageTensor
    (fun X d ↦ (sfRationalConstructibleLocalization C.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar
        (Padic.finiteCoefficientBase C.l C.Qbar)) X.obj.left).obj
          (sfOrientationIntegralLineOn D C
            (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar
              (Padic.finiteCoefficientBase C.l C.Qbar)) X d))
    (coefficients (Padic.finiteCoefficientBase C.l C.Qbar)).rationalCoordinates.twists
    (fun X ↦ GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := X.obj.left)
        (Padic.finiteCoefficientBase C.l C.Qbar))
    (S.commonStageComparison (Padic.finiteCoefficientBase C.l C.Qbar))
    (sixFunctorCoefficientExchange D C S.coefficientStages
      (Padic.finiteCoefficientBase C.l C.Qbar))
    S.commonStageExchange
    (S.commonStageExchangeComparison (Padic.finiteCoefficientBase C.l C.Qbar))
  common : SfGeometricOrientation commonCoordinates.twists commonCoordinates.exchange

  commonCompatibility : SfOrientationCoefficientCompatible
    (B := fun X ↦ GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left
      (Padic.finiteCoefficientBase C.l C.Qbar))
    (B' := fun X ↦ generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
    (S := sixFunctorCoefficientRational D C S.coefficientStages
      (Padic.finiteCoefficientBase C.l C.Qbar)) (S' := S.commonStage)
    (tensor := sixFunctorCoefficientTensor D C S.coefficientStages
      (Padic.finiteCoefficientBase C.l C.Qbar)) (tensor' := S.commonStageTensor)
    (coefficients (Padic.finiteCoefficientBase C.l C.Qbar)).rational common
    (S.commonStageComparison (Padic.finiteCoefficientBase C.l C.Qbar))
    (fun _ _ ↦ Iso.refl _)

/-- The full higher family and its finite-field transition equations.
Source: higher-stage clauses 1-3 (blueprint: def-sf-orientation-geometric-family). -/
structure SfOrientationHigherFamily {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) where
  higher : SfHigherOrientation S.higher
  coefficients : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    SfHigherOrientation (S.closure.coefficientStages E₀)
  commonFamily : SfOrientationCommonFamily S.closure coefficients
  scalarCompatibility : ∀ {E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E₀ ≤ L),
    SfStageOrientationCompatible S.closure h (coefficients E₀) (coefficients L)

/-- The common geometric family of the full higher datum.
Source: common-stage clause 3 (blueprint: def-sf-orientation-geometric-family). -/
def SfOrientationHigherFamily.common {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} (O : SfOrientationHigherFamily S) :=
  O.commonFamily.common

end WeilConjectures
