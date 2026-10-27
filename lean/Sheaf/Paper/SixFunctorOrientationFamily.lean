/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module
public import Sheaf.Paper.SixFunctorOrientationFiniteFamily

/-! # Full coherent orientation datum
Source: def-sf-orientation (blueprint: def-sf-orientation).
The finite line is presented as the reduction of the completed line. Its comparison
with the ordinary root line is the uniquely normalized comparison, not input data.
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
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  sixFunctorCoefficientRational sixFunctorCoefficientTensor sixFunctorCoefficientExchange

/-- The common-stage line comparison from any finite coefficient field. It uses
the actual stage-system transition and the normalized scalar comparison on the
completed line before localization.
Source: common-stage part of clause 3 (blueprint: def-sf-orientation). -/
def sfOrientationCommonLine (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (L : Padic.FiniteCoefficientFields C.l C.Qbar) (X : SixFunctorSpace D) (d : ℕ) :=
  ((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left).isoToStage
    ((GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := X.obj.left)
      (Padic.finiteCoefficientBase C.l C.Qbar)).obj
        ((sfRationalConstructibleLocalization C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar
            (Padic.finiteCoefficientBase C.l C.Qbar)) X.obj.left).obj
              (sfOrientationIntegralLineOn D C
                (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar
                  (Padic.finiteCoefficientBase C.l C.Qbar)) X d)))
    (RationalSmoothPurityCanonical.base_le C.l C.Qbar L) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) L).mapIso
        (sfOrientationStageScalarLine D C
          (RationalSmoothPurityCanonical.base_le C.l C.Qbar L) X d)).symm

/-- A full orientation datum is the coherent family, not a single purity iso.
The completed, rational, common-stage, finite and etale components are retained.
Finite geometry is read through its faithful etale realization, and all integral
finite reductions agree with the actual A5 right-adjoint comparison. Consequently
finite-to-finite quotient comparisons have the same root-normalized transposes.
Affine normalization at integral coefficients is precisely these finite
normalizations; the rational and common normalizations are their scalar images.
No existence assertion for this record is made.
Source: every clause of def-sf-orientation (blueprint: def-sf-orientation). -/
structure SfOrientationDatum {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {m : ℕ}
    (S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))) where
  higher : SfOrientationHigherFamily S
  commonCompatibility : ∀ L : Padic.FiniteCoefficientFields C.l C.Qbar,
    @SfOrientationCoefficientCompatible D
      (fun X ↦ GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left L)
      (fun X ↦ GeneralAlgebraicallyClosedCoefficients.stageCategory C.l C.Qbar X.obj.left L)
      (fun X ↦ generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
      (fun _ ↦ inferInstance)
      (sixFunctorCoefficientRational D C S.closure.coefficientStages L)
      S.closure.commonStage
      (sixFunctorCoefficientTensor D C S.closure.coefficientStages L)
      S.closure.commonStageTensor
      (fun X d ↦ (sfRationalConstructibleLocalization C.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X.obj.left).obj
          (sfOrientationIntegralLineOn D C
            (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar L) X d))
      (fun X d ↦ (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := X.obj.left)
          (Padic.finiteCoefficientBase C.l C.Qbar)).obj
            ((sfRationalConstructibleLocalization C.l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar
                (Padic.finiteCoefficientBase C.l C.Qbar)) X.obj.left).obj
                  (sfOrientationIntegralLineOn D C
                    (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar
                      (Padic.finiteCoefficientBase C.l C.Qbar)) X d)))
      (higher.coefficients L).rationalCoordinates.twists
      higher.commonFamily.commonCoordinates.twists
      (higher.coefficients L).rationalCoordinates.exchange
      higher.commonFamily.commonCoordinates.exchange
      (higher.coefficients L).rational higher.common
      (fun X ↦ GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) L)
      (S.closure.commonStageComparison L) (sfOrientationCommonLine D C L)
  finite : ∀ a : ℕ, SfFiniteOrientation (S.integralNormalization.finiteLevels a)
  finiteCompatibility : ∀ a : ℕ,
    SfIntegralFiniteOrientationCompatible S.integralNormalization higher.higher a (finite a)
  coefficientFinite : ∀ (L : Padic.FiniteCoefficientFields C.l C.Qbar) (a : ℕ),
    SfFiniteOrientation ((S.coefficientIntegralNormalization L).finiteLevels a)
  coefficientFiniteCompatibility : ∀ (L : Padic.FiniteCoefficientFields C.l C.Qbar) (a : ℕ),
    SfIntegralFiniteOrientationCompatible (S.coefficientIntegralNormalization L)
      (higher.coefficients L) a (coefficientFinite L a)
  primary : SfFiniteOrientation S.toSixFunctorFiniteOperations
  primaryEtale : ∀ (r : ℕ)
    (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0),
    primary.etale r hA = (finite m).etale r hA

end WeilConjectures
