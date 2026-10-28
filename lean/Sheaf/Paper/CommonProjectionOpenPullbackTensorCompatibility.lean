/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: SHEAF group S3
-/
module

public import Sheaf.Paper.CommonProjectionTensorComparison

/-! # Representative compatibility for the common-stage open pullback/tensor square

Source: thm-sf-pf-field.proof.md, Compatibility.
(blueprint: lem-sf-common-projection-open-pullback-tensor-forward-compatibility).

This is the concrete compatibility equation needed to apply the generic forward
transport lemma. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The finite-stage representative equation for the common-stage open square.

Source: thm-sf-pf-field.proof.md, Compatibility
(blueprint: lem-sf-common-projection-open-pullback-tensor-forward-compatibility).

Proof: normalize the rational and common tensorators and pullback comparisons,
evaluate the canonical common-stage pullback/tensor representative at the included
pair, and cancel the transition maps and scalar unit. -/
theorem commonProjectionOpenPullbackTensor_forward_compatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (H : SixFunctorCommonStages D C)
    (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (Q : SixFunctorCompactifiedSquare D)
    (M N : sfRationalConstructibleCategory C.l
      (AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar E) Q.Z.obj.left) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := Q.X.obj.left) E).map
        (((H.coefficientStages E).rationalExchange Q).openTensorPullback.hom.app M |>.app N) ≫
      (commonProjectionTensorComparison H E Q.X).hom.app
        ((H.coefficientStages E).rational.pull Q.i |>.obj M,
          (H.coefficientStages E).rational.pull Q.i |>.obj N) ≫
      (Functor.uncurry.obj (H.commonStageTensor Q.X)).map
        (Prod.mkHom
          (((H.commonStageComparison E).directAdjunction Q.i).left.hom.app M)
          (((H.commonStageComparison E).directAdjunction Q.i).left.hom.app N)) =
    (((H.commonStageComparison E).directAdjunction Q.i).left.hom.app
      ((Functor.uncurry.obj ((H.coefficientStages E).rationalTensor Q.Z)).obj (M, N))) ≫
      (H.commonStage.pull Q.i).map
        ((commonProjectionTensorComparison H E Q.Z).hom.app (M, N)) ≫
      (((H.commonStageExchange Q).openTensorPullback.hom.app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Q.Z.obj.left) E).obj M)).app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := C.Qbar) (Y := Q.Z.obj.left) E).obj N)) := by
  sorry

end WeilConjectures
