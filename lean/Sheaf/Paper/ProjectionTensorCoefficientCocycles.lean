/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum

/-! # Tensor coefficient comparison cocycles

Source: current blueprint, thm-sf-pf-field, Compatibility, and the field-stage
transport paragraph of fix-prop-projection-formula. This predicate spells out the
identity, tower and common-stage inclusion equations for the recorded tensor
comparison isomorphisms, without changing the six-functor operation datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.SuppliedExchangeProjection
open scoped CategoryTheory.Functor
namespace WeilConjectures.ProjectionCoefficient

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The tensor identity, tower and inclusion equations of the specified scalar comparisons.
Source: def-exchange-projection, identity/tower paragraph
(blueprint: def-sf-projection-tensor-coefficient-cocycles). -/
def TensorCoherence {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) : Prop :=
  (∀ (Q : SixFunctorCompactifiedSquare D) (X : SixFunctorSpace D),
    ExchangeProjectionScalarCocycle
      (fun E ↦ Stage C.l C.Qbar X.obj.left E × Stage C.l C.Qbar X.obj.left E)
      (fun E ↦ Stage C.l C.Qbar X.obj.left E)
      (fun E ↦ Functor.uncurry.obj
        (sixFunctorCoefficientTensor D C A.coefficientStages E X))
      (fun _ _ h ↦ ((stageSystem C.l C.Qbar X.obj.left).T h).prod
        ((stageSystem C.l C.Qbar X.obj.left).T h))
      (fun _ _ h ↦ (stageSystem C.l C.Qbar X.obj.left).T h)
      (fun E ↦ NatIso.prod (sixFunctorStageUnitor D C X E)
        (sixFunctorStageUnitor D C X E))
      (sixFunctorStageUnitor D C X)
      (fun _ _ _ h h' ↦ NatIso.prod ((stageSystem C.l C.Qbar X.obj.left).assoc h h')
        ((stageSystem C.l C.Qbar X.obj.left).assoc h h'))
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar X.obj.left).assoc h h')
      (fun _ _ h ↦ (A.coefficientExchangeComparison h Q).tensor X)) ∧
  (∀ (Q : SixFunctorCompactifiedSquare D) (X : SixFunctorSpace D)
    (E F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F)
    (M N : Stage C.l C.Qbar X.obj.left E),
    (Functor.uncurry.obj (A.commonStageTensor X)).map
        (Prod.mkHom (((stageSystem C.l C.Qbar X.obj.left).transIso h).hom.app M)
          (((stageSystem C.l C.Qbar X.obj.left).transIso h).hom.app N)) ≫
        ((A.commonStageExchangeComparison E Q).tensor X).inv.app (M, N) =
      ((A.commonStageExchangeComparison F Q).tensor X).inv.app
          (((stageSystem C.l C.Qbar X.obj.left).T h).obj M,
            ((stageSystem C.l C.Qbar X.obj.left).T h).obj N) ≫
        (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).map
          (((A.coefficientExchangeComparison h Q).tensor X).inv.app (M, N)) ≫
        ((stageSystem C.l C.Qbar X.obj.left).transIso h).hom.app
          ((sixFunctorCoefficientTensor D C A.coefficientStages E X).obj M |>.obj N))


end WeilConjectures.ProjectionCoefficient
