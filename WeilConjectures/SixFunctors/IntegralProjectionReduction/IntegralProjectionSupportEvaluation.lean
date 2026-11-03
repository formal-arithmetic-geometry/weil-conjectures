/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionEvaluationFactors
public import WeilConjectures.SixFunctors.FixProjectionCompactification.Coordinates.IntegralProjectionCoordinateData
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralSupportAdjunctFiniteCoordinates

/-! # Unary support-adjunction evaluation

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open IntegralSystemRealization

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (d : SixFunctorOperationDatum D C E n hn) (m : ℕ)

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

/-- Evaluation of the actual support adjunct agrees with the datum's specified
finite support comparison, before tensoring with a second input.

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions;
Stacks 0941, the reduction/limit adjunction and its projection equations.
(blueprint: lem-sf-integral-projection-support-evaluation).

Proof: specialize integralSupportCounitProjection to the canonical reduced input.
Write supportReduction as reduction of supportValue inverse followed by the
reconstruction counit. The calculus's counit_projection identifies its evaluation
with the finite scalar-adjunction transpose of the actual system-limit projection.
Expand supportValue into proper/limit conjugation, the open reduction mate, inverse
reconstruction unit, and the qcqs support realization. Direct evaluation carries the
proper counit to the finite counit; the openEvaluation transpose identifies the open
factor with the canonical open scalar mate. The reconstruction triangle cancels its
unit. The projection normalization of sfQcqsCompactSupportRealization identifies the
remaining scalar mate with sfCompactSupportChosenReduction. Finally supportProjection
of d.integralNormalization identifies precisely this map with supportAdjunction.left,
after its finiteSupport realization. Cancel that realization to obtain the equation.
This comparison uses one input only and includes the zero input and identity/empty
opens; at m=0 the same projection equation is the residue quotient equation. -/
theorem integralProjectionSupportEvaluation
    (hl : IsUnit (C.l : D.k)) (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (evaluation (C := C) (E := E) m Y).map
        (FixProjectionCompactification.Coordinates.supportReduction
          D C E d.higher hl o z f c K) ≫
      (evaluatedSupport d m o f c K).hom =
    (reductionEvaluation d m Y ((d.higher.integral.support f c).obj K)).hom ≫
      (finiteInclusion (C := C) (E := E) m Y).map
        (((d.integralNormalization.reduction m).supportAdjunction f c).left.hom.app K) := by
  have h := FixProjectionCompactification.integralSupportAdjunctFiniteCoordinates
    D C E n hn d hl o z f c K m
  have h' := congrArg
    (fun v ↦ v ≫ ((stage d m).finiteSupport f c).inv.app ((reduction d m X).obj K)) h
  simpa only [evaluatedSupport, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, reductionEvaluation, stage, reduction, evaluation, finiteInclusion,
    ObjectProperty.ι_map, ObjectProperty.ι_obj, Functor.comp_obj, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id] using h'

end WeilConjectures.IntegralProjectionReduction
