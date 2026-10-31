/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionEvaluationFactors
public import WeilConjectures.SixFunctors.FixProjectionCompactification.Coordinates.IntegralProjectionCoordinateData

/-! # Lifting evaluated tensor coordinates through the full finite inclusion

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
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf

/-- The natural reduction/evaluation identification on constructible inputs.
Source: reductionEvaluation of the coefficient calculus
(blueprint: lem-sf-integral-projection-tensor-evaluation). -/
def reductionSystemEvaluation (X : SixFunctorSpace D) :
    ((sfIntegralConstructible C.l E X.obj.left).ι ⋙
      (calculus C.l E X.obj.left).reduction) ⋙ evaluation (C := C) (E := E) m X ≅
    reduction d m X ⋙ finiteInclusion (C := C) (E := E) m X :=
  Functor.isoWhiskerLeft (sfIntegralConstructible C.l E X.obj.left).ι
    ((calculus C.l E X.obj.left).reductionEvaluation m)

/-- Explicit tensor evaluation before lifting through the finite inclusion.
Source: datum tensor reduction, system tensor evaluation, and reduction evaluation
(blueprint: lem-sf-integral-projection-tensor-evaluation). -/
def tensorEvaluationComparison (hl : IsUnit (C.l : D.k))
    (b : SystemTensorEvaluation (C := C) (E := E) m) (X : SixFunctorSpace D) :
    (Functor.uncurry.obj (d.higher.integralTensor X) ⋙ reduction d m X) ⋙
        finiteInclusion (C := C) (E := E) m X ≅
      ((reduction d m X ⋙ finiteInclusion (C := C) (E := E) m X).prod
        (reduction d m X ⋙ finiteInclusion (C := C) (E := E) m X)) ⋙
          evaluatedTensor (C := C) (E := E) m X :=
  Functor.isoWhiskerLeft (Functor.uncurry.obj (d.higher.integralTensor X))
      (reductionSystemEvaluation d m X).symm ≪≫
    Functor.isoWhiskerRight
      (FixProjectionCompactification.Coordinates.datumTensorReductionIso D C E
        d.higher hl X) (evaluation (C := C) (E := E) m X) ≪≫
    Functor.isoWhiskerLeft
      (((sfIntegralConstructible C.l E X.obj.left).ι ⋙
        (calculus C.l E X.obj.left).reduction).prod
          ((sfIntegralConstructible C.l E X.obj.left).ι ⋙
            (calculus C.l E X.obj.left).reduction)) (b X) ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (reductionSystemEvaluation d m X) (reductionSystemEvaluation d m X))
      (evaluatedTensor (C := C) (E := E) m X)

/-- The target partial tensor has exactly the ambient tensor after full inclusion.
Source: currying counit and the definition of the partial tensor
(blueprint: lem-sf-integral-projection-tensor-evaluation). -/
def partialTensorEvaluation (X : SixFunctorSpace D) :
    (((reduction d m X).prod (torReduction d m X)) ⋙
      Functor.uncurry.obj (CompactSupportFiniteProjection.partialTensor (stage d m) X)) ⋙
        finiteInclusion (C := C) (E := E) m X ≅
      ((reduction d m X ⋙ finiteInclusion (C := C) (E := E) m X).prod
        (reduction d m X ⋙ finiteInclusion (C := C) (E := E) m X)) ⋙
          evaluatedTensor (C := C) (E := E) m X :=
  let F := (intrinsicFiniteTorsionConstructible C.l E (m + 1)
    (Nat.le_add_left 1 m) X.obj.left).lift
      (((finiteInclusion (C := C) (E := E) m X).prod
        (finiteTorConstructible C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left).ι) ⋙
          evaluatedTensor (C := C) (E := E) m X)
      (fun KL ↦ (CompactSupportFiniteProjection.domains (stage d m)).1 X KL.1 KL.2)
  Functor.isoWhiskerLeft ((reduction d m X).prod (torReduction d m X))
    (Functor.isoWhiskerRight (Functor.currying.counitIso.app F)
      (finiteInclusion (C := C) (E := E) m X))

/-- Any ambient system tensor evaluation lifts naturally to the finite constructible
category. The comparison is a construction from b; no witness of an existence theorem
is used to define it. Source: fullness and faithfulness of an object-property inclusion
(blueprint: lem-sf-integral-projection-tensor-evaluation). -/
def liftedTensorEvaluation (hl : IsUnit (C.l : D.k))
    (b : SystemTensorEvaluation (C := C) (E := E) m) : TensorComparison d m :=
  fun X ↦ Functor.fullyFaithfulCancelRight (finiteInclusion (C := C) (E := E) m X)
    (tensorEvaluationComparison d m hl b X ≪≫ (partialTensorEvaluation d m X).symm)

/-- The lifted tensor comparison maps to its explicit ambient composite.
Source: the full inclusion's preimage identity
(blueprint: lem-sf-integral-projection-tensor-evaluation). -/
theorem liftedTensorEvaluation_hom (hl : IsUnit (C.l : D.k))
    (b : SystemTensorEvaluation (C := C) (E := E) m) (X : SixFunctorSpace D)
    (K L : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (finiteInclusion (C := C) (E := E) m X).map
        ((tensorCoordinates d m (liftedTensorEvaluation d m hl b)) X K L).hom =
      (tensorEvaluationComparison d m hl b X).hom.app (K, L) := by
  change (finiteInclusion (C := C) (E := E) m X).map
    ((finiteInclusion (C := C) (E := E) m X).preimage
      ((tensorEvaluationComparison d m hl b X).hom.app (K, L) ≫
        (partialTensorEvaluation d m X).inv.app (K, L))) = _
  rw [Functor.map_preimage]
  change (tensorEvaluationComparison d m hl b X).hom.app (K, L) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The tensor coordinate equation is forced by the explicit lift, independently of
support or projection. Source: cancellation of reductionEvaluation with its inverse
(blueprint: lem-sf-integral-projection-tensor-evaluation). -/
theorem liftedTensorEvaluation_square (hl : IsUnit (C.l : D.k))
    (b : SystemTensorEvaluation (C := C) (E := E) m) (X : SixFunctorSpace D)
    (K L : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (evaluation (C := C) (E := E) m X).map
        (FixProjectionCompactification.Coordinates.datumTensorReduction
          D C E d.higher hl X K L).hom ≫
      (b X).hom.app ((calculus C.l E X.obj.left).reduction.obj K.obj,
        (calculus C.l E X.obj.left).reduction.obj L.obj) ≫
      (evaluatedTensor (C := C) (E := E) m X).map
        (Prod.mkHom (reductionEvaluation d m X K).hom (reductionEvaluation d m X L).hom) =
    (reductionEvaluation d m X (((d.higher.integralTensor X).obj K).obj L)).hom ≫
      (finiteInclusion (C := C) (E := E) m X).map
        ((tensorCoordinates d m (liftedTensorEvaluation d m hl b)) X K L).hom := by
  rw [liftedTensorEvaluation_hom]
  simp only [Functor.comp_obj, Functor.uncurry_obj_obj, ObjectProperty.ι_obj, Functor.prod_obj,
    FixProjectionCompactification.Coordinates.datumTensorReduction, Iso.app_hom,
    reductionEvaluation, Functor.uncurry_obj_map, tensorEvaluationComparison,
    reductionSystemEvaluation, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_twice, Functor.isoWhiskerRight_hom,
    NatIso.prod_hom, Category.assoc, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.whiskerRight_app,
    NatTrans.prod_app_fst, NatTrans.prod_app_snd, Category.id_comp]
  change _ =
    (reductionEvaluation d m X (((d.higher.integralTensor X).obj K).obj L)).hom ≫
      𝟙 _ ≫
        (reductionEvaluation d m X (((d.higher.integralTensor X).obj K).obj L)).inv ≫ _
  rw [Category.id_comp, Iso.hom_inv_id_assoc]

/-- Inclusion commutes with a morphism in the first variable of partial tensor.
Source: the restriction and currying definitions
(blueprint: lem-sf-integral-projection-tensor-evaluation). -/
theorem partialTensor_map_left (X : SixFunctorSpace D)
    {K K' : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X}
    (a : K ⟶ K')
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left) :
    (evaluatedTensor (C := C) (E := E) m X).map
        (Prod.mkHom ((finiteInclusion (C := C) (E := E) m X).map a) (𝟙 L.obj)) =
      (finiteInclusion (C := C) (E := E) m X).map
        (((CompactSupportFiniteProjection.partialTensor (stage d m) X).map a).app L) := by
  rfl

/-- Inclusion commutes with a morphism in the second variable of partial tensor.
Source: the restriction and currying definitions
(blueprint: lem-sf-integral-projection-tensor-evaluation). -/
theorem partialTensor_map_right (X : SixFunctorSpace D)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    {L L' : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left}
    (a : L ⟶ L') :
    (evaluatedTensor (C := C) (E := E) m X).map
        (Prod.mkHom (𝟙 K.obj)
          ((finiteTorConstructible C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left).ι.map a)) =
      (finiteInclusion (C := C) (E := E) m X).map
        (((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj K).map a) := by
  rfl

end WeilConjectures.IntegralProjectionReduction
