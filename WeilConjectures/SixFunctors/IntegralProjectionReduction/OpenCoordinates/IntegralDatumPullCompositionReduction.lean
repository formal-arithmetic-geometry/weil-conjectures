/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.ProperCoordinates.IntegralProperProjectionCoefficientData
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionPullEvaluation
import WeilConjectures.SixFunctors.Integral.IntegralReductionJointFaithfulness
import WeilConjectures.SmoothPurity.IntegralSystemRealization.SystemPullbackCompositorEvaluation

/-! # Whole-system coefficient coordinates for the datum pullback compositor

Source: prop-sf-pf-coherence.proof.md, composition in the mate construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction.OpenCoordinates
open IntegralSystemRealization ProperCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

attribute [local implicit_reducible] integralCoefficientSheaf
  scalarReductionSourceDerived scalarReductionTargetDerived integralTowerHasDerivedCategory
  coefficientFiniteHasDerived
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  sixFunctorFinitePullback sixFunctorIntegralReduction coefficientFiniteDerivedExtension
  scalarReductionDerivedExtension

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  SheafOfModules.instAbelian

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

private def finitePullReduction (S : SixFunctorOperationDatum D C E n hn) (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) :
    S.higher.integral.pull f ⋙ reduction S m X ⋙ finiteInclusion (C := C) (E := E) m X ≅
      reduction S m Y ⋙ finiteInclusion (C := C) (E := E) m Y ⋙
        finiteDerivedPullback C.l E m f.hom.left :=
  Functor.isoWhiskerRight ((S.integralNormalization.reduction m).directAdjunction f).left
      (finiteInclusion (C := C) (E := E) m X) ≪≫
    Functor.isoWhiskerLeft (reduction S m Y) ((stage S m).finitePullback f)

private theorem finitePullReduction_comp (S : SixFunctorOperationDatum D C E n hn)
    (m : ℕ) {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : sfIntegralConstructibleCategory C.l E Z.obj.left) :
    (finiteInclusion (C := C) (E := E) m X).map
        ((reduction S m X).map ((S.higher.integral.pullComposition f g).hom.app N)) ≫
      (finitePullReduction S m f).hom.app ((S.higher.integral.pull g).obj N) ≫
      (finiteDerivedPullback C.l E m f.hom.left).map
        ((finitePullReduction S m g).hom.app N) =
    (finitePullReduction S m (f ≫ g)).hom.app N ≫
      (Scheme.sfIntrinsicDerivedPullbackComp
        (Padic.coefficientExtensionRing C.l E (m + 1)) f.hom.left g.hom.left).hom.app
          (((reduction S m Z).obj N).obj) := by
  let T := stage S m
  let I := finiteInclusion (C := C) (E := E) m X
  have hc := congrArg I.map ((S.integralNormalization.reduction m).pullComposition f g N)
  simp only [Functor.map_comp] at hc
  have hnat := (T.finitePullback f).hom.naturality
    (((S.integralNormalization.reduction m).directAdjunction g).left.hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  simp only [finitePullReduction, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hnat, reassoc_of% hc]
  erw [T.finitePullCompositionNormalization f g ((reduction S m Z).obj N)]

private theorem pullComparison_evaluation (S : SixFunctorOperationDatum D C E n hn)
    (hl : IsUnit (C.l : D.k)) (o : Operations C.l E) (z : Realizations C.l E D o)
    (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (evaluation (C := C) (E := E) m X).map ((pullComparison S.higher hl o z f).hom.app N) ≫
      (pullbackTensorDerivedEvaluation C.l E f.hom.left m).hom.app ((reduce Y).obj N) ≫
      (finiteDerivedPullback C.l E m f.hom.left).map
        ((reductionEvaluation S m Y N).hom) =
    (reductionEvaluation S m X ((S.higher.integral.pull f).obj N)).hom ≫
      (finitePullReduction S m f).hom.app N := by
  have h := integralProjectionPullEvaluation S m hl o z f N
  have h' := congrArg (fun a ↦ a ≫
    ((stage S m).finitePullback f).hom.app ((reduction S m Y).obj N)) h
  erw [pullComparison_hom_app]
  simp only [Functor.map_comp, Iso.trans_hom, evaluatedPull, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app,
    pullIso, ObjectProperty.homMk, reduce, Functor.comp_obj, ObjectProperty.ι_obj,
    ObjectProperty.isoMk_hom, finitePullReduction, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    ObjectProperty.ι_map] at h' ⊢
  erw [Category.comp_id] at h'
  exact h'

private theorem system_composition_evaluation (o : Operations C.l E)
    (c : Compositors C.l E o) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : ℕ) (M : System C.l E Z) :
    (coefficientSequenceDerivedEvaluation C.l E X m).map ((c.pullComp f g).hom.app M) ≫
      (pullbackTensorDerivedEvaluation C.l E f m).hom.app ((pull C.l E g).obj M) ≫
      (finiteDerivedPullback C.l E m f).map
        ((pullbackTensorDerivedEvaluation C.l E g m).hom.app M) =
    (pullbackTensorDerivedEvaluation C.l E (f ≫ g) m).hom.app M ≫
      (Scheme.sfIntrinsicDerivedPullbackComp
        (Padic.coefficientExtensionRing C.l E (m + 1)) f g).hom.app
          ((coefficientSequenceDerivedEvaluation C.l E Z m).obj M) := by
  have h := systemPullbackCompositorEvaluation C.l E o c f g m M
  have h' := congrArg (fun a ↦
    (coefficientSequenceDerivedEvaluation C.l E X m).map ((c.pullComp f g).hom.app M) ≫
      a ≫ (Scheme.sfIntrinsicDerivedPullbackComp
        (Padic.coefficientExtensionRing C.l E (m + 1)) f g).hom.app
          ((coefficientSequenceDerivedEvaluation C.l E Z m).obj M)) h
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app] at h'
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h'
  exact h'.symm

set_option maxHeartbeats 800000 in
-- The finite diagram converts between two presentations of the coefficient categories.
private theorem evaluated_composition (S : SixFunctorOperationDatum D C E n hn)
    (hl : IsUnit (C.l : D.k)) (o : Operations C.l E) (z : Realizations C.l E D o)
    (m : ℕ) {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : sfIntegralConstructibleCategory C.l E Z.obj.left) :
    (evaluation (C := C) (E := E) m X).map
        ((reduce X).map ((S.higher.integral.pullComposition f g).hom.app N)) ≫
      (evaluation (C := C) (E := E) m X).map
        ((pullComparison S.higher hl o z f).hom.app ((S.higher.integral.pull g).obj N)) ≫
      (evaluation (C := C) (E := E) m X).map
        ((pull C.l E f.hom.left).map ((pullComparison S.higher hl o z g).hom.app N)) =
    (evaluation (C := C) (E := E) m X).map
        ((pullComparison S.higher hl o z (f ≫ g)).hom.app N) ≫
      (evaluation (C := C) (E := E) m X).map
        ((z.compositors.pullComp f.hom.left g.hom.left).hom.app ((reduce Z).obj N)) := by
  let F := finiteDerivedPullback C.l E m f.hom.left
  let G := finiteDerivedPullback C.l E m g.hom.left
  let M := (reduce Z).obj N
  let post := (pullbackTensorDerivedEvaluation C.l E f.hom.left m).hom.app
      ((pull C.l E g.hom.left).obj M) ≫
    F.map ((pullbackTensorDerivedEvaluation C.l E g.hom.left m).hom.app M) ≫
    F.map (G.map (reductionEvaluation S m Z N).hom)
  apply (cancel_mono post).1
  dsimp only [post]
  simp only [Category.assoc]
  have hnat := (pullbackTensorDerivedEvaluation C.l E f.hom.left m).hom.naturality
    ((pullComparison S.higher hl o z g).hom.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  erw [reassoc_of% hnat]
  erw [← F.map_comp, ← F.map_comp]
  erw [pullComparison_evaluation S hl o z m g N]
  erw [F.map_comp]
  erw [reassoc_of% (pullComparison_evaluation S hl o z m f
    ((S.higher.integral.pull g).obj N))]
  have hn := ((calculus C.l E X.obj.left).reductionEvaluation m).hom.naturality
    (((S.higher.integral.pullComposition f g).hom.app N).hom)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn, finitePullReduction_comp S m f g N]
  erw [← reassoc_of% (pullComparison_evaluation S hl o z m (f ≫ g) N)]
  have hnc := (Scheme.sfIntrinsicDerivedPullbackComp
    (Padic.coefficientExtensionRing C.l E (m + 1)) f.hom.left g.hom.left).hom.naturality
      (reductionEvaluation S m Z N).hom
  dsimp only [Functor.comp_map] at hnc
  erw [hnc]
  erw [← reassoc_of% (system_composition_evaluation o z.compositors
    f.hom.left g.hom.left m M)]
  simp only [Functor.map_comp]
  rfl

/-- Pullback composition preserves the actual quotient/counit comparison. This
statement involves only pullback, with no tensor, open extension, or projection.

Source: prop-sf-pf-coherence.proof.md, composition of mates;
proof step 2 of lem-sf-integral-projection-open-tensor-coordinates.
(blueprint: lem-sf-integral-datum-pull-composition-reduction).

Proof: use fullness of whole-system reduction on constructible integral objects
to lift the system compositor conjugated by the three pullback comparisons.
At each finite coefficient level, integralProjectionPullEvaluation identifies
the unary comparisons. Naturality, the pullComposition equation of
integralNormalization.reduction, and finitePullCompositionNormalization paste
them into the finite compositor square. The forward form of
systemPullbackCompositorEvaluation identifies its other side. Naturality of
reductionEvaluation then identifies the finite reductions of the lifted arrow
and the datum compositor. Apply integral_reductions_jointly_faithful and reduce
again, cancelling the comparison isomorphisms. No faithfulness of arbitrary
finite derived evaluation is assumed. Identity arrows, zero inputs and empty
schemes use the same maps. -/
theorem integralDatumPullCompositionReduction
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : sfIntegralConstructibleCategory C.l E Z.obj.left) :
    (reduce X).map ((S.higher.integral.pullComposition f g).hom.app N) ≫
        (pullComparison S.higher hl o z f).hom.app ((S.higher.integral.pull g).obj N) ≫
        (pull C.l E f.hom.left).map ((pullComparison S.higher hl o z g).hom.app N) =
      (pullComparison S.higher hl o z (f ≫ g)).hom.app N ≫
        (z.compositors.pullComp f.hom.left g.hom.left).hom.app ((reduce Z).obj N) := by
  let := FixProjectionCompactification.Coordinates.residueUnits hl X
  let R := reduce (C := C) (E := E) X
  let : R.Full := by
    simpa only [R, reduce, calculus, pullbackTensorCalculus, integralSystemReduction] using
      (integralSystemReduction_fullyFaithful C.l E X.obj.left).1
  let a := (S.higher.integral.pullComposition f g).hom.app N
  let qf := (pullComparison S.higher hl o z f).app ((S.higher.integral.pull g).obj N)
  let qg := (pullComparison S.higher hl o z g).app N
  let q := (pullComparison S.higher hl o z (f ≫ g)).app N
  let c := (z.compositors.pullComp f.hom.left g.hom.left).app ((reduce Z).obj N)
  let P := pull C.l E f.hom.left
  let b := R.preimage (q.hom ≫ c.hom ≫ P.map qg.inv ≫ qf.inv)
  have hb : R.map b ≫ qf.hom ≫ P.map qg.hom = q.hom ≫ c.hom := by
    erw [Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    erw [← P.map_comp, qg.inv_hom_id, P.map_id, Category.comp_id]
  have hab : a = b := by
    apply integral_reductions_jointly_faithful S X
    intro m
    let ev := evaluation (C := C) (E := E) m X
    have h := evaluated_composition S hl o z m f g N
    have hb' := congrArg ev.map hb
    simp only [Functor.map_comp] at hb'
    have he : ev.map (R.map a) = ev.map (R.map b) := by
      apply (cancel_mono (ev.map qf.hom ≫ ev.map (P.map qg.hom))).1
      exact h.trans hb'.symm
    apply (finiteInclusion (C := C) (E := E) m X).map_injective
    apply (cancel_epi (reductionEvaluation S m X
      ((S.higher.integral.pull (f ≫ g)).obj N)).hom).1
    have ha := ((calculus C.l E X.obj.left).reductionEvaluation m).hom.naturality a.hom
    have hb := ((calculus C.l E X.obj.left).reductionEvaluation m).hom.naturality b.hom
    dsimp only [Functor.comp_map] at ha hb
    erw [← ha, ← hb, he]
    rfl
  change R.map a ≫ qf.hom ≫ P.map qg.hom = q.hom ≫ c.hom
  erw [hab]
  exact hb

end WeilConjectures.IntegralProjectionReduction.OpenCoordinates
