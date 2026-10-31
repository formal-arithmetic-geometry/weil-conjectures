/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.Coordinates.IntegralProjectionCoordinateData
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionCounit
import WeilConjectures.SixFunctors.IntegralSystemRealization.ConstructibleReductionGood
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenSupportStepBounds
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.ProperSupportStepBounds
import WeilConjectures.SixFunctors.Integral.IntegralReductionJointFaithfulness
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralSupportAdjunctFiniteCoordinates
import WeilConjectures.SixFunctors.FixProjectionCompactification.SystemRefinementFiniteCoordinates

/-! # One-input support reduction and refinement normalization

Source: prop-sf-pf-coherence.proof.md, compatibility of refinements with counits and j_!;
integral compactification-system realization, steps 3--5.
(blueprint: lem-sf-integral-support-reduction-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification
open IntegralSystemRealization

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  sfIntrinsicExtensionByZero coefficientSequenceLimit
  Functor.mapDerivedCategory Functor.rightDerivedFunctor DerivedCategory
  instCategoryDerivedCategory SheafOfModules.instAbelian
  scalarReductionDerivedExtension scalarReductionDerivedRestriction
  scalarReductionExistence scalarReductionExtension scalarReductionDerivedExistence
  completedIntegralCommRingSheafUnrestricted

attribute [local implicit_reducible] coefficientFiniteDerivedExtension
  coefficientFiniteDerivedRestriction coefficientFiniteAdjunction sixFunctorIntegralReduction
  sixFunctorFiniteSupport sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  SemilinearSections.moduleAbelian scalarReductionSourceDerived scalarReductionTargetDerived
  integralOperationsCommHasDerivedCategory integralCompletedRingHasDerivedCategory
  integralTowerHasDerivedCategory coefficientFiniteHasDerived
  reductionModulesHasDerivedCategory integralCoefficientSheaf integralCoefficientCommRingSheaf

private theorem adjunct_transport
    {A N : Type*} [Category A] [Category N] {R : A ⥤ N} {L : N ⥤ A}
    (adj : R ⊣ L) {Ad Ac : A} {Nd Nc : N}
    (Vd : L.obj Nd ≅ Ad) (Vc : L.obj Nc ≅ Ac) (s : Nd ⟶ Nc) :
    (adj.homEquiv Ad Nd).symm Vd.inv ≫ s =
      R.map (Vd.inv ≫ L.map s ≫ Vc.hom) ≫ (adj.homEquiv Ac Nc).symm Vc.inv := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (R.map Vc.hom), ← R.map_comp, Vc.hom_inv_id, R.map_id,
    Category.id_comp]
  exact congrArg (fun t ↦ R.map Vd.inv ≫ t) (adj.counit.naturality s).symm

private theorem finite_square
    {A N B : Type*} [Category A] [Category N] [Category B]
    (R : A ⥤ N) (ev : N ⥤ B) (red : A ⥤ B) (rho : R ⋙ ev ≅ red)
    {Ad Ac : A} {Nd Nc : N} {Bd Bc : B}
    (dd : R.obj Ad ⟶ Nd) (dc : R.obj Ac ⟶ Nc) (s : Nd ⟶ Nc)
    (a t : Ad ⟶ Ac) (bd : ev.obj Nd ≅ Bd) (bc : ev.obj Nc ≅ Bc)
    (qd : red.obj Ad ≅ Bd) (qc : red.obj Ac ≅ Bc) (q : Bd ⟶ Bc)
    (hs : dd ≫ s = R.map a ≫ dc)
    (hd : ev.map dd ≫ bd.hom = rho.hom.app Ad ≫ qd.hom)
    (hc : ev.map dc ≫ bc.hom = rho.hom.app Ac ≫ qc.hom)
    (hf : ev.map s ≫ bc.hom = bd.hom ≫ q)
    (ht : red.map t ≫ qc.hom = qd.hom ≫ q) : red.map a = red.map t := by
  apply (cancel_mono qc.hom).mp
  apply (cancel_epi (rho.hom.app Ad)).mp
  calc
    rho.hom.app Ad ≫ red.map a ≫ qc.hom =
        ev.map (R.map a) ≫ rho.hom.app Ac ≫ qc.hom := by
      rw [← Category.assoc, ← rho.hom.naturality a]
      simp only [Functor.comp_map, Category.assoc]
    _ = ev.map (R.map a) ≫ ev.map dc ≫ bc.hom := by rw [hc]
    _ = ev.map dd ≫ ev.map s ≫ bc.hom := by
      rw [← ev.map_comp_assoc, ← hs, ev.map_comp]
      simp only [Category.assoc]
    _ = ev.map dd ≫ bd.hom ≫ q := by rw [hf]
    _ = rho.hom.app Ad ≫ qd.hom ≫ q := by rw [← Category.assoc, hd, Category.assoc]
    _ = rho.hom.app Ad ≫ red.map t ≫ qc.hom := by rw [ht]

private theorem inverse_square
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : A} {X' Y' : B} (i : X ≅ Y) (j : X' ≅ Y')
    (a : F.obj X ≅ X') (b : F.obj Y ≅ Y')
    (h : F.map i.hom ≫ b.hom = a.hom ≫ j.hom) :
    F.map i.inv ≫ a.hom = b.hom ≫ j.inv := by
  apply (cancel_mono j.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, ← Category.assoc, ← F.map_comp, i.inv_hom_id, F.map_id,
    Category.id_comp]

private theorem support_normalized
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (o : Operations C.l E)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    IsNormalizedCoefficientSequence C.l E Y.obj.left
      ((Operations.push C.l E o c.g).obj ((Operations.shriek C.l E o c.i).obj
        ((calculus C.l E X.obj.left).reduction.obj K.obj))) := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : QuasiCompact X.obj.hom := X.property.2
  let : LocallyOfFiniteType Y.obj.hom := Y.property.1
  let : QuasiCompact Y.obj.hom := Y.property.2
  let Z := compactAmbient (f := f.hom) c
  let : LocallyOfFiniteType Z.hom :=
    show LocallyOfFiniteType (c.g ≫ Y.obj.hom) from inferInstance
  let : QuasiCompact Z.hom :=
    show QuasiCompact (c.g ≫ Y.obj.hom) from inferInstance
  let : IsOpenImmersion (compactOpen (f := f.hom) c).left := c.isOpenImmersion
  let : QuasiCompact (compactOpen (f := f.hom) c).left := inferInstanceAs (QuasiCompact c.i)
  let : IsProper (compactProper (f := f.hom) c).left := c.isProper
  have hR := constructibleReduction_good C.l E D C.different X.obj K.obj K.property
  have hJ := openSupportStep_bounds C.l E D C.different o
    (compactOpen (f := f.hom) c) _ hR K.obj K.property
  have hP := properSupportStep_bounds C.l E D C.different o
    (compactProper (f := f.hom) c) _ hJ.1
    ((ringedOpen C.l E c.i).obj K.obj) hJ.2
  intro m n hmn P
  exact hP.1.1 hmn P

private theorem support_reduction_isIso
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    IsIso (Coordinates.supportReduction D C E H hl o z f c K) := by
  have hn : IsNormalizedCoefficientSequence C.l E Y.obj.left
      ((Operations.push C.l E o c.g).obj ((Operations.shriek C.l E o c.i).obj
        ((calculus C.l E X.obj.left).reduction.obj K.obj))) :=
    fun h P ↦ support_normalized D C E o f c K h P
  have hc := ((purNormalizedReconstructionOfScheme C.l E Y.obj.left
    (calculus C.l E Y.obj.left)).1 _ hn).2
  let := hc
  dsimp only [Coordinates.supportReduction]
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- The explicit support adjunct is invertible and intertwines a single directed
refinement. There is only one input, and no tensor or projection map in this assertion.

Source: prop-sf-pf-coherence.proof.md, compactification independence;
integral compactification-system realization, steps 3--5.
(blueprint: lem-sf-integral-support-reduction-normalization).

Proof: the proved constructible-reduction bound gives Good input. The proved open
and proper support bounds give Good intermediate and output systems, hence normalization. The actual
reconstruction counit is therefore invertible, and the defining adjunct of supportValue
inverse is a composite of two invertible maps.
For a directed refinement, transport its system map through supportValue to an actual
morphism between the two integral constructible outputs. Naturality of the reconstruction
counit gives the desired support-reduction square with this morphism. At each positive
quotient, the support-adjunct coordinate formula and the finite refinement coordinate
formula compute its reduction. The coefficient datum's compactification square, inverted,
gives the same reduction for the inverse datum comparison. Joint faithfulness of integral
constructible reductions identifies the two integral morphisms. This joint faithfulness
uses finite shifted Hom groups and the Milnor injection; no faithfulness of evaluation
on arbitrary derived systems is assumed. Substitution into the counit square finishes.
All constructions include identity refinements, empty opens and zero inputs. -/
theorem integralSupportReductionNormalization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left] :
    (∀ (c : Compactification f.hom.left)
      (K : sfIntegralConstructibleCategory C.l E X.obj.left),
      IsIso (Coordinates.supportReduction D C E S.higher hl o z f c K)) ∧
    (∀ (c d : Compactification f.hom.left) (r : c.Refinement d)
      (K : sfIntegralConstructibleCategory C.l E X.obj.left),
      Coordinates.supportReduction D C E S.higher hl o z f d K ≫
          RefinementProjection.systemComparison C.l E D o z r
            ((calculus C.l E X.obj.left).reduction.obj K.obj) =
        (calculus C.l E Y.obj.left).reduction.map
          (((S.higher.integral.comparison f c d).inv.app K).hom) ≫
            Coordinates.supportReduction D C E S.higher hl o z f c K) := by
  constructor
  · intro c K
    exact support_reduction_isIso D C E S.higher hl o z f c K
  · intro c d r K
    let A := calculus C.l E Y.obj.left
    let M := (calculus C.l E X.obj.left).reduction.obj K.obj
    let Nc := (Operations.push C.l E o c.g).obj
      ((Operations.shriek C.l E o c.i).obj M)
    let Nd := (Operations.push C.l E o d.g).obj
      ((Operations.shriek C.l E o d.i).obj M)
    let Ac := (S.higher.integral.support f c).obj K
    let Ad := (S.higher.integral.support f d).obj K
    let Vc := Coordinates.supportValue D C E S.higher hl o z f c K
    let Vd := Coordinates.supportValue D C E S.higher hl o z f d K
    let s := RefinementProjection.systemComparison C.l E D o z r M
    let a : Ad ⟶ Ac := ObjectProperty.homMk
      (Vd.inv ≫ (coefficientSequenceLimit C.l E Y.obj.left).map s ≫ Vc.hom)
    let t : Ad ⟶ Ac := (S.higher.integral.comparison f c d).inv.app K
    have hs : Coordinates.supportReduction D C E S.higher hl o z f d K ≫ s =
        A.reduction.map a.hom ≫
          Coordinates.supportReduction D C E S.higher hl o z f c K :=
      adjunct_transport A.adjunction Vd Vc s
    have hat : a = t := by
      apply integral_reductions_jointly_faithful S Y
      intro m
      let F := S.integralNormalization.finiteLevels m
      let Rm := sixFunctorIntegralReduction D C E m Y
      let I := (intrinsicFiniteTorsionConstructible C.l E (m + 1)
        (Nat.le_add_left 1 m) Y.obj.left).ι
      apply I.map_injective
      change (coefficientFiniteDerivedExtension C.l E Y.obj.left m).map a.hom =
        (coefficientFiniteDerivedExtension C.l E Y.obj.left m).map t.hom
      let ev := coefficientSequenceDerivedEvaluation C.l E Y.obj.left m
      let red := coefficientFiniteDerivedExtension C.l E Y.obj.left m
      let Kn := (sixFunctorIntegralReduction D C E m X).obj K
      let e := ((calculus C.l E X.obj.left).reductionEvaluation m).app K.obj
      let Fc := sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c
      let Fd := sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f d
      let bc : ev.obj Nc ≅ Fc.obj Kn.obj :=
        (supportEvaluation C.l E o c m).app M ≪≫ Fc.mapIso e
      let bd : ev.obj Nd ≅ Fd.obj Kn.obj :=
        (supportEvaluation C.l E o d m).app M ≪≫ Fd.mapIso e
      let beta := S.integralNormalization.reduction m
      let qc : red.obj Ac.obj ≅ Fc.obj Kn.obj :=
        I.mapIso ((beta.supportAdjunction f c).left.app K) ≪≫
          (F.finiteSupport f c).app Kn
      let qd : red.obj Ad.obj ≅ Fd.obj Kn.obj :=
        I.mapIso ((beta.supportAdjunction f d).left.app K) ≪≫
          (F.finiteSupport f d).app Kn
      let q : Fd.obj Kn.obj ≅ Fc.obj Kn.obj :=
        ((F.finiteSupport f d).app Kn).symm ≪≫
          I.mapIso (((F.finite.comparison f c d).app Kn).symm) ≪≫
            (F.finiteSupport f c).app Kn
      apply finite_square A.reduction ev red (A.reductionEvaluation m)
        (Coordinates.supportReduction D C E S.higher hl o z f d K)
        (Coordinates.supportReduction D C E S.higher hl o z f c K)
        s a.hom t.hom bd bc qd qc q.hom hs
      · exact integralSupportAdjunctFiniteCoordinates D C E n hn S hl o z f d K m
      · exact integralSupportAdjunctFiniteCoordinates D C E n hn S hl o z f c K m
      · simpa only [bc, bd, q, I, Iso.trans_hom, Functor.mapIso_hom,
          Iso.symm_hom, Iso.app_hom, Iso.app_inv, ObjectProperty.ι_map,
          Category.assoc] using
          (systemRefinementFiniteCoordinates D C E m F hl o z f c d r M Kn e)
      · have hi := inverse_square Rm
          ((S.higher.integral.comparison f c d).app K)
          ((F.finite.comparison f c d).app Kn)
          ((beta.supportAdjunction f c).left.app K)
          ((beta.supportAdjunction f d).left.app K)
          (beta.compactification f c d K)
        have hi' : red.map t.hom ≫
              (((beta.supportAdjunction f c).left.hom.app K).hom) =
            (((beta.supportAdjunction f d).left.hom.app K).hom) ≫
              ((F.finite.comparison f c d).inv.app Kn).hom :=
          congrArg (fun v ↦ v.hom) hi
        dsimp only [qc, qd, q, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
        simp only [I, ObjectProperty.ι_map, Iso.app_hom, Iso.app_inv,
          Category.assoc, Iso.hom_inv_id_app_assoc]
        rw [← Category.assoc, hi', Category.assoc]
    simpa only [hat] using hs

end WeilConjectures.FixProjectionCompactification
