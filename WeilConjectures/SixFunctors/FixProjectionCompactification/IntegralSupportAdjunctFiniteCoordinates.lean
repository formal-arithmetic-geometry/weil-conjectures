/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.Coordinates.IntegralProjectionCoordinateData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Support.IntegralSupportTowerNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.ConstructibleReductionGood
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenSupportStepBounds
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.ProperSupportStepBounds

/-! # Finite coordinates of a single support adjunct

Source: Stacks 0941 and 0F7J; compactification realization steps 3--5.
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
  RealizationModel.push RealizationModel.openReduction sfQcqsCompactSupportRealization
  scalarReductionExistence scalarReductionExtension scalarReductionDerivedExistence
  sfCompactSupportChosenReduction sfCompactSupportFiniteReductionIso
  sfIntegralCompactSupportValue
  scalarReductionDerivedExtension scalarReductionDerivedRestriction
  completedIntegralCommRingSheafUnrestricted

attribute [local implicit_reducible] coefficientFiniteDerivedExtension
  coefficientFiniteDerivedRestriction coefficientFiniteAdjunction sixFunctorIntegralReduction
  PurCompactSupport.image PurCompactSupport.completed basicSupportInput
  sixFunctorFiniteSupport sfIntrinsicCompactSupport
  sfAmbientCompactSupportCandidate
  SemilinearSections.moduleAbelian scalarReductionSourceDerived scalarReductionTargetDerived
  integralOperationsCommHasDerivedCategory integralCompletedRingHasDerivedCategory
  integralTowerHasDerivedCategory coefficientFiniteHasDerived
  reductionModulesHasDerivedCategory
  integralCoefficientSheaf integralCoefficientCommRingSheaf

private theorem and_rec_eq {P Q : Prop} {α : Sort*}
    (g : P → Q → α) (h : P ∧ Q) : And.rec g h = g h.1 h.2 := by
  cases h
  rfl

private theorem transport_cancel
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : B ⥤ C) (I : A ⥤ B) {x y z : A} (p : x = z) (q : y = z) :
    F.map (I.map (eqToHom (p.trans q.symm))) ≫ F.map (I.map (eqToHom q)) =
      F.map (I.map (eqToHom p)) := by
  rw [← F.map_comp, ← I.map_comp, eqToHom_trans]

private theorem assoc_four
    {A : Type*} [Category A] {w x y z t : A}
    (a : w ⟶ x) (b : x ⟶ y) (c : y ⟶ z) (d : z ⟶ t) :
    a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

private theorem value_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : B ⥤ C) (I : A ⥤ B) {x y z : A} (hx : x = z) (hy : y = z)
    {N : B} (v : N ⟶ I.obj y) (d : N ⟶ I.obj x) {T : C}
    (p : F.obj (I.obj y) ⟶ T) (q : F.obj (I.obj z) ⟶ T)
    (hv : v = d ≫ I.map (eqToHom (hx.trans hy.symm)))
    (hp : p = F.map (I.map (eqToHom hy)) ≫ q) :
    F.map v ≫ p = F.map d ≫ F.map (I.map (eqToHom hx)) ≫ q := by
  rw [hv, F.map_comp, Category.assoc, hp]
  rw [← Category.assoc (F.map (I.map (eqToHom (hx.trans hy.symm)))),
    transport_cancel F I hx hy]

private theorem evaluation_adjunct
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    (A : CoefficientDerivedSystemCalculus l E W)
    (N : coefficientSequenceDerived l E W)
    (B : Integral l E W) (V : (coefficientSequenceLimit l E W).obj N ≅ B)
    (m : ℕ) (T : normalizedDVRDerived l E W m)
    (t : (coefficientSequenceDerivedEvaluation l E W m).obj N ⟶ T)
    (p : (coefficientFiniteDerivedExtension l E W m).obj B ⟶ T)
    (h : (coefficientFiniteDerivedExtension l E W m).map V.hom ≫ p =
      ((coefficientFiniteAdjunction l E W m).homEquiv _ _).symm
        ((coefficientSequenceProjection l E W m).app N ≫
          (coefficientFiniteDerivedRestriction l E W m).map t)) :
    (coefficientSequenceDerivedEvaluation l E W m).map
        ((A.adjunction.homEquiv B N).symm V.inv) ≫ t =
      (A.reductionEvaluation m).hom.app B ≫ p := by
  let ev := coefficientSequenceDerivedEvaluation l E W m
  let red := coefficientFiniteDerivedExtension l E W m
  let rho := A.reductionEvaluation m
  have hp : rho.inv.app ((coefficientSequenceLimit l E W).obj N) ≫
        ev.map (A.adjunction.counit.app N) ≫ t =
      ((coefficientFiniteAdjunction l E W m).homEquiv _ _).symm
        ((coefficientSequenceProjection l E W m).app N ≫
          (coefficientFiniteDerivedRestriction l E W m).map t) := by
    apply ((coefficientFiniteAdjunction l E W m).homEquiv _ _).injective
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    rw [A.counit_projection, Equiv.apply_symm_apply]
  apply (cancel_epi (rho.inv.app B)).mp
  change rho.inv.app B ≫ ev.map ((A.adjunction.homEquiv B N).symm V.inv) ≫ t =
    rho.inv.app B ≫ rho.hom.app B ≫ p
  simp only [Iso.inv_hom_id_app_assoc]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change rho.inv.app B ≫ ev.map (A.reduction.map V.inv) ≫
      ev.map (A.adjunction.counit.app N) ≫ t = p
  rw [← Category.assoc (rho.inv.app B)]
  erw [← rho.inv.naturality V.inv]
  change (red.map V.inv ≫ rho.inv.app _) ≫ _ = _
  rw [Category.assoc, hp, ← h, ← Category.assoc, ← red.map_comp,
    V.inv_hom_id, red.map_id, Category.id_comp]

attribute [local irreducible] SheafOfModules.instCategory in
private theorem datum_projection_eq
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ) :
    @CategoryStruct.comp (normalizedDVRDerived C.l E Y.obj.left m) inferInstance _ _ _
      (((S.integralNormalization.reduction m).supportAdjunction f c).left.hom.app K).hom
      (((S.integralNormalization.finiteLevels m).finiteSupport f c).hom.app
        ((sixFunctorIntegralReduction D C E m X).obj K)) =
    (scalarReductionDerivedExtension C.l E Y.obj.left m).map
        ((sfIntegralConstructible C.l E Y.obj.left).ι.map
          (eqToHom ((S.higher.supportConstruction f hl c).choose_spec.2.2.1 K))) ≫
      sfCompactSupportChosenReduction C.l D.k hl c E K m := by
  apply eq_of_heq
  exact S.integralNormalization.supportProjection f hl c K m

attribute [local irreducible] SheafOfModules.instCategory in
private theorem support_value_hom
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (H : SixFunctorHigherOperations D C E) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) [QuasiCompact c.i]
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    (hunit : IsIso ((calculus C.l E c.Z).adjunction.unit.app
      ((ringedOpen C.l E c.i).obj K.obj))) :
    (Coordinates.supportValue D C E H hl o z f c K).hom =
      (z.realizationModel.push C.l E c.g).hom.app
        ((Operations.shriek C.l E o c.i).obj ((calculus C.l E X.obj.left).reduction.obj K.obj)) ≫
      (ringedPush C.l E c.g).map
        ((coefficientSequenceLimit C.l E c.Z).map
            ((z.realizationModel.openReduction C.l E c.i).app K.obj) ≫
          @inv _ _ _ _ ((calculus C.l E c.Z).adjunction.unit.app
            ((ringedOpen C.l E c.i).obj K.obj)) hunit) ≫
      (sfQcqsCompactSupportRealization C.l E D.k hl c).hom.app K ≫
      (sfIntegralConstructible C.l E Y.obj.left).ι.map
        (eqToHom ((sfCompactSupportFiniteIntegralFunctor_obj C.l D.k hl c E K).trans
          ((H.supportConstruction f hl c).choose_spec.2.2.1 K).symm)) := by
  dsimp only [Coordinates.supportValue]
  conv_lhs =>
    arg 1
    rw [and_rec_eq]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Iso.app_hom, eqToIso.hom]

attribute [local irreducible] SheafOfModules.instCategory in
private theorem finite_reduction_hom
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (hl : IsUnit (C.l : D.k))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ) :
    (sfCompactSupportFiniteReductionIso C.l D.k hl c E K m).hom =
      (scalarReductionDerivedExtension C.l E Y.obj.left m).map
        ((sfIntegralConstructible C.l E Y.obj.left).ι.map
          (eqToHom (sfCompactSupportFiniteIntegralFunctor_obj C.l D.k hl c E K))) ≫
        sfCompactSupportChosenReduction C.l D.k hl c E K m := by
  unfold sfCompactSupportFiniteReductionIso
  rfl

/-- The finite evaluation of the explicitly constructed support adjunct is the
specified integral-to-finite support comparison. There is no refinement in this statement.

Source: prop-sf-pf-coherence.proof.md, compactification independence; the projection
normalizations in integralSupportTowerNormalization and SixFunctorIntegralNormalization.
(blueprint: lem-sf-integral-support-adjunct-finite-coordinates).

Proof: the proved reduction, open and proper bounds give the support domain. Use the
normalized whole support tower, retaining its actual quotient transitions.
Its direct limit comparison is proper/limit conjugation followed by the open reduction
mate and the inverse open reconstruction unit. The formula for d in the tower
normalization identifies it with the first three factors of supportValue. The final
object equality is precisely supportConstruction's prescribed Roos value. Apply scalar
adjunction to the normalized tower projection: its transpose is reductionEvaluation
inverse followed by evaluation of the actual reconstruction counit. Naturality of
reductionEvaluation moves reduction of supportValue inverse across that expression.
The adjacent comparison and inverse comparison cancel. The remaining map is exactly
the prescribed supportProjection of the integral normalization, followed by the finite
support realization. This proves the displayed equality at a single positive quotient.
No comparison of distinct compactifications or equality detection by evaluation enters.
Zero objects and empty opens obey the same scalar-adjunction formulas. -/
theorem integralSupportAdjunctFiniteCoordinates
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ) :
    (coefficientSequenceDerivedEvaluation C.l E Y.obj.left m).map
        (Coordinates.supportReduction D C E S.higher hl o z f c K) ≫
      (supportEvaluation C.l E o c m).hom.app
        ((calculus C.l E X.obj.left).reduction.obj K.obj) ≫
      (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).map
        (((calculus C.l E X.obj.left).reductionEvaluation m).hom.app K.obj) =
    ((calculus C.l E Y.obj.left).reductionEvaluation m).hom.app
        (((S.higher.integral.support f c).obj K).obj) ≫
      (((S.integralNormalization.reduction m).supportAdjunction f c).left.hom.app K).hom ≫
      ((S.integralNormalization.finiteLevels m).finiteSupport f c).hom.app
        ((sixFunctorIntegralReduction D C E m X).obj K) := by
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
  have hdomain : basicSupportDomain C.l E o c K.obj :=
    ⟨⟨K.property, hR, hP.1⟩, hJ.1⟩
  let K' : (basicSupportDomain C.l E o c).FullSubcategory := ⟨K.obj, hdomain⟩
  obtain ⟨T, e, hT, he, ht, tower, d, hunit, hd, heval, hp⟩ :=
    integralSupportTowerNormalization C.l E D o z.realizationModel f.hom.left hl c
  let Rm := scalarReductionDerivedExtension C.l E Y.obj.left m
  refine evaluation_adjunct C.l E Y.obj.left (calculus C.l E Y.obj.left)
    ((Operations.push C.l E o c.g).obj ((Operations.shriek C.l E o c.i).obj
      ((calculus C.l E X.obj.left).reduction.obj K.obj)))
    (((S.higher.integral.support f c).obj K).obj)
    (Coordinates.supportValue D C E S.higher hl o z f c K) m
    ((sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).obj
      ((sixFunctorIntegralReduction D C E m X).obj K).obj)
    ((supportEvaluation C.l E o c m).hom.app
        ((calculus C.l E X.obj.left).reduction.obj K.obj) ≫
      (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).map
        (((calculus C.l E X.obj.left).reductionEvaluation m).hom.app K.obj))
    ((((S.integralNormalization.reduction m).supportAdjunction f c).left.hom.app K).hom ≫
      ((S.integralNormalization.finiteLevels m).finiteSupport f c).hom.app
        ((sixFunctorIntegralReduction D C E m X).obj K)) ?_
  change Rm.map
      (Coordinates.supportValue D C E S.higher hl o z f c K).hom ≫ _ =
    ((derivedScalarExtensionRestrictionAdjunction C.l E Y.obj.left m).choose.homEquiv
      _ _).symm _
  have hp' := hp K' m
  dsimp only [K', basicSupportInput, ObjectProperty.ιOfLE] at hp'
  have hd' := hd K'
  dsimp only [K', basicSupportInput, ObjectProperty.ιOfLE] at hd'
  let I := (sfIntegralConstructible C.l E Y.obj.left).ι
  let hF := sfCompactSupportFiniteIntegralFunctor_obj C.l D.k hl c E K
  let hS := (S.higher.supportConstruction f hl c).choose_spec.2.2.1 K
  have hv0 := support_value_hom D C E S.higher hl o z f c K (hunit K')
  have hdpost := congrArg (fun v ↦ v ≫ I.map (eqToHom (hF.trans hS.symm))) hd'
  have hV : (Coordinates.supportValue D C E S.higher hl o z f c K).hom =
      d.hom.app K' ≫ I.map (eqToHom (hF.trans hS.symm)) := by
    refine hv0.trans ((assoc_four _ _ _ _).trans ?_)
    exact hdpost.symm
  let qcoord := sfCompactSupportChosenReduction C.l D.k hl c E K m
  have hc := value_transport Rm I hF hS
    (Coordinates.supportValue D C E S.higher hl o z f c K).hom (d.hom.app K')
    (Rm.map (I.map (eqToHom hS)) ≫ qcoord) qcoord hV rfl
  conv_lhs =>
    arg 2
    equals Rm.map (I.map (eqToHom hS)) ≫ qcoord =>
      with_reducible exact datum_projection_eq D C E n hn S hl f c K m
  have hi := finite_reduction_hom D C E hl f c K m
  have hq := congrArg (fun v ↦ Rm.map (d.hom.app K') ≫ v) hi
  refine hc.trans (hq.symm.trans ?_)
  exact hp'

end WeilConjectures.FixProjectionCompactification
