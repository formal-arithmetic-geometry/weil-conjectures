/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SystemEvaluationNormalizationData
import WeilConjectures.CategoryTheory.SystemRestrictionScalarMateInvertibility
import WeilConjectures.CategoryTheory.SystemRestrictionLevelMateInvertibility

/-! # Restriction mates and their coherence

Source: Stacks Project, Tags 03D2, 0D6E and 07A6; Zheng, Construction 4.1.
(blueprint: lem-route-system-restriction-mate-coherence-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem normalization_underlying_comparison
    {A B : Type*} [Category A] [Category B] (U : A ⥤ B)
    {E T Y Z R L : A} {Y' Z' : B}
    (e : E ⟶ T) (fa : T ⟶ Y) (r : Y ⟶ Z)
    (vx : E ⟶ R) (fb : R ⟶ L) (level : L ⟶ Z)
    (iz : U.obj Z ⟶ Z') (iy : U.obj Y ⟶ Y') (v : Y' ⟶ Z') (ib : U.obj L ⟶ Z')
    (hcomp : e ≫ fa ≫ r = vx ≫ fb ≫ level)
    (hnat : U.map r ≫ iz = iy ≫ v) (hlevel : U.map level ≫ iz = ib) :
    U.map e ≫ U.map fa ≫ iy ≫ v = U.map vx ≫ U.map fb ≫ ib := by
  have hp := congrArg U.map hcomp
  simp only [Functor.map_comp] at hp
  calc
    U.map e ≫ U.map fa ≫ iy ≫ v =
        (U.map e ≫ U.map fa ≫ U.map r) ≫ iz := by rw [Category.assoc, ← hnat,
          Category.assoc]
    _ = (U.map vx ≫ U.map fb ≫ U.map level) ≫ iz := by rw [hp]
    _ = U.map vx ≫ U.map fb ≫ ib := by rw [Category.assoc, Category.assoc, hlevel]

private theorem normalization_left_transition
    {A B : Type*} [Category A] [Category B] (U : A ⥤ B)
    {An Am Yn Ym : A} {Xn Xm En Em : B}
    (t : Am ⟶ An) (yn : An ⟶ Yn) (ym : Am ⟶ Ym) (b : Ym ⟶ Yn)
    (en : Xn ⟶ En) (em : Xm ⟶ Em) (in' : En ≅ U.obj An) (im : Em ≅ U.obj Am)
    (tx : Xm ⟶ Xn)
    (h : em ≫ im.hom ≫ U.map t ≫ in'.inv = tx ≫ en)
    (hv : t ≫ yn = ym ≫ b) :
    tx ≫ en ≫ in'.hom ≫ U.map yn = em ≫ im.hom ≫ U.map ym ≫ U.map b := by
  rw [← Category.assoc tx en, ← h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← U.map_comp, hv, U.map_comp]

private theorem normalization_right_transition
    {A : Type*} [Category A] {Xn Xm Bn Bm En Em Yn Ym : A}
    (a : Xm ⟶ Xn) (vn : Xn ⟶ Bn) (vm : Xm ⟶ Bm) (t : Bm ⟶ Bn)
    (en : Bn ⟶ En) (em : Bm ⟶ Em) (in' : En ≅ Yn) (im : Em ≅ Ym)
    (b : Ym ⟶ Yn) (hv : a ≫ vn = vm ≫ t)
    (h : em ≫ im.hom ≫ b ≫ in'.inv = t ≫ en) :
    a ≫ vn ≫ en ≫ in'.hom = vm ≫ em ≫ im.hom ≫ b := by
  rw [← Category.assoc a vn, hv]
  simp only [Category.assoc]
  rw [← Category.assoc t en, ← h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem normalization_transition_square
    {A : Type*} [Category A] {An Am Bn Bm Zn Zm : A}
    (en : An ⟶ Bn) (em : Am ⟶ Bm) (gan : Bn ⟶ Zn) (gam : Bm ⟶ Zm)
    (gbn : An ⟶ Zn) (gbm : Am ⟶ Zm) (ta : Bm ⟶ Bn) (tb : Am ⟶ An)
    (tz : Zm ⟶ Zn) [Mono gan]
    (hen : en ≫ gan = gbn) (hem : em ≫ gam = gbm)
    (ha : ta ≫ gan = gam ≫ tz) (hb : tb ≫ gbn = gbm ≫ tz) :
    em ≫ ta = tb ≫ en := by
  apply (cancel_mono gan).1
  rw [Category.assoc, ha, ← Category.assoc, hem, ← hb, Category.assoc, hen]

end CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (AY : Sheaf J CommRingCat.{w}) (AX : Sheaf K CommRingCat.{w})
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (aY : (Functor.const ℕᵒᵖ).obj AY ⟶ BY)
  (aX : (Functor.const ℕᵒᵖ).obj AX ⟶ BX)
  (uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (IA : AlgebraicInverseImage uTop.inverse AY AX)
  (IB : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n)))
  (FB : SystemGeometricInverseImageData BY BX uTop IB)
  (FA : SystemGeometricInverseImageData
    ((Functor.const ℕᵒᵖ).obj AY) ((Functor.const ℕᵒᵖ).obj AX) uTop (fun _ ↦ IA))


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem normalization_underlying_transition
    (A B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : A ⟶ B)
    (M : StrictRingSystem B) {n m : ℕ} (h : n ≤ m) :
    (systemGeometricUnderlying A m).map (((systemNormalizationRestriction a).obj M).transition h) ≫
        (systemGeometricUnderlying A n).map
          ((systemNormalizationRestrictionEvaluation a n).hom.app M) =
      (systemGeometricUnderlying A m).map
          ((systemNormalizationRestrictionEvaluation a m).hom.app M) ≫
        (systemGeometricUnderlying B m).map (M.transition h) := by
  ext U x
  change (M.level n).val.map (𝟙 U) ((M.transition h).val.app U x) =
    (M.transition h).val.app U x
  erw [PresheafOfModules.map_id]
  rfl

variable (level : ∀ n : ℕ,
    FB.levelFunctor n ⋙ singletonLevelRestriction aX n ≅
      singletonLevelRestriction aY n ⋙ FA.levelFunctor 0)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def normalization_level_iso (n : ℕ) :
    FB.functor ⋙ systemNormalizationRestriction aX ⋙
        systemEvaluation ((Functor.const ℕᵒᵖ).obj AX) n ≅
      systemNormalizationRestriction aY ⋙ FA.functor ⋙
        systemEvaluation ((Functor.const ℕᵒᵖ).obj AX) n :=
  Functor.isoWhiskerLeft FB.functor (systemNormalizationRestrictionEvaluation aX n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (FB.evaluation n) (singletonLevelRestriction aX n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (systemEvaluation BY n) (level n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (systemNormalizationRestrictionEvaluation aY n).symm
      (FA.levelFunctor 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (systemNormalizationRestriction aY) (FA.evaluation n).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem normalization_level_evaluation (M : StrictRingSystem BY) (n : ℕ) :
    (normalization_level_iso AY AX BY BX aY aX uTop IA IB FB FA level n).hom.app M ≫
        (FA.evaluation n).hom.app ((systemNormalizationRestriction aY).obj M) ≫
        (FA.levelFunctor 0).map
          ((systemNormalizationRestrictionEvaluation aY n).hom.app M) =
      (systemNormalizationRestrictionEvaluation aX n).hom.app (FB.functor.obj M) ≫
        (singletonLevelRestriction aX n).map ((FB.evaluation n).hom.app M) ≫
        (level n).hom.app (M.level n) := by
  simp only [normalization_level_iso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc]
  erw [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.symm_hom, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 2000000 in
-- The strict-system construction unfolds nested coefficient-restriction equivalences.
private theorem normalization_exists
    (levelUnderlying : ∀ (n : ℕ) (M : systemLevel BY n),
      (systemGeometricUnderlying ((Functor.const ℕᵒᵖ).obj AX) 0).map
            ((level n).hom.app M) ≫
          IA.moduleUnderlying.hom.app ((singletonLevelRestriction aY n).obj M) =
        (IB n).moduleUnderlying.hom.app M)
    (restriction : ∀ {n m : ℕ} (h : n ≤ m),
      FB.levelFunctor n ⋙ systemRestriction BX h ≅
        systemRestriction BY h ⋙ FB.levelFunctor m)
    (restrictionUnderlying : ∀ {n m : ℕ} (h : n ≤ m) (M : systemLevel BY n),
      (systemGeometricUnderlying BX m).map ((restriction h).hom.app M) ≫
          (IB m).moduleUnderlying.hom.app ((systemRestriction BY h).obj M) =
        (IB n).moduleUnderlying.hom.app M) :
    ∃ d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA,
      d.level = level ∧ @d.restriction = @restriction := by
  let AYs := (Functor.const ℕᵒᵖ).obj AY
  let AXs := (Functor.const ℕᵒᵖ).obj AX
  let UY := systemNormalizationRestriction aY
  let UX := systemNormalizationRestriction aX
  let e := normalization_level_iso AY AX BY BX aY aX uTop IA IB FB FA level
  let vy (M : StrictRingSystem BY) (n : ℕ) :=
    (systemGeometricUnderlying AYs n).map
      ((systemNormalizationRestrictionEvaluation aY n).hom.app M)
  let vx (M : StrictRingSystem BX) (n : ℕ) :=
    (systemGeometricUnderlying AXs n).map
      ((systemNormalizationRestrictionEvaluation aX n).hom.app M)
  let ga (M : StrictRingSystem BY) (n : ℕ) :=
    (systemGeometricUnderlying AXs n).map ((FA.evaluation n).hom.app (UY.obj M)) ≫
      IA.moduleUnderlying.hom.app ((UY.obj M).level n) ≫ uTop.inverse.map (vy M n)
  let gb (M : StrictRingSystem BY) (n : ℕ) :=
    vx (FB.functor.obj M) n ≫
      (systemGeometricUnderlying BX n).map ((FB.evaluation n).hom.app M) ≫
      (IB n).moduleUnderlying.hom.app (M.level n)
  have he (M : StrictRingSystem BY) (n : ℕ) :
      (systemGeometricUnderlying AXs n).map ((e n).hom.app M) ≫ ga M n = gb M n := by
    dsimp only [ga, gb, vy, vx]
    have hn := IA.moduleUnderlying.hom.naturality
      ((systemNormalizationRestrictionEvaluation aY n).hom.app M)
    change (systemGeometricUnderlying AXs n).map
        ((FA.levelFunctor 0).map
          ((systemNormalizationRestrictionEvaluation aY n).hom.app M)) ≫
        IA.moduleUnderlying.hom.app ((singletonLevelRestriction aY n).obj (M.level n)) =
      IA.moduleUnderlying.hom.app ((UY.obj M).level n) ≫
        uTop.inverse.map ((systemGeometricUnderlying AYs n).map
          ((systemNormalizationRestrictionEvaluation aY n).hom.app M)) at hn
    have hh := normalization_level_evaluation AY AX BY BX aY aX uTop IA IB FB FA level M n
    exact normalization_underlying_comparison (systemGeometricUnderlying AXs n)
      ((e n).hom.app M) ((FA.evaluation n).hom.app (UY.obj M))
      ((FA.levelFunctor 0).map ((systemNormalizationRestrictionEvaluation aY n).hom.app M))
      ((systemNormalizationRestrictionEvaluation aX n).hom.app (FB.functor.obj M))
      ((singletonLevelRestriction aX n).map ((FB.evaluation n).hom.app M))
      ((level n).hom.app (M.level n))
      (IA.moduleUnderlying.hom.app ((singletonLevelRestriction aY n).obj (M.level n)))
      (IA.moduleUnderlying.hom.app ((UY.obj M).level n)) (uTop.inverse.map (vy M n))
      ((IB n).moduleUnderlying.hom.app (M.level n)) hh hn (levelUnderlying n (M.level n))
  have ha (M : StrictRingSystem BY) {n m : ℕ} (h : n ≤ m) :
      (systemGeometricUnderlying AXs m).map ((FA.functor.obj (UY.obj M)).transition h) ≫
          ga M n =
        ga M m ≫ uTop.inverse.map ((systemGeometricUnderlying BY m).map (M.transition h)) := by
    have hv := normalization_underlying_transition AYs BY aY M h
    change (systemGeometricUnderlying AYs m).map ((UY.obj M).transition h) ≫ vy M n =
      vy M m ≫ (systemGeometricUnderlying BY m).map (M.transition h) at hv
    exact normalization_left_transition uTop.inverse _ (vy M n) (vy M m) _
      ((systemGeometricUnderlying AXs n).map ((FA.evaluation n).hom.app (UY.obj M)))
      ((systemGeometricUnderlying AXs m).map ((FA.evaluation m).hom.app (UY.obj M)))
      (IA.moduleUnderlying.app ((UY.obj M).level n))
      (IA.moduleUnderlying.app ((UY.obj M).level m)) _ (FA.transition (UY.obj M) h) hv
  have hb (M : StrictRingSystem BY) {n m : ℕ} (h : n ≤ m) :
      (systemGeometricUnderlying AXs m).map ((UX.obj (FB.functor.obj M)).transition h) ≫
          gb M n =
        gb M m ≫ uTop.inverse.map ((systemGeometricUnderlying BY m).map (M.transition h)) := by
    have hv := normalization_underlying_transition AXs BX aX (FB.functor.obj M) h
    change (systemGeometricUnderlying AXs m).map
        ((UX.obj (FB.functor.obj M)).transition h) ≫ vx (FB.functor.obj M) n =
      vx (FB.functor.obj M) m ≫
        (systemGeometricUnderlying BX m).map ((FB.functor.obj M).transition h) at hv
    exact normalization_right_transition _ (vx (FB.functor.obj M) n)
      (vx (FB.functor.obj M) m) _
      ((systemGeometricUnderlying BX n).map ((FB.evaluation n).hom.app M))
      ((systemGeometricUnderlying BX m).map ((FB.evaluation m).hom.app M))
      ((IB n).moduleUnderlying.app (M.level n))
      ((IB m).moduleUnderlying.app (M.level m)) _ hv (FB.transition M h)
  let f (M : StrictRingSystem BY) : UX.obj (FB.functor.obj M) ⟶ FA.functor.obj (UY.obj M) :=
    { app := fun n ↦ (e n).hom.app M
      comm := by
        intro n m h
        apply (systemGeometricUnderlying AXs m).map_injective
        have : IsIso (ga M n) := by
          change IsIso
            (((systemGeometricUnderlying AXs n).mapIso ((FA.evaluation n).app (UY.obj M)) ≪≫
              IA.moduleUnderlying.app ((UY.obj M).level n) ≪≫
              uTop.inverse.mapIso ((systemGeometricUnderlying AYs n).mapIso
                ((systemNormalizationRestrictionEvaluation aY n).app M))).hom)
          infer_instance
        simp only [Functor.map_comp]
        change (systemGeometricUnderlying AXs m).map ((e m).hom.app M) ≫
            (systemGeometricUnderlying AXs m).map
              ((FA.functor.obj (UY.obj M)).transition h) =
          (systemGeometricUnderlying AXs m).map ((UX.obj (FB.functor.obj M)).transition h) ≫
            (systemGeometricUnderlying AXs n).map ((e n).hom.app M)
        exact normalization_transition_square _ _ (ga M n) (ga M m) (gb M n) (gb M m)
          _ _ _ (he M n) (he M m) (ha M h) (hb M h) }
  have hf (M : StrictRingSystem BY) : IsIso (f M) := by
    apply (strictRingSystem_isIso_iff AXs (f M)).2
    intro n
    change IsIso ((e n).hom.app M)
    infer_instance
  let scalar : FB.functor ⋙ UX ≅ UY ⋙ FA.functor :=
    NatIso.ofComponents (fun M ↦ asIso (f M)) (by
      intro M N t
      apply strictRingSystem_hom_ext AXs
      intro n
      exact (e n).hom.naturality t)
  refine ⟨{ level := level
            levelUnderlying := levelUnderlying
            scalar := scalar
            scalarEvaluation := ?_
            restriction := restriction
            restrictionUnderlying := restrictionUnderlying }, rfl, rfl⟩
  intro M n
  exact normalization_level_evaluation AY AX BY BX aY aX uTop IA IB FB FA level M n


variable (HB : StrictRingSystem BX ⥤ StrictRingSystem BY) [HB.Additive]
  (HA : StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX) ⥤
    StrictRingSystem ((Functor.const ℕᵒᵖ).obj AY)) [HA.Additive]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem ((Functor.const ℕᵒᵖ).obj AX))]
  (adjB : FB.functor ⊣ HB) (adjA : FA.functor ⊣ HA)
  (Hn : ∀ n : ℕ, systemLevel BX n ⥤ systemLevel BY n)
  [∀ n : ℕ, (Hn n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n)]
  (adjn : ∀ n : ℕ, FB.levelFunctor n ⊣ Hn n)
  (H0 : systemLevel ((Functor.const ℕᵒᵖ).obj AX) 0 ⥤
    systemLevel ((Functor.const ℕᵒᵖ).obj AY) 0) [H0.Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel ((Functor.const ℕᵒᵖ).obj AX) n)]
  (adj0 : FA.levelFunctor 0 ⊣ H0)

/-- Construct the normalization datum and prove invertibility of its derived mates.
Source: Stacks Project, Tags 03D2, 0D6E and 07A6.
(blueprint: lem-route-system-restriction-mate-coherence-data).

Proof: Define the scalar comparison levelwise by the supplied level comparison and
by the evaluation and restriction/evaluation isomorphisms. Naturality of the
underlying module comparison identifies its underlying map. The given transition
equations and faithfulness show that the components commute with transitions and
assemble into a strict-system natural isomorphism. Its defining component equation
proves scalarEvaluation. Apply the scalar and level/transition invertibility lemmas
to this explicitly constructed datum. -/
theorem SystemRestrictionMateCoherenceData
    (htransition : ∀ {n m : ℕ} (h : n ≤ m),
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (BY.map (homOfLE h).op)) ≫ (IB n).ringUnderlying.hom =
        (IB m).ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map
            (BX.map (homOfLE h).op))
    (halgebra : ∀ n : ℕ,
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (aY.app (op n))) ≫ (IB n).ringUnderlying.hom =
        IA.ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map (aX.app (op n)))
    (level : ∀ n : ℕ,
    FB.levelFunctor n ⋙ singletonLevelRestriction aX n ≅
      singletonLevelRestriction aY n ⋙ FA.levelFunctor 0)
    (levelUnderlying : ∀ (n : ℕ) (M : systemLevel BY n),
    (systemGeometricUnderlying ((Functor.const ℕᵒᵖ).obj AX) 0).map
          ((level n).hom.app M) ≫
        IA.moduleUnderlying.hom.app ((singletonLevelRestriction aY n).obj M) =
      (IB n).moduleUnderlying.hom.app M)
    (restriction : ∀ {n m : ℕ} (h : n ≤ m),
    FB.levelFunctor n ⋙ systemRestriction BX h ≅
      systemRestriction BY h ⋙ FB.levelFunctor m)
    (restrictionUnderlying : ∀ {n m : ℕ} (h : n ≤ m) (M : systemLevel BY n),
    (systemGeometricUnderlying BX m).map ((restriction h).hom.app M) ≫
        (IB m).moduleUnderlying.hom.app ((systemRestriction BY h).obj M) =
      (IB n).moduleUnderlying.hom.app M) :
    ∃ d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA,
      d.level = level ∧ @d.restriction = @restriction ∧
      IsIso (CategoryTheory.SystemEvaluationNormalization.derivedMate adjB adjA d.scalar) ∧
      (∀ n : ℕ, IsIso (CategoryTheory.SystemEvaluationNormalization.derivedMate
        (adjn n) adj0 (d.level n))) ∧
      (∀ {n m : ℕ} (h : n ≤ m),
        IsIso (CategoryTheory.SystemEvaluationNormalization.derivedMate
          (adjn n) (adjn m) (d.restriction h))) := by
  obtain ⟨d, hd, hr⟩ := normalization_exists AY AX BY BX aY aX uTop IA IB FB FA
    level levelUnderlying restriction restrictionUnderlying
  have hs := systemRestrictionScalarMateInvertibility AY AX BY BX aY aX uTop IA IB
    FB FA HB HA adjB adjA htransition halgebra d
  obtain ⟨hl, ht⟩ := systemRestrictionLevelMateInvertibility AY AX BY BX aY aX uTop
    IA IB FB FA Hn adjn H0 adj0 htransition halgebra d
  exact ⟨d, hd, hr, hs, hl, ht⟩

end SheafOfModules
