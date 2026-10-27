/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.CategoryTheory.AlgebraDiagramEvaluationOrdinaryComparisons
import all Sheaf.CategoryTheory.DerivedExactSquareCoherence

/-! # Coherence of unit-normalized algebra diagram comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

attribute [local instance 100000] evaluationRingCompose evaluationAddCompose evaluationSheafify
  evaluationLocallyBijective cacheKinj cacheSheafLimits cacheSheafColimits
  algebraDiagramModules_abelian

private theorem transpose_of_counit
    {A B Ap Bp : Type*} [Category* A] [Category* B] [Category* Ap] [Category* Bp]
    {F : B ⥤ A} {G : A ⥤ B} {Fp : Bp ⥤ Ap} {Gp : Ap ⥤ Bp}
    (adj : F ⊣ G) (adjp : Fp ⊣ Gp) (r : A ⥤ Ap) (s : B ⥤ Bp)
    (l : F ⋙ r ≅ s ⋙ Fp) (b : G ⋙ s ≅ r ⋙ Gp)
    (hc : ∀ N : A, r.map (adj.counit.app N) =
      l.hom.app (G.obj N) ≫ Fp.map (b.hom.app N) ≫ adjp.counit.app (r.obj N))
    (M : B) (N : A) (t : M ⟶ G.obj N) :
    (adjp.homEquiv (s.obj M) (r.obj N)).symm (s.map t ≫ b.hom.app N) =
      l.inv.app M ≫ r.map ((adj.homEquiv M N).symm t) := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, hc, Category.assoc]
  have hn := l.hom.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem transition_fac
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    {K : GrothendieckTopology C}
    (B : Sheaf (diagramSiteTopology J C K) RingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u} B)]
    [∀ j : J, HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramRingAt B j))]
    {j k : J} (a : j ⟶ k) (I : CochainComplex (ringedSiteModules.{u} B) ℤ) :
    (algebraDiagramDerivedTransition B a).app (DerivedCategory.Q.obj I) ≫
        (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow B a)).mapDerivedCategory.map
          ((algebraDiagramEvaluation B k).mapDerivedCategoryFactors.hom.app I) ≫
        (SheafOfModules.restrictScalars.{u}
          (algebraDiagramRingArrow B a)).mapDerivedCategoryFactors.hom.app
          (((algebraDiagramEvaluation B k).mapHomologicalComplex (.up ℤ)).obj I) =
      (algebraDiagramEvaluation B j).mapDerivedCategoryFactors.hom.app I ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (algebraDiagramTransition B a) (.up ℤ)).app I) := by
  dsimp only [algebraDiagramDerivedTransition, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors]
  rw [Localization.liftNatTrans_app]
  dsimp only [Localization.Lifting.iso]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    Functor.whiskerRight_app]
private theorem ordinary_cube
    {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {AX BX : Sheaf (diagramSiteTopology J C K) RingCat.{u}}
    {AY BY : Sheaf (diagramSiteTopology J D L) RingCat.{u}}
    (aX : AX ⟶ BX) (aY : AY ⟶ BY) (j : J)
    (fB : RingedToposMorphism BX BY) (fA : RingedToposMorphism AX AY)
    (gB : RingedToposMorphism (algebraDiagramRingAt BX j) (algebraDiagramRingAt BY j))
    (gA : RingedToposMorphism (algebraDiagramRingAt AX j) (algebraDiagramRingAt AY j))
    (G : Sheaf K (Type u) ⥤ Sheaf L (Type u))
    (hb : fB.direct = diagramCoefficientDirect J C D K L G)
    (ha : fA.direct = diagramCoefficientDirect J C D K L G)
    (hjb : gB.direct = G) (hja : gA.direct = G)
    (c : fB.modules ⋙ SheafOfModules.restrictScalars aY ≅
      SheafOfModules.restrictScalars aX ⋙ fA.modules)
    (cB : fB.modules ⋙ algebraDiagramEvaluation BY j ≅ algebraDiagramEvaluation BX j ⋙ gB.modules)
    (cA : fA.modules ⋙ algebraDiagramEvaluation AY j ≅ algebraDiagramEvaluation AX j ⋙ gA.modules)
    (cj : gB.modules ⋙ SheafOfModules.restrictScalars (algebraDiagramCoefficientAt aY j) ≅
      SheafOfModules.restrictScalars (algebraDiagramCoefficientAt aX j) ⋙ gA.modules)
    (hc : AlgebraDiagramOrdinaryRestrictionNormalized aX aY fB fA (hb.trans ha.symm) c)
    (hcB : AlgebraDiagramOrdinaryEvaluationNormalized G fB j gB hb hjb cB)
    (hcA : AlgebraDiagramOrdinaryEvaluationNormalized G fA j gA ha hja cA)
    (hcj : AlgebraDiagramOrdinaryRestrictionNormalized
      (algebraDiagramCoefficientAt aX j) (algebraDiagramCoefficientAt aY j)
      gB gA (hjb.trans hja.symm) cj)
    (M : ringedSiteModules.{u} BX) :
    (algebraDiagramEvaluation AY j).map (c.hom.app M) ≫
        cA.hom.app ((SheafOfModules.restrictScalars aX).obj M) ≫
        gA.modules.map ((algebraDiagramRestrictionEvaluation aX j).hom.app M) =
      (algebraDiagramRestrictionEvaluation aY j).hom.app (fB.modules.obj M) ≫
        (SheafOfModules.restrictScalars (algebraDiagramCoefficientAt aY j)).map (cB.hom.app M) ≫
        cj.hom.app ((algebraDiagramEvaluation BX j).obj M) := by
  let qB : fB.modules ⋙ diagramCoefficientUnderlying BY ≅
      diagramCoefficientUnderlying BX ⋙ diagramCoefficientDirect J C D K L G :=
    fB.underlying ≪≫ Functor.isoWhiskerLeft (diagramCoefficientUnderlying BX) (eqToIso hb)
  let qA : fA.modules ⋙ diagramCoefficientUnderlying AY ≅
      diagramCoefficientUnderlying AX ⋙ diagramCoefficientDirect J C D K L G :=
    fA.underlying ≪≫ Functor.isoWhiskerLeft (diagramCoefficientUnderlying AX) (eqToIso ha)
  let qjB : gB.modules ⋙ diagramCoefficientUnderlying (algebraDiagramRingAt BY j) ≅
      diagramCoefficientUnderlying (algebraDiagramRingAt BX j) ⋙ G :=
    gB.underlying ≪≫ Functor.isoWhiskerLeft
      (diagramCoefficientUnderlying (algebraDiagramRingAt BX j)) (eqToIso hjb)
  let qjA : gA.modules ⋙ diagramCoefficientUnderlying (algebraDiagramRingAt AY j) ≅
      diagramCoefficientUnderlying (algebraDiagramRingAt AX j) ⋙ G :=
    gA.underlying ≪≫ Functor.isoWhiskerLeft
      (diagramCoefficientUnderlying (algebraDiagramRingAt AX j)) (eqToIso hja)
  apply (diagramCoefficientUnderlying (algebraDiagramRingAt AY j)).map_injective
  simp only [Functor.map_comp]
  apply (cancel_mono (qjA.hom.app
    ((SheafOfModules.restrictScalars (algebraDiagramCoefficientAt aX j)).obj
      ((algebraDiagramEvaluation BX j).obj M)))).mp
  dsimp only [algebraDiagramRestrictionEvaluation, Iso.refl_hom, NatTrans.id_app]
  erw [Functor.map_id, Functor.map_id, Functor.map_id]
  simp only [Category.comp_id, Category.id_comp, Category.assoc]
  change
    (algebraDiagramSetEvaluation J D L j).map
        ((diagramCoefficientUnderlying AY).map (c.hom.app M)) ≫
      ((diagramCoefficientUnderlying (algebraDiagramRingAt AY j)).map
        (cA.hom.app ((SheafOfModules.restrictScalars aX).obj M)) ≫
          qjA.hom.app ((algebraDiagramEvaluation AX j).obj
            ((SheafOfModules.restrictScalars aX).obj M))) =
      (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map (cB.hom.app M) ≫
        ((diagramCoefficientUnderlying (algebraDiagramRingAt AY j)).map
          (cj.hom.app ((algebraDiagramEvaluation BX j).obj M)) ≫
            qjA.hom.app ((SheafOfModules.restrictScalars
              (algebraDiagramCoefficientAt aX j)).obj ((algebraDiagramEvaluation BX j).obj M)))
  have hc0 (N : ringedSiteModules.{u} BX) :
      (diagramCoefficientUnderlying AY).map (c.hom.app N) ≫
        qA.hom.app ((SheafOfModules.restrictScalars aX).obj N) = qB.hom.app N := by
    have hh := congrArg (fun t ↦ t ≫ (eqToIso ha).hom.app
      ((diagramCoefficientUnderlying BX).obj N)) (hc N)
    simpa only [qA, qB, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
      eqToIso.hom, eqToHom_app, eqToHom_trans] using hh
  have hcj0 (N : ringedSiteModules.{u} (algebraDiagramRingAt BX j)) :
      (diagramCoefficientUnderlying (algebraDiagramRingAt AY j)).map (cj.hom.app N) ≫
        qjA.hom.app ((SheafOfModules.restrictScalars (algebraDiagramCoefficientAt aX j)).obj N) =
          qjB.hom.app N := by
    have hh := congrArg (fun t ↦ t ≫ (eqToIso hja).hom.app
      ((diagramCoefficientUnderlying (algebraDiagramRingAt BX j)).obj N)) (hcj N)
    simpa only [qjA, qjB, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
      eqToIso.hom, eqToHom_app, eqToHom_trans] using hh
  have hcA0 (N : ringedSiteModules.{u} AX) :
      (diagramCoefficientUnderlying (algebraDiagramRingAt AY j)).map (cA.hom.app N) ≫
        qjA.hom.app ((algebraDiagramEvaluation AX j).obj N) =
      (algebraDiagramSetEvaluation J D L j).map (qA.hom.app N) ≫
        (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app
          ((diagramCoefficientUnderlying AX).obj N) := by
    simpa only [qA, qjA, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
      Category.assoc] using hcA N
  have hcB0 (N : ringedSiteModules.{u} BX) :
      (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map (cB.hom.app N) ≫
        qjB.hom.app ((algebraDiagramEvaluation BX j).obj N) =
      (algebraDiagramSetEvaluation J D L j).map (qB.hom.app N) ≫
        (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app
          ((diagramCoefficientUnderlying BX).obj N) := by
    simpa only [qB, qjB, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
      Category.assoc] using hcB N
  have hA := congrArg (fun t ↦
    (algebraDiagramSetEvaluation J D L j).map
      ((diagramCoefficientUnderlying AY).map (c.hom.app M)) ≫ t)
      (hcA0 ((SheafOfModules.restrictScalars aX).obj M))
  have h := congrArg (fun t ↦
    (algebraDiagramSetEvaluation J D L j).map t ≫
      (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app
        ((diagramCoefficientUnderlying BX).obj M)) (hc0 M)
  have hj := congrArg (fun t ↦
    (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map (cB.hom.app M) ≫ t)
    (hcj0 ((algebraDiagramEvaluation BX j).obj M))
  refine hA.trans (Eq.trans ?_ ((hcB0 M).symm.trans hj.symm))
  simp only [Functor.map_comp, Category.assoc] at h
  dsimp only [diagramCoefficientUnderlying, algebraDiagramEvaluation,
    SheafOfModules.restrictScalars, PresheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalarsObj] at h ⊢
  exact h
private theorem ordinary_transition
    {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {BX : Sheaf (diagramSiteTopology J C K) RingCat.{u}}
    {BY : Sheaf (diagramSiteTopology J D L) RingCat.{u}}
    (f : RingedToposMorphism BX BY) {j k : J} (a : j ⟶ k)
    (fj : RingedToposMorphism (algebraDiagramRingAt BX j) (algebraDiagramRingAt BY j))
    (fk : RingedToposMorphism (algebraDiagramRingAt BX k) (algebraDiagramRingAt BY k))
    (G : Sheaf K (Type u) ⥤ Sheaf L (Type u))
    (hf : f.direct = diagramCoefficientDirect J C D K L G)
    (hj : fj.direct = G) (hk : fk.direct = G)
    (cj : f.modules ⋙ algebraDiagramEvaluation BY j ≅ algebraDiagramEvaluation BX j ⋙ fj.modules)
    (ck : f.modules ⋙ algebraDiagramEvaluation BY k ≅ algebraDiagramEvaluation BX k ⋙ fk.modules)
    (ca : fk.modules ⋙ SheafOfModules.restrictScalars (algebraDiagramRingArrow BY a) ≅
      SheafOfModules.restrictScalars (algebraDiagramRingArrow BX a) ⋙ fj.modules)
    (hcj : AlgebraDiagramOrdinaryEvaluationNormalized G f j fj hf hj cj)
    (hck : AlgebraDiagramOrdinaryEvaluationNormalized G f k fk hf hk ck)
    (hca : AlgebraDiagramOrdinaryRestrictionNormalized
      (algebraDiagramRingArrow BX a) (algebraDiagramRingArrow BY a)
      fk fj (hk.trans hj.symm) ca)
    (M : ringedSiteModules.{u} BX) :
    (algebraDiagramTransition BY a).app (f.modules.obj M) ≫
        (SheafOfModules.restrictScalars (algebraDiagramRingArrow BY a)).map (ck.hom.app M) ≫
        ca.hom.app ((algebraDiagramEvaluation BX k).obj M) =
      cj.hom.app M ≫ fj.modules.map ((algebraDiagramTransition BX a).app M) := by
  let q : f.modules ⋙ diagramCoefficientUnderlying BY ≅
      diagramCoefficientUnderlying BX ⋙ diagramCoefficientDirect J C D K L G :=
    f.underlying ≪≫ Functor.isoWhiskerLeft (diagramCoefficientUnderlying BX) (eqToIso hf)
  let qj : fj.modules ⋙ diagramCoefficientUnderlying (algebraDiagramRingAt BY j) ≅
      diagramCoefficientUnderlying (algebraDiagramRingAt BX j) ⋙ G :=
    fj.underlying ≪≫ Functor.isoWhiskerLeft
      (diagramCoefficientUnderlying (algebraDiagramRingAt BX j)) (eqToIso hj)
  let qk : fk.modules ⋙ diagramCoefficientUnderlying (algebraDiagramRingAt BY k) ≅
      diagramCoefficientUnderlying (algebraDiagramRingAt BX k) ⋙ G :=
    fk.underlying ≪≫ Functor.isoWhiskerLeft
      (diagramCoefficientUnderlying (algebraDiagramRingAt BX k)) (eqToIso hk)
  have hca0 (N : ringedSiteModules.{u} (algebraDiagramRingAt BX k)) :
      (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map (ca.hom.app N) ≫
        qj.hom.app ((SheafOfModules.restrictScalars (algebraDiagramRingArrow BX a)).obj N) =
          qk.hom.app N := by
    have hh := congrArg (fun t ↦ t ≫ (eqToIso hj).hom.app
      ((diagramCoefficientUnderlying (algebraDiagramRingAt BX k)).obj N)) (hca N)
    simpa only [qj, qk, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
      eqToIso.hom, eqToHom_app, eqToHom_trans] using hh
  have hcj0 (N : ringedSiteModules.{u} BX) :
      (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map (cj.hom.app N) ≫
        qj.hom.app ((algebraDiagramEvaluation BX j).obj N) =
      (algebraDiagramSetEvaluation J D L j).map (q.hom.app N) ≫
        (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app
          ((diagramCoefficientUnderlying BX).obj N) := by
    simpa only [q, qj, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
      Category.assoc] using hcj N
  have hck0 (N : ringedSiteModules.{u} BX) :
      (diagramCoefficientUnderlying (algebraDiagramRingAt BY k)).map (ck.hom.app N) ≫
        qk.hom.app ((algebraDiagramEvaluation BX k).obj N) =
      (algebraDiagramSetEvaluation J D L k).map (q.hom.app N) ≫
        (algebraDiagramSetDirectEvaluation J C D K L G k).hom.app
          ((diagramCoefficientUnderlying BX).obj N) := by
    simpa only [q, qk, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp,
      Category.assoc] using hck N
  apply (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map_injective
  apply (cancel_mono (qj.hom.app ((SheafOfModules.restrictScalars
    (algebraDiagramRingArrow BX a)).obj ((algebraDiagramEvaluation BX k).obj M)))).mp
  simp only [Functor.map_comp, Category.assoc]
  change
    (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map
      ((algebraDiagramTransition BY a).app (f.modules.obj M)) ≫
      ((diagramCoefficientUnderlying (algebraDiagramRingAt BY k)).map (ck.hom.app M) ≫
        ((diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map
          (ca.hom.app ((algebraDiagramEvaluation BX k).obj M)) ≫
          qj.hom.app ((SheafOfModules.restrictScalars (algebraDiagramRingArrow BX a)).obj
            ((algebraDiagramEvaluation BX k).obj M)))) =
    (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map (cj.hom.app M) ≫
      ((fj.modules ⋙ diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map
        ((algebraDiagramTransition BX a).app M) ≫
          qj.hom.app ((SheafOfModules.restrictScalars (algebraDiagramRingArrow BX a)).obj
            ((algebraDiagramEvaluation BX k).obj M)))
  have hleft := congrArg (fun z ↦
    (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map
      ((algebraDiagramTransition BY a).app (f.modules.obj M)) ≫
      ((diagramCoefficientUnderlying (algebraDiagramRingAt BY k)).map (ck.hom.app M) ≫ z))
      (hca0 ((algebraDiagramEvaluation BX k).obj M))
  have hright := congrArg (fun z ↦
    (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map (cj.hom.app M) ≫ z)
    (qj.hom.naturality ((algebraDiagramTransition BX a).app M))
  have hjpost := congrArg (fun z ↦ z ≫
    G.map ((diagramCoefficientUnderlying (algebraDiagramRingAt BX j)).map
      ((algebraDiagramTransition BX a).app M))) (hcj0 M)
  refine hleft.trans (Eq.trans ?_ (hright.trans
    (by simpa only [Functor.comp_map, Category.assoc] using hjpost)).symm)
  have hck' := hck0 M
  ext U t
  have he := (q.hom.app M).hom.naturality
    (Quiver.Hom.op (Prod.mkHom a.op (𝟙 U.unop)))
  have hckU := congrArg (fun q ↦ q.hom.app U
    (((algebraDiagramTransition BY a).app (f.modules.obj M)).val.app U t)) hck'
  have heU := CategoryTheory.congr_fun he t
  dsimp [algebraDiagramSetDirectEvaluation, diagramSiteSheafEquivalence,
    diagramSiteSheafCurry, diagramSiteSheafUncurry] at hckU ⊢
  change _ = _ at heU
  have hmap : ((diagramCoefficientUnderlying BX ⋙
      diagramCoefficientDirect J C D K L G).obj M).obj.map
      (Prod.mkHom a.op (𝟙 U.unop)).op =
      (G.map ((diagramCoefficientUnderlying (algebraDiagramRingAt BX j)).map
        ((algebraDiagramTransition BX a).app M))).hom.app U := by
    dsimp only [Functor.comp_obj, diagramCoefficientDirect,
      diagramSiteSheafEquivalence, diagramSiteSheafUncurry, diagramSiteUncurry]
    change (G.map (((diagramSiteSheafCurry J C K).obj
      ((diagramCoefficientUnderlying BX).obj M)).map a)).hom.app U ≫
        (G.obj (((diagramSiteSheafCurry J C K).obj
          ((diagramCoefficientUnderlying BX).obj M)).obj k)).obj.map (𝟙 U) = _
    rw [Functor.map_id, Category.comp_id]
    congr 1
  rw [hmap] at heU
  have hh := hckU.trans heU
  simp only [ConcreteCategory.comp_apply] at hh ⊢
  dsimp only [diagramCoefficientUnderlying, algebraDiagramEvaluation,
    SheafOfModules.restrictScalars, PresheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalarsObj] at hh ⊢
  exact hh


attribute [local irreducible] algebraDiagramConstantRing Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.mapDerivedCategoryCompIso

namespace AlgebraDiagramAdjunctionPresentation

attribute [local instance 100000] eAX_additive eAY_additive eAX_limits eAY_limits
  eAX_colimits eAY_colimits

variable {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D} {A : CommRingCat.{u}}
    (p : AlgebraDiagramAdjunctionPresentation J C D K L A)

variable [HasDerivedCategory.{w} (ringedSiteModules.{u} p.BX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} p.BY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} p.AX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} p.AY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramConstantRing K A))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramConstantRing L A))]
    [∀ j : J, HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramRingAt p.BX j))]
    [∀ j : J, HasDerivedCategory.{w} (ringedSiteModules.{u} (algebraDiagramRingAt p.BY j))]


variable [∀ j : J, (p.eAX j).Additive] [∀ j : J, (p.eAY j).Additive]
    [∀ j : J, PreservesFiniteLimits (p.eAX j)]
    [∀ j : J, PreservesFiniteLimits (p.eAY j)]
    [∀ j : J, PreservesFiniteColimits (p.eAX j)]
    [∀ j : J, PreservesFiniteColimits (p.eAY j)]

variable (o : p.OrdinaryComparisons)
  (d : p.PB ⋙ p.rY.mapDerivedCategory ≅ p.rX.mapDerivedCategory ⋙ p.PA)
  (beta : ∀ j : J, p.PB ⋙ (p.eBY j).mapDerivedCategory ≅
    (p.eBX j).mapDerivedCategory ⋙ p.Pj j)
  (delta : ∀ j : J, p.PA ⋙ (p.eAY j).mapDerivedCategory ≅
    (p.eAX j).mapDerivedCategory ⋙ p.P)
  (dj : ∀ j : J, p.Pj j ⋙ (p.rYj j).mapDerivedCategory ≅
    (p.rXj j).mapDerivedCategory ⋙ p.P)
  (qaB : ∀ {j k : J} (a : j ⟶ k),
    p.Pj k ⋙ (SheafOfModules.restrictScalars.{u}
        (algebraDiagramRingArrow p.BY a)).mapDerivedCategory ≅
      (SheafOfModules.restrictScalars.{u}
        (algebraDiagramRingArrow p.BX a)).mapDerivedCategory ⋙ p.Pj j)
  (qaA : ∀ {j k : J} (a : j ⟶ k),
    p.P ⋙ (SheafOfModules.restrictScalars.{u}
        (algebraDiagramRingArrow p.AY a)).mapDerivedCategory ≅
      (SheafOfModules.restrictScalars.{u}
        (algebraDiagramRingArrow p.AX a)).mapDerivedCategory ⋙ p.P)

/-- The coherence equations after the comparison isomorphisms have been constructed.
Source: Stacks 07A6 and 0D6E, uniqueness of normalized derived transformations.
(blueprint: lem-pur-algebra-diagram-derived-comparison-coherence). -/
structure DerivedComparisonCoherence : Prop where
  counit : ∀ (j : J) (N : DerivedCategory (ringedSiteModules.{u} p.BX)),
    (p.eBX j).mapDerivedCategory.map (p.adjDB.counit.app N) =
      (Functor.mapDerivedCategorySquareIso (o.lambda j)).hom.app (p.PB.obj N) ≫
        (p.Gj j).map ((beta j).hom.app N) ≫
        (p.adjDj j).counit.app ((p.eBX j).mapDerivedCategory.obj N)
  transpose : ∀ (j : J) (M : DerivedCategory (ringedSiteModules.{u} p.BY))
      (N : DerivedCategory (ringedSiteModules.{u} p.BX)) (t : M ⟶ p.PB.obj N),
    ((p.adjDj j).homEquiv ((p.eBY j).mapDerivedCategory.obj M)
      ((p.eBX j).mapDerivedCategory.obj N)).symm
        ((p.eBY j).mapDerivedCategory.map t ≫ (beta j).hom.app N) =
      (Functor.mapDerivedCategorySquareIso (o.lambda j)).inv.app M ≫
        (p.eBX j).mapDerivedCategory.map ((p.adjDB.homEquiv M N).symm t)
  coefficient : ∀ (j : J) (N : DerivedCategory (ringedSiteModules.{u} p.BX)),
    (p.eAY j).mapDerivedCategory.map (d.hom.app N) ≫
        (delta j).hom.app (p.rX.mapDerivedCategory.obj N) ≫
        p.P.map ((Functor.mapDerivedCategorySquareIso
          (algebraDiagramRestrictionEvaluation p.aX j)).hom.app N) =
      (Functor.mapDerivedCategorySquareIso
        (algebraDiagramRestrictionEvaluation p.aY j)).hom.app (p.PB.obj N) ≫
        (p.rYj j).mapDerivedCategory.map ((beta j).hom.app N) ≫
        (dj j).hom.app ((p.eBX j).mapDerivedCategory.obj N)
  transitionB : ∀ {j k : J} (a : j ⟶ k)
      (N : DerivedCategory (ringedSiteModules.{u} p.BX)),
    (algebraDiagramDerivedTransition p.BY a).app (p.PB.obj N) ≫
        (SheafOfModules.restrictScalars.{u}
          (algebraDiagramRingArrow p.BY a)).mapDerivedCategory.map
          ((beta k).hom.app N) ≫ (qaB a).hom.app ((p.eBX k).mapDerivedCategory.obj N) =
      (beta j).hom.app N ≫
        (p.Pj j).map ((algebraDiagramDerivedTransition p.BX a).app N)
  transitionA : ∀ {j k : J} (a : j ⟶ k)
      (N : DerivedCategory (ringedSiteModules.{u} p.AX)),
    (algebraDiagramDerivedTransition p.AY a).app (p.PA.obj N) ≫
        (SheafOfModules.restrictScalars.{u}
          (algebraDiagramRingArrow p.AY a)).mapDerivedCategory.map
          ((delta k).hom.app N) ≫ (qaA a).hom.app ((p.eAX k).mapDerivedCategory.obj N) =
      (delta j).hom.app N ≫ p.P.map ((algebraDiagramDerivedTransition p.AX a).app N)

/-- Unit-normalized comparisons respect mates, coefficient squares and actual transitions.
Source: Stacks 07A6 and 0D6E, the common-resolution normalization and adjunction Hom formula.
(blueprint: lem-pur-algebra-diagram-derived-comparison-coherence).

Proof: The ordinary counit field identifies cB with the mate of lambda inverse.
Localize lambda termwise and take its mate under the specified derived adjunctions.
The derived mate unit formula gives exactly the normalization hbeta. Uniqueness of
right derived transformations identifies this mate with beta: after precomposition
with Q and the right-derived unit both transformations are the same ordinary map.
The mate counit equation gives counit, and unit naturality gives the transpose
formula for an arbitrary morphism t. For the coefficient square, precompose both
routes with Q and the unit of fB. Apply hd, hbeta, hdelta and hdj and naturality of
the exact-localization factorization isomorphisms. The results are Q applied to the
two ordinary coefficient/evaluation composites, followed by the unit of s. These
ordinary composites agree after forgetting to sheaves of sets: each is the supplied
underlying direct-image comparison and the diagram-site equivalence counit. The
forgetful functor is faithful, so they agree as module maps. Right-derived uniqueness
proves the required equality; it does not assert faithfulness of derived forgetting.
For an actual arrow a, repeat the calculation with the localized ordinary transition.
Its naturality and the structural ring-map naturality identify both ordinary routes.
Use hqaB and hqaA for the restriction comparison normalizations. Localization and
right-derived uniqueness give transitionB and transitionA, for identities and
nonidentity endomorphisms alike. -/
theorem derivedComparisonCoherence
    (hd : AlgebraDiagramDerivedSquareNormalized p.fB.modules p.fA.modules
      p.rX p.rY o.c d)
    (hbeta : ∀ j : J, AlgebraDiagramDerivedSquareNormalized
      p.fB.modules (p.fj j).modules (p.eBX j) (p.eBY j) (o.cB j) (beta j))
    (hdelta : ∀ j : J, AlgebraDiagramDerivedSquareNormalized
      p.fA.modules p.s.modules (p.eAX j) (p.eAY j) (o.cA j) (delta j))
    (hdj : ∀ j : J, AlgebraDiagramDerivedSquareNormalized
      (p.fj j).modules p.s.modules (p.rXj j) (p.rYj j) (o.cj j) (dj j))
    (hqaB : ∀ {j k : J} (a : j ⟶ k), AlgebraDiagramDerivedSquareNormalized
      (p.fj k).modules (p.fj j).modules
      (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BX a))
      (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BY a))
      (o.caB a) (qaB a))
    (hqaA : ∀ {j k : J} (a : j ⟶ k), AlgebraDiagramDerivedSquareNormalized
      p.s.modules p.s.modules
      (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AX a))
      (SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AY a))
      (o.caA a) (qaA a)) :
    p.DerivedComparisonCoherence o d beta delta dj qaB qaA := by
  have hc (j : J) := ExactDerivedSquare.square_counit
    p.fB.modules (p.fj j).modules (p.eBX j) (p.eBY j) p.pullB (p.pullj j)
    p.moduleAdjB (p.moduleAdjj j) (o.lambda j) (o.cB j) (o.counit j)
    (beta j) (hbeta j)
  refine ⟨hc, ?_, ?_, ?_, ?_⟩
  · intro j M N t
    exact transpose_of_counit p.adjDB (p.adjDj j)
      (p.eBX j).mapDerivedCategory (p.eBY j).mapDerivedCategory
      (Functor.mapDerivedCategorySquareIso (o.lambda j)) (beta j) (hc j) M N t
  · intro j N
    exact ExactDerivedSquare.normalized_cube p.fB.modules p.fA.modules p.rX p.rY
      p.s.modules (p.fj j).modules (p.eAX j) (p.eAY j)
      (p.eBX j) (p.eBY j) (p.rXj j) (p.rYj j)
      o.c (o.cA j) (o.cB j) (o.cj j) d (delta j) (beta j) (dj j)
      hd (hdelta j) (hbeta j) (hdj j)
      (algebraDiagramRestrictionEvaluation p.aX j)
      (algebraDiagramRestrictionEvaluation p.aY j)
      (fun M ↦ (ordinary_cube p.aX p.aY j p.fB p.fA (p.fj j) p.s p.s.direct
        p.directB p.directA (p.directLevel j) rfl o.c (o.cB j) (o.cA j) (o.cj j)
        o.hc (o.hcB j) (o.hcA j) (o.hcj j) M).symm) N
  · intro j k a N
    exact ExactDerivedSquare.normalized_transition
      p.fB.modules (p.fj j).modules (p.eBX j) (p.eBY j)
      (p.fj k).modules (p.eBX k) (p.eBY k)
      (SheafOfModules.restrictScalars (algebraDiagramRingArrow p.BX a))
      (SheafOfModules.restrictScalars (algebraDiagramRingArrow p.BY a))
      (o.cB j) (o.cB k) (o.caB a) (beta j) (beta k) (qaB a)
      (hbeta j) (hbeta k) (hqaB a)
      (algebraDiagramTransition p.BX a) (algebraDiagramTransition p.BY a)
      (algebraDiagramDerivedTransition p.BX a) (algebraDiagramDerivedTransition p.BY a)
      (transition_fac p.BX a) (transition_fac p.BY a)
      (ordinary_transition p.fB a (p.fj j) (p.fj k) p.s.direct p.directB
        (p.directLevel j) (p.directLevel k) (o.cB j) (o.cB k) (o.caB a)
        (o.hcB j) (o.hcB k) (o.hcaB a)) N
  · intro j k a N
    exact ExactDerivedSquare.normalized_transition p.fA.modules p.s.modules
      (p.eAX j) (p.eAY j) p.s.modules (p.eAX k) (p.eAY k)
      (SheafOfModules.restrictScalars (algebraDiagramRingArrow p.AX a))
      (SheafOfModules.restrictScalars (algebraDiagramRingArrow p.AY a))
      (o.cA j) (o.cA k) (o.caA a) (delta j) (delta k) (qaA a)
      (hdelta j) (hdelta k) (hqaA a)
      (algebraDiagramTransition p.AX a) (algebraDiagramTransition p.AY a)
      (algebraDiagramDerivedTransition p.AX a) (algebraDiagramDerivedTransition p.AY a)
      (transition_fac p.AX a) (transition_fac p.AY a)
      (ordinary_transition p.fA a p.s p.s p.s.direct p.directA rfl rfl
        (o.cA j) (o.cA k) (o.caA a) (o.hcA j) (o.hcA k) (o.hcaA a)) N

end AlgebraDiagramAdjunctionPresentation
end CategoryTheory
