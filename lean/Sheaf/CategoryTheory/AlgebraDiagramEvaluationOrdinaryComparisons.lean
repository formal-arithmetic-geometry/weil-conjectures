/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.CategoryTheory.AlgebraDiagramEvaluationAdjunctionNormalizationDefs
import Sheaf.CategoryTheory.CartesianModulePullbackUnderlying
import all Sheaf.CategoryTheory.DiagramRingRestrictionPushforward
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Normalized ordinary evaluation comparisons for an algebra diagram -/


@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

attribute [local instance 100000] evaluationRingCompose evaluationAddCompose evaluationSheafify
  evaluationLocallyBijective cacheKinj cacheSheafLimits cacheSheafColimits
  algebraDiagramModules_abelian

private theorem hom_heq_cast {E : Type (u + 1)} [Category.{u} E]
    {X X' Y Y' : E} (hx : X = X') (hy : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) :
    f ≫ eqToHom hy = eqToHom hx ≫ g := by
  subst X'
  subst Y'
  simpa using eq_of_heq h

private theorem sheaf_app_heq {C : Type u} [SmallCategory C]
    {K : GrothendieckTopology C} {X X' Y Y' : Sheaf K (Type u)}
    (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : HEq f g) (U : Cᵒᵖ) : HEq (f.hom.app U) (g.hom.app U) := by
  subst X'
  subst Y'
  exact heq_of_eq (congrArg (fun z ↦ z.hom.app U) (eq_of_heq h))
private theorem transpose_eval
    {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {F : Sheaf L (Type u) ⥤ Sheaf K (Type u)}
    {G : Sheaf K (Type u) ⥤ Sheaf L (Type u)} (adj : F ⊣ G)
    (T : Sheaf (diagramSiteTopology J D L) (Type u))
    (M : Sheaf (diagramSiteTopology J C K) (Type u))
    (h : T ⟶ (diagramCoefficientDirect J C D K L G).obj M) (j : J) :
    ∀ (U : Cᵒᵖ) (t : (F.obj (((diagramSiteSheafCurry J D L).obj T).obj j)).obj.obj U),
    (((diagramSiteSheafCurry J C K).map
      (((diagramCoefficientAdjunction J C D K L adj).homEquiv T M).symm h)).app j).hom.app U t =
    ((adj.homEquiv ((diagramSiteSheafCurry J D L).obj T |>.obj j)
      ((diagramSiteSheafCurry J C K).obj M |>.obj j)).symm
        (((diagramSiteSheafCurry J D L).map h).app j ≫
          (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app M)).hom.app U t := by
  intro U t
  simp only [Adjunction.homEquiv_counit]
  simp only [diagramCoefficientAdjunction, Adjunction.comp_counit_app]
  dsimp [diagramCoefficientInverse, diagramSiteSheafEquivalence, diagramSiteSheafCurry,
    diagramSiteSheafUncurry, algebraDiagramSetDirectEvaluation]
  simp only [Functor.map_comp]
  rfl
private theorem ordinary_eval
    {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {BX : Sheaf (diagramSiteTopology J C K) RingCat.{u}}
    {BY : Sheaf (diagramSiteTopology J D L) RingCat.{u}}
    {F : Sheaf L (Type u) ⥤ Sheaf K (Type u)}
    {G : Sheaf K (Type u) ⥤ Sheaf L (Type u)} (adj : F ⊣ G)
    (f : RingedToposMorphism BX BY) (j : J)
    (g : RingedToposMorphism (algebraDiagramRingAt BX j) (algebraDiagramRingAt BY j))
    (hfInv : f.inverse = diagramCoefficientInverse J C D K L F)
    (hfDir : f.direct = diagramCoefficientDirect J C D K L G)
    (hfAdj : HEq f.adj (diagramCoefficientAdjunction J C D K L adj))
    (hgInv : g.inverse = F) (hgDir : g.direct = G) (hgAdj : HEq g.adj adj)
    (hRing : HEq (((diagramSiteSheafCurry J C K).map f.ringMap).app j) g.ringMap) :
    ∃ c : f.modules ⋙ algebraDiagramEvaluation BY j ≅
        algebraDiagramEvaluation BX j ⋙ g.modules,
      AlgebraDiagramOrdinaryEvaluationNormalized G f j g hfDir hgDir c := by
  classical
  rcases f with ⟨F', G', adj', hF, p, hp0, hp1, hpadd, hpmul, H, hH, eH, hlinH⟩
  rcases g with ⟨F'', G'', adj'', hF', q, hq0, hq1, hqadd, hqmul, I, hI, eI, hlinI⟩
  dsimp only at hfInv hfDir hfAdj hgInv hgDir hgAdj hRing ⊢
  subst F'
  subst G'
  cases hfAdj
  subst F''
  subst G''
  cases hgAdj
  unfold AlgebraDiagramOrdinaryEvaluationNormalized
  dsimp only
  clear hp0 hp1 hpadd hpmul hq0 hq1 hqadd hqmul hF hF'
  let evX := algebraDiagramEvaluation BX j
  let evY := algebraDiagramEvaluation BY j
  let ex := algebraDiagramSetEvaluation J C K j
  let ey := algebraDiagramSetEvaluation J D L j
  let α (M : ringedSiteModules.{u} BX) :
      (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).obj (evY.obj (H.obj M)) ≅
        (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).obj (I.obj (evX.obj M)) :=
    ey.mapIso (eH.app M) ≪≫
      (algebraDiagramSetDirectEvaluation J C D K L G j).app
        ((diagramCoefficientUnderlying BX).obj M) ≪≫ (eI.app (evX.obj M)).symm
  have hα (M : ringedSiteModules.{u} BX) :
      (α M).hom ≫ eI.hom.app (evX.obj M) = ey.map (eH.hom.app M) ≫
        (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app
          ((diagramCoefficientUnderlying BX).obj M) := by
    change ((ey.map (eH.hom.app M) ≫
      (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app
        ((diagramCoefficientUnderlying BX).obj M)) ≫ eI.inv.app (evX.obj M)) ≫ _ = _
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  have hlinear (M : ringedSiteModules.{u} BX)
      (T : Sheaf (diagramSiteTopology J D L) (Type u))
      (a : T ⟶ (sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj BY)
      (x y : T ⟶ (diagramCoefficientUnderlying BY).obj (H.obj M)) :
      ey.map (linearOperation (H.obj M) T a x y) ≫ (α M).hom =
        linearOperation (I.obj (evX.obj M)) (ey.obj T) (ey.map a)
          (ey.map x ≫ (α M).hom) (ey.map y ≫ (α M).hom) := by
    apply (cancel_mono (eI.hom.app (evX.obj M))).mp
    apply (adj.homEquiv (ey.obj T) ((diagramCoefficientUnderlying
      (algebraDiagramRingAt BX j)).obj (evX.obj M))).symm.injective
    rw [Category.assoc, hα]
    ext U t
    have hb := hlinH M T a x y (linearOperation (H.obj M) T a x y)
      (fun _ _ ↦ rfl) (op (op j, U.unop)) t
    have hs := hlinI (evX.obj M) (ey.obj T) (ey.map a)
      (ey.map x ≫ (α M).hom) (ey.map y ≫ (α M).hom)
      (linearOperation (I.obj (evX.obj M)) (ey.obj T) (ey.map a)
        (ey.map x ≫ (α M).hom) (ey.map y ≫ (α M).hom)) (fun _ _ ↦ rfl) U t
    simp only [Category.assoc, hα] at hs
    have hb2 := transpose_eval adj T ((diagramCoefficientUnderlying BX).obj M)
      (linearOperation (H.obj M) T a x y ≫ eH.hom.app M) j U t
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc] at hb2
    have hx2 := transpose_eval adj T ((diagramCoefficientUnderlying BX).obj M)
      (x ≫ eH.hom.app M) j U t
    have hy2 := transpose_eval adj T ((diagramCoefficientUnderlying BX).obj M)
      (y ≫ eH.hom.app M) j U t
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc] at hx2 hy2
    erw [← hx2, ← hy2] at hs
    apply hb2.symm.trans
    have hInput : ((diagramSiteSheafCurry J D L).obj
        ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj BY)).obj j =
        (sheafCompose L (forget RingCat)).obj (algebraDiagramRingAt BY j) := by
      apply ObjectProperty.FullSubcategory.ext
      rfl
    have hr (v : (F.obj ((sheafCompose L (forget RingCat)).obj
        (algebraDiagramRingAt BY j))).obj.obj U) :
        (p.hom.app (op (op j, U.unop))) v = q.hom.app U v := by
      have he : ex.obj ((diagramCoefficientInverse J C D K L F).obj
          ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj BY)) =
          F.obj ((sheafCompose L (forget RingCat)).obj (algebraDiagramRingAt BY j)) := by
        trans F.obj (((diagramSiteSheafCurry J D L).obj
          ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj BY)).obj j)
        · apply ObjectProperty.FullSubcategory.ext
          apply Functor.ext
          · intro V W f
            change (F.map (((diagramSiteSheafCurry J D L).obj
              ((sheafCompose (diagramSiteTopology J D L)
                (forget RingCat)).obj BY)).map (𝟙 j))).hom.app V ≫ _ = _
            rw [Functor.map_id, Functor.map_id]
            simp
            rfl
          · intro V
            rfl
        · exact congrArg F.obj hInput
      have ht : ex.obj ((sheafCompose (diagramSiteTopology J C K)
          (forget RingCat)).obj BX) =
          (sheafCompose K (forget RingCat)).obj (algebraDiagramRingAt BX j) := rfl
      have hh := hRing
      change HEq (ex.map p) q at hh
      have hh' := eq_of_heq (sheaf_app_heq he ht _ _ hh U)
      exact CategoryTheory.congr_fun hh' v
    have hr2 := hr ((F.map (ey.map a)).hom.app U t)
    change _ = _ at hr2
    erw [hr2] at hb
    exact hb.trans hs.symm
  let one (T : Sheaf (diagramSiteTopology J D L) (Type u)) :
      T ⟶ (sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj BY :=
    ⟨{ app := fun U ↦ ↾(fun _ ↦ (1 : BY.obj.obj U))
       naturality := by intro U V f; ext t; exact (BY.obj.map f).hom.map_one.symm }⟩
  have hadd (M : ringedSiteModules.{u} BX) (U : Dᵒᵖ)
      (x y : (evY.obj (H.obj M)).val.obj U) :
      (α M).hom.hom.app U (x + y) =
        (show (I.obj (evX.obj M)).val.obj U from (α M).hom.hom.app U x) +
          (show (I.obj (evX.obj M)).val.obj U from (α M).hom.hom.app U y) := by
    let X := (diagramCoefficientUnderlying BY).obj (H.obj M)
    have hh := congrArg (fun f ↦ f.hom.app U (x, y))
      (hlinear M (X ⊗ X) (one _) (CartesianMonoidalCategory.fst X X)
        (CartesianMonoidalCategory.snd X X))
    change (α M).hom.hom.app U ((1 : (algebraDiagramRingAt BY j).obj.obj U) • x + y) =
      (1 : (algebraDiagramRingAt BY j).obj.obj U) •
        (show (I.obj (evX.obj M)).val.obj U from (α M).hom.hom.app U x) +
          (show (I.obj (evX.obj M)).val.obj U from (α M).hom.hom.app U y) at hh
    simpa only [one_smul] using hh
  have hsmul (M : ringedSiteModules.{u} BX) (U : Dᵒᵖ)
      (r : (algebraDiagramRingAt BY j).obj.obj U) (x : (evY.obj (H.obj M)).val.obj U) :
      (α M).hom.hom.app U (r • x) = r •
        (show (I.obj (evX.obj M)).val.obj U from (α M).hom.hom.app U x) := by
    let X := (diagramCoefficientUnderlying BY).obj (H.obj M)
    let R := (sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj BY
    let z : R ⊗ X ⟶ X :=
      ⟨{ app := fun U ↦ ↾(fun _ ↦ (0 : (H.obj M).val.obj U))
         naturality := by
           intro U V f
           ext t
           exact ((H.obj M).val.map f).hom.map_zero.symm }⟩
    have hh := congrArg (fun f ↦ f.hom.app U (r, x))
      (hlinear M (R ⊗ X) (CartesianMonoidalCategory.fst R X)
        (CartesianMonoidalCategory.snd R X) z)
    have hzero : (α M).hom.hom.app U (0 : (evY.obj (H.obj M)).val.obj U) =
        (0 : (I.obj (evX.obj M)).val.obj U) := by
      have hz := hadd M U 0 0
      exact (@add_eq_left ((I.obj (evX.obj M)).val.obj U)
        inferInstance inferInstance _ _).mp (by simpa only [zero_add] using hz.symm)
    change (α M).hom.hom.app U (r • x + (0 : (evY.obj (H.obj M)).val.obj U)) = r •
      (show (I.obj (evX.obj M)).val.obj U from (α M).hom.hom.app U x) +
        (show (I.obj (evX.obj M)).val.obj U from
          (α M).hom.hom.app U (0 : (evY.obj (H.obj M)).val.obj U)) at hh
    simpa only [add_zero, hzero] using hh
  let f (M : ringedSiteModules.{u} BX) : evY.obj (H.obj M) ⟶ I.obj (evX.obj M) :=
    { val :=
        { app := fun U ↦ @ModuleCat.ofHom ((algebraDiagramRingAt BY j).obj.obj U) inferInstance
            ((evY.obj (H.obj M)).val.obj U) ((I.obj (evX.obj M)).val.obj U)
            ((evY.obj (H.obj M)).val.obj U).isAddCommGroup
            ((evY.obj (H.obj M)).val.obj U).isModule
            ((I.obj (evX.obj M)).val.obj U).isAddCommGroup
            ((I.obj (evX.obj M)).val.obj U).isModule
            { toFun := (α M).hom.hom.app U
              map_add' := hadd M U
              map_smul' := hsmul M U }
          naturality := by
            intro U V h
            ext x
            exact CategoryTheory.congr_fun ((α M).hom.hom.naturality h) x } }
  have hf (M : ringedSiteModules.{u} BX) :
      (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map (f M) = (α M).hom := rfl
  have hi (M : ringedSiteModules.{u} BX) : IsIso (f M) := by
    have : IsIso ((diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map (f M)) := by
      rw [hf]; infer_instance
    exact isIso_of_reflects_iso (f M) (diagramCoefficientUnderlying (algebraDiagramRingAt BY j))
  let β : H ⋙ evY ⟶ evX ⋙ I :=
    { app := f
      naturality := by
        intro M N h
        apply (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map_injective
        simp only [Functor.map_comp, hf]
        let e : (H ⋙ evY) ⋙ diagramCoefficientUnderlying (algebraDiagramRingAt BY j) ≅
            (evX ⋙ I) ⋙ diagramCoefficientUnderlying (algebraDiagramRingAt BY j) :=
          Functor.isoWhiskerRight eH ey ≪≫
            Functor.isoWhiskerLeft (diagramCoefficientUnderlying BX)
              (algebraDiagramSetDirectEvaluation J C D K L G j) ≪≫
            (Functor.isoWhiskerLeft evX eI).symm
        exact e.hom.naturality h }
  have : IsIso β := NatIso.isIso_of_isIso_app β
  refine ⟨asIso β, ?_⟩
  intro M
  change (α M).hom ≫ eI.hom.app (evX.obj M) ≫ 𝟙 _ =
    ey.map (eH.hom.app M) ≫ ey.map (𝟙 _) ≫ _
  simpa only [Functor.map_id, Category.comp_id, Category.id_comp] using hα M
private def inverse_eval_iso
    {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    (F : Sheaf L (Type u) ⥤ Sheaf K (Type u)) (j : J) :
    diagramCoefficientInverse J C D K L F ⋙ algebraDiagramSetEvaluation J C K j ≅
      algebraDiagramSetEvaluation J D L j ⋙ F :=
  NatIso.ofComponents (fun M ↦ ((evaluation J (Sheaf K (Type u))).obj j).mapIso
    ((diagramSiteSheafEquivalence J C K).counitIso.app
      (((Functor.whiskeringRight J _ _).obj F).obj
        ((diagramSiteSheafEquivalence J D L).functor.obj M)))) (by
    intro M N a
    exact congrArg (fun z ↦ z.app j)
      ((diagramSiteSheafEquivalence J C K).counitIso.hom.naturality
        (((Functor.whiskeringRight J _ _).obj F).map
          ((diagramSiteSheafEquivalence J D L).functor.map a))))
private theorem transpose_eval_morphism
    {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {F : Sheaf L (Type u) ⥤ Sheaf K (Type u)}
    {G : Sheaf K (Type u) ⥤ Sheaf L (Type u)} (adj : F ⊣ G)
    (T : Sheaf (diagramSiteTopology J D L) (Type u))
    (M : Sheaf (diagramSiteTopology J C K) (Type u))
    (h : T ⟶ (diagramCoefficientDirect J C D K L G).obj M) (j : J) :
    (algebraDiagramSetEvaluation J C K j).map
      (((diagramCoefficientAdjunction J C D K L adj).homEquiv T M).symm h) =
      (inverse_eval_iso F j).hom.app T ≫
        ((adj.homEquiv ((algebraDiagramSetEvaluation J D L j).obj T)
          ((algebraDiagramSetEvaluation J C K j).obj M)).symm
          ((algebraDiagramSetEvaluation J D L j).map h ≫
            (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app M)) := by
  ext U t
  exact transpose_eval adj T M h j U t
private theorem inverse_eval
    {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {BX : Sheaf (diagramSiteTopology J C K) RingCat.{u}}
    {BY : Sheaf (diagramSiteTopology J D L) RingCat.{u}}
    {F : Sheaf L (Type u) ⥤ Sheaf K (Type u)}
    {G : Sheaf K (Type u) ⥤ Sheaf L (Type u)} (aset : F ⊣ G)
    (f : RingedToposMorphism BX BY) (j : J)
    (g : RingedToposMorphism (algebraDiagramRingAt BX j) (algebraDiagramRingAt BY j))
    (hfInv : f.inverse = diagramCoefficientInverse J C D K L F)
    (hfDir : f.direct = diagramCoefficientDirect J C D K L G)
    (hfAdj : HEq f.adj (diagramCoefficientAdjunction J C D K L aset))
    (hgInv : g.inverse = F) (hgDir : g.direct = G) (hgAdj : HEq g.adj aset)
    (PB : ringedSiteModules.{u} BY ⥤ ringedSiteModules.{u} BX)
    (Pj : ringedSiteModules.{u} (algebraDiagramRingAt BY j) ⥤
      ringedSiteModules.{u} (algebraDiagramRingAt BX j))
    (adjB : PB ⊣ f.modules) (adjj : Pj ⊣ g.modules)
    (eB : PB ⋙ diagramCoefficientUnderlying BX ≅ diagramCoefficientUnderlying BY ⋙ f.inverse)
    (ej : Pj ⋙ diagramCoefficientUnderlying (algebraDiagramRingAt BX j) ≅
      diagramCoefficientUnderlying (algebraDiagramRingAt BY j) ⋙ g.inverse)
    (hB : ∀ M H (a : PB.obj M ⟶ H),
      (diagramCoefficientUnderlying BY).map (adjB.homEquiv M H a) ≫
        f.underlying.hom.app H =
      f.adj.homEquiv _ _ (eB.inv.app M ≫ (diagramCoefficientUnderlying BX).map a))
    (hj : ∀ M H (a : Pj.obj M ⟶ H),
      (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map
        (adjj.homEquiv M H a) ≫ g.underlying.hom.app H =
      g.adj.homEquiv _ _ (ej.inv.app M ≫
        (diagramCoefficientUnderlying (algebraDiagramRingAt BX j)).map a))
    (c : f.modules ⋙ algebraDiagramEvaluation BY j ≅
      algebraDiagramEvaluation BX j ⋙ g.modules)
    (hc : AlgebraDiagramOrdinaryEvaluationNormalized G f j g hfDir hgDir c) :
    ∃ l : PB ⋙ algebraDiagramEvaluation BX j ≅ algebraDiagramEvaluation BY j ⋙ Pj,
      ∀ N, (algebraDiagramEvaluation BX j).map (adjB.counit.app N) =
        l.hom.app (f.modules.obj N) ≫ Pj.map (c.hom.app N) ≫
          adjj.counit.app ((algebraDiagramEvaluation BX j).obj N) := by
  classical
  rcases f with ⟨F', G', af, hF, p, hp0, hp1, hpa, hpm, H, hH, eH, hlH⟩
  rcases g with ⟨F'', G'', ag, hgF, q, hq0, hq1, hqa, hqm, I, hI, eI, hlI⟩
  dsimp only at hfInv hfDir hfAdj hgInv hgDir hgAdj eB ej hB hj adjB adjj c hc ⊢
  subst F'
  subst G'
  cases hfAdj
  subst F''
  subst G''
  cases hgAdj
  dsimp only [AlgebraDiagramOrdinaryEvaluationNormalized, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Functor.map_id, Category.comp_id, Category.id_comp] at hc
  have hc0 (N : ringedSiteModules.{u} BX) :
      (diagramCoefficientUnderlying (algebraDiagramRingAt BY j)).map (c.hom.app N) ≫
        eI.hom.app ((algebraDiagramEvaluation BX j).obj N) =
      (algebraDiagramSetEvaluation J D L j).map (eH.hom.app N) ≫
        (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app
          ((diagramCoefficientUnderlying BX).obj N) := by
    have hh := hc N
    erw [Functor.map_id, Category.comp_id, Category.id_comp] at hh
    exact hh
  clear * - aset PB Pj adjB adjj eB ej hB hj c hc0 eH eI
  let ex := algebraDiagramSetEvaluation J C K j
  let ey := algebraDiagramSetEvaluation J D L j
  let ux := diagramCoefficientUnderlying BX
  let uy := diagramCoefficientUnderlying BY
  let uxj := diagramCoefficientUnderlying (algebraDiagramRingAt BX j)
  let uyj := diagramCoefficientUnderlying (algebraDiagramRingAt BY j)
  let x := algebraDiagramEvaluation BX j
  let y := algebraDiagramEvaluation BY j
  let α : y ⋙ Pj ⟶ PB ⋙ x :=
    ((mateEquiv adjB adjj).symm (TwoSquare.mk _ _ _ _ c.hom)).natTrans
  have hα (M : ringedSiteModules.{u} BY) :
      adjj.homEquiv _ _ (α.app M) = y.map (adjB.unit.app M) ≫ c.hom.app (PB.obj M) := by
    exact (unit_mateEquiv_symm adjB adjj (TwoSquare.mk _ _ _ _ c.hom) M).symm
  have he (M : ringedSiteModules.{u} BY) :
      uxj.map (α.app M) = ej.hom.app (y.obj M) ≫
        (inverse_eval_iso F j).inv.app (uy.obj M) ≫ ex.map (eB.inv.app M) := by
    apply (cancel_epi (ej.inv.app (y.obj M))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    apply (aset.homEquiv _ _).injective
    have hh := hj (y.obj M) (x.obj (PB.obj M)) (α.app M)
    change uyj.map (adjj.homEquiv _ _ (α.app M)) ≫ eI.hom.app _ = _ at hh
    rw [hα, uyj.map_comp, Category.assoc] at hh
    have hcn := hc0 (PB.obj M)
    erw [hcn] at hh
    have hu := hB M (PB.obj M) (𝟙 _)
    erw [Adjunction.homEquiv_id, Functor.map_id, Category.comp_id] at hu
    have ht := transpose_eval_morphism aset (uy.obj M) (ux.obj (PB.obj M))
      (uy.map (adjB.unit.app M) ≫ eH.hom.app (PB.obj M)) j
    rw [hu, Equiv.symm_apply_apply] at ht
    apply hh.symm.trans
    apply (aset.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply]
    apply (cancel_epi ((inverse_eval_iso F j).hom.app (uy.obj M))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    change (inverse_eval_iso F j).hom.app (uy.obj M) ≫
      (aset.homEquiv (ey.obj (uy.obj M)) (ex.obj (ux.obj (PB.obj M)))).symm
        (ey.map (uy.map (adjB.unit.app M)) ≫ ey.map (eH.hom.app (PB.obj M)) ≫
          (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app
            (ux.obj (PB.obj M))) = ex.map (eB.inv.app M)
    have hmap := congrArg (fun z ↦ ey.map z) hu
    simp only [Functor.map_comp] at hmap
    have hmap' := congrArg (fun z ↦ (inverse_eval_iso F j).hom.app (uy.obj M) ≫
      (aset.homEquiv (ey.obj (uy.obj M)) (ex.obj (ux.obj (PB.obj M)))).symm
        (z ≫ (algebraDiagramSetDirectEvaluation J C D K L G j).hom.app
          (ux.obj (PB.obj M)))) hmap
    simpa only [Category.assoc] using hmap'.trans ht.symm
  have hi (M : ringedSiteModules.{u} BY) : IsIso (α.app M) := by
    have : IsIso (uxj.map (α.app M)) := by rw [he]; infer_instance
    exact isIso_of_reflects_iso _ uxj
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let l := (asIso α).symm
  refine ⟨l, ?_⟩
  intro N
  apply (cancel_epi (α.app (H.obj N))).mp
  change α.app (H.obj N) ≫ x.map (adjB.counit.app N) =
    (asIso α).hom.app (H.obj N) ≫ (asIso α).inv.app (H.obj N) ≫
      Pj.map (c.hom.app N) ≫ adjj.counit.app (x.obj N)
  rw [Iso.hom_inv_id_app_assoc]
  exact (mateEquiv_counit_symm adjB adjj (TwoSquare.mk _ _ _ _ c.hom) N).symm

private theorem transition_coefficient_square_general
    {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {j k : J} (a : j ⟶ k) (F0 : Sheaf L (Type u) ⥤ Sheaf K (Type u))
    (BX : Sheaf (diagramSiteTopology J C K) RingCat.{u})
    (BY : Sheaf (diagramSiteTopology J D L) RingCat.{u})
    (fB : RingedToposMorphism BX BY)
    (fj : RingedToposMorphism (algebraDiagramRingAt BX j) (algebraDiagramRingAt BY j))
    (fk : RingedToposMorphism (algebraDiagramRingAt BX k) (algebraDiagramRingAt BY k))
    (hi : fB.inverse = diagramCoefficientInverse J C D K L F0)
    (hij : fj.inverse = F0) (hik : fk.inverse = F0)
    (hj : HEq (((diagramSiteSheafCurry J C K).map fB.ringMap).app j) fj.ringMap)
    (hk : HEq (((diagramSiteSheafCurry J C K).map fB.ringMap).app k) fk.ringMap) :
    fk.inverse.map ((sheafCompose L (forget RingCat)).map
        (algebraDiagramRingArrow BY a)) ≫ fk.ringMap =
      eqToHom (congrArg (fun H ↦ H.obj ((sheafCompose L (forget RingCat)).obj
        (algebraDiagramRingAt BY j))) (hik.trans hij.symm)) ≫ fj.ringMap ≫
        (sheafCompose K (forget RingCat)).map (algebraDiagramRingArrow BX a) := by
  have h := ((diagramSiteSheafCurry J C K).map fB.ringMap).naturality a
  rcases fB with ⟨FB, GB, ab, lb, rb, z, o, ad, mu, HB, add, e, lin⟩
  rcases fj with ⟨Fj, Gj, aj, lj, rj, zj, oj, adj, muj, Hj, addj, ej, linj⟩
  rcases fk with ⟨Fk, Gk, ak, lk, rk, zk, ok, adk, muk, Hk, addk, ek, link⟩
  dsimp only at hi hij hik hj hk h ⊢
  subst FB
  subst Fj
  subst Fk
  have src_eq (v : J) :
      ((diagramSiteSheafCurry J C K).obj
        ((diagramCoefficientInverse J C D K L F0).obj
          ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj BY))).obj v =
        F0.obj ((sheafCompose L (forget RingCat)).obj (algebraDiagramRingAt BY v)) := by
    apply ObjectProperty.FullSubcategory.ext
    apply Functor.ext
    · intro V W f
      change (F0.map (((diagramSiteSheafCurry J D L).obj
        ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj BY)).map
          (𝟙 v))).hom.app V ≫ _ = _
      rw [Functor.map_id, Functor.map_id]
      simp
      rfl
    · intro V
      rfl
  have hj' := hom_heq_cast (src_eq j) rfl _ _ hj
  have hk' := hom_heq_cast (src_eq k) rfl _ _ hk
  simp only [eqToHom_refl, Category.comp_id] at hj' hk'
  rw [hj', hk'] at h
  have hmap : (((diagramSiteSheafCurry J C K).obj
      ((diagramCoefficientInverse J C D K L F0).obj
        ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj BY))).map a) ≫
        eqToHom (src_eq k) = eqToHom (src_eq j) ≫
      F0.map ((sheafCompose L (forget RingCat)).map (algebraDiagramRingArrow BY a)) := by
    ext U t
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ObjectProperty.eqToHom_hom,
      eqToHom_app, eqToHom_refl, Category.comp_id, Category.id_comp]
    dsimp [diagramCoefficientInverse, diagramSiteSheafEquivalence,
      diagramSiteSheafCurry, diagramSiteCurry, diagramSiteSheafUncurry, diagramSiteUncurry]
    simp only [Functor.map_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
      Functor.map_comp, Category.comp_id, ConcreteCategory.id_apply]
    rfl
  have hout : ((diagramSiteSheafCurry J C K).obj
      ((sheafCompose (diagramSiteTopology J C K) (forget RingCat)).obj BX)).map a =
      (sheafCompose K (forget RingCat)).map (algebraDiagramRingArrow BX a) := rfl
  rw [← Category.assoc, hmap, hout] at h
  apply (cancel_epi (eqToHom (src_eq j))).mp
  simpa only [Category.assoc, eqToHom_refl, Category.id_comp] using h

attribute [local irreducible] algebraDiagramConstantRing

namespace AlgebraDiagramAdjunctionPresentation

variable {J C D : Type u} [SmallCategory J] [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D} {A : CommRingCat.{u}}
    (p : AlgebraDiagramAdjunctionPresentation J C D K L A)

private theorem ordinary_evaluation_B (j : J) :
    ∃ c : p.fB.modules ⋙ p.eBY j ≅ p.eBX j ⋙ (p.fj j).modules,
      AlgebraDiagramOrdinaryEvaluationNormalized p.s.direct p.fB j (p.fj j)
        p.directB (p.directLevel j) c :=
  ordinary_eval p.s.adj p.fB j (p.fj j) p.inverseB p.directB p.adjB
    (p.inverseLevel j) (p.directLevel j) (p.adjLevel j) (p.structuralB j)
private theorem ordinary_evaluation_A (j : J) :
    ∃ c : p.fA.modules ⋙ p.eAY j ≅ p.eAX j ⋙ p.s.modules,
      AlgebraDiagramOrdinaryEvaluationNormalized p.s.direct p.fA j p.s p.directA rfl c :=
  ordinary_eval p.s.adj p.fA j p.s p.inverseA p.directA p.adjA rfl rfl
    (heq_of_eq rfl) (p.structuralA j)
private theorem ordinary_coefficient :
    ∃ c : p.fB.modules ⋙ p.rY ≅ p.rX ⋙ p.fA.modules,
      AlgebraDiagramOrdinaryRestrictionNormalized p.aX p.aY p.fB p.fA
        (p.directB.trans p.directA.symm) c := by
  obtain ⟨c, hc⟩ := ordinaryCoefficientComparison p.aX p.aY p.fB p.fA
    (p.inverseB.trans p.inverseA.symm) (p.directB.trans p.directA.symm)
    (p.adjB.trans p.adjA.symm) p.coefficientSquare
  refine ⟨c, ?_⟩
  intro M
  simpa only [AlgebraDiagramOrdinaryRestrictionNormalized, eqToIso.hom, eqToHom_app] using hc M
private theorem vertex_coefficient_square (j : J) :
    (p.fj j).inverse.map ((sheafCompose L (forget RingCat)).map
        (algebraDiagramCoefficientAt p.aY j)) ≫ (p.fj j).ringMap =
      eqToHom (congrArg (fun H ↦ H.obj ((sheafCompose L (forget RingCat)).obj
          (algebraDiagramConstantRing L A)))
        ((p.inverseLevel j).trans rfl)) ≫ p.s.ringMap ≫
        (sheafCompose K (forget RingCat)).map (algebraDiagramCoefficientAt p.aX j) := by
  have h := congrArg (fun t ↦ ((diagramSiteSheafCurry J C K).map t).app j)
    p.coefficientSquare
  have ha := p.structuralA j
  have hb := p.structuralB j
  rcases p with ⟨BX, BY, commX, commY, aX, aY, s, cn, fA, fB, fj,
    ca, cb, cda, cl, iA, dA, adjA, iB, dB, adjB, il, dl, al,
    sa, sb, sq, pull, adj, ad, li, co, pullj, adjj, adjjA, lj, cj⟩
  dsimp only at *
  rcases fA with ⟨F, G, a, he, r, r0, r1, ra, rm, H, haH, eH, lH⟩
  rcases fB with ⟨F', G', a', he', r', r0', r1', ra', rm', H', haH', eH', lH'⟩
  rcases s with ⟨F0, G0, a0, he0, rbase, rb0, rb1, rba, rbm, H0, haH0, eH0, lH0⟩
  dsimp only at iA iB dA dB adjA adjB il dl al sa sb h ha hb ⊢
  subst F
  subst F'
  subst G
  subst G'
  cases adjA
  cases adjB
  have aux (f : RingedToposMorphism (algebraDiagramRingAt BX j)
      (algebraDiagramRingAt BY j)) (hi : f.inverse = F0)
      (hr : HEq (((diagramSiteSheafCurry J C K).map r').app j) f.ringMap) :
      f.inverse.map ((sheafCompose L (forget RingCat)).map
          (algebraDiagramCoefficientAt aY j)) ≫ f.ringMap =
        eqToHom (congrArg (fun H ↦ H.obj ((sheafCompose L (forget RingCat)).obj
          (algebraDiagramConstantRing L A))) hi) ≫ rbase ≫
          (sheafCompose K (forget RingCat)).map (algebraDiagramCoefficientAt aX j) := by
    clear * - h ha hi hr
    rcases f with ⟨Fj, Gj, aj, hej, rj, rj0, rj1, rja, rjm, Hj, haHj, eHj, lHj⟩
    dsimp only at hi hr ⊢
    subst Fj
    have input_eq (R : Sheaf (diagramSiteTopology J D L) RingCat.{u}) :
        ((diagramSiteSheafCurry J D L).obj
          ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj R)).obj j =
        (sheafCompose L (forget RingCat)).obj (algebraDiagramRingAt R j) := by
      apply ObjectProperty.FullSubcategory.ext
      rfl
    have src_eq (R : Sheaf (diagramSiteTopology J D L) RingCat.{u}) :
        ((diagramSiteSheafCurry J C K).obj
          ((diagramCoefficientInverse J C D K L F0).obj
            ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj R))).obj j =
          F0.obj ((sheafCompose L (forget RingCat)).obj (algebraDiagramRingAt R j)) := by
      trans F0.obj (((diagramSiteSheafCurry J D L).obj
        ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj R)).obj j)
      · apply ObjectProperty.FullSubcategory.ext
        apply Functor.ext
        · intro V W f
          change (F0.map (((diagramSiteSheafCurry J D L).obj
            ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).obj R)).map
              (𝟙 j))).hom.app V ≫ _ = _
          rw [Functor.map_id, Functor.map_id]
          simp
          rfl
        · intro V
          rfl
      · exact congrArg F0.obj (input_eq R)
    have ha' := hom_heq_cast
      (src_eq (diagramSiteRing J D L (algebraDiagramConstantRing L A))) rfl _ _ ha
    have hb' := hom_heq_cast (src_eq BY) rfl _ _ hr
    simp only [eqToHom_refl, Category.comp_id] at ha' hb'
    simp only [Functor.map_comp, Functor.comp_map, NatTrans.comp_app,
      eqToHom_refl, Category.id_comp] at h
    change _ ≫ ((diagramSiteSheafCurry J C K).map r').app j =
      ((diagramSiteSheafCurry J C K).map r).app j ≫ _ at h
    rw [ha', hb'] at h
    have hmap : ((diagramSiteSheafCurry J C K).map
        ((diagramCoefficientInverse J C D K L F0).map
          ((sheafCompose (diagramSiteTopology J D L) (forget RingCat)).map aY))).app j ≫
        eqToHom (src_eq BY) =
      eqToHom (src_eq (diagramSiteRing J D L (algebraDiagramConstantRing L A))) ≫
        F0.map ((sheafCompose L (forget RingCat)).map
          (algebraDiagramCoefficientAt aY j)) := by
      ext U t
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ObjectProperty.eqToHom_hom,
        eqToHom_app]
      rfl
    rw [← Category.assoc, hmap] at h
    apply (cancel_epi (eqToHom (src_eq
      (diagramSiteRing J D L (algebraDiagramConstantRing L A))))).mp
    have hm : ((diagramSiteSheafCurry J C K).map
        ((sheafCompose (diagramSiteTopology J C K) (forget RingCat)).map aX)).app j =
          (sheafCompose K (forget RingCat)).map (algebraDiagramCoefficientAt aX j) := rfl
    rw [hm] at h
    exact h
  exact aux (fj j) (il j) hb
private theorem ordinary_restriction_vertex (j : J) :
    ∃ c : (p.fj j).modules ⋙ p.rYj j ≅ p.rXj j ⋙ p.s.modules,
      AlgebraDiagramOrdinaryRestrictionNormalized
        (algebraDiagramCoefficientAt p.aX j) (algebraDiagramCoefficientAt p.aY j)
        (p.fj j) p.s (p.directLevel j) c := by
  obtain ⟨c, hc⟩ := ordinaryCoefficientComparison
    (algebraDiagramCoefficientAt p.aX j) (algebraDiagramCoefficientAt p.aY j)
    (p.fj j) p.s (p.inverseLevel j) (p.directLevel j) (p.adjLevel j)
    (vertex_coefficient_square p j)
  refine ⟨c, ?_⟩
  intro M
  simpa only [AlgebraDiagramOrdinaryRestrictionNormalized, eqToIso.hom, eqToHom_app] using hc M

private theorem ordinary_transition_restriction {j k : J} (a : j ⟶ k) :
    ∃ c : (p.fj k).modules ⋙
        SheafOfModules.restrictScalars (algebraDiagramRingArrow p.BY a) ≅
      SheafOfModules.restrictScalars (algebraDiagramRingArrow p.BX a) ⋙ (p.fj j).modules,
      AlgebraDiagramOrdinaryRestrictionNormalized
        (algebraDiagramRingArrow p.BX a) (algebraDiagramRingArrow p.BY a)
        (p.fj k) (p.fj j) ((p.directLevel k).trans (p.directLevel j).symm) c := by
  obtain ⟨c, hc⟩ := ordinaryCoefficientComparison
    (algebraDiagramRingArrow p.BX a) (algebraDiagramRingArrow p.BY a)
    (p.fj k) (p.fj j) ((p.inverseLevel k).trans (p.inverseLevel j).symm)
    ((p.directLevel k).trans (p.directLevel j).symm)
    ((p.adjLevel k).trans (p.adjLevel j).symm)
    (transition_coefficient_square_general a p.s.inverse p.BX p.BY p.fB
      (p.fj j) (p.fj k) p.inverseB (p.inverseLevel j) (p.inverseLevel k)
      (p.structuralB j) (p.structuralB k))
  refine ⟨c, ?_⟩
  intro M
  simpa only [AlgebraDiagramOrdinaryRestrictionNormalized, eqToIso.hom, eqToHom_app]
    using hc M

private theorem ordinary_transition_restriction_A {j k : J} (a : j ⟶ k) :
    ∃ c : p.s.modules ⋙
        SheafOfModules.restrictScalars (algebraDiagramRingArrow p.AY a) ≅
      SheafOfModules.restrictScalars (algebraDiagramRingArrow p.AX a) ⋙ p.s.modules,
      AlgebraDiagramOrdinaryRestrictionNormalized
        (algebraDiagramRingArrow p.AX a) (algebraDiagramRingArrow p.AY a)
        p.s p.s rfl c := by
  obtain ⟨c, hc⟩ := ordinaryCoefficientComparison
    (algebraDiagramRingArrow p.AX a) (algebraDiagramRingArrow p.AY a)
    p.s p.s rfl rfl (HEq.rfl)
    (transition_coefficient_square_general a p.s.inverse p.AX p.AY p.fA
      p.s p.s p.inverseA rfl rfl (p.structuralA j) (p.structuralA k))
  refine ⟨c, ?_⟩
  intro M
  simpa only [AlgebraDiagramOrdinaryRestrictionNormalized, eqToIso.hom, eqToHom_app]
    using hc M

private theorem inverse_evaluation_B (j : J)
    (c : p.fB.modules ⋙ p.eBY j ≅ p.eBX j ⋙ (p.fj j).modules)
    (hc : AlgebraDiagramOrdinaryEvaluationNormalized p.s.direct p.fB j (p.fj j)
      p.directB (p.directLevel j) c) :
    ∃ l : p.pullB ⋙ p.eBX j ≅ p.eBY j ⋙ p.pullj j,
      ∀ N, (p.eBX j).map (p.moduleAdjB.counit.app N) =
        l.hom.app (p.fB.modules.obj N) ≫ (p.pullj j).map (c.hom.app N) ≫
          (p.moduleAdjj j).counit.app ((p.eBX j).obj N) := by
  let := p.cartesianB
  let := p.cartesianLevel j
  obtain ⟨eB, heB⟩ := cartesianModulePullbackUnderlying p.commX p.commY
    p.fB p.pullB p.moduleAdjB
  obtain ⟨ej, hej⟩ := cartesianModulePullbackUnderlying
    (fun U ↦ p.commX (op (op j, U.unop)))
    (fun U ↦ p.commY (op (op j, U.unop)))
    (p.fj j) (p.pullj j) (p.moduleAdjj j)
  exact inverse_eval p.s.adj p.fB j (p.fj j) p.inverseB p.directB p.adjB
    (p.inverseLevel j) (p.directLevel j) (p.adjLevel j) p.pullB (p.pullj j)
    p.moduleAdjB (p.moduleAdjj j) eB ej heB hej c hc

/-- Ordinary ring-action comparisons, before localization.
Source: Stacks 07A6, componentwise induced module direct image.
(blueprint: lem-pur-algebra-diagram-normalized-ordinary-comparisons). -/
structure OrdinaryComparisons where
  c : p.fB.modules ⋙ p.rY ≅ p.rX ⋙ p.fA.modules
  cB : ∀ j : J, p.fB.modules ⋙ p.eBY j ≅ p.eBX j ⋙ (p.fj j).modules
  cA : ∀ j : J, p.fA.modules ⋙ p.eAY j ≅ p.eAX j ⋙ p.s.modules
  lambda : ∀ j : J, p.pullB ⋙ p.eBX j ≅ p.eBY j ⋙ p.pullj j
  cj : ∀ j : J, (p.fj j).modules ⋙ p.rYj j ≅ p.rXj j ⋙ p.s.modules
  caB : ∀ {j k : J} (a : j ⟶ k),
    (p.fj k).modules ⋙ SheafOfModules.restrictScalars.{u}
        (algebraDiagramRingArrow p.BY a) ≅
      SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.BX a) ⋙ (p.fj j).modules
  caA : ∀ {j k : J} (a : j ⟶ k),
    p.s.modules ⋙ SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AY a) ≅
      SheafOfModules.restrictScalars.{u} (algebraDiagramRingArrow p.AX a) ⋙ p.s.modules
  hc : AlgebraDiagramOrdinaryRestrictionNormalized p.aX p.aY p.fB p.fA
    (p.directB.trans p.directA.symm) c
  hcB : ∀ j : J, AlgebraDiagramOrdinaryEvaluationNormalized p.s.direct p.fB j (p.fj j)
    p.directB (p.directLevel j) (cB j)
  hcA : ∀ j : J, AlgebraDiagramOrdinaryEvaluationNormalized p.s.direct p.fA j p.s
    p.directA rfl (cA j)
  hcj : ∀ j : J, AlgebraDiagramOrdinaryRestrictionNormalized
    (algebraDiagramCoefficientAt p.aX j) (algebraDiagramCoefficientAt p.aY j)
    (p.fj j) p.s (p.directLevel j) (cj j)
  hcaB : ∀ {j k : J} (a : j ⟶ k), AlgebraDiagramOrdinaryRestrictionNormalized
    (algebraDiagramRingArrow p.BX a) (algebraDiagramRingArrow p.BY a)
    (p.fj k) (p.fj j) ((p.directLevel k).trans (p.directLevel j).symm) (caB a)
  hcaA : ∀ {j k : J} (a : j ⟶ k), AlgebraDiagramOrdinaryRestrictionNormalized
    (algebraDiagramRingArrow p.AX a) (algebraDiagramRingArrow p.AY a)
    p.s p.s rfl (caA a)
  counit : ∀ (j : J) (N : ringedSiteModules.{u} p.BX),
    (p.eBX j).map (p.moduleAdjB.counit.app N) =
      (lambda j).hom.app (p.fB.modules.obj N) ≫
        (p.pullj j).map ((cB j).hom.app N) ≫
        (p.moduleAdjj j).counit.app ((p.eBX j).obj N)

/-- Evaluation, scalar restriction and their mates have normalized ordinary comparisons.
Source: Stacks, Cohomology on Sites, Tag 07A6, with the vertical diagram-site construction.
(blueprint: lem-pur-algebra-diagram-normalized-ordinary-comparisons).

Proof: Identify the underlying sheaf of each direct image with componentwise direct
image using its supplied underlying isomorphism and the counit of the diagram-site
sheaf equivalence. The module-linearity axiom, applied to the universal pairs of
sections, identifies addition and scalar multiplication with direct images of their
operation maps. Evaluation preserves finite products. The structuralA and structuralB
identities therefore make the underlying comparison linear. Its inverse is linear by
cancellation, giving cA and cB. Apply the same argument to the coefficient square and
to naturality of the structural map along each actual diagram arrow to obtain c and
cj and caB and caA. These are normalized on underlying sheaves by construction.
For inverse images, transport module operations along the geometric inverse images;
the invertible structural ring maps identify those module functors with the supplied
left adjoints by uniqueness of left adjoints. Their componentwise identification is
lambda. The unit-compatible uniqueness equation says that its right mate is cB;
the mate counit formula gives the last field. All constructions are sectionwise and
apply to empty index categories, arbitrary endomorphisms and zero coefficient rings. -/
theorem ordinaryComparisons_exists : Nonempty (p.OrdinaryComparisons) := by
  classical
  obtain ⟨c, hc⟩ := ordinary_coefficient p
  choose cB hcB using ordinary_evaluation_B p
  choose cA hcA using ordinary_evaluation_A p
  choose cj hcj using ordinary_restriction_vertex p
  have htB (j k : J) (a : j ⟶ k) := ordinary_transition_restriction p a
  have htA (j k : J) (a : j ⟶ k) := ordinary_transition_restriction_A p a
  choose caB hcaB using htB
  choose caA hcaA using htA
  choose lambda hcounit using fun j ↦ inverse_evaluation_B p j (cB j) (hcB j)
  exact ⟨⟨c, cB, cA, lambda, cj,
    (fun {j k} a ↦ caB j k a), (fun {j k} a ↦ caA j k a),
    hc, hcB, hcA, hcj, (fun {j k} a ↦ hcaB j k a),
    (fun {j k} a ↦ hcaA j k a), hcounit⟩⟩

end AlgebraDiagramAdjunctionPresentation
end CategoryTheory
