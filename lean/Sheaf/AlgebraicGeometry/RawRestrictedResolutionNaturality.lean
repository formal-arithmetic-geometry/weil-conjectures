module

public import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalizationData
import Sheaf.AlgebraicGeometry.RawRestrictedResolutionCocycle
import Mathlib.Algebra.Homology.Functor
import all WeilConjectures.AlgebraicGeometry.RawRestrictedHomotopySectionsIso

/-! # Raw evaluation on a fixed resolution

Source: Stacks Project, Tags 03Q8 and 072W.
(blueprint: lem-weil-pbc-raw-restricted-resolution-naturality).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

set_option backward.defeqAttrib.useBackward true
attribute [local instance] normalizationShiftedResolution_restriction_isKInjective
attribute [local irreducible] normalizationRestrictedIso
  RawRestrictedComparison.shiftIso normalizationResolutionCocycleIso
  RawRestrictedComparison.resolutionSectionsIso normalizationShiftedAugmentation
  RawRestrictedComparison.Evaluation.shiftIso
  RawRestrictedComparison.Evaluation.zeroIso
  Functor.rightDerivedFunctorObjQIso
  Functor.mapDerivedCategoryFactors

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

private noncomputable def chartSource {X S : Scheme.{u}} (f : X ⟶ S) :
    S.Etale ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} where
  obj V := (upperStar AddCommGrpCat.{u + 1} f).obj
    (RawRestrictedComparison.freeSheaf S V)
  map t := (abelianComparisonFree S ⋙ upperStar AddCommGrpCat.{u + 1} f).map t
  map_id V := (abelianComparisonFree S ⋙ upperStar AddCommGrpCat.{u + 1} f).map_id V
  map_comp t t' :=
    (abelianComparisonFree S ⋙ upperStar AddCommGrpCat.{u + 1} f).map_comp t t'

private noncomputable abbrev sectionFunctor {X S : Scheme.{u}} (f : X ⟶ S) :=
  lowerStar AddCommGrpCat.{u + 1} f ⋙
    sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}

private noncomputable abbrev sectionComplex {X S : Scheme.{u}} (f : X ⟶ S)
    (J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :=
  ((sectionFunctor f).mapHomologicalComplex (.up ℤ)).obj J

private theorem representedEquiv_precomp {X S : Scheme.{u}} (f : X ⟶ S)
    {V V' : S.Etale} (t : V' ⟶ V)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : (chartSource f).obj V ⟶ G) :
    RawRestrictedComparison.representedEquiv f V' G ((chartSource f).map t ≫ a) =
      ((lowerStar AddCommGrpCat.{u + 1} f).obj G).obj.map t.op
        (RawRestrictedComparison.representedEquiv f V G a) := by
  change uliftYonedaEquiv
    (((AddCommGrpCat.adj.whiskerRight (C := S.Etaleᵒᵖ)).homEquiv _ _)
      (((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _) (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
          ((upperStar AddCommGrpCat.{u + 1} f).map
            ((abelianComparisonFree S).map t) ≫ a)))) = _
  rw [Adjunction.homEquiv_naturality_left]
  change uliftYonedaEquiv
    (((AddCommGrpCat.adj.whiskerRight (C := S.Etaleᵒᵖ)).homEquiv _ _)
      (((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _) ((presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
            (uliftYoneda.map t)) ≫
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _) a))) = _
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ t.op).symm

attribute [local irreducible] RawRestrictedComparison.representedEquiv

private noncomputable def chartRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    {V V' : S.Etaleᵒᵖ} (t : V ⟶ V') :
    RawRestrictedComparison.underivedSections
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V.unop) ⟶
      RawRestrictedComparison.underivedSections
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V'.unop) :=
by
  refine { app := fun G ↦ ?_, naturality := ?_ }
  · exact (RawRestrictedComparison.sectionsIso
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V.unop) G).hom ≫
      G.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ f).map t.unop).op ≫
      (RawRestrictedComparison.sectionsIso
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V'.unop) G).inv
  · intro G G' g
    have hn (W : X.Etale) :
        (RawRestrictedComparison.underivedSections W).map g ≫
          (RawRestrictedComparison.sectionsIso W G').hom =
        (RawRestrictedComparison.sectionsIso W G).hom ≫ g.hom.app (op W) := by
      dsimp [RawRestrictedComparison.underivedSections, RawRestrictedComparison.sectionsIso]
      simp only [Category.assoc]
      rw [← Functor.map_comp_assoc,
        (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.hom W.prop).hom.naturality,
        Functor.map_comp_assoc]
      rw [(Sheaf.ΓNatIsoSheafSections W.left.smallEtaleTopology AddCommGrpCat.{u + 1}
        (MorphismProperty.Over.mkIdTerminal @Etale W.left)).hom.naturality_assoc]
      congr 1
      congr 1
      exact (g.hom.naturality _).symm
    have hi (W : X.Etale) : g.hom.app (op W) ≫
        (RawRestrictedComparison.sectionsIso W G').inv =
      (RawRestrictedComparison.sectionsIso W G).inv ≫
        (RawRestrictedComparison.underivedSections W).map g := by
      apply (cancel_epi (RawRestrictedComparison.sectionsIso W G).hom).1
      rw [← Category.assoc, ← hn W]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    have hg := g.hom.naturality
      ((MorphismProperty.Over.pullback @Etale ⊤ f).map t.unop).op
    erw [← reassoc_of% hg]
    rw [hi]

private theorem single_comparison_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {L M : C ⥤ D} [L.Additive] [M.Additive] (α : L ⟶ M) (A : C) :
    (NatTrans.mapHomologicalComplex α (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj A) ≫
      (HomologicalComplex.singleMapHomologicalComplex M (.up ℤ) 0).hom.app A =
    (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app A ≫
      (HomologicalComplex.single D (.up ℤ) 0).map (α.app A) := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact (α.naturality_assoc
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom _).symm
  · simp only [HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_ne _ _ hn,
      Limits.comp_zero, Limits.zero_comp]

private noncomputable def singleHomologyIso
    {C : Type*} [Category C] [Abelian C] (L : C ⥤ AddCommGrpCat.{u}) [L.Additive]
    (A : C) :
    (((L.mapHomologicalComplex (.up ℤ)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj A)).homology 0) ≅ L.obj A :=
  (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app A) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 _

private theorem singleHomologyIso_naturality
    {C : Type*} [Category C] [Abelian C]
    {L M : C ⥤ AddCommGrpCat.{u}} [L.Additive] [M.Additive]
    (α : L ⟶ M) (A : C) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (.up ℤ)).app
          ((HomologicalComplex.single C (.up ℤ) 0).obj A)) 0 ≫
      (singleHomologyIso M A).hom =
    (singleHomologyIso L A).hom ≫ α.app A := by
  unfold singleHomologyIso
  simp only [Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor_map, Iso.app_hom]
  rw [← HomologicalComplex.homologyMap_comp_assoc,
    single_comparison_naturality, HomologicalComplex.homologyMap_comp_assoc,
    HomologicalComplex.singleObjHomologySelfIso_hom_naturality]
  rw [Category.assoc]

private theorem singleHomologyIso_map
    {C : Type*} [Category C] [Abelian C]
    (M : C ⥤ AddCommGrpCat.{u}) [M.Additive] {A A' : C} (b : A' ⟶ A) :
    HomologicalComplex.homologyMap
        ((M.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.single C (.up ℤ) 0).map b)) 0 ≫
      (singleHomologyIso M A).hom =
    (singleHomologyIso M A').hom ≫ M.map b := by
  have hn := (HomologicalComplex.singleMapHomologicalComplex M (.up ℤ) 0).hom.naturality b
  have h := congrArg (fun k ↦ HomologicalComplex.homologyMap k 0) hn
  simp only [Functor.comp_map, HomologicalComplex.homologyMap_comp] at h
  unfold singleHomologyIso
  simp only [Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor_map, Iso.app_hom]
  rw [← Category.assoc, h, Category.assoc]
  rw [HomologicalComplex.singleObjHomologySelfIso_hom_naturality]
  rw [Category.assoc]

private theorem chain_generator_naturality
    {C : Type*} [Category C] [Abelian C]
    {L M : C ⥤ AddCommGrpCat.{u}} [L.Additive] [M.Additive]
    (α : L ⟶ M) {A A' : C} (b : A' ⟶ A)
    (x : L.obj A) (x' : M.obj A') (hx : α.app A x = M.map b x')
    (J : CochainComplex C ℤ)
    (c : (HomologicalComplex.single C (.up ℤ) 0).obj A ⟶ J) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (.up ℤ)).app J) 0
      (HomologicalComplex.homologyMap ((L.mapHomologicalComplex (.up ℤ)).map c) 0
        ((singleHomologyIso L A).inv x)) =
    HomologicalComplex.homologyMap ((M.mapHomologicalComplex (.up ℤ)).map
      ((HomologicalComplex.single C (.up ℤ) 0).map b ≫ c)) 0
      ((singleHomologyIso M A').inv x') := by
  have hn := (NatTrans.mapHomologicalComplex α (.up ℤ)).naturality c
  have h := congrArg (fun k ↦ HomologicalComplex.homologyMap k 0) hn
  simp only [HomologicalComplex.homologyMap_comp] at h
  change _ = HomologicalComplex.homologyMap ((M.mapHomologicalComplex (.up ℤ)).map
    ((HomologicalComplex.single C (.up ℤ) 0).map b ≫ c)) 0 _
  rw [Functor.map_comp, HomologicalComplex.homologyMap_comp]
  rw [← ConcreteCategory.comp_apply, h]
  simp only [ConcreteCategory.comp_apply]
  congr 1
  apply (ConcreteCategory.isIso_iff_bijective (singleHomologyIso M A).hom).mp
    (by infer_instance) |>.injective
  rw [← ConcreteCategory.comp_apply, singleHomologyIso_naturality,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rw [← ConcreteCategory.comp_apply, singleHomologyIso_map,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  exact hx

private theorem generator_restriction {X S : Scheme.{u}} (f : X ⟶ S)
    {V V' : S.Etaleᵒᵖ} (t : V ⟶ V') :
    (chartRestriction f t).app ((upperStar AddCommGrpCat.{u + 1} f).obj
      (RawRestrictedComparison.freeSheaf S V.unop))
        (RawRestrictedComparison.generator f V.unop) =
    (RawRestrictedComparison.underivedSections
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V'.unop)).map
        ((chartSource f).map t.unop) (RawRestrictedComparison.generator f V'.unop) := by
  let A := (upperStar AddCommGrpCat.{u + 1} f).obj
    (RawRestrictedComparison.freeSheaf S V.unop)
  have h := representedEquiv_precomp f t.unop A (𝟙 A)
  erw [Category.comp_id] at h
  rw [RawRestrictedComparison.representedEquiv_apply,
    RawRestrictedComparison.representedEquiv_apply] at h
  have hi : (RawRestrictedComparison.underivedSections
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V.unop)).map (𝟙 A) = 𝟙 _ :=
    (RawRestrictedComparison.underivedSections _).map_id A
  rw [hi] at h
  apply (ConcreteCategory.isIso_iff_bijective
    (RawRestrictedComparison.sectionsIso
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V'.unop) A).hom).mp
      (by infer_instance) |>.injective
  change (RawRestrictedComparison.sectionsIso _ A).hom
    ((RawRestrictedComparison.sectionsIso _ A).inv
      (((lowerStar AddCommGrpCat.{u + 1} f).obj A).obj.map t
        ((RawRestrictedComparison.sectionsIso _ A).hom
          (RawRestrictedComparison.generator f V.unop)))) = _
  rw [Iso.inv_hom_id_apply]
  exact h.symm

private theorem chainEvaluation_formula {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Etale)
    (J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (c : (HomologicalComplex.single _ (.up ℤ) 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
      (RawRestrictedComparison.freeSheaf S V)) ⟶ J) :
    RawRestrictedComparison.chainEvaluation f V J c =
      HomologicalComplex.homologyMap
        (((RawRestrictedComparison.underivedSections
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)).mapHomologicalComplex
            (.up ℤ)).map c) 0
        ((singleHomologyIso (RawRestrictedComparison.underivedSections
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))
            ((upperStar AddCommGrpCat.{u + 1} f).obj
      (RawRestrictedComparison.freeSheaf S V))).inv (RawRestrictedComparison.generator f V)) := by
  rfl

attribute [local irreducible] singleHomologyIso RawRestrictedComparison.underivedSingleIso
attribute [local irreducible] RawRestrictedComparison.chainEvaluation

private theorem chainEvaluation_naturality {X S : Scheme.{u}} (f : X ⟶ S)
    {V V' : S.Etaleᵒᵖ} (t : V ⟶ V')
    (J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (c : (HomologicalComplex.single _ (.up ℤ) 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
      (RawRestrictedComparison.freeSheaf S V.unop)) ⟶ J) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (chartRestriction f t) (.up ℤ)).app J) 0
      (RawRestrictedComparison.chainEvaluation f V.unop J c) =
    RawRestrictedComparison.chainEvaluation f V'.unop J
      ((HomologicalComplex.single _ (.up ℤ) 0).map ((chartSource f).map t.unop) ≫ c) := by
  have h := chain_generator_naturality
    (A := (upperStar AddCommGrpCat.{u + 1} f).obj
      (RawRestrictedComparison.freeSheaf S V.unop))
    (A' := (upperStar AddCommGrpCat.{u + 1} f).obj
      (RawRestrictedComparison.freeSheaf S V'.unop))
    (chartRestriction f t) ((chartSource f).map t.unop)
    (RawRestrictedComparison.generator f V.unop)
    (RawRestrictedComparison.generator f V'.unop) (generator_restriction f t) J c
  exact (congrArg (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (chartRestriction f t) (.up ℤ)).app J) 0)
        (chainEvaluation_formula f V.unop J c)).trans
    (h.trans (chainEvaluation_formula f V'.unop J
      ((HomologicalComplex.single _ (.up ℤ) 0).map ((chartSource f).map t.unop) ≫ c)).symm)

private theorem shiftUndo_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {L M : C ⥤ D} [L.Additive] [M.Additive] (α : L ⟶ M)
    (J : CochainComplex C ℤ) (q : ℤ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (.up ℤ)).app (J⟦q⟧)) 0 ≫
      HomologicalComplex.homologyMap
        (((M.mapHomologicalComplex (.up ℤ)).commShiftIso q).hom.app J) 0 ≫
      ((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso q 0 q
        (add_zero q)).hom.app ((M.mapHomologicalComplex (.up ℤ)).obj J) =
    HomologicalComplex.homologyMap
        (((L.mapHomologicalComplex (.up ℤ)).commShiftIso q).hom.app J) 0 ≫
      ((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso q 0 q
        (add_zero q)).hom.app ((L.mapHomologicalComplex (.up ℤ)).obj J) ≫
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (.up ℤ)).app J) q := by
  let a := (NatTrans.mapHomologicalComplex α (.up ℤ)).app J
  have h : (NatTrans.mapHomologicalComplex α (.up ℤ)).app (J⟦q⟧) ≫
      ((M.mapHomologicalComplex (.up ℤ)).commShiftIso q).hom.app J =
    ((L.mapHomologicalComplex (.up ℤ)).commShiftIso q).hom.app J ≫ a⟦q⟧' := by
    apply HomologicalComplex.Hom.ext
    funext n
    change α.app (J.X (n + q)) ≫ 𝟙 _ = 𝟙 _ ≫ α.app (J.X (n + q))
    rw [Category.comp_id, Category.id_comp]
  rw [← HomologicalComplex.homologyMap_comp_assoc, h,
    HomologicalComplex.homologyMap_comp_assoc]
  exact congrArg
    (fun k ↦ HomologicalComplex.homologyMap
      (((L.mapHomologicalComplex (.up ℤ)).commShiftIso q).hom.app J) 0 ≫ k)
    (((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso q 0 q
      (add_zero q)).hom.naturality a)

private theorem sectionHomology_naturality {X S : Scheme.{u}} (f : X ⟶ S)
    {V V' : S.Etaleᵒᵖ} (t : V ⟶ V')
    (J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (n : ℤ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (chartRestriction f t) (.up ℤ)).app J) n ≫
      HomologicalComplex.homologyMap
        ((NatIso.mapHomologicalComplex (normalizationSectionsIso
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V'.unop)) (.up ℤ)).app J).hom n ≫
      (((sectionComplex f J).sc n).mapHomologyIso
        ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj V')).hom =
    HomologicalComplex.homologyMap
        ((NatIso.mapHomologicalComplex (normalizationSectionsIso
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V.unop)) (.up ℤ)).app J).hom n ≫
      (((sectionComplex f J).sc n).mapHomologyIso
        ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj V)).hom ≫
      ((sectionComplex f J).homology n).map t := by
  let e := (NatIso.mapHomologicalComplex (normalizationSectionsIso
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V.unop)) (.up ℤ)).app J
  let e' := (NatIso.mapHomologicalComplex (normalizationSectionsIso
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V'.unop)) (.up ℤ)).app J
  have h : (NatTrans.mapHomologicalComplex (chartRestriction f t) (.up ℤ)).app J ≫
      e'.hom = e.hom ≫ (sectionComplex f J).asFunctor.map t := by
    apply HomologicalComplex.Hom.ext
    funext i
    change ((normalizationSectionsIso _).hom.app (J.X i) ≫ _ ≫
      (normalizationSectionsIso _).inv.app (J.X i)) ≫
        (normalizationSectionsIso _).hom.app (J.X i) = _
    change ((normalizationSectionsIso _).hom.app (J.X i) ≫ _ ≫
      (normalizationSectionsIso _).inv.app (J.X i)) ≫
        (normalizationSectionsIso _).hom.app (J.X i) =
      (normalizationSectionsIso _).hom.app (J.X i) ≫ _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    congr 1
  have hn := ((sectionComplex f J).sc n).homologyMap_mapNatTrans
    ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map t)
  change HomologicalComplex.homologyMap ((sectionComplex f J).asFunctor.map t) n = _ at hn
  change HomologicalComplex.homologyMap _ n ≫
    HomologicalComplex.homologyMap e'.hom n ≫ _ =
      HomologicalComplex.homologyMap e.hom n ≫ _
  rw [← HomologicalComplex.homologyMap_comp_assoc, h,
    HomologicalComplex.homologyMap_comp_assoc, hn]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private theorem resolutionCocycleIso_naturality {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) {V V' : S.Etaleᵒᵖ} (t : V ⟶ V') :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (chartRestriction f t) (.up ℤ)).app
          (normalizationShiftedResolution F I q).obj) 0 ≫
      (normalizationResolutionCocycleIso f q F I V'.unop).hom =
    (normalizationResolutionCocycleIso f q F I V.unop).hom ≫
      ((normalizationPresheafComplex f F I).homology (q : ℤ)).map t := by
  have hshift := shiftUndo_naturality (chartRestriction f t) I.cochainComplex (q : ℤ)
  have hsec := sectionHomology_naturality f t I.cochainComplex (q : ℤ)
  unfold normalizationResolutionCocycleIso
  simp only [Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor_map, Iso.app_hom]
  dsimp only [normalizationShiftedResolution]
  simp only [Category.assoc]
  erw [reassoc_of% hshift]
  dsimp only [sectionComplex, sectionFunctor] at hsec
  change _ ≫ _ ≫ (HomologicalComplex.homologyMap _ (q : ℤ) ≫
    HomologicalComplex.homologyMap _ (q : ℤ) ≫ _) = _
  congr 1
  congr 1

private theorem normalized_chain {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) (V : S.Etale)
    (c : (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V)) ⟶
        (normalizationShiftedResolution F I q).obj) :
    (normalizationRestrictedIso f q F I V).hom
      (rawRestrictedCohomologyComparison f q F V
        ((DerivedCategory.Plus.ι.preimage (X := (DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V))) (Y :=
          DerivedCategory.Plus.Q.obj (normalizationShiftedResolution F I q))
          (DerivedCategory.Q.map c)) ≫ (normalizationShiftedAugmentation F I q).inv)) =
    (normalizationResolutionCocycleIso f q F I V).hom
      (RawRestrictedComparison.chainEvaluation f V (normalizationShiftedResolution F I q).obj c)
        := by
  have ha : (RawRestrictedComparison.sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤
    f).obj V) ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
    (normalizationShiftedAugmentation F I q).hom ((RawRestrictedComparison.sectionsFunctor
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ⋙ DerivedCategory.homologyFunctor
    AddCommGrpCat.{u + 1} 0).map ((DerivedCategory.Plus.ι.preimage (X :=
    (DerivedCategory.Plus.singleFunctor _ 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
    (RawRestrictedComparison.freeSheaf S V))) (Y := DerivedCategory.Plus.Q.obj
    (normalizationShiftedResolution F I q)) (DerivedCategory.Q.map c)) ≫
    (normalizationShiftedAugmentation F I q).inv) ((RawRestrictedComparison.zeroIso
    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ((upperStar AddCommGrpCat.{u + 1} f).obj
    (RawRestrictedComparison.freeSheaf S V))).inv (RawRestrictedComparison.generator f V))) =
    (RawRestrictedComparison.sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map (DerivedCategory.Plus.ι.preimage
    (X := (DerivedCategory.Plus.singleFunctor _ 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
    (RawRestrictedComparison.freeSheaf S V))) (Y := DerivedCategory.Plus.Q.obj
    (normalizationShiftedResolution F I q)) (DerivedCategory.Q.map c))
    ((RawRestrictedComparison.zeroIso ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
    ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V))).inv
    (RawRestrictedComparison.generator f V)) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hs : (normalizationRestrictedIso f q F I V).hom
      ((RawRestrictedComparison.shiftIso f q F V).hom ((RawRestrictedComparison.sectionsFunctor
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ⋙ DerivedCategory.homologyFunctor
        AddCommGrpCat.{u + 1} 0).map ((DerivedCategory.Plus.ι.preimage (X :=
        (DerivedCategory.Plus.singleFunctor _ 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
        (RawRestrictedComparison.freeSheaf S V))) (Y := DerivedCategory.Plus.Q.obj
        (normalizationShiftedResolution F I q)) (DerivedCategory.Q.map c)) ≫
        (normalizationShiftedAugmentation F I q).inv) ((RawRestrictedComparison.zeroIso
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ((upperStar AddCommGrpCat.{u + 1}
        f).obj (RawRestrictedComparison.freeSheaf S V))).inv (RawRestrictedComparison.generator f
        V)))) =
    (normalizationResolutionCocycleIso f q F I V).hom
      ((RawRestrictedComparison.resolutionSectionsIso ((MorphismProperty.Over.pullback @Etale ⊤
        f).obj V) (normalizationShiftedResolution F I q)).hom
        ((RawRestrictedComparison.sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
          V) ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
          (normalizationShiftedAugmentation F I q).hom ((RawRestrictedComparison.sectionsFunctor
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ⋙ DerivedCategory.homologyFunctor
          AddCommGrpCat.{u + 1} 0).map ((DerivedCategory.Plus.ι.preimage (X :=
          (DerivedCategory.Plus.singleFunctor _ 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
          (RawRestrictedComparison.freeSheaf S V))) (Y := DerivedCategory.Plus.Q.obj
          (normalizationShiftedResolution F I q)) (DerivedCategory.Q.map c)) ≫
          (normalizationShiftedAugmentation F I q).inv) ((RawRestrictedComparison.zeroIso
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ((upperStar AddCommGrpCat.{u + 1}
          f).obj (RawRestrictedComparison.freeSheaf S V))).inv (RawRestrictedComparison.generator
          f V))))) := by
    simpa only [ConcreteCategory.comp_apply] using!
      (ConcreteCategory.congr_hom
    (rawRestricted_resolution_shift_square f q F I V) ((RawRestrictedComparison.sectionsFunctor
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ⋙ DerivedCategory.homologyFunctor
      AddCommGrpCat.{u + 1} 0).map ((DerivedCategory.Plus.ι.preimage (X :=
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
      (RawRestrictedComparison.freeSheaf S V))) (Y := DerivedCategory.Plus.Q.obj
      (normalizationShiftedResolution F I q)) (DerivedCategory.Q.map c)) ≫
      (normalizationShiftedAugmentation F I q).inv) ((RawRestrictedComparison.zeroIso
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ((upperStar AddCommGrpCat.{u + 1} f).obj
      (RawRestrictedComparison.freeSheaf S V))).inv (RawRestrictedComparison.generator f V))))
  have he : (RawRestrictedComparison.resolutionSectionsIso ((MorphismProperty.Over.pullback @Etale ⊤
    f).obj V) (normalizationShiftedResolution F I q)).hom
    ((RawRestrictedComparison.sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
    ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
    (DerivedCategory.Plus.ι.preimage (X := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V))) (Y :=
    DerivedCategory.Plus.Q.obj (normalizationShiftedResolution F I q)) (DerivedCategory.Q.map c))
    ((RawRestrictedComparison.zeroIso ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
    ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V))).inv
    (RawRestrictedComparison.generator f V))) =
    RawRestrictedComparison.chainEvaluation f V (normalizationShiftedResolution F I q).obj c := by
    simpa only using!
      (RawRestrictedComparison.rawRestricted_resolution_evaluation f V
        (normalizationShiftedResolution F I q) c)
  change (normalizationRestrictedIso f q F I V).hom
      ((RawRestrictedComparison.shiftIso f q F V).hom ((RawRestrictedComparison.sectionsFunctor
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ⋙ DerivedCategory.homologyFunctor
        AddCommGrpCat.{u + 1} 0).map ((DerivedCategory.Plus.ι.preimage (X :=
        (DerivedCategory.Plus.singleFunctor _ 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
        (RawRestrictedComparison.freeSheaf S V))) (Y := DerivedCategory.Plus.Q.obj
        (normalizationShiftedResolution F I q)) (DerivedCategory.Q.map c)) ≫
        (normalizationShiftedAugmentation F I q).inv) ((RawRestrictedComparison.zeroIso
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ((upperStar AddCommGrpCat.{u + 1}
        f).obj (RawRestrictedComparison.freeSheaf S V))).inv (RawRestrictedComparison.generator f
        V)))) = _
  exact hs.trans (congrArg (normalizationResolutionCocycleIso f q F I V).hom
    ((congrArg (RawRestrictedComparison.resolutionSectionsIso ((MorphismProperty.Over.pullback
      @Etale ⊤ f).obj V) (normalizationShiftedResolution F I q)).hom ha).trans he))

/-- On the chosen injective resolution, evaluation is natural in the etale object.
Source: Stacks Project, Tag 03Q8, proof of higher direct images; Tags 072W and 0BKV.
(blueprint: lem-weil-pbc-raw-restricted-resolution-naturality).

Proof: Put A(V)=f^{-1}Z[V] and let I be the chosen injective resolution.
Compose the given raw morphism with F[0][q] -> Q(I)[q]. The target is K-injective,
so fullness of localization on maps into a K-injective complex and fullness of the
homotopy quotient give a chain representative A(V)[0] -> I[q]. For t:V' -> V,
precomposition with A(t)[0] represents the restriction of the original morphism.
Apply rawRestricted_resolution_evaluation to these two chain maps and the shifted
resolution. It identifies derived evaluation, followed by the resolution sections
comparison, with evaluation of the chain map at the represented identity generator.

In every degree, the inverse-image/direct-image, sheafification and free-abelian
adjunctions followed by Yoneda identify Hom(A(V),I^n) with I^n(V times_S X).
Under this identification, precomposition by A(t) is exactly restriction of a
section: the represented map sends the identity generator at V' to the restriction
of the generator at V. Thus the two evaluated chain maps give the same section
after restriction. These identifications commute with the differential, since
they are natural in I^n. Applying homology gives the square for the section
complexes. The termwise normalizationSectionsIso and the homology/evaluation
comparison are natural transformations, so their naturality moves restriction to
homology of normalizationPresheafComplex.

Finally undo the shift. The sections, localization and homology shift comparisons
commute with these maps by their naturality. Their factors are the ones in
normalizationRestrictedIso, including the augmentation comparison, so cancellation
of the inverse augmentation recovers the displayed square for the original raw
morphism. A different chain representative changes the evaluated cocycle by a
boundary; hence the equality descends to every raw class. Degree zero, identity
arrows and empty charts use the same calculation. -/
theorem rawRestrictedResolution_naturality {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etaleᵒᵖ} (t : V ⟶ V') :
    (abelianHigherDirectImageRawPresheaf f q F).map t ≫
        rawRestrictedCohomologyComparison f q F V'.unop ≫
          (normalizationRestrictedIso f q F (injectiveResolution F) V'.unop).hom =
      rawRestrictedCohomologyComparison f q F V.unop ≫
        (normalizationRestrictedIso f q F (injectiveResolution F) V.unop).hom ≫
          ((normalizationPresheafComplex f F (injectiveResolution F)).homology
            (q : ℤ)).map t := by
  refine AddCommGrpCat.ext (fun (z :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj
        (RawRestrictedComparison.freeSheaf S V.unop)) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) ↦ ?_)
  let b : ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V'.unop))
    ⟶ ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V.unop)) :=
    (chartSource f).map t.unop
  have : (normalizationShiftedResolution F (injectiveResolution F) q).obj.IsKInjective := by
    change ((injectiveResolution F).cochainComplex⟦(q : ℤ)⟧).IsKInjective
    infer_instance
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
        (RawRestrictedComparison.freeSheaf S V.unop)))) (normalizationShiftedResolution F
        (injectiveResolution F) q).obj).surjective
      (DerivedCategory.Plus.ι.map (z ≫ (normalizationShiftedAugmentation F (injectiveResolution F)
        q).hom))
  obtain ⟨c, rfl⟩ := (HomotopyCategory.quotient _ (.up ℤ)).map_surjective
    (X := (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj
        (RawRestrictedComparison.freeSheaf S V.unop)))
    (Y := (normalizationShiftedResolution F (injectiveResolution F) q).obj) g
  let qc : (DerivedCategory.Plus.singleFunctor _ 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
    (RawRestrictedComparison.freeSheaf S V.unop)) ⟶
      DerivedCategory.Plus.Q.obj (normalizationShiftedResolution F (injectiveResolution F) q) :=
        DerivedCategory.Plus.ι.preimage
        (X := (DerivedCategory.Plus.singleFunctor _ 0).obj ((upperStar AddCommGrpCat.{u + 1}
          f).obj (RawRestrictedComparison.freeSheaf S V.unop)))
        (Y := DerivedCategory.Plus.Q.obj (normalizationShiftedResolution F (injectiveResolution F)
          q)) (DerivedCategory.Q.map c)
  have hc : qc = z ≫ (normalizationShiftedAugmentation F (injectiveResolution F) q).hom := by
    apply DerivedCategory.Plus.ι.map_injective
    dsimp only [qc]
    rw [Functor.map_preimage]
    exact hg
  have hz : qc ≫ (normalizationShiftedAugmentation F (injectiveResolution F) q).inv = z := by
    rw [hc]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let c' : (HomologicalComplex.single _ (.up ℤ) 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
    (RawRestrictedComparison.freeSheaf S V'.unop)) ⟶ (normalizationShiftedResolution F
    (injectiveResolution F) q).obj :=
    (HomologicalComplex.single _ (.up ℤ) 0).map (X := ((upperStar AddCommGrpCat.{u + 1} f).obj
      (RawRestrictedComparison.freeSheaf S V'.unop))) (Y := ((upperStar AddCommGrpCat.{u + 1}
      f).obj (RawRestrictedComparison.freeSheaf S V.unop))) b ≫ c
  let qc' : (DerivedCategory.Plus.singleFunctor _ 0).obj ((upperStar AddCommGrpCat.{u + 1} f).obj
    (RawRestrictedComparison.freeSheaf S V'.unop)) ⟶
      DerivedCategory.Plus.Q.obj (normalizationShiftedResolution F (injectiveResolution F) q) :=
        DerivedCategory.Plus.ι.preimage
        (X := (DerivedCategory.Plus.singleFunctor _ 0).obj ((upperStar AddCommGrpCat.{u + 1}
          f).obj (RawRestrictedComparison.freeSheaf S V'.unop)))
        (Y := DerivedCategory.Plus.Q.obj (normalizationShiftedResolution F (injectiveResolution F)
          q)) (DerivedCategory.Q.map c')
  have hqc : (DerivedCategory.Plus.singleFunctor _ 0).map b ≫ qc = qc' := by
    apply DerivedCategory.Plus.ι.map_injective
    dsimp only [qc, qc', c']
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
    change DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map b) ≫
      DerivedCategory.Q.map c = _
    rw [Functor.map_comp]
    rfl
  change (normalizationRestrictedIso f q F (injectiveResolution F) V'.unop).hom
      (rawRestrictedCohomologyComparison f q F V'.unop
        ((DerivedCategory.Plus.singleFunctor _ 0).map b ≫ z)) =
    ((normalizationPresheafComplex f F (injectiveResolution F)).homology (q : ℤ)).map t
      ((normalizationRestrictedIso f q F (injectiveResolution F) V.unop).hom
        (rawRestrictedCohomologyComparison f q F V.unop z))
  rw [← hz, ← Category.assoc, hqc]
  rw [normalized_chain f q F (injectiveResolution F) V'.unop c', normalized_chain f q F
    (injectiveResolution F) V.unop c]
  dsimp only [c', b]
  rw [← chainEvaluation_naturality f t (normalizationShiftedResolution F (injectiveResolution F)
    q).obj c]
  exact ConcreteCategory.congr_hom (resolutionCocycleIso_naturality f q F (injectiveResolution F) t)
    (RawRestrictedComparison.chainEvaluation f V.unop (normalizationShiftedResolution F
      (injectiveResolution F) q).obj c)

end AlgebraicGeometry.Etale
