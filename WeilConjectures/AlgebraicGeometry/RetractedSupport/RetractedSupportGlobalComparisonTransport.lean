/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportLocalizationComparison
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonGlobalCohomologyFiniteNormalized
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeComp
import all WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison

/-! # Global comparison and the canonical direct-image compositor -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
private lemma terminalEvaluation_res {C : Type*} [Category C]
    (J : GrothendieckTopology C) (A : Type*) [Category A]
    [HasWeakSheafify J A] [HasTerminal C] [HasGlobalSectionsFunctor J A]
    {T : C} (hT : IsTerminal T) (F : Sheaf J A) {S : C} (f : S ⟶ T) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F ≫ F.obj.map f.op =
      F.ΓRes (op S) := by
  have he : (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (op T) := by
    simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
      Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom,
      conjugateEquiv_apply_app]
    dsimp
    erw [Adjunction.homEquiv_counit]
    erw [Adjunction.homEquiv_unit]
    simp [constantSheafAdj, Adjunction.comp_unit_app]
  rw [he]
  exact Sheaf.ΓRes_map F f.op

section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]

private theorem compPlusCompatibility (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.PreservesInjectiveObjects]
    [F.PreservesKInjectiveComplexes] :
    Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIso F G).hom
        DerivedCategory.Plus.ι ≫
      Functor.whiskerLeft F.rightDerivedFunctorPlus
        G.rightDerivedFunctorPlusCompatibility.hom ≫
      Functor.whiskerRight F.rightDerivedFunctorPlusCompatibility.hom G.rightDerivedFunctor =
    (F ⋙ G).rightDerivedFunctorPlusCompatibility.hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.ι
        (Functor.rightDerivedFunctorCompIso F G).hom := by
  refine Functor.rightDerived_ext ((F ⋙ G).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    (F ⋙ G).rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C) _ _ _ ?_
  ext K : 2
  have hc : (F ⋙ G).rightDerivedFunctorUnit.app K.obj ≫
      (Functor.rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj K.obj) =
    (Functor.rightDerivedFunctorCompUnit F G).app K.obj := by
    have h := NatTrans.congr_app (Functor.rightDerivedNatTrans_fac
      (F ⋙ G).rightDerivedFunctor (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
      (F ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F G)
      (HomotopyCategory.quasiIso C (.up ℤ)) (𝟙 _)) K.obj
    simpa only [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique,
      Functor.rightDerivedNatIso_hom, Iso.refl_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      NatTrans.id_app, Category.id_comp] using h
  simp only [Functor.rightDerivedFunctorPlusιUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← DerivedCategory.Plus.ι.map_comp_assoc,
    Functor.rightDerivedFunctorPlusCompIso_fac_app,
    Functor.rightDerivedFunctorPlusCompUnit_app, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  erw [G.rightDerivedFunctorPlusCompatibility.hom.naturality_assoc]
  rw [reassoc_of% compatibility_fac G]
  simp only [Functor.comp_map]
  erw [← G.rightDerivedFunctor.map_comp, compatibility_fac F]
  erw [reassoc_of% compatibility_fac (F ⋙ G), hc]
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app
      K.obj = 𝟙 _ := by
    rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
      (.up ℤ)).hom.app K.obj), Iso.hom_inv_id_app,
      Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    hi, CategoryTheory.Functor.map_id,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id]
  erw [Category.id_comp]
  rfl

private theorem compPlusFormula (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [F.PreservesInjectiveObjects]
    [F.PreservesKInjectiveComplexes] (e : F ⋙ G ≅ H)
    (B : DerivedCategory.Plus C) :
    (Functor.rightDerivedFunctorCompIso' F G e).hom.app B.obj =
      G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.inv.app B) ≫
        G.rightDerivedFunctorPlusCompatibility.inv.app (F.rightDerivedFunctorPlus.obj B) ≫
        DerivedCategory.Plus.ι.map
          ((Functor.rightDerivedFunctorPlusCompIso' F G e).hom.app B) ≫
        H.rightDerivedFunctorPlusCompatibility.hom.app B := by
  have hc := NatTrans.congr_app (compPlusCompatibility F G) B
  have hn := NatTrans.congr_app (compatibility_naturality e.hom) B
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc hn
  apply (cancel_epi (G.rightDerivedFunctor.map
    (F.rightDerivedFunctorPlusCompatibility.hom.app B))).mp
  apply (cancel_epi (G.rightDerivedFunctorPlusCompatibility.hom.app
    (F.rightDerivedFunctorPlus.obj B))).mp
  apply (cancel_epi (DerivedCategory.Plus.ι.map
    ((Functor.rightDerivedFunctorPlusCompIso F G).hom.app B))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% hc]
  simp only [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorPlusCompIso',
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.hom_inv_id_app_assoc]
  erw [Iso.hom_inv_id_app_assoc]
  simpa only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorPlusNatIso,
    Functor.comp_obj, ObjectProperty.ι_obj] using hn.symm

end

namespace AlgebraicGeometry.ProEtale.RetractedSupport

/-- Terminal evaluation of etale pushforward along its canonical pullback projection.
Source: `lem-pur-gysin-structure.proof.md`, global-comparison step
(blueprint: lem-pur-retracted-support-global-comparison-transport). -/
def etImageSectionsIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Etale.lowerStar (Modules P) p ⋙ Etale.sectionsFunctor (Modules P) Y ≅
      Etale.sectionsFunctor (Modules P) X :=
  ((sheafSections X.smallEtaleTopology (Modules P)).mapIso
    (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 Y) p))
      (Category.comp_id _)).op).symm

/-- Unbounded etale Leray comparison using the canonical terminal evaluation.
Source: `lem-pur-gysin-structure.proof.md`, global-comparison step
(blueprint: lem-pur-retracted-support-global-comparison-transport). -/
def etImageGlobalIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (Etale.lowerStar (Modules P) p).rightDerivedFunctor ⋙
        (Etale.sectionsFunctor (Modules P) Y).rightDerivedFunctor ≅
      (Etale.sectionsFunctor (Modules P) X).rightDerivedFunctor :=
  let := (Etale.upperStarLowerStarAdjunction (Modules P) p).preservesKInjectiveComplexes
  Functor.rightDerivedFunctorCompIso' _ _ (etImageSectionsIso P p)

/-- Global-sections and terminal-evaluation Leray identifications agree.
Source: `lem-pur-gysin-structure.proof.md`, global-comparison step
(blueprint: lem-pur-retracted-support-global-comparison-transport).
Proof: all terminal evaluations are restrictions of the global-section cone.
Naturality of those restrictions reduces the equation to uniqueness of a morphism
between terminal objects, including the base-changed terminal object. -/
theorem etImageSectionsIso_global (P : WeilConjectures.PurityFiniteSetting.{u})
    {T Y : Scheme.{u}} (p : T ⟶ Y) (H : EtSheaves P T) :
    (etImageSectionsIso P p).hom.app H ≫
        (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (Modules P)
          (MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) T)).inv.app H =
      (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (Modules P)
        (MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) Y)).inv.app
          ((Etale.lowerStar (Modules P) p).obj H) ≫
        (Etale.lowerStarCompGlobalSectionsIso (Modules P) p).hom.app H := by
  let A := Modules P
  let wY : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let wT : T.Etale := Scheme.Etale.mk (𝟙 T)
  let tY := supportEtaleGlobalEvaluationIso P.Coefficient Y
  let tT := supportEtaleGlobalEvaluationIso P.Coefficient T
  let e := ((MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) Y).isTerminalObj
    p.Etale).uniqueUpToIso
      (MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) T)
  let F := (Etale.lowerStar A p).obj H
  let a : ⊤_ Y.Etale ⟶ wY :=
    (MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) Y).from _
  let b : ⊤_ T.Etale ⟶ wT :=
    (MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) T).from _
  let c := (PreservesTerminal.iso p.Etale).inv
  have ht : c ≫ p.Etale.map a = b ≫ e.inv :=
    ((MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) Y).isTerminalObj
      p.Etale).hom_ext _ _
  have hy : tY.inv.app F ≫ F.ΓRes (op (⊤_ Y.Etale)) = F.obj.map a.op := by
    erw [← Sheaf.ΓRes_map F a.op]
    have he := terminalEvaluation_res _ _
      (MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) Y) F (𝟙 wY)
    rw [op_id] at he
    erw [F.obj.map_id, Category.comp_id] at he
    rw [← he]
    change tY.inv.app F ≫ tY.hom.app F ≫ _ = _
    simp only [Iso.inv_hom_id_app_assoc]
  have hz : H.obj.map b.op ≫ (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app H =
      tT.inv.app H := by
    apply (cancel_epi (tT.hom.app H)).mp
    simp only [← Category.assoc]
    erw [terminalEvaluation_res _ _
      (MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) T) H b]
    have he := terminalEvaluation_res _ _ terminalIsTerminal H (𝟙 (⊤_ T.Etale))
    rw [op_id] at he
    erw [H.obj.map_id, Category.comp_id] at he
    rw [← he]
    exact (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom_inv_id_app H
      |>.trans (tT.hom_inv_id_app H).symm
  have he : e = MorphismProperty.Over.isoMk
      (asIso (pullback.snd (𝟙 Y) p)) (Category.comp_id _) := by
    apply Iso.ext
    exact (MorphismProperty.Over.mkIdTerminal (P := @AlgebraicGeometry.Etale) T).hom_ext _ _
  symm
  change tY.inv.app F ≫ (Etale.lowerStarCompGlobalSectionsIso A p).hom.app H = _
  simp only [Etale.lowerStarCompGlobalSectionsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  change tY.inv.app F ≫ (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app F ≫
    H.obj.map c.op ≫ (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app H = _
  have hr := terminalEvaluation_res _ _ terminalIsTerminal F (𝟙 (⊤_ Y.Etale))
  rw [op_id] at hr
  erw [F.obj.map_id, Category.comp_id] at hr
  rw [hr, ← Category.assoc, ← Category.assoc, hy]
  change H.obj.map (p.Etale.map a).op ≫ H.obj.map c.op ≫ _ = _
  have hmap : H.obj.map (p.Etale.map a).op ≫ H.obj.map c.op =
      H.obj.map e.inv.op ≫ H.obj.map b.op := by
    rw [← Functor.map_comp, ← op_comp, ht, op_comp, Functor.map_comp]
  rw [← Category.assoc, hmap, Category.assoc]
  erw [hz]
  rw [he]
  rfl

private theorem globalUnit_pushforward (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (F : EtSheaves P X) :
    (etImageSectionsIso P p).inv.app F ≫
      (finiteComparisonGlobalSectionsUnit Y P.Coefficient).app
        ((Etale.lowerStar (Modules P) p).obj F) ≫
      (globalSectionsFunctor (Modules P) Y).map
        ((lowerStarComparisonUpperStarBaseChange p (Modules P)).app F) =
    (finiteComparisonGlobalSectionsUnit X P.Coefficient).app F ≫
      (imageSectionsIso P p).inv.app ((comparisonUpperStar (Modules P) X).obj F) := by
  have hm := unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app
    (Modules P) p F
  have hs := congrArg (fun t ↦ t.hom.app (op (Scheme.Etale.mk (𝟙 Y)))) hm
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hs
  dsimp only [finiteComparisonGlobalSectionsUnit, globalSectionsFunctor]
  change (etImageSectionsIso P p).inv.app F ≫
    ((comparisonAdjunction (Modules P) Y).unit.app
      ((Etale.lowerStar (Modules P) p).obj F)).hom.app (op (Scheme.Etale.mk (𝟙 Y))) ≫
    ((comparisonLowerStar (Modules P) Y).map
      ((lowerStarComparisonUpperStarBaseChange p (Modules P)).app F)).hom.app
        (op (Scheme.Etale.mk (𝟙 Y))) = _
  erw [hs]
  have hn := ((comparisonAdjunction (Modules P) X).unit.app F).hom.naturality
    ((MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 Y) p))
      (Category.comp_id _) : Scheme.Etale.mk (pullback.snd (𝟙 Y) p) ≅
        Scheme.Etale.mk (𝟙 X)).hom).op
  let e : Scheme.Etale.mk (pullback.snd (𝟙 Y) p) ≅ Scheme.Etale.mk (𝟙 X) :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 Y) p)) (Category.comp_id _)
  let M := (comparisonUpperStar (Modules P) X).obj F
  change F.obj.map e.hom.op ≫
      ((Etale.lowerStar (Modules P) p).map
        ((comparisonAdjunction (Modules P) X).unit.app F)).hom.app
          (op (Scheme.Etale.mk (𝟙 Y))) ≫ 𝟙 _ ≫
      M.obj.map (𝟙 (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).obj
        (Y.toProEt.obj (Scheme.Etale.mk (𝟙 Y)))))) ≫ 𝟙 _ =
    ((comparisonAdjunction (Modules P) X).unit.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 X))) ≫
      ((comparisonLowerStar (Modules P) X).obj M).obj.map e.hom.op
  erw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  exact hn

/-- Bounded-below etale Leray comparison, with the canonical derived units.
Source: `lem-pur-gysin-structure.proof.md`, global-comparison step
(blueprint: lem-pur-retracted-support-global-comparison-transport). -/
def etImageGlobalPlusIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (Etale.lowerStar (Modules P) p).rightDerivedFunctorPlus ⋙
        (Etale.sectionsFunctor (Modules P) Y).rightDerivedFunctorPlus ≅
      (Etale.sectionsFunctor (Modules P) X).rightDerivedFunctorPlus :=
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction (Modules P) p)
  Functor.rightDerivedFunctorPlusCompIso' _ _ (etImageSectionsIso P p)

/-- Bounded-below pro-etale Leray comparison in the same coordinates.
Source: `lem-pur-gysin-structure.proof.md`, global-comparison step
(blueprint: lem-pur-retracted-support-global-comparison-transport). -/
def imageGlobalPlusIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (lowerStar (Modules P) p).rightDerivedFunctorPlus ⋙
        (globalSectionsFunctor (Modules P) Y).rightDerivedFunctorPlus ≅
      (globalSectionsFunctor (Modules P) X).rightDerivedFunctorPlus :=
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction (Modules P) p)
  Functor.rightDerivedFunctorPlusCompIso' _ _ (imageSectionsIso P p)

/-- Global comparison commutes with pushforward and its specified Leray comparison.
Source: `lem-pur-gysin-structure.proof.md`, global-comparison step
(blueprint: lem-pur-retracted-support-global-comparison-transport).
Proof: evaluation of the underived mate equation at the terminal object is naturality
of the comparison unit along the pullback projection. The composition theorem for
derived base change derives exactly this square, retaining all the derived units. -/
theorem globalComparisonPlus_comp (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (B : DerivedCategory.Plus (EtSheaves P X)) :
    (𝟭 (Modules P)).mapDerivedCategoryPlus.map ((etImageGlobalPlusIso P p).inv.app B) ≫
      (finiteComparisonGlobalSections Y P.Coefficient).app
        ((Etale.lowerStar (Modules P) p).rightDerivedFunctorPlus.obj B) ≫
      (globalSectionsFunctor (Modules P) Y).rightDerivedFunctorPlus.map
        ((comparisonDirectImageCanonicalMate P.Coefficient p).app B) =
    (finiteComparisonGlobalSections X P.Coefficient).app B ≫
      (imageGlobalPlusIso P p).inv.app ((nuPlus P X).obj B) := by
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction (Modules P) p)
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction (Modules P) p)
  apply Functor.rightDerivedFunctorPlusBaseChange_comp (etImageSectionsIso P p)
    (imageSectionsIso P p) (lowerStarComparisonUpperStarBaseChange p (Modules P))
    (finiteComparisonGlobalSectionsUnit Y P.Coefficient)
    (finiteComparisonGlobalSectionsUnit X P.Coefficient)
  intro F
  exact globalUnit_pushforward P p F

/-- Remove the derived identity from the finite global comparison.
Source: `lem-pur-gysin-structure.proof.md`, derived-unit transport
(blueprint: lem-pur-retracted-support-global-comparison-transport). -/
def globalComparisonPlusIso (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    (Etale.sectionsFunctor (Modules P) X).rightDerivedFunctorPlus ≅
      nuPlus P X ⋙ (globalSectionsFunctor (Modules P) X).rightDerivedFunctorPlus := by
  let := isIso_finiteComparisonGlobalSections X P.Coefficient
  exact (Functor.rightUnitor _).symm ≪≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso (Modules P))).symm ≪≫
    asIso (finiteComparisonGlobalSections X P.Coefficient)

/-- The unit-normalized global comparison in unbounded coordinates on bounded inputs.
Source: `lem-pur-gysin-structure.proof.md`, derived-unit transport
(blueprint: lem-pur-retracted-support-global-comparison-transport). -/
def globalComparisonIso (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    DerivedCategory.Plus.ι ⋙ (Etale.sectionsFunctor (Modules P) X).rightDerivedFunctor ≅
      input P X ⋙ global P X :=
  (Etale.sectionsFunctor (Modules P) X).rightDerivedFunctorPlusCompatibility.symm ≪≫
    Functor.isoWhiskerRight (globalComparisonPlusIso P X) DerivedCategory.Plus.ι ≪≫
    Functor.isoWhiskerLeft (nuPlus P X)
      (globalSectionsFunctor (Modules P) X).rightDerivedFunctorPlusCompatibility

/-- The unbounded extension of the ordinary comparison-unit map on terminal sections.
Source: `lem-pur-gysin-structure.proof.md`, derived-unit transport
(blueprint: lem-pur-retracted-support-global-comparison-transport). -/
def globalComparisonDerived (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    (Etale.sectionsFunctor (Modules P) X).rightDerivedFunctor ⟶
      nu P X ⋙ global P X :=
  Functor.rightDerivedPullback (comparisonUpperStar (Modules P) X)
    (finiteComparisonGlobalSectionsUnit X P.Coefficient)

/-- The comparison is the extension of the ordinary unit by the derived universal property.
Source: `lem-pur-gysin-structure.proof.md`, derived-unit transport
(blueprint: lem-pur-retracted-support-global-comparison-transport).
Proof: the bounded/unbounded compatibility isomorphisms identify the normalized
bounded-below base change with the right-derived pullback. Cancel the source
compatibility isomorphism in its defining normalization equation. -/
theorem globalComparisonIso_hom (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) (B : DerivedCategory.Plus (EtSheaves P X)) :
    (globalComparisonIso P X).hom.app B =
      (Functor.rightDerivedPullback (comparisonUpperStar (Modules P) X)
        (finiteComparisonGlobalSectionsUnit X P.Coefficient)).app B.obj := by
  have h := NatTrans.congr_app
    (baseChange_rightDerivedPullback (finiteComparisonGlobalSectionsUnit X P.Coefficient)) B
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  dsimp only [globalComparisonIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.isoWhiskerLeft_hom]
  change _ ≫ DerivedCategory.Plus.ι.map
    ((normalizedBaseChange (finiteComparisonGlobalSectionsUnit X P.Coefficient)).app B) ≫ _ = _
  erw [h, Iso.inv_hom_id_app_assoc]
  rfl


private theorem globalPlusSquare (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (B : DerivedCategory.Plus (EtSheaves P X)) :
    (globalComparisonPlusIso P Y).hom.app
        ((Etale.lowerStar (Modules P) p).rightDerivedFunctorPlus.obj B) ≫
      (globalSectionsFunctor (Modules P) Y).rightDerivedFunctorPlus.map
        ((comparisonDirectImageCanonicalMate P.Coefficient p).app B) ≫
      (imageGlobalPlusIso P p).hom.app ((nuPlus P X).obj B) =
    (etImageGlobalPlusIso P p).hom.app B ≫ (globalComparisonPlusIso P X).hom.app B := by
  have h := globalComparisonPlus_comp P p B
  let d := Functor.mapDerivedCategoryPlusIdIso (Modules P)
  apply (cancel_epi (d.hom.app
      ((Etale.sectionsFunctor (Modules P) X).rightDerivedFunctorPlus.obj B) ≫
    (etImageGlobalPlusIso P p).inv.app B)).mp
  have hn := d.inv.naturality ((etImageGlobalPlusIso P p).inv.app B)
  simp only [Functor.id_map] at hn
  simp only [globalComparisonPlusIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_inv,
    Category.id_comp, asIso_hom, Category.assoc]
  erw [reassoc_of% hn]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% h]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  dsimp only [d]
  erw [Iso.hom_inv_id_app_assoc, Category.comp_id]

private theorem etImageGlobalIso_plus (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (B : DerivedCategory.Plus (EtSheaves P X)) :
    (etImageGlobalIso P p).hom.app B.obj =
      (Etale.sectionsFunctor (Modules P) Y).rightDerivedFunctor.map
          ((Etale.lowerStar (Modules P) p).rightDerivedFunctorPlusCompatibility.inv.app B) ≫
        (Etale.sectionsFunctor (Modules P) Y).rightDerivedFunctorPlusCompatibility.inv.app
          ((Etale.lowerStar (Modules P) p).rightDerivedFunctorPlus.obj B) ≫
        DerivedCategory.Plus.ι.map ((etImageGlobalPlusIso P p).hom.app B) ≫
        (Etale.sectionsFunctor (Modules P) X).rightDerivedFunctorPlusCompatibility.hom.app B := by
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction (Modules P) p)
  let := (Etale.upperStarLowerStarAdjunction (Modules P) p).preservesKInjectiveComplexes
  exact compPlusFormula _ _ _ (etImageSectionsIso P p) B

private theorem imageGlobalIso_plus (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (B : DerivedCategory.Plus (ProSheaves P X)) :
    (imageGlobalIso P p).hom.app B.obj =
      (global P Y).map
          ((lowerStar (Modules P) p).rightDerivedFunctorPlusCompatibility.inv.app B) ≫
        (globalSectionsFunctor (Modules P) Y).rightDerivedFunctorPlusCompatibility.inv.app
          ((lowerStar (Modules P) p).rightDerivedFunctorPlus.obj B) ≫
        DerivedCategory.Plus.ι.map ((imageGlobalPlusIso P p).hom.app B) ≫
        (globalSectionsFunctor (Modules P) X).rightDerivedFunctorPlusCompatibility.hom.app B := by
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction (Modules P) p)
  let := (upperStarLowerStarAdjunction (Modules P) p).preservesKInjectiveComplexes
  exact compPlusFormula _ _ _ (imageSectionsIso P p) B

set_option maxHeartbeats 1600000 in
-- Elaborating the derived comparison square needs the compatibility maps of four functors.
/-- The canonical direct-image mate commutes with the specified global comparisons.
Source: `lem-pur-gysin-structure.proof.md`, global-comparison step
(blueprint: lem-pur-retracted-support-global-comparison-transport).
Proof: apply the derived base-change composition equation to terminal evaluation.
The derived composition maps and the bounded/unbounded identifications have the same
unit normalization. Cancel those identifications and the derived identity comparison. -/
theorem globalComparison_transport (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (B : DerivedCategory.Plus (EtSheaves P X)) :
    (globalComparisonDerived P Y).app
        ((Etale.lowerStar (Modules P) p).rightDerivedFunctor.obj B.obj) ≫
      (global P Y).map (imageComparison P p B) ≫
      (imageGlobalIso P p).hom.app ((input P X).obj B) =
    (etImageGlobalIso P p).hom.app B.obj ≫ (globalComparisonDerived P X).app B.obj := by
  let F := Etale.lowerStar (Modules P) p
  let G := globalSectionsFunctor (Modules P) Y
  let := (Etale.upperStarLowerStarAdjunction (Modules P) p).preservesKInjectiveComplexes
  let := (upperStarLowerStarAdjunction (Modules P) p).preservesKInjectiveComplexes
  apply (cancel_epi ((Etale.sectionsFunctor (Modules P) Y).rightDerivedFunctor.map
    (F.rightDerivedFunctorPlusCompatibility.hom.app B))).mp
  have hn := (globalComparisonDerived P Y).naturality
    (F.rightDerivedFunctorPlusCompatibility.hom.app B)
  simp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← globalComparisonIso_hom P Y (F.rightDerivedFunctorPlus.obj B),
    ← globalComparisonIso_hom P X B]
  erw [etImageGlobalIso_plus P p B]
  erw [imageGlobalIso_plus P p ((nuPlus P X).obj B)]
  have hm : (nu P Y).map (F.rightDerivedFunctorPlusCompatibility.hom.app B) ≫
      imageComparison P p B =
    DerivedCategory.Plus.ι.map ((comparisonDirectImageCanonicalMate P.Coefficient p).app B) ≫
      (lowerStar (Modules P) p).rightDerivedFunctorPlusCompatibility.hom.app
        ((nuPlus P X).obj B) := by
    dsimp only [imageComparison, Iso.app_inv, Iso.app_hom]
    simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_inv, Iso.refl_hom,
      NatTrans.id_app]
    dsimp only [F]
    erw [← (nu P Y).map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [← (global P Y).map_comp_assoc, hm]
  dsimp only [F]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [globalComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  erw [Category.comp_id, Iso.hom_inv_id_app_assoc]
  erw [← G.rightDerivedFunctorPlusCompatibility.hom.naturality_assoc
    ((comparisonDirectImageCanonicalMate P.Coefficient p).app B)]
  dsimp only [Functor.comp_map, ObjectProperty.ι_map]
  erw [Iso.hom_inv_id_app_assoc]
  erw [← DerivedCategory.Plus.ι.map_comp_assoc, ← DerivedCategory.Plus.ι.map_comp_assoc]
  rw [Category.assoc]
  erw [globalPlusSquare P p B]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.RetractedSupport
