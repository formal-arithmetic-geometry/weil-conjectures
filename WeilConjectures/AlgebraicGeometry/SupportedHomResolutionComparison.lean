/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
public import Mathlib.CategoryTheory.Preadditive.Comma
import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
import WeilConjectures.Algebra.Homology.SmoothPurity.ClosedSupportHom
import WeilConjectures.AlgebraicGeometry.RelativeCone.PurityRelativeCone
import WeilConjectures.AlgebraicGeometry.Closed.ClosedSupportHomSequence
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.CategoryTheory.Abelian.ExtResolutionDerivedConnecting
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# Evaluation on module-valued supported Hom resolutions

Source: Stacks Tags 06XR and 095L; the supported-Hom paragraph of the proof of
lem-amb-cartier-kummer-map.
(blueprint: lem-pur-supported-hom-resolution-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4000

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex

namespace AlgebraicGeometry.Etale

attribute [local instance] hasExt_of_enoughInjectives

private local instance (priority := 3000) additiveSelfForget :
    HasForget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1} := ⟨𝟭 _, rfl⟩

private local instance additiveSelfForget_additive :
    (forget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1}).Additive :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u + 1}).Additive

private local instance additiveSelfForget_homology :
    (forget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1}).PreservesHomology :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u + 1}).PreservesHomology

private abbrev sectionFunctor (B : Type (u + 1)) [CommRing B] (T : Scheme.{u})
    (U : T.Etale) := moduleAbelianForget B T ⋙ etaleSectionFunctor U

private abbrev sectionOneEquiv (B : Type (u + 1)) [CommRing B] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
      (ModuleCat.of B B)) ⟶ F) ≃+
        (sectionFunctor B T (Scheme.Etale.mk (𝟙 T))).obj F :=
  ((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} B)
    (MorphismProperty.Over.mkIdTerminal @Etale T)).homAddEquiv _ F).trans
      (ModuleCat.homAddEquiv.trans (LinearMap.ringLmapEquivSelf B B _).toAddEquiv)

private lemma sectionOneEquiv_apply (B : Type (u + 1)) [CommRing B] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (f : ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
      (ModuleCat.of B B)) ⟶ F) :
    sectionOneEquiv B T F f = f.hom.app (op (Scheme.Etale.mk (𝟙 T)))
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of B B))).app
          (op (Scheme.Etale.mk (𝟙 T))) (1 : B)) := by
  rw [sectionOneEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_unit]
  rfl

private abbrev evaluationMap (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) :
    preadditiveCoyoneda.obj (op ((lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B B)))) ⟶ sectionFunctor B T (Scheme.Etale.mk (𝟙 T)) where
  app F := AddCommGrpCat.ofHom
    { toFun k := sectionOneEquiv B T F (supportedConstantUnit B i ≫ k)
      map_zero' := by
        change sectionOneEquiv B T F (supportedConstantUnit B i ≫ 0) = 0
        rw [comp_zero]
        exact (sectionOneEquiv B T F).map_zero
      map_add' k l := by
        change sectionOneEquiv B T F (supportedConstantUnit B i ≫ (k + l)) = _
        rw [Preadditive.comp_add, map_add] }
  naturality F F' f := by
    ext k
    simp only [sectionOneEquiv_apply]
    rfl

private abbrev sectionRestrictionMap (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    sectionFunctor B T (Scheme.Etale.mk (𝟙 T)) ⟶
      sectionFunctor B T (Scheme.Etale.mk i.openComplement.ι) where
  app F := ((moduleAbelianForget B T).obj F).obj.map
    ((MorphismProperty.Over.mkIdTerminal @Etale T).from
      (Scheme.Etale.mk i.openComplement.ι)).op
  naturality _ _ f := (((moduleAbelianForget B T).map f).hom.naturality _).symm

private abbrev globalSectionsEvaluationIso (B : Type (u + 1)) [CommRing B]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).obj
      ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} B)).obj F) ≅
        (sectionFunctor B T (Scheme.Etale.mk (𝟙 T))).obj F :=
  (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).mapIso
    ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} B)
      terminalIsTerminal).app F ≪≫ F.obj.mapIso
        (terminalIsTerminal.uniqueUpToIso (MorphismProperty.Over.mkIdTerminal @Etale T)).op.symm)

private abbrev openSectionsEvaluationIso (B : Type (u + 1)) [CommRing B]
    {T V : Scheme.{u}} (v : V ⟶ T) [IsOpenImmersion v]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    ((upperStar (ModuleCat.{u + 1} B) v ⋙
      Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} B)) ⋙
        forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).obj F ≅
          (sectionFunctor B T (Scheme.Etale.mk v)).obj F := by
  let L := MorphismProperty.Over.map ⊤ (inferInstance : Etale v)
  let e : L.obj (Scheme.Etale.mk (𝟙 V)) ≅ Scheme.Etale.mk v :=
    MorphismProperty.Over.isoMk (Iso.refl V) (Category.id_comp v)
  let d := L.mapIso
    (terminalIsTerminal.uniqueUpToIso (MorphismProperty.Over.mkIdTerminal @Etale V)) ≪≫ e
  exact (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).mapIso
    ((Sheaf.ΓNatIsoSheafSections V.smallEtaleTopology (ModuleCat.{u + 1} B)
        terminalIsTerminal).app _ ≪≫
      ((sheafToPresheaf _ _).mapIso
        ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) v
          inferInstance).app F)).app (op (⊤_ V.Etale)) ≪≫
      F.obj.mapIso d.op.symm)

private lemma evaluationMap_normalized (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).map
        ((closedSupportHomToSections B i).app F) ≫
      (globalSectionsEvaluationIso B T F).hom = (evaluationMap B i).app F := by
  ext k
  change (F.obj.map _)
    ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} B)
      terminalIsTerminal).hom.app F
        (rankOneSectionsEquiv B T F (supportedConstantUnit B i ≫ k))) = _
  dsimp only [rankOneSectionsEquiv]
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  simp only [Iso.toLinearEquiv_apply, Iso.symm_hom]
  rw [← ConcreteCategory.comp_apply]
  change F.obj.map _
    ((((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} B)
      terminalIsTerminal).app F).inv ≫
      ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} B)
        terminalIsTerminal).app F).hom) _) = _
  rw [Iso.inv_hom_id, ConcreteCategory.id_apply]
  change F.obj.map _
    (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} B)
      terminalIsTerminal).homEquiv _ F (supportedConstantUnit B i ≫ k)) (1 : B)) =
    sectionOneEquiv B T F (supportedConstantUnit B i ≫ k)
  rw [Adjunction.homEquiv_unit, sectionOneEquiv_apply]
  change F.obj.map _ (((supportedConstantUnit B i ≫ k).hom.app _)
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of B B))).app _ (1 : B))) = _
  rw [← ConcreteCategory.comp_apply, ← (supportedConstantUnit B i ≫ k).hom.naturality,
    ConcreteCategory.comp_apply]
  congr 1
  exact (ConcreteCategory.congr_hom
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of B B))).naturality _) (1 : B)).symm

private lemma unit_restriction (B : Type (u + 1)) [CommRing B]
    {T V : Scheme.{u}} (v : V ⟶ T) [IsOpenImmersion v]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) v).unit.app F).hom.app
        (op (⊤_ T.Etale)) ≫
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} B) v).hom.app
        ((upperStar (ModuleCat.{u + 1} B) v).obj F) ≫
      ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) v
        inferInstance).hom.app F).hom.app (op (⊤_ V.Etale)) =
    F.obj.map (terminal.from
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).obj (⊤_ V.Etale))).op := by
  let ι := upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) v inferInstance
  let P : (MorphismProperty.Over.pullback @Etale ⊤ v).obj (⊤_ T.Etale) ≅
      ⊤_ V.Etale := PreservesTerminal.iso _
  have h₁ : ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) v).unit.app F).hom.app
        (op (⊤_ T.Etale)) ≫ (ι.hom.app F).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj (⊤_ T.Etale))) =
      ((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) v
        inferInstance).unit.app F).hom.app (op (⊤_ T.Etale)) :=
    congrArg (fun φ ↦ φ.hom.app (op (⊤_ T.Etale)))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) v).unit_leftAdjointUniq_hom_app
        (localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) v inferInstance) F)
  obtain ⟨m, hm⟩ : ∃ m,
      ((localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) v
        inferInstance).unit.app F).hom.app (op (⊤_ T.Etale)) =
          F.obj.map (Quiver.Hom.op m) := ⟨_, rfl⟩
  have h₂ := (ι.hom.app F).hom.naturality P.inv.op
  have h₃ : (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} B) v).hom.app
      ((upperStar (ModuleCat.{u + 1} B) v).obj F) =
        ((upperStar (ModuleCat.{u + 1} B) v).obj F).obj.map P.inv.op := rfl
  rw [h₃, h₂, ← Category.assoc, h₁, hm]
  change F.obj.map _ ≫ F.obj.map _ = _
  rw [← Functor.map_comp]
  congr 1
  exact Quiver.Hom.unop_inj (terminal.hom_ext _ _)

private lemma openSectionsEvaluationIso_restrict (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).map
        (globalSectionsUpperStarMap (ModuleCat.{u + 1} B) i.openComplement.ι F) ≫
      (openSectionsEvaluationIso B i.openComplement.ι F).hom =
        (globalSectionsEvaluationIso B T F).hom ≫ (sectionRestrictionMap B i).app F := by
  dsimp only [openSectionsEvaluationIso, globalSectionsEvaluationIso, Iso.trans_hom,
    Functor.mapIso_hom]
  rw [← Functor.map_comp]
  unfold globalSectionsUpperStarMap
  simp only [Category.assoc, Iso.app_hom]
  erw [Iso.inv_hom_id_app_assoc]
  change (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).map
    ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} B)
      terminalIsTerminal).hom.app F ≫
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) i.openComplement.ι).unit.app F).hom.app
        (op (⊤_ T.Etale)) ≫
        (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} B) i.openComplement.ι).hom.app _ ≫
        ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) i.openComplement.ι
          inferInstance).hom.app F).hom.app (op (⊤_ i.openComplement.toScheme.Etale))) ≫
      F.obj.map _) = _
  rw [unit_restriction]
  rw [← Functor.map_comp]
  change _ = (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).map
    (((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} B)
      terminalIsTerminal).hom.app F ≫ F.obj.map _) ≫ F.obj.map _)
  rw [Category.assoc, ← F.obj.map_comp]
  congr 2
  apply congrArg F.obj.map
  apply Quiver.Hom.unop_inj
  exact terminal.hom_ext _ _

private lemma evaluationMap_comp_restriction (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    ∀ F, (evaluationMap B i).app F ≫ (sectionRestrictionMap B i).app F = 0 := by
  let τ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} B) ⟶
      upperStar (ModuleCat.{u + 1} B) i.openComplement.ι ⋙
        Sheaf.Γ i.openComplement.toScheme.smallEtaleTopology (ModuleCat.{u + 1} B) :=
    closedSupportSectionsPullback B i.openComplement.ι
  have hcomp : Set.range i.openComplement.ι.base = (Set.range i.base)ᶜ := by
    simpa only [Scheme.Opens.range_ι] using i.coe_openComplement
  have hz := closedSupportHomToSections_comp B i i.openComplement.ι hcomp τ (fun _ ↦ rfl)
  intro F
  rw [← evaluationMap_normalized, Category.assoc, ← openSectionsEvaluationIso_restrict]
  rw [← Category.assoc, ← Functor.map_comp]
  exact (congrArg (fun f ↦
    (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}).map f ≫
      (openSectionsEvaluationIso B i.openComplement.ι F).hom) (hz F)).trans
        (by rw [Functor.map_zero, zero_comp])

private lemma evaluationMap_shortExact (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) [Injective F] :
    (ShortComplex.mk ((evaluationMap B i).app F) ((sectionRestrictionMap B i).app F)
      (evaluationMap_comp_restriction B i F)).ShortExact := by
  let τ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} B) ⟶
      upperStar (ModuleCat.{u + 1} B) i.openComplement.ι ⋙
        Sheaf.Γ i.openComplement.toScheme.smallEtaleTopology (ModuleCat.{u + 1} B) :=
    closedSupportSectionsPullback B i.openComplement.ι
  have hcomp : Set.range i.openComplement.ι.base = (Set.range i.base)ᶜ := by
    simpa only [Scheme.Opens.range_ι] using i.coe_openComplement
  let S : ShortComplex (ModuleCat.{u + 1} B) :=
    ShortComplex.mk ((closedSupportHomToSections B i).app F) (τ.app F)
    (closedSupportHomToSections_comp B i i.openComplement.ι hcomp τ (fun _ ↦ rfl) F)
  have hS : S.ShortExact :=
    closedSupportHomSequence_shortExact B i i.openComplement.ι hcomp τ (fun _ ↦ rfl)
      F inferInstance
  let e : S.map (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) ≅
      (ShortComplex.mk ((evaluationMap B i).app F) ((sectionRestrictionMap B i).app F)
        (evaluationMap_comp_restriction B i F) : ShortComplex AddCommGrpCat.{u + 1}) :=
    ShortComplex.isoMk
    (S₁ := S.map (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}))
    (S₂ := ShortComplex.mk ((evaluationMap B i).app F) ((sectionRestrictionMap B i).app F)
      (evaluationMap_comp_restriction B i F))
    (Iso.refl _) (globalSectionsEvaluationIso B T F)
    (openSectionsEvaluationIso B i.openComplement.ι F)
    (by
      change 𝟙 _ ≫ (evaluationMap B i).app F = _
      rw [Category.id_comp]
      exact (evaluationMap_normalized B i F).symm)
    (by
      change (globalSectionsEvaluationIso B T F).hom ≫ (sectionRestrictionMap B i).app F = _
      exact (openSectionsEvaluationIso_restrict B i F).symm)
  have hf : (S.map (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})).ShortExact := by
    have := hS.mono_f
    have := hS.epi_g
    exact hS.map (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})
  exact ShortComplex.shortExact_of_iso e hf

private abbrev homComplex (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ) :=
  ((preadditiveCoyoneda.obj (op ((lowerStar (ModuleCat.{u + 1} B) i).obj
    ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
      (ModuleCat.of B B))))).mapHomologicalComplex (.up ℕ)).obj I

private abbrev evaluationComplexMap (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ) :
    (homComplex B i I).extend ComplexShape.embeddingUpNat ⟶
      relativeSections (Scheme.Etale.mk (𝟙 T))
        (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I) :=
  extendMap ((NatTrans.mapHomologicalComplex (evaluationMap B i) (.up ℕ)).app I)
    ComplexShape.embeddingUpNat

private lemma evaluationComplexMap_zero (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ) :
    evaluationComplexMap B i I ≫
      relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι)
        (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I) = 0 := by
  dsimp only [evaluationComplexMap, relativeSectionRestriction]
  rw [← extendMap_comp]
  have h : (NatTrans.mapHomologicalComplex (evaluationMap B i) (.up ℕ)).app I ≫
      etaleSectionMap ((MorphismProperty.Over.mkIdTerminal @Etale T).from
        (Scheme.Etale.mk i.openComplement.ι))
        (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I) = 0 := by
    ext n : 1
    exact evaluationMap_comp_restriction B i (I.X n)
  rw [h, extendMap_zero]

private abbrev evaluationConeMap (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ) :
    (homComplex B i I).extend ComplexShape.embeddingUpNat ⟶
      relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I) :=
  CochainComplex.closedConeLift _ (evaluationComplexMap B i I) (evaluationComplexMap_zero B i I)

private lemma evaluationConeMap_quasiIso (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (I : InjectiveResolution F) :
    QuasiIso (evaluationConeMap B i I.cocomplex) := by
  let A := relativeSections (Scheme.Etale.mk (𝟙 T))
    (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  let W := relativeSections (Scheme.Etale.mk i.openComplement.ι)
    (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  let L := (homComplex B i I.cocomplex).extend ComplexShape.embeddingUpNat
  let r : A ⟶ W := relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι)
    (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  let S := ShortComplex.mk (evaluationComplexMap B i I.cocomplex) r
    (evaluationComplexMap_zero B i I.cocomplex)
  have hS : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    by_cases hn : 0 ≤ n
    · let q := n.toNat
      have hq : (q : ℤ) = n := Int.toNat_of_nonneg hn
      let e₁ := (homComplex B i I.cocomplex).extendXIso ComplexShape.embeddingUpNat hq
      let e₂ := (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex
        (.up ℕ)).obj
        (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)).extendXIso
          ComplexShape.embeddingUpNat hq
      let e₃ := (((etaleSectionFunctor (Scheme.Etale.mk i.openComplement.ι)).mapHomologicalComplex
        (.up ℕ)).obj
        (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)).extendXIso
          ComplexShape.embeddingUpNat hq
      let e := ShortComplex.isoMk
        (S₁ := S.map (HomologicalComplex.eval _ (.up ℤ) n))
        (S₂ := ShortComplex.mk ((evaluationMap B i).app (I.cocomplex.X q))
          ((sectionRestrictionMap B i).app (I.cocomplex.X q))
          (evaluationMap_comp_restriction B i (I.cocomplex.X q))) e₁ e₂ e₃
        (by
          change e₁.hom ≫ (evaluationMap B i).app (I.cocomplex.X q) =
            (evaluationComplexMap B i I.cocomplex).f n ≫ e₂.hom
          unfold evaluationComplexMap
          rw [extendMap_f _ ComplexShape.embeddingUpNat (i := q) hq]
          change e₁.hom ≫ (evaluationMap B i).app (I.cocomplex.X q) =
            e₁.hom ≫ (evaluationMap B i).app (I.cocomplex.X q) ≫ e₂.inv ≫ e₂.hom
          simp only [Iso.inv_hom_id, Category.comp_id])
        (by
          change e₂.hom ≫ (sectionRestrictionMap B i).app (I.cocomplex.X q) = r.f n ≫ e₃.hom
          dsimp only [r, relativeSectionRestriction]
          rw [extendMap_f _ ComplexShape.embeddingUpNat (i := q) hq]
          simp only [e₂, e₃, Category.assoc, Iso.inv_hom_id, Category.comp_id]
          rfl)
      exact ShortComplex.shortExact_of_iso e.symm (evaluationMap_shortExact B i _)
    · have h₁ : IsZero (L.X n) :=
        (homComplex B i I.cocomplex).isZero_extend_X _ n (by
          rintro q hq
          change (q : ℤ) = n at hq
          omega)
      have h₂ : IsZero (A.X n) := by
        apply HomologicalComplex.isZero_extend_X
        rintro q hq
        change (q : ℤ) = n at hq
        omega
      have h₃ : IsZero (W.X n) := by
        apply HomologicalComplex.isZero_extend_X
        rintro q hq
        change (q : ℤ) = n at hq
        omega
      exact (show (S.map (HomologicalComplex.eval _ (.up ℤ) n)).Splitting from
        { r := 0
          s := 0
          f_r := h₁.eq_of_src _ _
          s_g := h₃.eq_of_src _ _
          id := h₂.eq_of_src _ _ }).shortExact
  exact CochainComplex.closedConeLift_quasiIso S hS

/-- The normalized cocycle formula for module-valued supported Hom.
Source: Stacks Tags 06XR and 095L, supported-Hom paragraph of lem-amb-cartier-kummer-map.
(blueprint: lem-pur-supported-hom-resolution-comparison). -/
def SupportedHomResolutionNormalization (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (I : InjectiveResolution F)
    (e : ∀ q : ℕ, Ext.{u + 1} ((lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))) F q ≃+
        (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
          (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj
            I.cocomplex)).homology (q : ℤ)) : Prop :=
  let J := ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let U := Scheme.Etale.mk i.openComplement.ι
  let C : CochainComplex AddCommGrpCat.{u + 1} ℤ := relativeSectionComplex T U J
  ∀ (q : ℕ)
    (k : (lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B)) ⟶
        I.cocomplex.X q) (hk : k ≫ I.cocomplex.d q (q + 1) = 0),
    ∃ z : C.cycles (q : ℤ),
      (relativeForgetComplex T U J).f q (C.iCycles q z) =
        (extendXIso
          (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj J)
          ComplexShape.embeddingUpNat (rfl : (q : ℤ) = q)).inv
            (((supportedConstantUnit B i) ≫ k).hom.app (op (Scheme.Etale.mk (𝟙 T)))
              ((toSheafify T.smallEtaleTopology
                ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of B B))).app
                  (op (Scheme.Etale.mk (𝟙 T))) (1 : B))) ∧
      (((CochainComplex.mappingCone (relativeSectionRestriction T U J)).shiftFunctorObjXIso
        (-1) (q : ℤ) ((q : ℤ) + -1) rfl).hom ≫
          homotopyCofiber.sndX (relativeSectionRestriction T U J) ((q : ℤ) + -1))
            (C.iCycles q z) = 0 ∧
      e q (InjectiveResolution.extMk.{u + 1, u + 1, u + 2} I k (q + 1) rfl hk) = C.homologyπ q z

set_option maxHeartbeats 1000000 in
-- The resolution and cone transports require substantial definitional elaboration.
/-- Evaluation and the kernel inclusion determine the supported Hom comparison uniquely.
Source: Stacks Tags 06XR and 095L; blueprint lem-amb-cartier-kummer-map, supported Hom.
(blueprint: lem-pur-supported-hom-resolution-comparison).

Proof: evaluate maps out of the closed constant sheaf at one. The normalized closed-support
Hom sequence identifies their image with the kernel of restriction and is short exact on
injectives. Apply it degreewise to the supplied resolution, extend by zero to negative
degrees, and include its kernel into the shifted restriction cone. This is a quasi-isomorphism
by the degreewise epimorphic kernel/cone theorem. Compute Ext on the Hom resolution and
apply homology of this map. Naturality of cycles and homology gives the displayed formula.
Every Ext class has a cocycle representative, and its two coordinates determine a cone
cycle uniquely; hence the formula determines the additive equivalences uniquely. -/
theorem supportedHomResolutionComparison_existsUnique (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (I : InjectiveResolution F) :
    ∃! e : ∀ q : ℕ, Ext.{u + 1} ((lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))) F q ≃+
        (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
          (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj
            I.cocomplex)).homology (q : ℤ),
      SupportedHomResolutionNormalization B i F I e := by
  classical
  let J := ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let U := Scheme.Etale.mk i.openComplement.ι
  let H := preadditiveCoyoneda.obj (op ((lowerStar (ModuleCat.{u + 1} B) i).obj
    ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj (ModuleCat.of B B))))
  obtain ⟨x, hx⟩ := exists_ext_rightDerived_cocycle_comparison _ H (Iso.refl _)
  let K := homComplex B i I.cocomplex
  let L := K.extend ComplexShape.embeddingUpNat
  let C : CochainComplex AddCommGrpCat.{u + 1} ℤ := relativeSectionComplex T U J
  let A := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj J
  let m : L ⟶ C := evaluationConeMap B i I.cocomplex
  have : QuasiIso m := evaluationConeMap_quasiIso B i F I
  let e (q : ℕ) :=
    (((x q).symm.app F ≪≫ I.isoRightDerivedObj H q ≪≫
      (K.extendHomologyIso ComplexShape.embeddingUpNat (j := q) rfl).symm) ≪≫
        asIso (homologyMap m (q : ℤ))).addCommGroupIsoToAddEquiv
  let fst (q : ℕ) := (relativeForgetComplex T U J).f (q : ℤ)
  let snd (q : ℕ) :=
    ((CochainComplex.mappingCone (relativeSectionRestriction T U J)).shiftFunctorObjXIso
      (-1) (q : ℤ) ((q : ℤ) - 1) (by omega)).hom ≫
        homotopyCofiber.sndX (relativeSectionRestriction T U J) ((q : ℤ) - 1)
  have hm₁ (q : ℕ) : m.f q ≫ fst q =
      (K.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        (evaluationMap B i).app (I.cocomplex.X q) ≫
          (A.extendXIso ComplexShape.embeddingUpNat rfl).inv := by
    dsimp only [fst]
    change m.f q ≫ (RelativeCone.projection (relativeSectionRestriction T U J)).f q = _
    rw [cone_projection_f]
    exact (CochainComplex.closedConeLift_projections _ _ _ (q : ℤ) ((q : ℤ) - 1)
      (by omega)).2.trans
        (extendMap_f _ ComplexShape.embeddingUpNat (i := q) rfl)
  have hm₂ (q : ℕ) : m.f q ≫ snd q = 0 :=
    (CochainComplex.closedConeLift_projections _ _ _ (q : ℤ) ((q : ℤ) - 1) (by omega)).1
  have hrep : SupportedHomResolutionNormalization B i F I e := by
    dsimp only [SupportedHomResolutionNormalization]
    intro q k hk
    have hz : K.d q (q + 1) k = 0 := hk
    let c : K.cycles q := K.cyclesMk k (q + 1) (by simp) hz
    have hc : K.iCycles q c = k := K.i_cyclesMk _ _ _ _
    let w : L.cycles (q : ℤ) := (K.extendCyclesIso ComplexShape.embeddingUpNat rfl).inv c
    have hw : L.iCycles q w = (K.extendXIso ComplexShape.embeddingUpNat rfl).inv k := by
      have h := ConcreteCategory.congr_hom
        (K.extendCyclesIso_inv_iCycles ComplexShape.embeddingUpNat (j := q) rfl) c
      simp only [ConcreteCategory.comp_apply, hc] at h
      exact h
    let z := cyclesMap m (q : ℤ) w
    have hzi : C.iCycles q z = m.f q (L.iCycles q w) :=
      ConcreteCategory.congr_hom (cyclesMap_i m (q : ℤ)) w
    refine ⟨z, ?_, ?_, ?_⟩
    · change fst q (C.iCycles q z) = _
      rw [hzi, ← ConcreteCategory.comp_apply, hm₁]
      change (A.extendXIso ComplexShape.embeddingUpNat rfl).inv
        ((evaluationMap B i).app (I.cocomplex.X q)
          ((K.extendXIso ComplexShape.embeddingUpNat rfl).hom (L.iCycles q w))) = _
      rw [hw, Iso.inv_hom_id_apply]
      change (A.extendXIso ComplexShape.embeddingUpNat rfl).inv
        (sectionOneEquiv B T (I.cocomplex.X q) (supportedConstantUnit B i ≫ k)) = _
      rw [sectionOneEquiv_apply]
      rfl
    · change snd q (C.iCycles q z) = 0
      rw [hzi]
      exact ConcreteCategory.congr_hom (hm₂ q) (L.iCycles q w)
    · change homologyMap m (q : ℤ)
        ((K.extendHomologyIso ComplexShape.embeddingUpNat rfl).inv
          ((I.isoRightDerivedObj H q).hom ((x q).inv.app F
            (InjectiveResolution.extMk.{u + 1, u + 1, u + 2} I k (q + 1) rfl hk)))) = _
      rw [hx F I q k hk c hc]
      have hp := ConcreteCategory.congr_hom
        (K.homologyπ_extendHomologyIso_inv ComplexShape.embeddingUpNat (j := q) rfl) c
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hp
      rw [hp]
      exact ConcreteCategory.congr_hom (homologyπ_naturality m (q : ℤ)) w
  refine ⟨e, hrep, ?_⟩
  intro e' he'
  funext q
  apply AddEquiv.ext
  intro y
  obtain ⟨k, hk, rfl⟩ := I.extMk_surjective y (q + 1) rfl
  obtain ⟨z, hz₁, hz₂, hz₃⟩ := hrep q k hk
  obtain ⟨z', hz₁', hz₂', hz₃'⟩ := he' q k hk
  have hez : z' = z := by
    apply (AddCommGrpCat.mono_iff_injective (C.iCycles (q : ℤ))).mp inferInstance
    apply cone_element_ext (relativeSectionRestriction T U J) (q : ℤ)
    · exact hz₁'.trans hz₁.symm
    · exact hz₂'.trans hz₂.symm
  exact hz₃'.trans ((congrArg (C.homologyπ q) hez).trans hz₃.symm)

/-- The comparison fixed by evaluation on every cocycle.
Source: Stacks Tag 06XR (blueprint: lem-pur-supported-hom-resolution-comparison). -/
def supportedHomResolutionComparison (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (I : InjectiveResolution F) (q : ℕ) :=
  Classical.choose (supportedHomResolutionComparison_existsUnique B i F I) q

/-- The chosen comparison has the normalization that uniquely determines it.
Source: Stacks Tag 06XR (blueprint: lem-pur-supported-hom-resolution-comparison). -/
theorem supportedHomResolutionComparison_normalized (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (I : InjectiveResolution F) :
    SupportedHomResolutionNormalization B i F I (supportedHomResolutionComparison B i F I) :=
  (Classical.choose_spec (supportedHomResolutionComparison_existsUnique B i F I)).1

private abbrev homComplexMap (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ}
    (a : I ⟶ J) :=
  extendMap (((preadditiveCoyoneda.obj (op ((lowerStar (ModuleCat.{u + 1} B) i).obj
    ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
      (ModuleCat.of B B))))).mapHomologicalComplex (.up ℕ)).map a)
        ComplexShape.embeddingUpNat

private lemma homComplexMap_apply (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ}
    (a : I ⟶ J) (q : ℕ)
    (k : (lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B B)) ⟶ I.X q) :
    (homComplexMap B i a).f (q : ℤ)
      (((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).inv k) =
    ((homComplex B i J).extendXIso ComplexShape.embeddingUpNat rfl).inv (k ≫ a.f q) := by
  let H := preadditiveCoyoneda.obj (op ((lowerStar (ModuleCat.{u + 1} B) i).obj
    ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
      (ModuleCat.of B B))))
  have he := ConcreteCategory.congr_hom
    (extendMap_f ((H.mapHomologicalComplex (.up ℕ)).map a)
      ComplexShape.embeddingUpNat (i := q) rfl)
    (((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).inv k)
  change (homComplexMap B i a).f (q : ℤ)
      (((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).inv k) =
    ((homComplex B i J).extendXIso ComplexShape.embeddingUpNat rfl).inv
      (H.map (a.f q)
        (((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).hom
          (((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).inv k))) at he
  rw [Iso.inv_hom_id_apply] at he
  exact he

private lemma homComplex_d_apply (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (q : ℕ)
    (k : (lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B B)) ⟶ I.X q) :
    ((homComplex B i I).extend ComplexShape.embeddingUpNat).d
      (q : ℤ) ((q + 1 : ℕ) : ℤ)
        (((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).inv k) =
    ((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).inv
      (k ≫ I.d q (q + 1)) := by
  have he := ConcreteCategory.congr_hom
    ((homComplex B i I).extend_d_eq ComplexShape.embeddingUpNat
      (i := q) (j := q + 1) rfl rfl)
    (((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).inv k)
  change ((homComplex B i I).extend ComplexShape.embeddingUpNat).d
      (q : ℤ) ((q + 1 : ℕ) : ℤ)
        (((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).inv k) =
    ((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).inv
      ((homComplex B i I).d q (q + 1)
        (((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).hom
          (((homComplex B i I).extendXIso ComplexShape.embeddingUpNat rfl).inv k))) at he
  rw [Iso.inv_hom_id_apply] at he
  exact he

private lemma coneMap_eq (A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ)
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) :
    homotopyCofiber.mapArrowHom r r' (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
      (Arrow.homMk a b h) = CochainComplex.mappingCone.map r r' a b h.symm := by
  ext n : 1
  apply homotopyCofiber.ext_from_X r (n + 1) n rfl
  · conv_lhs =>
      simp [homotopyCofiber.mapArrowHom, homotopyCofiber.inrCompHomotopy_hom]
    change a.f (n + 1) ≫ (CochainComplex.mappingCone.inl r').v (n + 1) n (by omega) =
      (CochainComplex.mappingCone.inl r).v (n + 1) n (by omega) ≫
        (CochainComplex.mappingCone.map r r' a b h.symm).f n
    simp [CochainComplex.mappingCone.map,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
  · conv_lhs =>
      simp [homotopyCofiber.mapArrowHom, homotopyCofiber.inrCompHomotopy_hom]
    change b.f n ≫ (CochainComplex.mappingCone.inr r').f n =
      (CochainComplex.mappingCone.inr r).f n ≫
        (CochainComplex.mappingCone.map r r' a b h.symm).f n
    simp [CochainComplex.mappingCone.map]

private lemma evaluationConeMap_naturality (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    {I J : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ}
    (a : I ⟶ J) :
    homComplexMap B i a ≫ evaluationConeMap B i J = evaluationConeMap B i I ≫
      relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι)
        (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).map a) := by
  unfold evaluationConeMap relativeSectionMap relativeFiberMap
  rw [coneMap_eq]
  apply CochainComplex.closedConeLift_naturality
  · dsimp only [homComplexMap, evaluationComplexMap]
    rw [← extendMap_comp, ← extendMap_comp]
    congr 1
  · exact relativeSectionMap_square T (Scheme.Etale.mk i.openComplement.ι)
      (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).map a)

private lemma comparison_on_cycle (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (I : InjectiveResolution F)
    (q : ℕ) (k : (lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B B)) ⟶ I.cocomplex.X q)
    (hk : k ≫ I.cocomplex.d q (q + 1) = 0)
    (w : ((homComplex B i I.cocomplex).extend ComplexShape.embeddingUpNat).cycles (q : ℤ))
    (hw : ((homComplex B i I.cocomplex).extend ComplexShape.embeddingUpNat).iCycles q w =
      ((homComplex B i I.cocomplex).extendXIso ComplexShape.embeddingUpNat rfl).inv k) :
    supportedHomResolutionComparison B i F I q
        (InjectiveResolution.extMk.{u + 1, u + 1, u + 2} I k (q + 1) rfl hk) =
      (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)).homologyπ q
          (cyclesMap (evaluationConeMap B i I.cocomplex) (q : ℤ) w) := by
  let J := ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let U := Scheme.Etale.mk i.openComplement.ι
  let K := homComplex B i I.cocomplex
  let L := K.extend ComplexShape.embeddingUpNat
  let C := relativeSectionComplex T U J
  let A := ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj J
  let m := evaluationConeMap B i I.cocomplex
  let z := cyclesMap m (q : ℤ) w
  obtain ⟨z', hz₁, hz₂, hz₃⟩ := supportedHomResolutionComparison_normalized B i F I q k hk
  have hzi : C.iCycles q z = m.f q (L.iCycles q w) :=
    ConcreteCategory.congr_hom (cyclesMap_i m (q : ℤ)) w
  have he : z' = z := by
    apply (AddCommGrpCat.mono_iff_injective (C.iCycles (q : ℤ))).mp inferInstance
    apply cone_element_ext (relativeSectionRestriction T U J) (q : ℤ)
    · change (relativeForgetComplex T U J).f q (C.iCycles q z') =
        (relativeForgetComplex T U J).f q (C.iCycles q z)
      rw [hz₁, hzi, ← ConcreteCategory.comp_apply]
      have hm : m.f q ≫ (relativeForgetComplex T U J).f q =
          (K.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
            (evaluationMap B i).app (I.cocomplex.X q) ≫
              (A.extendXIso ComplexShape.embeddingUpNat rfl).inv := by
        change m.f q ≫ (RelativeCone.projection (relativeSectionRestriction T U J)).f q = _
        rw [cone_projection_f]
        exact (CochainComplex.closedConeLift_projections _ _ _ (q : ℤ) ((q : ℤ) - 1)
          (by omega)).2.trans (extendMap_f _ ComplexShape.embeddingUpNat (i := q) rfl)
      rw [hm]
      change _ = (A.extendXIso ComplexShape.embeddingUpNat rfl).inv
        ((evaluationMap B i).app (I.cocomplex.X q)
          ((K.extendXIso ComplexShape.embeddingUpNat rfl).hom (L.iCycles q w)))
      rw [hw, Iso.inv_hom_id_apply]
      exact congrArg (A.extendXIso ComplexShape.embeddingUpNat rfl).inv
        (sectionOneEquiv_apply B T (I.cocomplex.X q) (supportedConstantUnit B i ≫ k)).symm
    · have hm := (CochainComplex.closedConeLift_projections
        (relativeSectionRestriction T U J) (evaluationComplexMap B i I.cocomplex)
          (evaluationComplexMap_zero B i I.cocomplex) (q : ℤ) ((q : ℤ) - 1) (by omega)).1
      calc
        _ = 0 := hz₂
        _ = _ := (ConcreteCategory.congr_hom hm (L.iCycles q w)).symm.trans
          (by rw [hzi]; rfl)
  exact hz₃.trans (congrArg (C.homologyπ q) he)

set_option maxHeartbeats 1000000 in
-- The resolution and cone transports require substantial definitional elaboration.
/-- Evaluation on supported Hom preserves the positive coefficient boundary.
Source: Stacks Tags 05TE, 06XR and 013T; the coefficient-boundary step of
lem-amb-cartier-kummer-map (blueprint: lem-pur-supported-hom-resolution-comparison).
Proof: lift a Hom cocycle along the split injective-resolution row and factor its
 differential through the first term. The Ext resolution boundary theorem identifies
 its class with positive Yoneda composition. The evaluation cone map is a chain map
 natural in the resolution, so the same lift and differential compute the relative
 boundary. Its two coordinates give exactly the normalized comparison cycles. -/
theorem supportedHomResolutionComparison_connecting (B : Type (u + 1)) [CommRing B]
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (S : ShortComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₂ : InjectiveResolution S.X₂) (I₃ : InjectiveResolution S.X₃)
    (a : I₁.cocomplex ⟶ I₂.cocomplex) (b : I₂.cocomplex ⟶ I₃.cocomplex)
    (hab : a ≫ b = 0)
    (ha : I₁.ι ≫ a = (CochainComplex.single₀ _).map S.f ≫ I₂.ι)
    (hb : I₂.ι ≫ b = (CochainComplex.single₀ _).map S.g ≫ I₃.ι)
    (hs : ∀ n : ℕ, Nonempty
      ((((ShortComplex.mk a b hab).map
        ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ))).map
          (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (q : ℕ) (x : Ext.{u + 1} ((lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B B))) S.X₃ q) :
    supportedHomResolutionComparison B i S.X₁ I₁ (q + 1)
      (Ext.comp.{u + 1} x (ShortComplex.ShortExact.extClass.{u + 1} hS) rfl) =
      relativeConnecting T (Scheme.Etale.mk i.openComplement.ι)
        ((ShortComplex.mk a b hab).map
          ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ))) hs (q : ℤ)
        (supportedHomResolutionComparison B i S.X₃ I₃ q x) := by
  classical
  let R := ShortComplex.mk a b hab
  have hr (n : ℕ) : (R.map (HomologicalComplex.eval _ (.up ℕ) n)).ShortExact := by
    apply ShortExact.reflects_shortExact_of_faithful (moduleAbelianForget B T)
    exact (hs n).some.shortExact
  obtain ⟨k, hk, rfl⟩ := I₃.extMk_surjective x (q + 1) rfl
  have : Injective (R.map (HomologicalComplex.eval _ (.up ℕ) q)).X₁ := by
    change Injective (I₁.cocomplex.X q)
    infer_instance
  let sp := (hr q).splittingOfInjective
  let g : (lowerStar (ModuleCat.{u + 1} B) i).obj
      ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B B)) ⟶ I₂.cocomplex.X q := k ≫ sp.s
  have hg : g ≫ b.f q = k := by
    change k ≫ sp.s ≫ (R.map (HomologicalComplex.eval _ (.up ℕ) q)).g = k
    rw [sp.s_g]
    change k ≫ 𝟙 _ = k
    exact Category.comp_id k
  have hgz : (g ≫ I₂.cocomplex.d q (q + 1)) ≫ b.f (q + 1) = 0 := by
    rw [Category.assoc, ← b.comm, ← Category.assoc, hg, hk]
  obtain ⟨h, hh⟩ := KernelFork.IsLimit.lift' (hr (q + 1)).fIsKernel
    (g ≫ I₂.cocomplex.d q (q + 1)) hgz
  change (lowerStar (ModuleCat.{u + 1} B) i).obj
    ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
      (ModuleCat.of B B)) ⟶ I₁.cocomplex.X (q + 1) at h
  have hh' : h ≫ a.f (q + 1) = g ≫ I₂.cocomplex.d q (q + 1) := hh
  have hhclosed : h ≫ I₁.cocomplex.d (q + 1) (q + 1 + 1) = 0 := by
    have : Mono (a.f (q + 1 + 1)) := (hr (q + 1 + 1)).mono_f
    rw [← cancel_mono (a.f (q + 1 + 1)), zero_comp,
      Category.assoc, ← a.comm, ← Category.assoc, hh', Category.assoc, d_comp_d, comp_zero]
  have hext :
      (InjectiveResolution.extMk.{u + 1, u + 1, u + 2} I₃ k (q + 1) rfl hk).comp
          (ShortComplex.ShortExact.extClass.{u + 1} hS) rfl =
      InjectiveResolution.extMk.{u + 1, u + 1, u + 2} I₁ h (q + 1 + 1) rfl hhclosed := by
    let := HasDerivedCategory.standard
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    apply Ext.ext
    have hd := InjectiveResolution.extMk_resolution_connecting_eq_triangle.{u + 1, u + 2}
      hS _ I₁ I₂ I₃ a b hab ha hb hr q k hk g hg h hhclosed hh'.symm
    rw [Ext.preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply.{u + 2, u + 2,
      u + 1, u + 2} hS _ rfl] at hd
    simpa only [Ext.comp_hom, ShortComplex.ShortExact.extClass_hom,
      InjectiveResolution.extMk_hom] using hd
  rw [hext]
  let U := Scheme.Etale.mk i.openComplement.ι
  let K₁ := homComplex B i I₁.cocomplex
  let K₂ := homComplex B i I₂.cocomplex
  let K₃ := homComplex B i I₃.cocomplex
  let L₁ := K₁.extend ComplexShape.embeddingUpNat
  let L₂ := K₂.extend ComplexShape.embeddingUpNat
  let L₃ := K₃.extend ComplexShape.embeddingUpNat
  let m₁ := evaluationConeMap B i I₁.cocomplex
  let m₂ := evaluationConeMap B i I₂.cocomplex
  let m₃ := evaluationConeMap B i I₃.cocomplex
  let wc : L₃.cycles (q : ℤ) := (K₃.extendCyclesIso ComplexShape.embeddingUpNat rfl).inv
    (K₃.cyclesMk k (q + 1) (by simp) hk)
  let wa : L₁.cycles ((q + 1 : ℕ) : ℤ) := (K₁.extendCyclesIso ComplexShape.embeddingUpNat rfl).inv
    (K₁.cyclesMk h (q + 1 + 1) (by simp) hhclosed)
  have hwc : L₃.iCycles (q : ℤ) wc =
      (K₃.extendXIso ComplexShape.embeddingUpNat rfl).inv k := by
    have he := ConcreteCategory.congr_hom
      (K₃.extendCyclesIso_inv_iCycles ComplexShape.embeddingUpNat (rfl : (q : ℤ) = q))
      (K₃.cyclesMk k (q + 1) (by simp) hk)
    exact he.trans (congrArg (K₃.extendXIso ComplexShape.embeddingUpNat rfl).inv
      (K₃.i_cyclesMk k (q + 1) (by simp) hk))
  have hwa : L₁.iCycles ((q + 1 : ℕ) : ℤ) wa =
      (K₁.extendXIso ComplexShape.embeddingUpNat rfl).inv h := by
    have he := ConcreteCategory.congr_hom
      (K₁.extendCyclesIso_inv_iCycles ComplexShape.embeddingUpNat
        (rfl : ((q + 1 : ℕ) : ℤ) = ↑(q + 1)))
      (K₁.cyclesMk h (q + 1 + 1) (by simp) hhclosed)
    exact he.trans (congrArg (K₁.extendXIso ComplexShape.embeddingUpNat rfl).inv
      (K₁.i_cyclesMk h (q + 1 + 1) (by simp) hhclosed))
  rw [comparison_on_cycle B i S.X₁ I₁ (q + 1) h hhclosed wa hwa,
    comparison_on_cycle B i S.X₃ I₃ q k hk wc hwc]
  let zc : (relativeSectionComplex T U
      (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I₃.cocomplex)).cycles
        (q : ℤ) := cyclesMap m₃ (q : ℤ) wc
  let za : (relativeSectionComplex T U
      (((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ)).obj I₁.cocomplex)).cycles
        ((q + 1 : ℕ) : ℤ) := cyclesMap m₁ ((q + 1 : ℕ) : ℤ) wa
  let R' := R.map ((moduleAbelianForget B T).mapHomologicalComplex (.up ℕ))
  let C := relativeShortComplex T U R'
  let v := m₂.f q ((K₂.extendXIso ComplexShape.embeddingUpNat rfl).inv g)
  have hc : C.X₃.iCycles (q : ℤ) zc =
      m₃.f q ((K₃.extendXIso ComplexShape.embeddingUpNat rfl).inv k) := by
    dsimp only [C, relativeShortComplex, R', R, ShortComplex.map, zc]
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply, hwc]
  have hz : C.X₁.iCycles ((q + 1 : ℕ) : ℤ) za =
      m₁.f ((q + 1 : ℕ) : ℤ) ((K₁.extendXIso ComplexShape.embeddingUpNat rfl).inv h) := by
    dsimp only [C, relativeShortComplex, R', R, ShortComplex.map, za]
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply, hwa]
  have hv : C.g.f q v = C.X₃.iCycles q zc := by
    rw [hc]
    have hn := ConcreteCategory.congr_hom
      (congrArg (fun φ ↦ φ.f (q : ℤ)) (evaluationConeMap_naturality B i b))
      ((K₂.extendXIso ComplexShape.embeddingUpNat rfl).inv g)
    have hv₁ : C.g.f q v =
        m₃.f q ((homComplexMap B i b).f q
          ((K₂.extendXIso ComplexShape.embeddingUpNat rfl).inv g)) := hn.symm
    rw [hv₁]
    exact (congrArg (m₃.f q) (homComplexMap_apply B i b q g)).trans
      (congrArg (fun k ↦ m₃.f q ((K₃.extendXIso _ rfl).inv k)) hg)
  have hvd : C.f.f ((q + 1 : ℕ) : ℤ) (C.X₁.iCycles ((q + 1 : ℕ) : ℤ) za) =
      C.X₂.d (q : ℤ) ((q + 1 : ℕ) : ℤ) v := by
    rw [hz]
    have hn := ConcreteCategory.congr_hom
      (congrArg (fun φ ↦ φ.f ((q + 1 : ℕ) : ℤ))
        (evaluationConeMap_naturality B i a))
      ((K₁.extendXIso ComplexShape.embeddingUpNat rfl).inv h)
    have hv₁ : C.f.f ((q + 1 : ℕ) : ℤ)
        (m₁.f ((q + 1 : ℕ) : ℤ) ((K₁.extendXIso ComplexShape.embeddingUpNat rfl).inv h)) =
      m₂.f ((q + 1 : ℕ) : ℤ) ((homComplexMap B i a).f ((q + 1 : ℕ) : ℤ)
        ((K₁.extendXIso ComplexShape.embeddingUpNat rfl).inv h)) := by
      exact hn.symm
    rw [hv₁]
    have hd := ConcreteCategory.congr_hom
      (m₂.comm (q : ℤ) ((q + 1 : ℕ) : ℤ))
        ((K₂.extendXIso ComplexShape.embeddingUpNat rfl).inv g)
    refine Eq.trans ?_ hd.symm
    apply congrArg (m₂.f ((q + 1 : ℕ) : ℤ))
    exact (homComplexMap_apply B i a (q + 1) h).trans
      ((congrArg (K₂.extendXIso ComplexShape.embeddingUpNat rfl).inv hh').trans
        (homComplex_d_apply B i I₂.cocomplex q g).symm)
  have hδ := (relativeShortComplex_shortExact T U R' hs).δ_apply
    (q : ℤ) ((q + 1 : ℕ) : ℤ) (by change (q : ℤ) + 1 = ↑(q + 1); omega)
    (C.X₃.iCycles q zc) (by
      exact ConcreteCategory.congr_hom (C.X₃.iCycles_d (q : ℤ) ((q + 1 : ℕ) : ℤ)) zc)
    v hv (C.X₁.iCycles ((q + 1 : ℕ) : ℤ) za) hvd
    (((q + 1 : ℕ) : ℤ) + 1) (by simp)
  have hzc : C.X₃.cyclesMk (C.X₃.iCycles q zc) ((q + 1 : ℕ) : ℤ)
      (by simp)
      (ConcreteCategory.congr_hom (C.X₃.iCycles_d (q : ℤ) ((q + 1 : ℕ) : ℤ)) zc) = zc := by
    apply (AddCommGrpCat.mono_iff_injective (C.X₃.iCycles (q : ℤ))).mp inferInstance
    exact C.X₃.i_cyclesMk _ _ _ _
  have hza : C.X₁.cyclesMk (C.X₁.iCycles ((q + 1 : ℕ) : ℤ) za) (((q + 1 : ℕ) : ℤ) + 1)
      (by simp)
      (ConcreteCategory.congr_hom
        (C.X₁.iCycles_d ((q + 1 : ℕ) : ℤ) (((q + 1 : ℕ) : ℤ) + 1)) za) = za := by
    apply (AddCommGrpCat.mono_iff_injective (C.X₁.iCycles ((q + 1 : ℕ) : ℤ))).mp
      inferInstance
    exact C.X₁.i_cyclesMk _ _ _ _
  rw [hzc, hza] at hδ
  change C.X₁.homologyπ ((q + 1 : ℕ) : ℤ) za =
    (relativeShortComplex_shortExact T U R' hs).δ
      (q : ℤ) ((q + 1 : ℕ) : ℤ) (by change (q : ℤ) + 1 = ↑(q + 1); omega)
      (C.X₃.homologyπ q zc)
  exact hδ.symm

end AlgebraicGeometry.Etale
