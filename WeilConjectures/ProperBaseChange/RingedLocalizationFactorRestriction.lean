/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.LocalizationRHom.RingedLocalizationRestrictionSupplement

/-! # Restriction of one augmented localization factor

Source: Stacks Project, sites-cohomology.tex, Tag 08JB; algebraization.tex, Tag 0996.
(blueprint: lem-weil-pbc-ringed-localization-factor-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

section ModuleRestriction
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F J K] [F.IsCocontinuous J K]
  (O : Sheaf K CommRingCat.{u})
private abbrev R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj O
private abbrev P := (F.sheafPushforwardContinuous CommRingCat J K).obj O
private def unitIso :
    (SheafOfModules.sliceModuleRestriction (J := J) F (R O)).obj
        (SheafOfModules.unit (R O)) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (P (J := J) F O)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intro X Y a; ext; rfl))

private def locIso (s : (O.obj ⋙ forget CommRingCat).sections) :
    (SheafOfModules.sliceModuleRestriction (J := J) F (R O)).obj
        (ringedSectionLocalization O s) ≅
      ringedSectionLocalization (P (J := J) F O)
        (LocalizationRHom.restrictedSection (K := J) F O s) :=
  (SheafOfModules.sliceSheafificationIso (J := J) F (R O)).app
      (ringedSectionLocalizationPresheaf O s) ≪≫
    (PresheafOfModules.sheafification (𝟙 ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj (P (J := J) F O)).obj)).mapIso
        (LocalizationRHom.restrictionPresheafIso (K := J) F O s)

private def preUnit (s : (O.obj ⋙ forget CommRingCat).sections) :
    PresheafOfModules.unit (R O).obj ⟶ ringedSectionLocalizationPresheaf O s :=
  (ringedSectionLocalizationPresheaf O s).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun X ↦ (1 : ringedSectionLocalizationCarrier O s X))
      (fun {_ _} a ↦ ringedSectionLocalizationPresheaf_one_natural O s a))

private lemma forget_unit (s : (O.obj ⋙ forget CommRingCat).sections) :
    (SheafOfModules.forget (R O)).map (ringedSectionLocalizationUnit O s) =
      preUnit O s ≫ (PresheafOfModules.sheafificationAdjunction (𝟙 (R O).obj)).unit.app
        (ringedSectionLocalizationPresheaf O s) :=
  (SheafOfModules.fullyFaithfulForget _).map_preimage _

private lemma unit_square (s : (O.obj ⋙ forget CommRingCat).sections) :
    (SheafOfModules.sliceModuleRestriction (J := J) F (R O)).map
        (ringedSectionLocalizationUnit O s) ≫ (locIso F O s).hom =
      (unitIso F O).hom ≫ ringedSectionLocalizationUnit (P (J := J) F O)
        (LocalizationRHom.restrictedSection (K := J) F O s) := by
  let PP := SheafOfModules.slicePresheafRestriction (J := J) F (R O)
  let V := SheafOfModules.sliceModuleRestriction (J := J) F (R O)
  let O' := (sheafCompose J (forget₂ CommRingCat RingCat)).obj (P (J := J) F O)
  let T := PresheafOfModules.sheafification (𝟙 O'.obj)
  let a := PresheafOfModules.sheafificationAdjunction (𝟙 (R O).obj)
  let a' := PresheafOfModules.sheafificationAdjunction (𝟙 O'.obj)
  let M := ringedSectionLocalizationPresheaf O s
  let M' := ringedSectionLocalizationPresheaf (P (J := J) F O)
    (LocalizationRHom.restrictedSection (K := J) F O s)
  let e := LocalizationRHom.restrictionPresheafIso (K := J) F O s
  let c := (SheafOfModules.sliceSheafificationComparison (J := J) F (R O)).app M
  have hc : a'.unit.app (PP.obj M) ≫ (SheafOfModules.forget O').map c =
      PP.map (a.unit.app M) := by
    apply (PresheafOfModules.toPresheaf O'.obj).map_injective
    have h := (a'.homEquiv _ _).apply_symm_apply
      (show PP.obj M ⟶ (SheafOfModules.forget O' ⋙
        PresheafOfModules.restrictScalars (𝟙 O'.obj)).obj (V.obj
          ((PresheafOfModules.sheafification (𝟙 (R O).obj)).obj M))
        from PP.map (a.unit.app M))
    exact congrArg ((PresheafOfModules.toPresheaf O'.obj).map) h
  have hpre : PP.map (preUnit O s) =
      (SheafOfModules.forget O').map (unitIso F O).hom ≫
        preUnit (P (J := J) F O)
          (LocalizationRHom.restrictedSection (K := J) F O s) ≫ e.inv := by
    ext W
    rfl
  apply (cancel_mono (locIso F O s).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (SheafOfModules.forget O').map_injective
  change PP.map ((SheafOfModules.forget (R O)).map (ringedSectionLocalizationUnit O s)) =
    (SheafOfModules.forget O').map
      ((unitIso F O).hom ≫ ringedSectionLocalizationUnit (P (J := J) F O)
        (LocalizationRHom.restrictedSection (K := J) F O s) ≫
        T.map e.inv ≫ c)
  rw [forget_unit, Functor.map_comp, hpre]
  simp only [Functor.map_comp, Category.assoc]
  have hu : (SheafOfModules.forget O').map
      (ringedSectionLocalizationUnit (P (J := J) F O)
        (LocalizationRHom.restrictedSection (K := J) F O s)) =
      preUnit (P (J := J) F O)
        (LocalizationRHom.restrictedSection (K := J) F O s) ≫ a'.unit.app M' :=
    forget_unit _ _
  rw [hu]
  simp only [Category.assoc]
  have hn := a'.unit.naturality e.inv
  change e.inv ≫ a'.unit.app (PP.obj M) =
    a'.unit.app M' ≫ (SheafOfModules.forget O').map (T.map e.inv) at hn
  have hx : e.inv ≫ PP.map (a.unit.app M) =
      a'.unit.app M' ≫ (SheafOfModules.forget O').map (T.map e.inv) ≫
        (SheafOfModules.forget O').map c := by
    rw [← hc, ← Category.assoc, hn, Category.assoc]
  exact congrArg (fun z ↦ (SheafOfModules.forget O').map (unitIso F O).hom ≫
    preUnit (P (J := J) F O)
      (LocalizationRHom.restrictedSection (K := J) F O s) ≫ z) hx
end ModuleRestriction

section ComplexRestriction
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (O : Sheaf K CommRingCat.{u}) (P : Sheaf J CommRingCat.{u})
  (V : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj O) ⥤
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj P)) [V.Additive]
  (s : (O.obj ⋙ forget CommRingCat).sections)
  (t : (P.obj ⋙ forget CommRingCat).sections)
  (h : Arrow.mk (V.map (ringedSectionLocalizationUnit O s)) ≅
    Arrow.mk (ringedSectionLocalizationUnit P t))

private def component (n : ℤ) :
    V.obj (ringedLocalizationTwoTermX O s n) ≅ ringedLocalizationTwoTermX P t n := by
  by_cases h0 : n = 0
  · subst n
    simpa only [ringedLocalizationTwoTermX, if_pos] using (show V.obj (SheafOfModules.unit
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj O)) ≅ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj P) from Arrow.leftFunc.mapIso h)
  · by_cases h1 : n = 1
    · subst n
      simpa only [ringedLocalizationTwoTermX, if_neg (show (1 : ℤ) ≠ 0 by decide), if_pos]
        using (show V.obj (ringedSectionLocalization O s) ≅
          ringedSectionLocalization P t from Arrow.rightFunc.mapIso h)
    · simpa only [ringedLocalizationTwoTermX, if_neg h0, if_neg h1]
        using V.mapZeroObject

private def complexIso :
    (V.mapHomologicalComplex (.up ℤ)).obj (ringedLocalizationTwoTerm O s) ≅
      ringedLocalizationTwoTerm P t := by
  refine HomologicalComplex.Hom.isoOfComponents (component O P V s t h) ?_
  intro n m hnm
  have hm : n + 1 = m := hnm
  subst m
  change (component O P V s t h n).hom ≫
      CochainComplex.of.d _ _ n (n + 1) =
    V.map (CochainComplex.of.d _ _ n (n + 1)) ≫
      (component O P V s t h (n + 1)).hom
  rw [CochainComplex.of_d, CochainComplex.of_d]
  by_cases hn : n = 0
  · subst n
    simp [component, ringedLocalizationTwoTermD]
  · simp [ringedLocalizationTwoTermD, hn]

private def ringIso :
    (V.mapHomologicalComplex (.up ℤ)).obj (ringedSiteRingComplex O) ≅
      ringedSiteRingComplex P :=
  (HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).app _ ≪≫
    (HomologicalComplex.single _ (.up ℤ) 0).mapIso (Arrow.leftFunc.mapIso h)

private def factorArrow :
    Arrow.mk ((V.mapHomologicalComplex (.up ℤ)).map
      (ringedLocalizationTwoTermAugmentation O s)) ≅
      Arrow.mk (ringedLocalizationTwoTermAugmentation P t) := by
  refine Arrow.isoMk (complexIso O P V s t h) (ringIso O P V s t h) ?_
  apply HomologicalComplex.hom_ext
  intro n
  symm
  change V.map ((ringedLocalizationTwoTermAugmentation O s).f n) ≫
      (ringIso O P V s t h).hom.f n =
    (complexIso O P V s t h).hom.f n ≫
      (ringedLocalizationTwoTermAugmentation P t).f n
  by_cases hn : n = 0
  · subst n
    simp only [ringedLocalizationTwoTermAugmentation, ringedLocalizationTwoTermAugmentationF,
      ↓reduceDIte, eqToHom_refl, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl, Iso.refl_inv, Category.comp_id,
      Category.id_comp, ringIso, Functor.comp_obj, HomologicalComplex.singleMapHomologicalComplex,
      NatIso.ofComponents.app, Iso.trans_hom, Functor.mapIso_hom, Arrow.leftFunc_map,
      HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self, Iso.refl_hom,
      complexIso, HomologicalComplex.Hom.isoOfComponents_hom_f, component, eq_mpr_eq_cast,
      cast_eq]
    change V.map (𝟙 (SheafOfModules.unit
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj O))) ≫ h.hom.left ≫ 𝟙 _ =
        h.hom.left ≫ 𝟙 _
    simp
  · simp [ringedLocalizationTwoTermAugmentation, ringedLocalizationTwoTermAugmentationF, hn]
end ComplexRestriction

section GenericFactor
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F J K] [F.IsCocontinuous J K]
  (O : Sheaf K CommRingCat.{u})

private instance restriction_additive :
    (SheafOfModules.sliceModuleRestriction (J := J) F (R O)).Additive := by
  constructor
  intro M N f g
  ext W x
  rfl

private theorem genericFactorRestriction (s : (O.obj ⋙ forget CommRingCat).sections) :
    Nonempty (Arrow.mk
      (((SheafOfModules.sliceModuleRestriction (J := J) F (R O)).mapHomologicalComplex
        (.up ℤ)).map (ringedLocalizationTwoTermAugmentation O s)) ≅
      Arrow.mk (ringedLocalizationTwoTermAugmentation (P (J := J) F O)
        (LocalizationRHom.restrictedSection (K := J) F O s))) := by
  let V := SheafOfModules.sliceModuleRestriction (J := J) F (R O)
  have : V.Additive := restriction_additive F O
  let t := LocalizationRHom.restrictedSection (K := J) F O s
  let h : Arrow.mk (V.map (ringedSectionLocalizationUnit O s)) ≅
      Arrow.mk (ringedSectionLocalizationUnit (P (J := J) F O) t) :=
    Arrow.isoMk (unitIso F O) (locIso F O s) (unit_square F O s).symm
  exact ⟨factorArrow O (P (J := J) F O) V s t h⟩
end GenericFactor

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

end CategoryTheory
