/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.RingedExtendedCech
public import Sheaf.CategoryTheory.RingedCompletionUnit
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.CategoryTheory.RingedKoszulSystem
import Sheaf.Paper.ExtendedCechCompletionModel
import Sheaf.Paper.RingedLocalizationRestriction

/-!
# Derived completeness under a unit times a positive power

Source: Stacks Project, algebraization.tex, Tags 099B, 099E and 099F
(blueprint: lem-pur-unit-power-completeness).

The principal ideal sheaf is the categorical image of multiplication by its generator.
Thus its sections include locally divisible sections, without requiring a global coefficient.
The comparison uses the actual two-term complexes and their augmentation-induced units.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace CategoryTheory

-- Cache this site-independent proof instead of repeating the general limit-preservation
-- instance search at every occurrence of the underlying ring sheaf.
private theorem unitPower_hasSheafCompose
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance

attribute [local instance] unitPower_hasSheafCompose

private abbrev sectionValue
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) : O.obj.obj X := s.val X

private def localizationMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (a b : (O.obj ⋙ forget CommRingCat).sections)
    (h : ∀ X : Cᵒᵖ, IsUnit
      (algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O b X) (sectionValue O a X))) :
    ringedSectionLocalizationPresheaf O a ⟶ ringedSectionLocalizationPresheaf O b where
  app X := ModuleCat.ofHom
    { toFun := IsLocalization.Away.lift (sectionValue O a X) (h X)
      map_add' := map_add _
      map_smul' := by
        intro r x
        simp only [Algebra.smul_def, map_mul, IsLocalization.Away.lift_eq, RingHom.id_apply] }
  naturality {X Y} f := by
    have hnat :
        (ringedSectionLocalizationMap O b f).comp
          (IsLocalization.Away.lift (sectionValue O a X) (h X)) =
        (IsLocalization.Away.lift (sectionValue O a Y) (h Y)).comp
          (ringedSectionLocalizationMap O a f) := by
      apply IsLocalization.ringHom_ext (R := O.obj.obj X) (Submonoid.powers (sectionValue O a X))
      ext r
      simp [ringedSectionLocalizationMap, IsLocalization.Away.lift_eq]
    ext x
    exact (DFunLike.congr_fun hnat x).symm

private theorem localizationMap_comp
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (a b : (O.obj ⋙ forget CommRingCat).sections)
    (hab : ∀ X : Cᵒᵖ, IsUnit
      (algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O b X) (sectionValue O a X)))
    (hba : ∀ X : Cᵒᵖ, IsUnit
      (algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O a X) (sectionValue O b X))) :
    localizationMap O a b hab ≫ localizationMap O b a hba = 𝟙 _ := by
  apply PresheafOfModules.hom_ext
  intro X
  have he : (IsLocalization.Away.lift (sectionValue O b X) (hba X)).comp
      (IsLocalization.Away.lift (sectionValue O a X) (hab X)) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (R := O.obj.obj X) (Submonoid.powers (sectionValue O a X))
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply, IsLocalization.Away.lift_eq,
      RingHom.id_apply]
  ext x
  exact DFunLike.congr_fun he x

private def localizationPreUnit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (s : (O.obj ⋙ forget CommRingCat).sections) :
    PresheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj ⟶
      ringedSectionLocalizationPresheaf O s :=
  (ringedSectionLocalizationPresheaf O s).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun X ↦ (1 : ringedSectionLocalizationCarrier O s X))
      (fun {_ _} f ↦ ringedSectionLocalizationPresheaf_one_natural O s f))

private theorem forget_localizationUnit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (s : (O.obj ⋙ forget CommRingCat).sections) :
    @Eq ((SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)).val ⟶
        (ringedSectionLocalization O s).val)
      ((SheafOfModules.forget
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)).map
          (ringedSectionLocalizationUnit O s))
      (localizationPreUnit O s ≫ (PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app
          (ringedSectionLocalizationPresheaf O s)) := by
  exact (SheafOfModules.fullyFaithfulForget _).map_preimage _

private theorem localization_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (a b unit : (O.obj ⋙ forget CommRingCat).sections) (e : ℕ)
    (hu : ∀ X : Cᵒᵖ, IsUnit (sectionValue O unit X)) (he : 1 ≤ e)
    (hab : ∀ X : Cᵒᵖ, sectionValue O a X = sectionValue O unit X * sectionValue O b X ^ e) :
    ∃ E : ringedSectionLocalization O a ≅ ringedSectionLocalization O b,
      ringedSectionLocalizationUnit O a ≫ E.hom = ringedSectionLocalizationUnit O b := by
  have ha (X : Cᵒᵖ) : IsUnit
      (algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O b X) (sectionValue O a X)) := by
    rw [hab X, map_mul, map_pow]
    exact ((hu X).map _).mul ((IsLocalization.Away.algebraMap_isUnit (sectionValue O b X)).pow e)
  have hb (X : Cᵒᵖ) : IsUnit
      (algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O a X) (sectionValue O b X)) := by
    have h := IsLocalization.Away.algebraMap_isUnit
      (R := O.obj.obj X) (S := ringedSectionLocalizationCarrier O a X) (sectionValue O a X)
    have hr := congrArg
      (algebraMap (O.obj.obj X) (ringedSectionLocalizationCarrier O a X)) (hab X)
    rw [hr, map_mul, map_pow] at h
    exact (isUnit_pow_iff (by omega : e ≠ 0)).mp (isUnit_of_mul_isUnit_right h)
  let E : ringedSectionLocalizationPresheaf O a ≅
      ringedSectionLocalizationPresheaf O b :=
    ⟨localizationMap O a b ha, localizationMap O b a hb,
      localizationMap_comp O a b ha hb, localizationMap_comp O b a hb ha⟩
  let S := PresheafOfModules.sheafification.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  refine ⟨S.mapIso E, ?_⟩
  apply (SheafOfModules.fullyFaithfulForget _).map_injective
  simp only [Functor.map_comp, Functor.mapIso_hom]
  rw [forget_localizationUnit, forget_localizationUnit]
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)
  have hn := adj.unit.naturality E.hom
  change E.hom ≫ adj.unit.app _ = adj.unit.app _ ≫ (S.map E.hom).val at hn
  have hp : localizationPreUnit O a ≫ E.hom = localizationPreUnit O b := by
    apply (PresheafOfModules.unitHomEquiv _).injective
    change PresheafOfModules.sectionsMap E.hom
      ((ringedSectionLocalizationPresheaf O a).unitHomEquiv (localizationPreUnit O a)) =
        (ringedSectionLocalizationPresheaf O b).unitHomEquiv (localizationPreUnit O b)
    simp only [localizationPreUnit, Equiv.apply_symm_apply]
    ext X
    change IsLocalization.Away.lift (sectionValue O a X) (ha X)
      (1 : ringedSectionLocalizationCarrier O a X) =
        (1 : ringedSectionLocalizationCarrier O b X)
    exact map_one _
  change (localizationPreUnit O a ≫ adj.unit.app _) ≫ (S.map E.hom).val =
    localizationPreUnit O b ≫ adj.unit.app _
  erw [Category.assoc, ← hn, ← Category.assoc, hp]

private def twoTermComponent
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (a b : (O.obj ⋙ forget CommRingCat).sections)
    (E : ringedSectionLocalization O a ≅ ringedSectionLocalization O b) (n : ℤ) :
    (ringedLocalizationTwoTerm O a).X n ≅ (ringedLocalizationTwoTerm O b).X n := by
  by_cases h0 : n = 0
  · subst n
    simpa only [ringedLocalizationTwoTerm, CochainComplex.of_X,
      ringedLocalizationTwoTermX, if_pos] using
        (Iso.refl (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))
  · by_cases h1 : n = 1
    · subst n
      simpa only [ringedLocalizationTwoTerm, CochainComplex.of_X,
        ringedLocalizationTwoTermX, if_neg (show (1 : ℤ) ≠ 0 by decide), if_pos] using E
    · simpa only [ringedLocalizationTwoTerm, CochainComplex.of_X,
        ringedLocalizationTwoTermX, if_neg h0, if_neg h1] using (Iso.refl (0 :
          SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))

private theorem twoTerm_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (a b : (O.obj ⋙ forget CommRingCat).sections)
    (E : ringedSectionLocalization O a ≅ ringedSectionLocalization O b)
    (hE : ringedSectionLocalizationUnit O a ≫ E.hom = ringedSectionLocalizationUnit O b) :
    ∃ e : ringedLocalizationTwoTerm O a ≅ ringedLocalizationTwoTerm O b,
      e.hom ≫ ringedLocalizationTwoTermAugmentation O b =
        ringedLocalizationTwoTermAugmentation O a := by
  let e : ringedLocalizationTwoTerm O a ≅ ringedLocalizationTwoTerm O b :=
    HomologicalComplex.Hom.isoOfComponents (twoTermComponent O a b E) (by
      intro n m h
      have hm : n + 1 = m := h
      subst m
      change (twoTermComponent O a b E n).hom ≫ CochainComplex.of.d _ _ n (n + 1) =
        CochainComplex.of.d _ _ n (n + 1) ≫ (twoTermComponent O a b E (n + 1)).hom
      rw [CochainComplex.of_d, CochainComplex.of_d]
      by_cases hn : n = 0
      · subst n
        simpa [twoTermComponent, ringedLocalizationTwoTermD, ringedLocalizationTwoTerm,
          ringedLocalizationTwoTermX, Category.id_comp] using hE.symm
      · simp [ringedLocalizationTwoTermD, hn])
  refine ⟨e, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp [e, twoTermComponent, ringedLocalizationTwoTermAugmentation,
      ringedLocalizationTwoTermAugmentationF, ringedLocalizationTwoTerm,
      ringedLocalizationTwoTermX, Category.id_comp]
  · simp [ringedLocalizationTwoTermAugmentation, ringedLocalizationTwoTermAugmentationF, hn]

private theorem completion_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    (K L : ringedSiteComplex O)
    (εK : K ⟶ ringedSiteRingComplex O) (εL : L ⟶ ringedSiteRingComplex O)
    (e : K ≅ L) (he : e.hom ≫ εL = εK) :
    ∃ alpha : ringedCechCompletionFunctor O K ≅ ringedCechCompletionFunctor O L,
      ∀ N : ringedSiteDerived O,
        ringedCechCompletionUnit O K εK N ≫ alpha.hom.app N =
          ringedCechCompletionUnit O L εL N := by
  let H := Functor.curry.obj (derivedInternalHom J O)
  let d := (DerivedCategory.Q.mapIso e).symm.op
  refine ⟨H.mapIso d, ?_⟩
  intro N
  change (ringedDerivedHomUnit O N ≫ (derivedInternalHom J O).map
      ((DerivedCategory.Q.map εK).op, 𝟙 N)) ≫
      (derivedInternalHom J O).map
        (X := (op (DerivedCategory.Q.obj K), N))
        (Y := (op (DerivedCategory.Q.obj L), N))
        ((DerivedCategory.Q.map e.inv).op, 𝟙 N) = _
  rw [Category.assoc, ← Functor.map_comp]
  have hi : e.inv ≫ εK = εL := by rw [← he, Iso.inv_hom_id_assoc]
  change ringedDerivedHomUnit O N ≫ (derivedInternalHom J O).map _ =
    ringedDerivedHomUnit O N ≫ (derivedInternalHom J O).map _
  congr 2
  ext
  · change (DerivedCategory.Q.map εK).op ≫ (DerivedCategory.Q.map e.inv).op =
      (DerivedCategory.Q.map εL).op
    rw [← op_comp, ← Functor.map_comp, hi]
  · simp

private def unitGenerators
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (R : Sheaf K RingCat.{u}) : (SheafOfModules.unit R).GeneratingSections where
  I := ULift.{u} (Fin 1)
  s _ := (SheafOfModules.unit R).unitHomEquiv (𝟙 _)
  epi := by
    have h : SheafOfModules.ιFree (R := R) (⟨0⟩ : ULift.{u} (Fin 1)) ≫
        (SheafOfModules.unit R).freeHomEquiv.symm
          (fun _ : ULift.{u} (Fin 1) ↦ (SheafOfModules.unit R).unitHomEquiv (𝟙 _)) = 𝟙 _ := by
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    exact epi_of_epi_fac h

private theorem principal_generators
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (c : (O.obj ⋙ forget CommRingCat).sections) (U : C) :
    IsRingedIdealGeneratingList O (image (ringedKoszulScalar O c))
      (image.ι (ringedKoszulScalar O c)) U 1 (fun _ ↦ c.val (op U)) := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let p := factorThruImage (ringedKoszulScalar O c)
  let σ := (unitGenerators (R.over U)).ofEpi (p.over U)
  refine ⟨σ, Equiv.ulift, ?_⟩
  intro i
  have h := congrArg (fun f ↦ f.val.app (op U)) (image.fac (ringedKoszulScalar O c))
  have h' := DFunLike.congr_fun (congrArg (fun f ↦ f.hom) h) (1 : O.obj.obj (op U))
  change (image.ι (ringedKoszulScalar O c)).val.app (op U)
    (p.val.app (op U) (show R.obj.obj (op U) from 1)) = c.val (op U)
  refine h'.trans ?_
  change (1 : O.obj.obj (op U)) * sectionValue O c (op U) = sectionValue O c (op U)
  exact one_mul _

private theorem principal_finiteType
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (c : (O.obj ⋙ forget CommRingCat).sections) :
    (image (ringedKoszulScalar O c)).IsFiniteType := by
  classical
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let σ : (image (ringedKoszulScalar O c)).LocalGeneratorsData :=
    { I := C
      X := id
      coversTop := fun _ ↦ GrothendieckTopology.covering_of_eq_top J (by simp)
      generators := fun U ↦ (unitGenerators (R.over U)).ofEpi
        ((factorThruImage (ringedKoszulScalar O c)).over U) }
  exact ⟨⟨σ, ⟨fun _ ↦ ⟨inferInstanceAs (Finite (ULift.{u} (Fin 1)))⟩⟩⟩⟩

-- The factor-restriction calculation keeps its ring component explicit: the local
-- description requires the canonical ring comparison, not just an arrow isomorphism.
namespace UnitPowerRestriction

section ModuleRestriction
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F J K] [F.IsCocontinuous J K]
  (O : Sheaf K CommRingCat.{u})
private abbrev R : Sheaf K RingCat.{u} := (sheafCompose K (forget₂ CommRingCat RingCat)).obj O
private abbrev P : Sheaf J CommRingCat.{u} := (F.sheafPushforwardContinuous CommRingCat J K).obj O
private def unitIso :
    (SheafOfModules.sliceModuleRestriction.{u} (J := J) F (R O)).obj
        (SheafOfModules.unit (R O)) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (P (J := J) F O)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intro X Y a; ext; rfl))

private def locIso (s : (O.obj ⋙ forget CommRingCat).sections) :
    (SheafOfModules.sliceModuleRestriction.{u} (J := J) F (R O)).obj
        (ringedSectionLocalization O s) ≅
      ringedSectionLocalization (P (J := J) F O)
        (LocalizationRHom.restrictedSection (K := J) F O s) :=
  (SheafOfModules.sliceSheafificationIso.{u} (J := J) F (R O)).app
      (ringedSectionLocalizationPresheaf O s) ≪≫
    (PresheafOfModules.sheafification.{u} (𝟙 ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj (P (J := J) F O)).obj)).mapIso
        (LocalizationRHom.restrictionPresheafIso (K := J) F O s)

private def preUnit (s : (O.obj ⋙ forget CommRingCat).sections) :
    PresheafOfModules.unit (R O).obj ⟶ ringedSectionLocalizationPresheaf O s :=
  (ringedSectionLocalizationPresheaf O s).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun X ↦ (1 : ringedSectionLocalizationCarrier O s X))
      (fun {_ _} a ↦ ringedSectionLocalizationPresheaf_one_natural O s a))

private theorem forget_unit (s : (O.obj ⋙ forget CommRingCat).sections) :
    (SheafOfModules.forget (R O)).map (ringedSectionLocalizationUnit O s) =
      preUnit O s ≫ (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (R O).obj)).unit.app
        (ringedSectionLocalizationPresheaf O s) :=
  (SheafOfModules.fullyFaithfulForget _).map_preimage _

private theorem unit_square (s : (O.obj ⋙ forget CommRingCat).sections) :
    (SheafOfModules.sliceModuleRestriction.{u} (J := J) F (R O)).map
        (ringedSectionLocalizationUnit O s) ≫ (locIso F O s).hom =
      (unitIso F O).hom ≫ ringedSectionLocalizationUnit (P (J := J) F O)
        (LocalizationRHom.restrictedSection (K := J) F O s) := by
  let PP := SheafOfModules.slicePresheafRestriction.{u} (J := J) F (R O)
  let V := SheafOfModules.sliceModuleRestriction.{u} (J := J) F (R O)
  let O' := (sheafCompose J (forget₂ CommRingCat RingCat)).obj (P (J := J) F O)
  let T := PresheafOfModules.sheafification.{u} (𝟙 O'.obj)
  let a := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (R O).obj)
  let a' := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 O'.obj)
  let M := ringedSectionLocalizationPresheaf O s
  let M' := ringedSectionLocalizationPresheaf (P (J := J) F O)
    (LocalizationRHom.restrictedSection (K := J) F O s)
  let e := LocalizationRHom.restrictionPresheafIso (K := J) F O s
  let c := (SheafOfModules.sliceSheafificationComparison.{u} (J := J) F (R O)).app M
  have hc : a'.unit.app (PP.obj M) ≫ (SheafOfModules.forget O').map c =
      PP.map (a.unit.app M) := by
    apply (PresheafOfModules.toPresheaf.{u} O'.obj).map_injective
    have h := (a'.homEquiv _ _).apply_symm_apply
      (show PP.obj M ⟶ (SheafOfModules.forget O' ⋙
        PresheafOfModules.restrictScalars (𝟙 O'.obj)).obj (V.obj
          ((PresheafOfModules.sheafification.{u} (𝟙 (R O).obj)).obj M))
        from PP.map (a.unit.app M))
    exact congrArg ((PresheafOfModules.toPresheaf.{u} O'.obj).map) h
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


set_option backward.isDefEq.respectTransparency false in
private theorem factor_restriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (s : (O.obj ⋙ forget CommRingCat).sections) (U : C) :
    ∃ e : ((SheafOfModules.overFunctor.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).mapHomologicalComplex
          (.up ℤ)).obj (ringedLocalizationTwoTerm O s) ≅
        ringedLocalizationTwoTerm (O.over U) (ringedKoszulSliceSection O s U),
      @Eq (((SheafOfModules.overFunctor.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).mapHomologicalComplex
          (.up ℤ)).obj (ringedLocalizationTwoTerm O s) ⟶
            ringedSiteRingComplex (O.over U))
        (((SheafOfModules.overFunctor.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U).mapHomologicalComplex
            (.up ℤ)).map (ringedLocalizationTwoTermAugmentation O s) ≫
              (ringedRestrictionRingComplexIso O U).hom)
        (e.hom ≫ ringedLocalizationTwoTermAugmentation (O.over U)
          (ringedKoszulSliceSection O s U)) := by
  let V := SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U
  have : V.Additive := ringedOverFunctor_additive O U
  let t := ringedKoszulSliceSection O s U
  let h : Arrow.mk (V.map (ringedSectionLocalizationUnit O s)) ≅
      Arrow.mk (ringedSectionLocalizationUnit (O.over U) t) :=
    Arrow.isoMk (unitIso (J := J.over U) (Over.forget U) O)
      (locIso (J := J.over U) (Over.forget U) O s)
      (unit_square (J := J.over U) (Over.forget U) O s).symm
  have hunit : unitIso (J := J.over U) (Over.forget U) O = ringedOverRingIso O U := by
    apply Iso.ext
    ext W
    rfl
  have hring : ringIso O (O.over U) V s t h = ringedRestrictionRingComplexIso O U := by
    apply Iso.ext
    change ((HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).app _).hom ≫
        (HomologicalComplex.single _ (.up ℤ) 0).map
          (unitIso (J := J.over U) (Over.forget U) O).hom = _
    rw [hunit]
    rfl
  refine ⟨complexIso O (O.over U) V s t h, ?_⟩
  rw [← hring]
  exact (factorArrow O (O.over U) V s t h).hom.w.symm

set_option backward.isDefEq.respectTransparency false in
private theorem derived_factor_restriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (s : (O.obj ⋙ forget CommRingCat).sections) (U : C) :
    ∃ e : DerivedCategory.Q.obj (ringedLocalizationTwoTerm (O.over U)
        (ringedKoszulSliceSection O s U)) ≅
        (ringedDerivedRestriction O U).obj (DerivedCategory.Q.obj
          (ringedLocalizationTwoTerm O s)),
      e.hom ≫ (ringedDerivedRestriction O U).map
          (DerivedCategory.Q.map (ringedLocalizationTwoTermAugmentation O s)) ≫
        (ringedDerivedRingRestrictionIso O U).hom =
          DerivedCategory.Q.map (ringedLocalizationTwoTermAugmentation (O.over U)
            (ringedKoszulSliceSection O s U)) := by
  let : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))))
  let V := SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U
  obtain ⟨k, hk⟩ := factor_restriction O s U
  refine ⟨DerivedCategory.Q.mapIso k.symm ≪≫
    (V.mapDerivedCategoryFactors.app (ringedLocalizationTwoTerm O s)).symm, ?_⟩
  change (DerivedCategory.Q.map k.inv ≫ _) ≫ _ ≫ _ = _
  have hn := V.mapDerivedCategoryFactors_hom_naturality
    (ringedLocalizationTwoTermAugmentation O s)
  simp only [ringedDerivedRingRestrictionIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  change DerivedCategory.Q.map k.inv ≫
    (V.mapDerivedCategoryFactors.app (ringedLocalizationTwoTerm O s)).inv ≫
      V.mapDerivedCategory.map
        (DerivedCategory.Q.map (ringedLocalizationTwoTermAugmentation O s)) ≫
        (V.mapDerivedCategoryFactors.app (ringedSiteRingComplex O)).hom ≫
          DerivedCategory.Q.map (ringedRestrictionRingComplexIso O U).hom = _
  rw [← Category.assoc
    (V.mapDerivedCategory.map
      (DerivedCategory.Q.map (ringedLocalizationTwoTermAugmentation O s)))
    (V.mapDerivedCategoryFactors.app (ringedSiteRingComplex O)).hom]
  erw [hn]
  simp only [← Iso.app_hom, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp]
  congr 1
  exact (congrArg (fun f ↦ k.inv ≫ f) hk).trans (Iso.inv_hom_id_assoc k _)

end UnitPowerRestriction

set_option backward.isDefEq.respectTransparency false in
private theorem singleton_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (c : (O.obj ⋙ forget CommRingCat).sections) :
    ∃ e : (ringedExtendedCech O 1 (fun _ ↦ c)).1 ≅ ringedLocalizationTwoTerm O c,
      e.hom ≫ ringedLocalizationTwoTermAugmentation O c =
        (ringedExtendedCech O 1 (fun _ ↦ c)).2 := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  refine ⟨HomologicalComplex.rightUnitor (ringedLocalizationTwoTerm O c), ?_⟩
  change (HomologicalComplex.rightUnitor (ringedLocalizationTwoTerm O c)).hom ≫
    ringedLocalizationTwoTermAugmentation O c =
      HomologicalComplex.tensorHom (ringedLocalizationTwoTermAugmentation O c) (𝟙 _) ≫
        (HomologicalComplex.leftUnitor (ringedSiteRingComplex O)).hom
  have hn := (CategoryTheory.MonoidalCategory.rightUnitor_naturality
    (ringedLocalizationTwoTermAugmentation O c)).symm
  have hu := CategoryTheory.MonoidalCategory.unitors_equal (C := ringedSiteComplex O)
  change (HomologicalComplex.leftUnitor (ringedSiteRingComplex O)).hom =
    (HomologicalComplex.rightUnitor (ringedSiteRingComplex O)).hom at hu
  rw [hu]
  exact hn

private theorem slice_section_eq
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (c : (O.obj ⋙ forget CommRingCat).sections) (U : C) :
    ringedSliceSection O U (c.val (op U)) = ringedKoszulSliceSection O c U := by
  apply Subtype.ext
  funext V
  exact c.property V.unop.hom.op

set_option backward.isDefEq.respectTransparency false in
private theorem principal_localDescription
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (c : (O.obj ⋙ forget CommRingCat).sections) :
    HasLocalExtendedCechDescription O (image (ringedKoszulScalar O c))
      (image.ι (ringedKoszulScalar O c)) (ringedLocalizationTwoTerm O c)
        (ringedLocalizationTwoTermAugmentation O c) := by
  have := principal_finiteType O c
  obtain ⟨K, ε, hK⟩ := exists_ringedExtendedCech_global_model J O
    (image (ringedKoszulScalar O c)) (image.ι (ringedKoszulScalar O c))
  intro U r f hf
  obtain ⟨a, ha⟩ := hK U r f hf
  have hs := hK U 1 (fun _ ↦ c.val (op U)) (principal_generators O c U)
  erw [slice_section_eq O c U] at hs
  obtain ⟨b, hb⟩ := hs
  obtain ⟨k, hk⟩ := singleton_iso (O.over U) (ringedKoszulSliceSection O c U)
  obtain ⟨d, hd⟩ := UnitPowerRestriction.derived_factor_restriction O c U
  refine ⟨a ≪≫ b.symm ≪≫ DerivedCategory.Q.mapIso k ≪≫ d, ?_⟩
  have hb' : b.inv ≫ DerivedCategory.Q.map
      (ringedExtendedCech (O.over U) 1
        (fun _ ↦ ringedKoszulSliceSection O c U)).2 =
      (ringedDerivedRestriction O U).map (DerivedCategory.Q.map ε) ≫
        (ringedDerivedRingRestrictionIso O U).hom := by
    rw [← hb, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [hd, ← Functor.map_comp, hk, hb']
  simpa only [Category.assoc] using ha

private theorem complete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    {N M : ringedSiteDerived O} (e : N ≅ M)
    (hN : IsLocallyDerivedRingedIdealComplete O I ι N) :
    IsLocallyDerivedRingedIdealComplete O I ι M := by
  intro U f hf
  let H := derivedInternalHom (J.over U) (O.over U)
  exact (hN U f hf).of_iso
    (H.mapIso ((Iso.refl _).prod ((ringedDerivedRestriction O U).mapIso e))).symm

private theorem reflective_unit_iff
    {D : Type*} [Category D] (P : D → Prop) (F : D ⥤ D)
    (η : ∀ N, N ⟶ F.obj N)
    (hc : ∀ N, P (F.obj N))
    (hu : ∀ N L, P L → Function.Bijective (fun f : F.obj N ⟶ L ↦ η N ≫ f))
    (hi : ∀ {N M}, (N ≅ M) → P N → P M) (N : D) :
    IsIso (η N) ↔ P N := by
  constructor
  · intro h
    exact hi (asIso (η N)).symm (hc N)
  · intro h
    obtain ⟨r, hr⟩ := (hu N N h).2 (𝟙 _)
    have hs : r ≫ η N = 𝟙 _ := by
      apply (hu N (F.obj N) (hc N)).1
      simp only [← Category.assoc, hr, Category.id_comp, Category.comp_id]
    exact ⟨⟨r, hr, hs⟩⟩

/-- Multiplying a positive power by a unit changes neither local derived completeness nor
its reflection, including the specified augmentation-induced units.

Source: Stacks Project, algebraization.tex, Tags 099B (augmented localization model),
099E (global extended Cech model), and 099F (derived completion as a reflection)
(blueprint: lem-pur-unit-power-completeness).

`image (ringedKoszulScalar O c)` with `image.ι` is exactly the ideal subsheaf generated
by `c`, since categorical images of module sheaves sheafify sectionwise images.
`hu` expresses invertibility of the global section: its sectionwise inverses are unique,
hence commute with restriction and give a global inverse. It imposes no nonzero-ring
condition. All derived objects are unbounded. The chosen derived-category instances
only specify the localization and the size of its morphisms, also on every slice.

Proof:
1. The relation a = u b^e makes a invertible in O[1/b] and b invertible in O[1/a].
   The localization universal property gives inverse maps fixing O. Uniqueness makes
   them natural under restrictions; sheafification gives an isomorphism preserving
   the canonical localization units.
2. Together with the identity in degree zero this gives an isomorphism of the actual
   two-term complexes preserving their augmentations. Contravariant derived internal
   Hom applied to its inverse gives the displayed natural isomorphism, and functoriality
   proves equality of the specified augmentation-induced completion units.
3. The image of multiplication by c has a singleton generating family, hence is of
   finite type. Take the existing global extended Cech model for this ideal. Its local
   description compares every generating list with the singleton list. The singleton
   extended Cech complex is the two-term complex tensored with O[0], identified with
   that complex by the right unitor, compatibly with augmentation. Localization
   commutes with restriction to slices by the localization universal property and
   the restriction/sheafification comparison. The induced chain and derived comparisons
   preserve the canonical ring-complex comparison. These comparisons give the required
   local description for the actual principal two-term complex.
4. Apply the general extended Cech reflector theorem to this local description.
   It gives completeness of the outputs and the Hom bijection for the actual units.
5. For a reflection with complete outputs, an object is complete exactly when its
   unit is invertible: surjectivity of the Hom bijection supplies a retraction and
   injectivity gives the other inverse identity. Completeness is invariant under
   derived isomorphism. The unit-preserving natural isomorphism from step 2 therefore
   identifies the complete objects for a and b. -/
theorem unit_power_localDerivedComplete
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (a b unit : (O.obj ⋙ forget CommRingCat).sections) (e : ℕ)
    (hu : ∀ U : Cᵒᵖ, IsUnit (unit.val U)) (he : 1 ≤ e)
    (hab : ∀ U : Cᵒᵖ, a.val U = unit.val U * b.val U ^ e) :
    (∀ N : ringedSiteDerived O,
      IsLocallyDerivedRingedIdealComplete O
        (image (ringedKoszulScalar O a)) (image.ι (ringedKoszulScalar O a)) N ↔
      IsLocallyDerivedRingedIdealComplete O
        (image (ringedKoszulScalar O b)) (image.ι (ringedKoszulScalar O b)) N) ∧
    (∃ alpha : ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O a) ≅
        ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O b),
      ∀ N : ringedSiteDerived O,
        ringedCechCompletionUnit O (ringedLocalizationTwoTerm O a)
          (ringedLocalizationTwoTermAugmentation O a) N ≫ alpha.hom.app N =
        ringedCechCompletionUnit O (ringedLocalizationTwoTerm O b)
          (ringedLocalizationTwoTermAugmentation O b) N) ∧
    ∀ c : (O.obj ⋙ forget CommRingCat).sections, c = a ∨ c = b →
      (∀ N : ringedSiteDerived O,
        IsLocallyDerivedRingedIdealComplete O
          (image (ringedKoszulScalar O c)) (image.ι (ringedKoszulScalar O c))
          ((ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O c)).obj N)) ∧
      ∀ (N L : ringedSiteDerived O),
        IsLocallyDerivedRingedIdealComplete O
          (image (ringedKoszulScalar O c)) (image.ι (ringedKoszulScalar O c)) L →
        Function.Bijective
          (fun f : (ringedCechCompletionFunctor O (ringedLocalizationTwoTerm O c)).obj N ⟶ L ↦
            ringedCechCompletionUnit O (ringedLocalizationTwoTerm O c)
              (ringedLocalizationTwoTermAugmentation O c) N ≫ f) := by
  obtain ⟨E, hE⟩ := localization_iso O a b unit e hu he hab
  obtain ⟨k, hk⟩ := twoTerm_iso O a b E hE
  obtain ⟨alpha, halpha⟩ := completion_iso O _ _
    (ringedLocalizationTwoTermAugmentation O a)
    (ringedLocalizationTwoTermAugmentation O b) k hk
  have href (c : (O.obj ⋙ forget CommRingCat).sections) := by
    have := principal_finiteType O c
    exact ringedExtendedCech_reflector_properties J O
      (image (ringedKoszulScalar O c)) (image.ι (ringedKoszulScalar O c))
      (ringedLocalizationTwoTerm O c) (ringedLocalizationTwoTermAugmentation O c)
      (principal_localDescription O c)
  have hunit (c : (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteDerived O) :=
    reflective_unit_iff _ _ _ (href c).1 (href c).2.2.1
      (fun {N M} e h ↦ complete_of_iso O _ _ e h) N
  refine ⟨?_, ⟨alpha, halpha⟩, ?_⟩
  · intro N
    rw [← hunit a N, ← hunit b N]
    constructor
    · intro h
      rw [← halpha N]
      infer_instance
    · intro h
      have hc : IsIso (ringedCechCompletionUnit O (ringedLocalizationTwoTerm O a)
          (ringedLocalizationTwoTermAugmentation O a) N ≫ alpha.hom.app N) := by
        rw [halpha N]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (alpha.hom.app N)
  · intro c _
    exact ⟨(href c).1, (href c).2.2.1⟩

end CategoryTheory
