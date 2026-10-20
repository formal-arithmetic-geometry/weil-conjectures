/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7, Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# The zeroth homology of the single-object right-derived unit

Source: Stacks Project, Tag 05TD. This is the generic augmentation calculation used
for the direct-image specialization in `CanonicalDirectImageH0Unit`.
-/

@[expose] public section

set_option autoImplicit false
open CategoryTheory Limits
noncomputable section

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
private theorem unit_plus {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (M : C) :
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M) ≫
      (F.rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj M)).inv =
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) := by
  apply (Iso.comp_inv_eq _).2
  have h := (Functor.rightDerivedNatTrans_app
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
      F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
      (HomotopyCategory.Plus.quasiIso C) (𝟙 _)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M)).symm
  simp only [NatTrans.id_app, Category.id_comp] at h
  change F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M).obj =
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) ≫
    (F.rightDerivedFunctorPlusCompatibility.app
      (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M))).hom at h
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
private theorem plus_unit_resolution {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (M : C) :
    F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M) ≫
      (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ M).hom =
    DerivedCategory.Plus.Q.map (ObjectProperty.homMk
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (injectiveResolution M).ι') :
        ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj M), 0, inferInstance⟩ ⟶
        F.rightDerivedPlusComplex M) := by
  let R := injectiveResolution M
  let K : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj M, 0, inferInstance⟩
  let L : CochainComplex.Plus C := ⟨R.cochainComplex, 0, inferInstance⟩
  let g : K ⟶ L := ObjectProperty.homMk R.ι'
  have h := F.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient C).map g)
  dsimp only [Functor.comp_map] at h
  unfold Functor.rightDerivedFunctorPlusObjSingleFunctorIsoQ
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
  have he : (DerivedCategory.Plus.ι.preimageIso
      (X := (DerivedCategory.Plus.singleFunctor C 0).obj M)
      (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj L))
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
        asIso (DerivedCategory.Q.map R.ι') ≪≫
        (DerivedCategory.quotientCompQhIso C).symm.app _)).hom =
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map g) := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom]
    dsimp [DerivedCategory.singleFunctorIsoCompQ, DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso]
    erw [Category.id_comp, Category.comp_id]
    rfl
  rw [he]
  change _ ≫ _ ≫ inv (F.rightDerivedFunctorPlusUnit.app
    ((HomotopyCategory.Plus.quotient C).obj L)) = _
  have h' : F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M) ≫
      F.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map g)) =
    DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map
      ((HomotopyCategory.Plus.quotient C).map g)) ≫
      F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj L) := h.symm
  rw [← Category.assoc, h', Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
private theorem unit_homology_resolution {C D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (M : C) (n : ℕ) :
    (DerivedCategory.homologyFunctor D n).map
        (F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M)) ≫
      (F.homologyRightDerivedFunctorObjSingleFunctorIso M n).hom =
    ((DerivedCategory.homologyFunctorFactorsh D n).app _ ≪≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) n).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj M))).hom ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (injectiveResolution M).ι') n ≫
      ((injectiveResolution M).isoRightDerivedObjCochainComplex F n).inv := by
  let K : CochainComplex.Plus D :=
    ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj M), 0, inferInstance⟩
  let g : K ⟶ F.rightDerivedPlusComplex M := ObjectProperty.homMk
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (injectiveResolution M).ι')
  dsimp only [Functor.homologyRightDerivedFunctorObjSingleFunctorIso,
    Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, unit_plus]
  change (DerivedCategory.Plus.homologyFunctor D n).map
      (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) ≫ _ = _
  rw [← Functor.map_comp_assoc, plus_unit_resolution]
  have h := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality g n
  change (DerivedCategory.Plus.homologyFunctor D n).map
      (DerivedCategory.Plus.Q.map g) ≫ _ = _
  erw [reassoc_of% h]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
private theorem augmentation_homology {C D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D]
    [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (M : C) :
    HomologicalComplex.homologyMap
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M ≫
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (injectiveResolution M).ι') 0 ≫
      ((injectiveResolution M).isoRightDerivedObjCochainComplex F 0).inv =
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj M)).hom ≫
      F.toRightDerivedZero.app M := by
  let R := injectiveResolution M
  let K := (CochainComplex.singleFunctor D 0).obj (F.obj M)
  let g := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M ≫
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.ι'
  change HomologicalComplex.homologyMap g 0 ≫
    (R.isoRightDerivedObjCochainComplex F 0).inv =
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj M)).hom ≫
      F.toRightDerivedZero.app M
  rw [R.toRightDerivedZero_eq F]
  dsimp only [InjectiveResolution.isoRightDerivedObjCochainComplex, Iso.trans_inv,
    Functor.mapIso_inv, Iso.symm_inv]
  simp only [Category.assoc]
  rw [← cancel_mono (R.isoRightDerivedObj F 0).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [HomologicalComplex.homologyFunctor_map]
  rw [← cancel_epi (K.homologyπ 0)]
  change K.homologyπ 0 ≫ HomologicalComplex.homologyMap g 0 ≫ _ = _
  dsimp [K]
  erw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom_assoc]
  erw [HomologicalComplex.homologyπ_extendHomologyIso_hom]
  change HomologicalComplex.cyclesMap g 0 ≫
      HomologicalComplex.cyclesMap (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom 0 ≫
      (((F.mapHomologicalComplex _).obj R.cocomplex).extendCyclesIso
        ComplexShape.embeddingUpNat rfl).hom ≫
      ((F.mapHomologicalComplex _).obj R.cocomplex).homologyπ 0 = _
  have hc : HomologicalComplex.cyclesMap g 0 ≫
      HomologicalComplex.cyclesMap (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom 0 ≫
      (((F.mapHomologicalComplex _).obj R.cocomplex).extendCyclesIso
        ComplexShape.embeddingUpNat rfl).hom =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (F.obj M)).hom ≫
        R.toRightDerivedZero' F := by
    apply (cancel_mono (((F.mapHomologicalComplex _).obj R.cocomplex).iCycles 0)).1
    simp only [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    erw [HomologicalComplex.cyclesMap_i_assoc, HomologicalComplex.cyclesMap_i_assoc]
    dsimp [g]
    change K.iCycles 0 ≫ g.f 0 ≫
      (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom.f 0 ≫
      (((F.mapHomologicalComplex _).obj R.cocomplex).extendXIso
        ComplexShape.embeddingUpNat rfl).hom = _
    dsimp only [g]
    erw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      InjectiveResolution.ι'_f_zero]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← F.map_comp_assoc]
    have hm : (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom.f 0 ≫
        (((F.mapHomologicalComplex _).obj R.cocomplex).extendXIso
          ComplexShape.embeddingUpNat rfl).hom =
        F.map (R.cochainComplexXIso 0 0 rfl).hom := by
      simp only [InjectiveResolution.cochainComplexXIso, HomologicalComplex.mapExtendIso,
        HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
        Functor.mapHomologicalComplex_obj_X, ComplexShape.embeddingUpNat_f,
        Int.cast_ofNat_Int, HomologicalComplex.Hom.isoOfComponents_hom_f]
      have hr : ComplexShape.embeddingUpNat.r (0 : ℤ) = some (0 : ℕ) :=
        ComplexShape.embeddingUpNat.r_f 0
      erw [HomologicalComplex.mapExtendX_hom_eq R.cocomplex F hr]
      erw [eqToHom_map]
      · simp only [eqToIso.hom, eqToHom_trans]
      · change HomologicalComplex.extend.X R.cocomplex
          (ComplexShape.embeddingUpNat.r 0) = R.cocomplex.X 0
        rw [hr]
        rfl
    erw [hm]
    erw [← F.map_comp]
    have hh : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫
        R.ι.f 0 ≫ (R.cochainComplexXIso 0 0 rfl).inv) ≫
        (R.cochainComplexXIso 0 0 rfl).hom = R.ι.f 0 := by
      simp
    erw [hh]
    exact (Category.assoc _ _ _).symm
  rw [reassoc_of% hc]

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical augmentation from `F M[0]` to `RF(M[0])`, natural in `M`.
Source: Stacks Project, Tag 05TD (blueprint: lem-kun-right-derived-single-h0). -/
def singleRightDerivedUnit (F : C ⥤ D) [F.Additive] :
    F ⋙ DerivedCategory.singleFunctor D 0 ⟶
      DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor where
  app M := DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M)
  naturality M N f := by
    have hs := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.naturality f
    have hu := F.rightDerivedFunctorUnit.naturality
      ((HomotopyCategory.singleFunctor C 0).map f)
    dsimp only [Functor.comp_map] at hu hs
    change DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map (F.map f)) ≫
      _ ≫ _ = _
    erw [← DerivedCategory.Q.map_comp_assoc, hs, DerivedCategory.Q.map_comp,
      Category.assoc]
    simp only [Category.assoc]
    apply congrArg (fun g ↦ DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫ g)
    exact hu


/-- The canonical zeroth-homology identification for a left exact functor.
Source: Stacks Tag 05TD (blueprint: lem-kun-right-derived-single-h0). -/
@[irreducible] def singleRightDerivedH0Iso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [EnoughInjectives C] (M : C) :
    (DerivedCategory.homologyFunctor D 0).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M)) ≅ F.obj M :=
  F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫ F.rightDerivedZeroIsoSelf.app M

/-- The named identification is the usual composite of canonical H⁰ comparisons.
Source: Stacks Tag 05TD (blueprint: lem-kun-right-derived-single-h0).
Proof: unfold the explicit construction. -/
theorem singleRightDerivedH0Iso_def (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [EnoughInjectives C] (M : C) :
    F.singleRightDerivedH0Iso M =
      F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫ F.rightDerivedZeroIsoSelf.app M := by
  delta singleRightDerivedH0Iso
  rfl

/-- The canonical zeroth-homology identification after an exact functor.
Source: Stacks Tag 05TD (blueprint: lem-kun-right-derived-single-h0). -/
@[irreducible] def mapSingleRightDerivedH0Iso
    {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [EnoughInjectives C]
    (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : C) :
    (DerivedCategory.homologyFunctor E 0).obj
        (F.mapDerivedCategory.obj
          (R.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M))) ≅
      F.obj (R.obj M) :=
  (F.mapDerivedCategoryHomologyFunctorIso 0).symm.app _ ≪≫
    F.mapIso (R.singleRightDerivedH0Iso M)

end CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
/-- The canonical map from the single object of `F M` to `RF(M[0])` is inverse on H⁰
 to the canonical left-exact zeroth-derived identification.

Source: Stacks Project, Tag 05TD, lemma-left-exact-higher-derived (3).
(blueprint: lem-kun-right-derived-single-h0).

Proof: compare the unbounded right-derived unit with its bounded-below unit by
uniqueness of right derived functors. Naturality on the injective-resolution
augmentation computes its homology as the classical map `toRightDerivedZero`.
The single-complex comparison cancels the single-map comparison in that computation.
Left exactness makes `toRightDerivedZero` inverse to `rightDerivedZeroIsoSelf`,
and the remaining map is the canonical single-complex homology identification.
The construction also applies to zero objects and zero functors. -/
theorem CategoryTheory.Functor.rightDerivedFunctorUnit_homology_zero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (M : C) :
    (DerivedCategory.homologyFunctor D 0).map (F.singleRightDerivedUnit.app M) ≫
      (F.singleRightDerivedH0Iso M).hom =
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).app (F.obj M)).hom := by
  delta Functor.singleRightDerivedH0Iso
  let H := DerivedCategory.homologyFunctor D 0
  let a := (HomologicalComplex.singleMapHomologicalComplex F
    (ComplexShape.up ℤ) 0).inv.app M
  have h := unit_homology_resolution F M 0
  have h' := augmentation_homology F M
  change H.map (DerivedCategory.Q.map a ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M)) ≫
      (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
        F.rightDerivedZeroIsoSelf.app M).hom = _
  simp only [Functor.map_comp, Iso.trans_hom, Category.assoc]
  erw [reassoc_of% h]
  have hn := (DerivedCategory.homologyFunctorFactorsh D 0).hom.naturality
    ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map a)
  have hn' := (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) 0).hom.naturality a
  dsimp only [Functor.comp_map] at hn hn'
  simp only [Iso.trans_hom, Category.assoc]
  erw [reassoc_of% hn, reassoc_of% hn']
  erw [← HomologicalComplex.homologyMap_comp_assoc, reassoc_of% h']
  erw [Functor.rightDerivedZeroIsoSelf_inv_hom_id_app, Category.comp_id]
  change _ = ((DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).app (F.obj M)).hom
  dsimp [DerivedCategory.singleFunctorCompHomologyFunctorIso]
  simp only [DerivedCategory.singleFunctorsPostcompQIso_hom_hom]
  simp only [NatTrans.id_app, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj]
  dsimp [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An exact functor preserves the zeroth-homology augmentation normalization.
Source: Stacks Project, Tag 05TD, and exact functors commuting with homology.
(blueprint: lem-kun-right-derived-single-h0).

Proof: move the exact-functor homology comparison past the right-derived unit
by naturality, apply the augmentation calculation, and cancel the exact-functor
single comparison using its homology normalization. -/
theorem CategoryTheory.Functor.rightDerivedFunctorUnit_homology_zero_after_exact
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    (F : D ⥤ E) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : C) :
    (DerivedCategory.homologyFunctor E 0).map
        ((F.mapDerivedCategorySingleFunctor 0).inv.app (R.obj X) ≫
          F.mapDerivedCategory.map (R.singleRightDerivedUnit.app X)) ≫
      (R.mapSingleRightDerivedH0Iso F X).hom =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso E 0).hom.app (F.obj (R.obj X)) := by
  delta Functor.mapSingleRightDerivedH0Iso Functor.singleRightDerivedH0Iso
  let H := DerivedCategory.homologyFunctor E 0
  let c := F.mapDerivedCategoryHomologyFunctorIso 0
  simp only [Functor.map_comp, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  have hn := c.inv.naturality (R.singleRightDerivedUnit.app X)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  have hr := R.rightDerivedFunctorUnit_homology_zero X
  rw [Functor.singleRightDerivedH0Iso_def] at hr
  change (DerivedCategory.homologyFunctor D 0).map (R.singleRightDerivedUnit.app X) ≫
    (R.homologyRightDerivedFunctorObjSingleFunctorIso X 0 ≪≫
      R.rightDerivedZeroIsoSelf.app X).hom = _ at hr
  have hz := congrArg F.map hr
  simp only [F.map_comp, Iso.trans_hom] at hz
  erw [hz]
  have hs := F.mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor 0 (R.obj X)
  change c.hom.app ((DerivedCategory.singleFunctor D 0).obj (R.obj X)) ≫
      H.map ((F.mapDerivedCategorySingleFunctor 0).hom.app (R.obj X)) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso E 0).hom.app (F.obj (R.obj X)) = _
    at hs
  erw [← hs]
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  change (H.map ((F.mapDerivedCategorySingleFunctor 0).inv.app (R.obj X)) ≫
    H.map ((F.mapDerivedCategorySingleFunctor 0).hom.app (R.obj X))) ≫ _ = _
  rw [← H.map_comp, Iso.inv_hom_id_app, H.map_id, Category.id_comp]

private theorem h0_augmentation_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (H : D ⥤ C)
    (e : F ⋙ H ≅ 𝟭 C) {x y : C} {X Y : D}
    (u : F.obj x ⟶ X) (v : F.obj y ⟶ Y) (f : X ⟶ Y) (c : x ⟶ y)
    (i : H.obj X ≅ x) (j : H.obj Y ≅ y)
    (hu : H.map u ≫ i.hom = e.hom.app x)
    (hv : H.map v ≫ j.hom = e.hom.app y)
    (hc : u ≫ f = F.map c ≫ v) : i.inv ≫ H.map f ≫ j.hom = c := by
  apply (cancel_epi (e.hom.app x)).1
  conv_lhs => rw [← hu]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← H.map_comp_assoc, hc, H.map_comp, Category.assoc, hv]
  exact e.hom.naturality c


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A square compatible with the single-object augmentations has the corresponding
ordinary map as its normalized zeroth homology.
Source: Stacks Tag 05TD (blueprint: lem-kun-right-derived-single-h0).

Proof: apply zeroth homology to the augmentation square. The two canonical augmentation
identities identify its vertical maps with the single/homology isomorphisms. Cancel those
isomorphisms and use their naturality. This calculation uses only the named normalization
maps, and is independent of the concrete objects used to construct an exact functor. -/
theorem CategoryTheory.Functor.mapSingleRightDerivedH0Iso_conjugate
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    (S : D ⥤ E) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (T : C ⥤ E) [T.Additive] [PreservesFiniteLimits T] (X : C)
    (f : S.mapDerivedCategory.obj
        (R.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X)) ⟶
      T.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X))
    (c : S.obj (R.obj X) ⟶ T.obj X)
    (h : ((S.mapDerivedCategorySingleFunctor 0).inv.app (R.obj X) ≫
        S.mapDerivedCategory.map (R.singleRightDerivedUnit.app X)) ≫ f =
      (DerivedCategory.singleFunctor E 0).map c ≫ T.singleRightDerivedUnit.app X) :
    (R.mapSingleRightDerivedH0Iso S X).inv ≫
        (DerivedCategory.homologyFunctor E 0).map f ≫
      (T.singleRightDerivedH0Iso X).hom = c := by
  have hv := R.rightDerivedFunctorUnit_homology_zero_after_exact S X
  have ht := T.rightDerivedFunctorUnit_homology_zero X
  exact h0_augmentation_square (DerivedCategory.singleFunctor E 0)
    (DerivedCategory.homologyFunctor E 0)
    (DerivedCategory.singleFunctorCompHomologyFunctorIso E 0)
    ((S.mapDerivedCategorySingleFunctor 0).inv.app (R.obj X) ≫
      S.mapDerivedCategory.map (R.singleRightDerivedUnit.app X))
    (T.singleRightDerivedUnit.app X) f c
    (R.mapSingleRightDerivedH0Iso S X) (T.singleRightDerivedH0Iso X) hv ht h
