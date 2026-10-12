/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Degree-zero normalization of the canonical direct-image unit

Source: Stacks Project, Tags 079V and 0A1G.
(blueprint: lem-pc-canonical-direct-image-h0-unit).
-/

@[expose] public section

set_option autoImplicit false
universe u w
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

namespace AlgebraicGeometry.Scheme.Modules
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The H⁰ comparison for direct image takes the canonical single-module unit to
 the single-complex homology identification.
Source: Stacks Project, Tags 079V and 0A1G; Mathlib's injective-resolution
construction of `rightDerivedZeroIsoSelf`.
(blueprint: lem-pc-canonical-direct-image-h0-unit).

Proof: The universal-property factorization for
`rightDerivedFunctorPlusCompatibility` carries the unbounded right-derived unit
to the bounded-below unit. Evaluate it on the single complex of M. Naturality of
the bounded-below unit along the injective-resolution augmentation identifies its
H⁰, after `homologyRightDerivedFunctorPlusObjSingleFunctorIso`, with the classical
map `toRightDerivedZero`. The single-map direct-image comparison cancels the
single-complex comparison in this computation. Pushforward is left exact, so
`rightDerivedZeroIsoSelf` is inverse to `toRightDerivedZero`; their composite is
the identity. Consequently the displayed composite is the canonical single
homology identification, not an unspecified isomorphism. No positive-cohomology
vanishing is assumed. Zero modules and empty schemes use the same augmentation
and inverse-cancellation formulas. -/
theorem canonicalDirectImageH0Unit {X S : Scheme.{u}} (f : X ⟶ S)
    [HasInjectiveResolutions X.Modules] (M : X.Modules) :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
        (canonicalSingleDirectImageMap f M) ≫
      (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) M 0 ≪≫
          (pushforward f).rightDerivedZeroIsoSelf.app M).hom =
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).app
        ((pushforward f).obj M)).hom := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let F : C ⥤ D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  have : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (pushforward f)
    infer_instance
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

end AlgebraicGeometry.Scheme.Modules
