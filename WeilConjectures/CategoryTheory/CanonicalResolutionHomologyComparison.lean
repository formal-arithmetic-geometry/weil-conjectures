/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CanonicalResolutionDerivedIso

/-! # Resolution comparisons and the composite derived unit

Source: Stacks Project, derived.tex, Tags 015M and 015N.
(blueprint: lem-pc-grothendieck-resolution-unit-comparison).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Homology of the canonical comparison computes the prescribed resolution comparison.
Source: Stacks Project, Tag 015M, resolution computation of derived functors.
(blueprint: lem-pc-canonical-resolution-homology-comparison).

Proof: For the chosen injective resolution, expand the single-object homology comparison;
its final inverse resolution comparison cancels the resolution comparison in the left
side. For the prescribed resolution, choose a comparison lifting the identity of X.
Its extension induces a homotopy equivalence, and naturality of the derived unit shows
that the chosen derived comparison followed by its image is resolutionDerivedIso F I.
Naturality of homologyFunctorObjQIso and isoRightDerivedObjCochainComplex identifies
its map on homology with the prescribed resolution comparison. Finally expand
isoRightDerivedObjCochainComplex: its inverse map/extension homology comparison cancels
the map/extension factor in canonicalResolutionDerivedIso, and its inverse extension
homology comparison cancels the last factor on the right. This works also for n = 0.
-/
theorem resolution_homology_transport
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [EnoughInjectives A] {B : Type uB} [Category.{vB} B]
    [Abelian B] [HasDerivedCategory A]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    (X : A) (I : InjectiveResolution X) (n : ℕ) :
    (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom ≫
          (I.isoRightDerivedObj F n).hom =
        (DerivedCategory.Plus.homologyFunctor B n).map (canonicalResolutionDerivedIso F I).hom ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso
            ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
              ComplexShape.embeddingUpNat, 0, inferInstance⟩ n).hom ≫
          (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom := by
  have hcore :
      (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom ≫
            (I.isoRightDerivedObj F n).hom =
          (DerivedCategory.Plus.homologyFunctor B n).map
            (resolutionDerivedIso F I).hom ≫
            (DerivedCategory.Plus.homologyFunctorObjQIso
              ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
                inferInstance⟩ n).hom ≫
            HomologicalComplex.homologyMap
              ((I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom) (n : ℤ) ≫
            (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
              ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom := by
    let R := injectiveResolution X
    let φ : R.Hom I (𝟙 X) :=
      ⟨InjectiveResolution.desc (𝟙 X) I R,
        by simp [InjectiveResolution.desc_commutes_zero]⟩
    let LX : CochainComplex.Plus A := ⟨R.cochainComplex, 0, inferInstance⟩
    let LY : CochainComplex.Plus A := ⟨I.cochainComplex, 0, inferInstance⟩
    let g : LX ⟶ LY := ObjectProperty.homMk φ.hom'
    have h₁ := F.rightDerivedFunctorPlusUnit.naturality
      ((HomotopyCategory.Plus.quotient A).map g)
    have h₂ : (resolutionAugmentationIso R).hom ≫ DerivedCategory.Plus.Q.map g =
        (resolutionAugmentationIso I).hom := by
      apply DerivedCategory.Plus.ι.map_injective
      have h := (DerivedCategory.quotientCompQhIso A).inv.naturality φ.hom'
      simp only [resolutionAugmentationIso, Functor.map_comp, Functor.preimageIso_hom,
        Functor.map_preimage]
      dsimp at h ⊢
      change ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app X ≫
          DerivedCategory.Q.map R.ι' ≫
          (DerivedCategory.quotientCompQhIso A).inv.app _) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient A _).map φ.hom') = _
      rw [Category.assoc, Category.assoc, ← h]
      simp only [← Functor.map_comp_assoc, InjectiveResolution.Hom.ι'_comp_hom',
        Functor.map_id, Category.id_comp]
    let FG : F.rightDerivedPlusComplex X ⟶
        ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
          inferInstance⟩ := ObjectProperty.homMk ((F.mapHomologicalComplex _).map φ.hom')
    have hcompare : (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ X).hom ≫
        DerivedCategory.Plus.Q.map FG = (resolutionDerivedIso F I).hom := by
      have hi : inv (F.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient A).obj LX)) ≫ DerivedCategory.Plus.Q.map FG =
          F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g) ≫
            inv (F.rightDerivedFunctorPlusUnit.app
              ((HomotopyCategory.Plus.quotient A).obj LY)) := by
        rw [IsIso.inv_comp_eq, ← Category.assoc]
        symm
        rw [IsIso.comp_inv_eq]
        exact h₁.symm
      change (F.rightDerivedFunctorPlus.map (resolutionAugmentationIso R).hom ≫
          inv (F.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient A).obj LX))) ≫ DerivedCategory.Plus.Q.map FG =
        F.rightDerivedFunctorPlus.map (resolutionAugmentationIso I).hom ≫
          inv (F.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient A).obj LY))
      rw [Category.assoc, hi, ← Category.assoc, ← Functor.map_comp, h₂]
    have hnat := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality FG (n : ℤ)
    have hres := R.isoRightDerivedObjCochainComplex_inv_naturality φ F n
    have hhom : (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom ≫
        (I.isoRightDerivedObjCochainComplex F n).hom =
        (DerivedCategory.Plus.homologyFunctor B n).map (resolutionDerivedIso F I).hom ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso
            ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
              inferInstance⟩ n).hom := by
      rw [← hcompare, Functor.map_comp, Category.assoc, hnat]
      simp only [Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso,
        Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
      dsimp [R] at hres
      simp only [Functor.map_id, Category.comp_id] at hres
      rw [← hres, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl
    rw [← reassoc_of% hhom]
    simp only [InjectiveResolution.isoRightDerivedObjCochainComplex, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
      Category.assoc]
    simp only [← HomologicalComplex.homologyMap_comp_assoc, Iso.inv_hom_id,
      HomologicalComplex.homologyMap_id, Category.id_comp,
      Category.comp_id]
  rw [hcore]
  simp only [canonicalResolutionDerivedIso, Iso.trans_hom, Functor.mapIso_hom]
  have hnat := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
    (K := ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
      inferInstance⟩)
    (L := ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
      ComplexShape.embeddingUpNat, 0, inferInstance⟩)
    ((CochainComplex.plus B).isoMk
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F)).hom n
  have hnat2 :
      (DerivedCategory.Plus.homologyFunctorObjQIso
          ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
            inferInstance⟩ n).hom ≫
        HomologicalComplex.homologyMap
          (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom (n : ℤ) =
      (DerivedCategory.Plus.homologyFunctor B n).map
          (DerivedCategory.Plus.Q.map
            ((CochainComplex.plus B).isoMk
              (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F)).hom) ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso
          ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
            ComplexShape.embeddingUpNat, 0, inferInstance⟩ n).hom := by
    simpa using hnat.symm
  calc
    _ = (DerivedCategory.Plus.homologyFunctor B n).map (resolutionDerivedIso F I).hom ≫
        ((DerivedCategory.Plus.homologyFunctorObjQIso
          ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
            inferInstance⟩ n).hom ≫
          HomologicalComplex.homologyMap
            (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom (n : ℤ)) ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom := by simp [Category.assoc]
    _ = (DerivedCategory.Plus.homologyFunctor B n).map (resolutionDerivedIso F I).hom ≫
        ((DerivedCategory.Plus.homologyFunctor B n).map
          (DerivedCategory.Plus.Q.map
            ((CochainComplex.plus B).isoMk
              (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F)).hom) ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso
            ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
              ComplexShape.embeddingUpNat, 0, inferInstance⟩ n).hom) ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom := by rw [hnat2]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

end CategoryTheory
