/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.CategoryTheory.FilteredDerivedOperationStructures
import Sheaf.CategoryTheory.FilteredExactObjectAction
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.CategoryTheory.Shift.Localization

/-!
# Descending exact filtered object actions

Source: Stacks Tag 05RX and localization universal property, Tag 015Q
(blueprint: lem-trf-exact-filtered-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe wA vA uA wB vB uB
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- The exact object action descends to the filtered derived localization.
Source: Stacks Tags 05RX and 015Q.
Proof: the evaluation comparisons conjugate each graded map to the image under the
exact functor H. Therefore the homotopy action preserves graded quasi-isomorphisms.
Localize this action; its shift and distinguished-triangle comparisons descend from
those of additive homotopy functors. Finally descend the total and graded comparison
isomorphisms by the fully faithful precomposition with the localization functor.
The retained object and step comparisons give precisely the termwise action record.
(blueprint: lem-trf-exact-filtered-localization). -/
theorem exactFilteredLocalization (H : A ⥤ B) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    Nonempty (FilteredTermwiseLift H) := by
  classical
  have actionData := exactFilteredObjectAction H
  choose action add evaluation step inclusion using actionData
  let (bounds : Option (ℤ × ℤ)) : (action bounds).Additive := add bounds
  let K (bounds : Option (ℤ × ℤ)) := (action bounds).mapHomotopyCategoryPlus
  let comparison (bounds : Option (ℤ × ℤ)) (p : Option ℤ) :
      K bounds ⋙ (filteredEvaluation B bounds false p).mapHomotopyCategoryPlus ≅
        (filteredEvaluation A bounds false p).mapHomotopyCategoryPlus ⋙
          H.mapHomotopyCategoryPlus :=
    Functor.mapHomotopyCategoryPlusCompIso (evaluation bounds p) ≪≫
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl _)).symm
  have preserves (bounds : Option (ℤ × ℤ)) :
      (finiteFilteredQuasiIso A bounds).IsInvertedBy (K bounds ⋙ finiteFilteredQh B bounds) := by
    intro X Y f hf
    apply Localization.inverts (finiteFilteredQh B bounds) (finiteFilteredQuasiIso B bounds)
    intro p
    have hq := hf p
    change HomotopyCategory.Plus.quasiIso A
      ((filteredEvaluation A bounds false (some p)).mapHomotopyCategoryPlus.map f) at hq
    have hi : IsIso ((H.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map
        ((filteredEvaluation A bounds false (some p)).mapHomotopyCategoryPlus.map f)) := by
      have h : IsIso (DerivedCategory.Plus.Qh.map
          ((filteredEvaluation A bounds false (some p)).mapHomotopyCategoryPlus.map f)) :=
        Localization.inverts DerivedCategory.Plus.Qh
          (HomotopyCategory.Plus.quasiIso A) _ hq
      apply (NatIso.isIso_map_iff H.mapDerivedCategoryPlusFactorsh _).1
      change IsIso (H.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map _))
      infer_instance
    have he : IsIso (((K bounds ⋙
        (filteredEvaluation B bounds false (some p)).mapHomotopyCategoryPlus) ⋙
          DerivedCategory.Plus.Qh).map f) :=
      (NatIso.isIso_map_iff
        (Functor.isoWhiskerRight (comparison bounds (some p)) DerivedCategory.Plus.Qh) f).2 hi
    change HomotopyCategory.Plus.quasiIso B
      ((filteredEvaluation B bounds false (some p)).mapHomotopyCategoryPlus.map
        ((K bounds).map f))
    change IsIso (DerivedCategory.Plus.Qh.map
      ((filteredEvaluation B bounds false (some p)).mapHomotopyCategoryPlus.map
        ((K bounds).map f))) at he
    apply (DerivedCategory.isIso_Qh_map_iff _).1
    exact (DerivedCategory.Plus.ι (C := B)).map_isIso
      (DerivedCategory.Plus.Qh.map
        ((filteredEvaluation B bounds false (some p)).mapHomotopyCategoryPlus.map
          ((K bounds).map f)))
  let filtered (bounds : Option (ℤ × ℤ)) :=
    Localization.lift (K bounds ⋙ finiteFilteredQh B bounds) (preserves bounds)
      (finiteFilteredQh A bounds)
  let (bounds : Option (ℤ × ℤ)) : (filtered bounds).CommShift ℤ :=
    Functor.commShiftOfLocalization (finiteFilteredQh A bounds)
      (finiteFilteredQuasiIso A bounds) ℤ (K bounds ⋙ finiteFilteredQh B bounds) (filtered bounds)
  have triangulated (bounds : Option (ℤ × ℤ)) : (filtered bounds).IsTriangulated := by
    let : (finiteFilteredQh A bounds).mapArrow.EssSurj :=
      Localization.essSurj_mapArrow _ (finiteFilteredQuasiIso A bounds)
    have : NatTrans.CommShift
        (Localization.fac (K bounds ⋙ finiteFilteredQh B bounds) (preserves bounds)
          (finiteFilteredQh A bounds)).hom ℤ := by
      exact NatTrans.commShift_iso_hom_of_localization (finiteFilteredQh A bounds)
        (finiteFilteredQuasiIso A bounds) ℤ (K bounds ⋙ finiteFilteredQh B bounds)
        (filtered bounds)
    exact Functor.isTriangulated_of_precomp_iso
      (Localization.fac (K bounds ⋙ finiteFilteredQh B bounds) (preserves bounds)
        (finiteFilteredQh A bounds))
  let derivedComparison (bounds : Option (ℤ × ℤ)) (p : Option ℤ) :
      filtered bounds ⋙ finiteFilteredDerivedEvaluation B bounds p ≅
        finiteFilteredDerivedEvaluation A bounds p ⋙ H.mapDerivedCategoryPlus := by
    let Q := finiteFilteredQh A bounds
    let W := finiteFilteredQuasiIso A bounds
    let E := finiteFilteredDerivedEvaluation B bounds p
    let e₁ : Q ⋙ filtered bounds ⋙ E ≅
        K bounds ⋙ (filteredEvaluation B bounds false p).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Localization.fac _ (preserves bounds) Q) E ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (K bounds) (eqToIso (Localization.Construction.fac _ _))
    let e₂ : Q ⋙ finiteFilteredDerivedEvaluation A bounds p ⋙ H.mapDerivedCategoryPlus ≅
        (filteredEvaluation A bounds false p).mapHomotopyCategoryPlus ⋙
          H.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (eqToIso (Localization.Construction.fac _ _))
          H.mapDerivedCategoryPlus ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ H.mapDerivedCategoryPlusFactorsh
    exact Localization.liftNatIso Q W _ _ _ _
      (e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (comparison bounds p) DerivedCategory.Plus.Qh ≪≫
        Functor.associator _ _ _ ≪≫ e₂.symm)
  exact ⟨{
    filtered := filtered
    filteredCommShift := fun bounds ↦ inferInstance
    filteredTriangulated := triangulated
    forgetComparison := fun bounds ↦ derivedComparison bounds none
    gradedComparison := fun bounds r ↦ derivedComparison bounds (some r)
    objectAction := action
    objectComparison := fun bounds ↦ evaluation bounds none
    stepComparison := step
    stepInclusion := inclusion
    localizationComparison := fun bounds ↦ Localization.fac _ (preserves bounds) _ }⟩

end CategoryTheory
