/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-!
# The comparison of total complexes commutes with shifts

Let `F : C₁ ⥤ C₂ ⥤ D` and `F' : C₁' ⥤ C₂' ⥤ D'` be bifunctors, `G₁ : C₁ ⥤ C₁'`,
`G₂ : C₂ ⥤ C₂'` and `G : D ⥤ D'` additive functors and
`τ : G (F X₁ X₂) ⟶ F' (G₁ X₁) (G₂ X₂)` a natural transformation. The comparison
`HomologicalComplex.mapBifunctorComparison τ (.up ℤ) K₁ K₂ :
  G(mapBifunctor K₁ K₂ F) ⟶ mapBifunctor (G₁ K₁) (G₂ K₂) F'` of cochain complexes commutes with
the shifts in each variable: for fixed `K₁` (resp. `K₂`) it is a natural transformation
commuting with the shifts by `ℤ`, for the shift compatibilities
`CochainComplex.mapBifunctorShift₂Iso` (resp. `CochainComplex.mapBifunctorShift₁Iso`) of
total complexes and the shift compatibilities of `G.mapHomologicalComplex`.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C₁ C₂ D C₁' C₂' D' : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Category* C₁'] [Category* C₂'] [Category* D']
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [Preadditive C₁'] [Preadditive C₂'] [Preadditive D']
  {F : C₁ ⥤ C₂ ⥤ D} [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  {F' : C₁' ⥤ C₂' ⥤ D'} [F'.Additive] [∀ X₁, (F'.obj X₁).Additive]
  {G₁ : C₁ ⥤ C₁'} {G₂ : C₂ ⥤ C₂'} {G : D ⥤ D'}
  [G₁.Additive] [G₂.Additive] [G.Additive]
  (τ : (Functor.postcompose₂.obj G).obj F ⟶ (((Functor.whiskeringLeft₂ D').obj G₁).obj G₂).obj F')
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ), CochainComplex.HasMapBifunctor K₁ K₂ F]
  [∀ (K₁ : CochainComplex C₁' ℤ) (K₂ : CochainComplex C₂' ℤ),
    CochainComplex.HasMapBifunctor K₁ K₂ F']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a fixed cochain complex `K₁`, the comparison `G(mapBifunctor K₁ K₂ F) ⟶
mapBifunctor (G₁ K₁) (G₂ K₂) F'` commutes with the shifts in `K₂`. -/
instance commShift_mapBifunctorComparisonNatTrans_app (K₁ : CochainComplex C₁ ℤ) :
    NatTrans.CommShift (F₁ := F.map₂CochainComplex.obj K₁ ⋙ G.mapHomologicalComplex (.up ℤ))
      (F₂ := G₂.mapHomologicalComplex (.up ℤ) ⋙
        F'.map₂CochainComplex.obj ((G₁.mapHomologicalComplex (.up ℤ)).obj K₁))
      ((mapBifunctorComparisonNatTrans τ (.up ℤ)).app K₁) ℤ where
  shift_comm n := by
    ext K₂ j
    refine mapBifunctor.hom_ext_of_map G (fun p q h ↦ ?_)
    dsimp
    simp only [Functor.commShiftIso_comp_hom_app,
      Functor.commShiftIso_map₂CochainComplex_hom_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Category.assoc]
    erw [Category.id_comp]
    rw [← G.map_comp_assoc]
    erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + n) (j + n) rfl rfl]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Iso.refl_inv, Category.comp_id, map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
    erw [ι_mapBifunctorMap_assoc,
      CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + n) (j + n) rfl rfl]
    simp only [Units.smul_def, CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id, Functor.map_zsmul,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, CategoryTheory.Functor.map_id,
      HomologicalComplex.id_f, NatTrans.id_app, Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    congr 1
    erw [CategoryTheory.Functor.map_id, Category.id_comp, map_ιMapBifunctor_mapBifunctorComparisonX]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.id_comp]
    erw [Category.id_comp]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a fixed cochain complex `K₂`, the comparison `G(mapBifunctor K₁ K₂ F) ⟶
mapBifunctor (G₁ K₁) (G₂ K₂) F'` commutes with the shifts in `K₁`. -/
instance commShift_mapBifunctorComparisonNatTrans_flipApp (K₂ : CochainComplex C₂ ℤ) :
    NatTrans.CommShift (F₁ := F.map₂CochainComplex.flip.obj K₂ ⋙ G.mapHomologicalComplex (.up ℤ))
      (F₂ := G₁.mapHomologicalComplex (.up ℤ) ⋙
        F'.map₂CochainComplex.flip.obj ((G₂.mapHomologicalComplex (.up ℤ)).obj K₂))
      ((mapBifunctorComparisonNatTrans τ (.up ℤ)).flipApp K₂) ℤ where
  shift_comm n := by
    ext K₁ j
    refine mapBifunctor.hom_ext_of_map G (fun p q h ↦ ?_)
    dsimp
    simp only [Functor.commShiftIso_comp_hom_app,
      Functor.commShiftIso_map₂CochainComplex_flip_hom_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Category.assoc]
    erw [Category.id_comp]
    rw [← G.map_comp_assoc]
    erw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + n) (j + n) rfl rfl]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Iso.refl_inv, Category.comp_id, map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
    erw [ι_mapBifunctorMap_assoc,
      CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + n) (j + n) rfl rfl]
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, Iso.refl_inv, Category.comp_id, CategoryTheory.Functor.map_id,
      HomologicalComplex.id_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      map_ιMapBifunctor_mapBifunctorComparisonX]
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
    erw [Category.id_comp]
    erw [Category.id_comp]
    rfl

end HomologicalComplex
