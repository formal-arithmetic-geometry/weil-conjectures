/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal

/-!
# Composites of comonoidal comparisons on complexes

Let `G₂ : C ⥤ D`, `G₁ : D ⥤ E` and `G₁₂ : C ⥤ E` be additive oplax monoidal functors which
preserve the coproducts defining the tensor product of homological complexes, and let
`e : G₁₂ ⟶ G₂ ⋙ G₁` be compatible with the comonoidal structures. Then the induced maps on
homological complexes and on homotopy categories are compatible with the comparisons
`G(K ⊗ L) ⟶ G(K) ⊗ G(L)`
(`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_comp` and
`CategoryTheory.Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_comp`).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor.OplaxMonoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Preadditive C] [Preadditive D]
  [Preadditive E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [HasZeroObject C]
  [HasZeroObject D] [HasZeroObject E]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive]
  [(curriedTensor E).Additive] [∀ (X₁ : E), ((curriedTensor E).obj X₁).Additive]
  {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns] [DecidableEq I]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject I D), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject I E), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} E) ((curriedTensor E).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I E), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I E), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I E), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  {G₁ : D ⥤ E} {G₂ : C ⥤ D} {G₁₂ : C ⥤ E} [G₁.Additive] [G₁.OplaxMonoidal]
  [G₂.Additive] [G₂.OplaxMonoidal] [G₁₂.Additive] [G₁₂.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G₁]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G₂]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G₁₂]
  (e : G₁₂ ⟶ G₂ ⋙ G₁)

set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` of homological complexes is compatible with a
transformation `e : G₁₂ ⟶ G₂ ⋙ G₁` compatible with the comonoidal structures:
```
G₁₂(K ⊗ L) ──e──▶ G₁(G₂(K ⊗ L)) ──G₁ δ──▶ G₁(G₂ K ⊗ G₂ L) ──δ──▶ G₁(G₂ K) ⊗ G₁(G₂ L)
     │ δ                                                                ‖
     ▼                                                                  ‖
G₁₂ K ⊗ G₁₂ L ──────────────────e ⊗ e──────────────────▶ G₁(G₂ K) ⊗ G₁(G₂ L)
``` -/
lemma mapHomologicalComplexδNatTrans_comp
    (he : ∀ X Y, e.app (X ⊗ Y) ≫ G₁.map (δ G₂ X Y) ≫ δ G₁ _ _ =
      δ G₁₂ X Y ≫ (e.app X ⊗ₘ e.app Y))
    (K L : HomologicalComplex C c) :
    (NatTrans.mapHomologicalComplex e c).app (K ⊗ L) ≫
        (G₁.mapHomologicalComplex c).map (((mapHomologicalComplexδNatTrans c G₂).app K).app L) ≫
          ((mapHomologicalComplexδNatTrans c G₁).app _).app _ =
      ((mapHomologicalComplexδNatTrans c G₁₂).app K).app L ≫
        ((NatTrans.mapHomologicalComplex e c).app K ⊗ₘ
          (NatTrans.mapHomologicalComplex e c).app L) := by
  ext n
  refine mapBifunctor.hom_ext_of_map G₁₂ (fun p q h ↦ ?_)
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    mapHomologicalComplexδNatTrans_app_app, mapBifunctorComparison_f,
    Functor.mapHomologicalComplex_map_f]
  erw [e.naturality_assoc]
  rw [Functor.comp_map, ← G₁.map_comp_assoc,
    map_ιMapBifunctor_mapBifunctorComparisonX, G₁.map_comp_assoc,
    map_ιMapBifunctor_mapBifunctorComparisonX, map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  erw [ι_mapBifunctorMap]
  simp only [mapBifunctorComparisonApp, δNatTrans_app_app,
    NatTrans.mapHomologicalComplex_app_f, curriedTensor_map_app, curriedTensor_obj_map]
  erw [reassoc_of% (he (K.X p) (L.X q))]
  rw [tensorHom_def, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` on homotopy categories is compatible with a
transformation `e : G₁₂ ⟶ G₂ ⋙ G₁` compatible with the comonoidal structures. This is
`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_comp` on the quotient. -/
lemma mapHomotopyCategoryδNatTrans_comp
    (he : ∀ X Y, e.app (X ⊗ Y) ≫ G₁.map (δ G₂ X Y) ≫ δ G₁ _ _ =
      δ G₁₂ X Y ≫ (e.app X ⊗ₘ e.app Y))
    (K L : HomotopyCategory C c) :
    (NatTrans.mapHomotopyCategory e c).app (K ⊗ L) ≫
        (G₁.mapHomotopyCategory c).map (((mapHomotopyCategoryδNatTrans c G₂).app K).app L) ≫
          ((mapHomotopyCategoryδNatTrans c G₁).app _).app _ =
      ((mapHomotopyCategoryδNatTrans c G₁₂).app K).app L ≫
        ((NatTrans.mapHomotopyCategory e c).app K ⊗ₘ
          (NatTrans.mapHomotopyCategory e c).app L) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  have h := (HomotopyCategory.quotient E c).congr_map
    (mapHomologicalComplexδNatTrans_comp c e he K L)
  simp only [Functor.map_comp] at h
  rw [tensorHom_def] at h ⊢
  simp only [Functor.map_comp, HomotopyCategory.MonoidalCategory.quotient_map_whiskerRight,
    HomotopyCategory.MonoidalCategory.quotient_map_whiskerLeft] at h
  exact h

end CategoryTheory.Functor.OplaxMonoidal
