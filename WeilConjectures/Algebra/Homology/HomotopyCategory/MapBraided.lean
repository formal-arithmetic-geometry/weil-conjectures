/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal

/-!
# A braided functor induces a braided functor on homotopy categories

Let `G : C ⥤ D` be an additive braided functor between braided monoidal preadditive categories,
which preserves the coproducts defining the tensor product of cochain complexes. Then the
monoidal functor `G.mapHomologicalComplex (.up ℤ)` is compatible with the Koszul braidings
(`CategoryTheory.Functor.mapCochainComplexμIso_hom_comp_map_braiding`): the signs are preserved
since `G` is additive. Hence so is the oplax monoidal functor `G.mapHomotopyCategory (.up ℤ)`
(`CategoryTheory.Functor.mapHomotopyCategory_δ_comp_braiding`).
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [BraidedCategory C] [BraidedCategory D]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.Braided]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

/-- The isomorphism `G(K) ⊗ G(L) ≅ G(K ⊗ L)` of cochain complexes induced by a braided functor
`G` is compatible with the Koszul braidings. -/
@[reassoc]
lemma mapCochainComplexμIso_hom_comp_map_braiding (K L : CochainComplex C ℤ) :
    (G.mapCochainComplexμIso K L).hom ≫ (G.mapHomologicalComplex (.up ℤ)).map (β_ K L).hom =
      (β_ ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L)).hom ≫ (G.mapCochainComplexμIso L K).hom := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  erw [ιTensorObj_mapCochainComplexμIso_hom_f_assoc, CochainComplex.Monoidal.ι_braiding_hom_assoc]
  rw [← G.map_comp]
  erw [CochainComplex.Monoidal.ι_braiding_hom]
  rw [G.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp, assoc]
  erw [ιTensorObj_mapCochainComplexμIso_hom_f]
  rw [G.map_comp, LaxBraided.braided_assoc]
  rfl

/-- The comonoidal structure of `G.mapHomotopyCategory (.up ℤ)` induced by a braided functor
`G` is compatible with the Koszul braidings. -/
@[reassoc]
lemma mapHomotopyCategory_δ_comp_braiding (X Y : HomotopyCategory C (.up ℤ)) :
    OplaxMonoidal.δ (G.mapHomotopyCategory (.up ℤ)) X Y ≫
        (β_ ((G.mapHomotopyCategory (.up ℤ)).obj X) ((G.mapHomotopyCategory (.up ℤ)).obj Y)).hom =
      (G.mapHomotopyCategory (.up ℤ)).map (β_ X Y).hom ≫
        OplaxMonoidal.δ (G.mapHomotopyCategory (.up ℤ)) Y X := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  have h : (G.mapCochainComplexμIso K L).inv ≫
      (β_ ((G.mapHomologicalComplex (.up ℤ)).obj K) ((G.mapHomologicalComplex (.up ℤ)).obj L)).hom =
      (G.mapHomologicalComplex (.up ℤ)).map (β_ K L).hom ≫ (G.mapCochainComplexμIso L K).inv := by
    rw [Iso.inv_comp_eq, mapCochainComplexμIso_hom_comp_map_braiding_assoc, Iso.hom_inv_id,
      comp_id]
  have := (HomotopyCategory.quotient D (.up ℤ)).congr_map h
  rw [Functor.map_comp, Functor.map_comp] at this
  exact this

end CategoryTheory.Functor
