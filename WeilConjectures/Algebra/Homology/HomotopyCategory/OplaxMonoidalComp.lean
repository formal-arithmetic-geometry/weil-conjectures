/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# Compatibility of the comparison `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` with composition, in the homotopy
category

The homotopy category version
`CategoryTheory.Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_comp` of
`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_comp`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CategoryTheory.Functor.OplaxMonoidal

open HomologicalComplex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
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
  {G₁ : C ⥤ D} {G₂ : D ⥤ E} {G₁₂ : C ⥤ E} [G₁.Additive] [G₂.Additive] [G₁₂.Additive]
  [G₁.OplaxMonoidal] [G₂.OplaxMonoidal] [G₁₂.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G₁]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G₂]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G₁₂]

set_option backward.isDefEq.respectTransparency.types false in
/-- The homotopy category version of
`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_comp`: a natural
transformation `u : G₁₂ ⟶ G₁ ⋙ G₂` compatible with the comparisons `δ` induces a morphism of
functors on homotopy categories compatible with the comparisons of
`CategoryTheory.Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans`. -/
lemma mapHomotopyCategoryδNatTrans_comp (u : G₁₂ ⟶ G₁ ⋙ G₂)
    (hu : ∀ X Y : C, u.app (X ⊗ Y) ≫ G₂.map (δ G₁ X Y) ≫ δ G₂ _ _ =
      δ G₁₂ X Y ≫ (u.app X ⊗ₘ u.app Y))
    (K L : HomotopyCategory C c) :
    (NatTrans.mapHomotopyCategory u c).app (K ⊗ L) ≫
        (G₂.mapHomotopyCategory c).map (((mapHomotopyCategoryδNatTrans c G₁).app K).app L) ≫
        ((mapHomotopyCategoryδNatTrans c G₂).app _).app _ =
      ((mapHomotopyCategoryδNatTrans c G₁₂).app K).app L ≫
        ((NatTrans.mapHomotopyCategory u c).app K ⊗ₘ
          (NatTrans.mapHomotopyCategory u c).app L) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  have h := (HomotopyCategory.quotient E c).congr_map
    (mapHomologicalComplexδNatTrans_comp c u hu K L)
  simp only [Functor.map_comp] at h
  refine h.trans ?_
  congr 1
  rw [tensorHom_def]
  rfl

end CategoryTheory.Functor.OplaxMonoidal
