/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# The comonoidal comparison of an oplax monoidal functor on homotopy categories

Let `G : C ⥤ D` be an additive oplax monoidal functor which preserves the coproducts
defining the tensor product of homological complexes. The comparison
`G(K ⊗ L) ⟶ G(K) ⊗ G(L)` of homological complexes
(`CategoryTheory.Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans`) descends to
a natural transformation of bifunctors on homotopy categories
`CategoryTheory.Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans`, between
`(K, L) ↦ G(K ⊗ L)` and `(K, L) ↦ G(K) ⊗ G(L)`. It is an isomorphism when `G` is
strong monoidal.

-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory HomologicalComplex

namespace CategoryTheory.Functor.OplaxMonoidal

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive]
  {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns] [DecidableEq I]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject I D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.OplaxMonoidal]
  [∀ j, PreservesColimitsOfShape (Discrete (ComplexShape.π c c c ⁻¹' {j})) G]

/-- The comparison `G(K ⊗ L) ⟶ G(K) ⊗ G(L)` in the homotopy category, induced by
the comonoidal structure `δ` of an additive oplax monoidal functor `G`: it is the image
in the homotopy category of `mapHomologicalComplexδNatTrans c G`. -/
noncomputable def mapHomotopyCategoryδNatTrans :
    (Functor.postcompose₂.obj (G.mapHomotopyCategory c)).obj
        (curriedTensor (HomotopyCategory C c)) ⟶
      (((whiskeringLeft₂ _).obj (G.mapHomotopyCategory c)).obj
        (G.mapHomotopyCategory c)).obj (curriedTensor (HomotopyCategory D c)) where
  app K :=
    { app L := (HomotopyCategory.quotient D c).map
        (((mapHomologicalComplexδNatTrans c G).app K.as).app L.as)
      naturality := by
        rintro L L' ⟨g⟩
        have := (HomotopyCategory.quotient D c).congr_map
          (((mapHomologicalComplexδNatTrans c G).app K.as).naturality g)
        simp only [Functor.map_comp] at this
        exact this }
  naturality := by
    rintro K K' ⟨f⟩
    ext L
    have := (HomotopyCategory.quotient D c).congr_map
      (NatTrans.congr_app ((mapHomologicalComplexδNatTrans c G).naturality f) L.as)
    rw [NatTrans.comp_app, NatTrans.comp_app, Functor.map_comp, Functor.map_comp] at this
    exact this

lemma mapHomotopyCategoryδNatTrans_app_app (K L : HomologicalComplex C c) :
    ((mapHomotopyCategoryδNatTrans c G).app ((HomotopyCategory.quotient C c).obj K)).app
        ((HomotopyCategory.quotient C c).obj L) =
      (HomotopyCategory.quotient D c).map (mapBifunctorComparison (δNatTrans G) c K L) :=
  rfl

variable [∀ X Y : C, IsIso (δ G X Y)]

instance (K : HomotopyCategory C c) : IsIso ((mapHomotopyCategoryδNatTrans c G).app K) := by
  have (L : HomotopyCategory C c) : IsIso (((mapHomotopyCategoryδNatTrans c G).app K).app L) :=
    inferInstanceAs (IsIso ((HomotopyCategory.quotient D c).map
      (((mapHomologicalComplexδNatTrans c G).app K.as).app L.as)))
  apply NatIso.isIso_of_isIso_app

instance : IsIso (mapHomotopyCategoryδNatTrans c G) :=
  NatIso.isIso_of_isIso_app _

end CategoryTheory.Functor.OplaxMonoidal
