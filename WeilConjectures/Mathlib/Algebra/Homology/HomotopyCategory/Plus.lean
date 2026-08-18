/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Natural transformations between functors on bounded below homotopy categories

A natural transformation `τ : F ⟶ G` of additive functors induces a natural transformation
`F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus` between the induced functors on the
bounded below homotopy categories (`CategoryTheory.NatTrans.mapHomotopyCategoryPlus`),
compatibly with identities and compositions.

This material is destined for `Mathlib/Algebra/Homology/HomotopyCategory/Plus.lean`, next to
`CategoryTheory.Functor.mapHomotopyCategoryPlus`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory.NatTrans

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

/-- The natural transformation `F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus`
induced by a natural transformation `τ : F ⟶ G` of additive functors. It is the
transformation `NatTrans.mapHomotopyCategory τ` of the ambient homotopy categories,
lifted through the fully faithful inclusion of the bounded below subcategory. -/
noncomputable def mapHomotopyCategoryPlus
    {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus :=
  ((HomotopyCategory.plus D).fullyFaithfulι.whiskeringRight (HomotopyCategory.Plus C)).preimage
    (Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
      (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)))

@[simp]
lemma mapHomotopyCategoryPlus_id (F : C ⥤ D) [F.Additive] :
    NatTrans.mapHomotopyCategoryPlus (𝟙 F) = 𝟙 F.mapHomotopyCategoryPlus := by
  rw [NatTrans.mapHomotopyCategoryPlus, NatTrans.mapHomotopyCategory_id (ComplexShape.up ℤ),
    Functor.whiskerLeft_id']
  exact ((HomotopyCategory.plus D).fullyFaithfulι.whiskeringRight
    (HomotopyCategory.Plus C)).preimage_id

@[reassoc, simp]
lemma mapHomotopyCategoryPlus_comp {F G H : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] (τ : F ⟶ G) (σ : G ⟶ H) :
    NatTrans.mapHomotopyCategoryPlus (τ ≫ σ) =
      NatTrans.mapHomotopyCategoryPlus τ ≫ NatTrans.mapHomotopyCategoryPlus σ := by
  have h : Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
        (NatTrans.mapHomotopyCategory (τ ≫ σ) (ComplexShape.up ℤ)) =
      Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
          (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)) ≫
        Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
          (NatTrans.mapHomotopyCategory σ (ComplexShape.up ℤ)) := by
    rw [NatTrans.mapHomotopyCategory_comp (ComplexShape.up ℤ)]
    rfl
  rw [NatTrans.mapHomotopyCategoryPlus, NatTrans.mapHomotopyCategoryPlus,
    NatTrans.mapHomotopyCategoryPlus, h]
  exact ((HomotopyCategory.plus D).fullyFaithfulι.whiskeringRight
    (HomotopyCategory.Plus C)).preimage_comp (Y := G.mapHomotopyCategoryPlus) _ _

end CategoryTheory.NatTrans
