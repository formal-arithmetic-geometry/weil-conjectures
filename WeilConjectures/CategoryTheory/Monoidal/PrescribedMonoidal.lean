/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Transport

/-! # Fully faithful transport with prescribed tensor objects -/

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

namespace CategoryTheory.Monoidal

/-- A fully faithful functor induces a monoidal structure with prescribed tensor objects.
Source: the categorical transport in Weil II (1.1.1), (1.1.6). -/
theorem nonempty_prescribedMonoidal
    {C : Type*} [Category C] {D : Type*} [Category D] [MonoidalCategory D]
    (T : C ⥤ D) (ff : T.FullyFaithful) (t : C → C → C) (I : C)
    (μ : ∀ X Y, T.obj X ⊗ T.obj Y ≅ T.obj (t X Y))
    (ε : 𝟙_ D ≅ T.obj I) :
    ∃ m : MonoidalCategory C,
      m.toMonoidalCategoryStruct.tensorObj = t ∧
      @MonoidalCategoryStruct.tensorUnit C _ m.toMonoidalCategoryStruct = I ∧
      Nonempty (@Functor.Monoidal C _ m D _ _ T) := by
  let := ff.faithful
  let s : MonoidalCategoryStruct C :=
    { tensorObj := t
      tensorUnit := I
      whiskerLeft := fun X _ _ f ↦
        ff.preimage ((μ _ _).inv ≫ (T.obj X ◁ T.map f) ≫ (μ _ _).hom)
      whiskerRight := fun f Y ↦
        ff.preimage ((μ _ _).inv ≫ (T.map f ▷ T.obj Y) ≫ (μ _ _).hom)
      tensorHom := fun f g ↦
        ff.preimage ((μ _ _).inv ≫ (T.map f ⊗ₘ T.map g) ≫ (μ _ _).hom)
      associator := fun X Y Z ↦ ff.preimageIso
        ((μ (t X Y) Z).symm ≪≫ ((μ X Y).symm ⊗ᵢ Iso.refl _) ≪≫
          α_ (T.obj X) (T.obj Y) (T.obj Z) ≪≫
          (Iso.refl _ ⊗ᵢ μ Y Z) ≪≫ μ X (t Y Z))
      leftUnitor := fun X ↦ ff.preimageIso
        ((μ I X).symm ≪≫ (ε.symm ⊗ᵢ Iso.refl _) ≪≫ λ_ (T.obj X))
      rightUnitor := fun X ↦ ff.preimageIso
        ((μ X I).symm ≪≫ (Iso.refl _ ⊗ᵢ ε.symm) ≪≫ ρ_ (T.obj X)) }
  let s' : MonoidalCategoryStruct C := s
  let h : Monoidal.InducingFunctorData T :=
    { μIso := μ
      εIso := ε
      whiskerLeft_eq := by intros; exact ff.map_preimage _
      whiskerRight_eq := by intros; exact ff.map_preimage _
      tensorHom_eq := by intros; exact ff.map_preimage _
      associator_eq := by
        intro X Y Z
        change T.map (ff.preimageIso _).hom = _
        rw [Functor.FullyFaithful.preimageIso_hom, ff.map_preimage]
        simp only [Iso.trans_hom, Category.assoc]
        rfl
      leftUnitor_eq := by
        intro X
        change T.map (ff.preimageIso _).hom = _
        rw [Functor.FullyFaithful.preimageIso_hom, ff.map_preimage]
        simp only [Iso.trans_hom, Category.assoc]
        rfl
      rightUnitor_eq := by
        intro X
        change T.map (ff.preimageIso _).hom = _
        rw [Functor.FullyFaithful.preimageIso_hom, ff.map_preimage]
        simp only [Iso.trans_hom, Category.assoc]
        rfl }
  exact ⟨Monoidal.induced T h, rfl, rfl, ⟨Monoidal.fromInducedMonoidal T h⟩⟩

end CategoryTheory.Monoidal
