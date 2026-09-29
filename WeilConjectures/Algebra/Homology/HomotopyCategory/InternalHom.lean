/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.InternalHom
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal

/-!
# The tensor-hom adjunction on the homotopy category

Let `C` be a monoidal closed preadditive category with countable products, in which the
tensor product of cochain complexes is defined. For a cochain complex `P`, the internal hom
functor `CochainComplex.internalHom P` sends homotopic morphisms to homotopic morphisms, hence
induces a functor `HomotopyCategory.internalHom P` on `K(C) = HomotopyCategory C (up ℤ)`, and
the tensor-hom adjunction `CochainComplex.tensorHomAdjunction P` descends to an adjunction
`HomotopyCategory.tensorHomAdjunction P : tensorLeft ((quotient _ _).obj P) ⊣ internalHom P`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

universe v u

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [HasCountableProducts C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (P : CochainComplex C ℤ)

/-- The internal hom functor `CochainComplex.internalHom P` sends homotopic morphisms to
homotopic morphisms. -/
noncomputable def internalHomMapHomotopy {Y Y' : CochainComplex C ℤ} {k k' : Y ⟶ Y'}
    (h : Homotopy k k') :
    Homotopy ((CochainComplex.internalHom P).map k) ((CochainComplex.internalHom P).map k') :=
  CochainComplex.internalHomEquivHomotopy _ (h.compLeft _)

/-- The internal hom functor `K(C) ⥤ K(C)` induced by `CochainComplex.internalHom P`. -/
noncomputable def internalHom :
    HomotopyCategory C (ComplexShape.up ℤ) ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _ (CochainComplex.internalHom P ⋙ quotient _ _)
    (fun _ _ _ _ ⟨h⟩ ↦ eq_of_homotopy _ _ (internalHomMapHomotopy P h))

@[simp]
lemma internalHom_map_quotient_map {Y Y' : CochainComplex C ℤ} (k : Y ⟶ Y') :
    (internalHom P).map ((quotient _ _).map k) =
      (quotient _ _).map ((CochainComplex.internalHom P).map k) := rfl

/-- The tensor-hom adjunction `P ⊗ - ⊣ internalHom P` on the homotopy category
`K(C) = HomotopyCategory C (ComplexShape.up ℤ)`. -/
noncomputable def tensorHomAdjunction :
    tensorLeft ((quotient C (ComplexShape.up ℤ)).obj P) ⊣ internalHom P where
  unit :=
    { app K := (quotient _ _).map ((CochainComplex.tensorHomAdjunction P).unit.app K.as)
      naturality K K' f := by
        rw [← quotient_map_out f]
        exact ((quotient _ _).map_comp _ _).symm.trans ((congrArg (quotient _ _).map
          ((CochainComplex.tensorHomAdjunction P).unit.naturality f.out)).trans
            ((quotient _ _).map_comp _ _)) }
  counit :=
    { app Y := (quotient _ _).map ((CochainComplex.tensorHomAdjunction P).counit.app Y.as)
      naturality Y Y' k := by
        rw [← quotient_map_out k]
        exact ((quotient _ _).map_comp _ _).symm.trans ((congrArg (quotient _ _).map
          ((CochainComplex.tensorHomAdjunction P).counit.naturality k.out)).trans
            ((quotient _ _).map_comp _ _)) }
  left_triangle_components K :=
    ((quotient _ _).map_comp _ _).symm.trans (((quotient _ _).congr_map
      ((CochainComplex.tensorHomAdjunction P).left_triangle_components K.as)).trans
        ((quotient _ _).map_id _))
  right_triangle_components Y :=
    ((quotient _ _).map_comp _ _).symm.trans (((quotient _ _).congr_map
      ((CochainComplex.tensorHomAdjunction P).right_triangle_components Y.as)).trans
        ((quotient _ _).map_id _))

end HomotopyCategory
