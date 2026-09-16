/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!
# Families of sections of a functor to types

Mathlib's `CategoryTheory.Functor.sectionsEquivHom` identifies the sections of a functor
`F : C ⥤ Type u₂` with the morphisms to `F` from the constant functor with value a one-element
type. Dropping the assumption that the value is a one-element type, a morphism to `F` from the
constant functor with value `X` is a family of sections of `F` indexed by `X`.

## Main declarations

- `CategoryTheory.Functor.constHomEquivSections`: morphisms from a constant functor to `F` are
  families of sections of `F`.
-/

@[expose] public section

universe v₁ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]

/-- A morphism to `F : C ⥤ Type u₂` from the constant functor with value `X` is the same thing as
a family of sections of `F` indexed by `X`.

For `X` a one-element type this is `CategoryTheory.Functor.sectionsEquivHom`. -/
def constHomEquivSections (F : C ⥤ Type u₂) (X : Type u₂) :
    ((const C).obj X ⟶ F) ≃ (X → F.sections) where
  toFun τ x :=
    ⟨fun j ↦ τ.app j x, fun f ↦ by
      simpa using (ConcreteCategory.congr_hom (τ.naturality f) x).symm⟩
  invFun s :=
    { app j := ↾fun x ↦ (s x).1 j
      naturality _ _ f := by
        ext x
        simp }

@[simp]
lemma constHomEquivSections_apply_val (F : C ⥤ Type u₂) (X : Type u₂)
    (τ : (const C).obj X ⟶ F) (x : X) (j : C) :
    (constHomEquivSections F X τ x).val j = τ.app j x :=
  rfl

@[simp]
lemma constHomEquivSections_symm_apply_app (F : C ⥤ Type u₂) (X : Type u₂)
    (s : X → F.sections) (j : C) (x : X) :
    ((constHomEquivSections F X).symm s).app j x = (s x).val j :=
  rfl

end CategoryTheory.Functor
