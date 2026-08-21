/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# The constant functor is monoidal and the precomposition functor is braided

When `C` is any category and `D` is a monoidal category, the functor category `C ⥤ D`
carries the pointwise monoidal structure (`CategoryTheory.Monoidal.functorCategoryMonoidal`).
The tensor unit and tensor products of constant functors are computed objectwise, so the
constant functor `Functor.const C : D ⥤ C ⥤ D` is a monoidal functor, with structure
isomorphisms whose components are identities. We record this as an instance
`(Functor.const C).Monoidal`.

When `D` is moreover braided, the braiding on `C ⥤ D` is computed objectwise as well
(`CategoryTheory.Monoidal.functorCategoryBraided`), so the constant functor is a braided
functor; this is the instance `(Functor.const C).Braided`. Since a symmetric monoidal
functor is by definition a braided functor between symmetric monoidal categories, this
also covers the symmetric case.

Moreover, when `E` is a braided monoidal category, the functor categories `C ⥤ E` and
`D ⥤ E` carry the pointwise braiding `Monoidal.functorCategoryBraided`, and precomposition
with any functor `F : C ⥤ D` is strong monoidal with identity structure maps
(`Functor.Monoidal.whiskeringLeft`). We record that this monoidal structure preserves the
pointwise braiding: `((whiskeringLeft C D E).obj F).Braided`.

Similarly, whiskering on the right with a (lax) braided functor `L : D ⥤ E` is (lax)
braided for the pointwise braidings.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

section Const

namespace Functor

open MonoidalCategory LaxMonoidal OplaxMonoidal

variable (C : Type u₁) [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory.{v₂} D]

/-- The constant functor `D ⥤ C ⥤ D` is monoidal for the pointwise monoidal structure
on the functor category `C ⥤ D`: the tensor unit and tensor products in `C ⥤ D` are
computed objectwise, so the structure isomorphisms have identity components. -/
def constCoreMonoidal : (const C : D ⥤ C ⥤ D).CoreMonoidal where
  εIso := Iso.refl _
  μIso X Y := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact id_tensorHom_id X Y)
  μIso_hom_natural_left f X' := by ext c; simp; rfl
  μIso_hom_natural_right X' f := by ext c; simp; rfl
  associativity X Y Z := by ext c; simp; rfl
  left_unitality X := by
    ext c
    simp only [Monoidal.tensorObj_obj, Monoidal.tensorUnit_obj, Monoidal.leftUnitor_hom_app,
      Iso.refl_hom, id_whiskerRight, Category.id_comp, NatTrans.comp_app,
      NatIso.ofComponents_hom_app, const_map_app]
    exact (Category.id_comp _).symm
  right_unitality X := by
    ext c
    simp only [Monoidal.tensorObj_obj, Monoidal.tensorUnit_obj, Monoidal.rightUnitor_hom_app,
      Iso.refl_hom, MonoidalCategory.whiskerLeft_id, Category.id_comp, NatTrans.comp_app,
      NatIso.ofComponents_hom_app, const_map_app]
    exact (Category.id_comp _).symm

instance : (const C : D ⥤ C ⥤ D).Monoidal :=
  (constCoreMonoidal C).toMonoidal

@[simp]
lemma const_ε : ε (const C : D ⥤ C ⥤ D) = 𝟙 _ := rfl

@[simp]
lemma const_η : η (const C : D ⥤ C ⥤ D) = 𝟙 _ := rfl

@[simp]
lemma const_μ_app (X Y : D) (c : C) : (μ (const C : D ⥤ C ⥤ D) X Y).app c = 𝟙 (X ⊗ Y) := rfl

@[simp]
lemma const_δ_app (X Y : D) (c : C) : (δ (const C : D ⥤ C ⥤ D) X Y).app c = 𝟙 (X ⊗ Y) := rfl

/-- The constant functor `D ⥤ C ⥤ D` into a functor category over a braided monoidal
category is braided: the braiding on the functor category is computed objectwise, and
the structure morphisms of `Functor.const C` have identity components. -/
instance [BraidedCategory D] : (const C : D ⥤ C ⥤ D).Braided where
  braided X Y := by
    ext c
    change 𝟙 _ ≫ (β_ X Y).hom = (β_ X Y).hom ≫ 𝟙 _
    simp

end Functor

end Const

section WhiskeringBraided

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Monoidal

variable [MonoidalCategory.{v₂} D] [BraidedCategory.{v₂} D]

@[simp]
theorem braiding_hom_app {F G : C ⥤ D} {X : C} :
    (β_ F G).hom.app X = (β_ (F.obj X) (G.obj X)).hom :=
  rfl

@[simp]
theorem braiding_inv_app {F G : C ⥤ D} {X : C} :
    (β_ F G).inv.app X = (β_ (F.obj X) (G.obj X)).inv :=
  rfl

end Monoidal

namespace Functor

/-- Precomposition with a functor is braided for the pointwise braidings on the
functor categories. -/
instance Braided.whiskeringLeft (E : Type u₃) [Category.{v₃} E] [MonoidalCategory E]
    [BraidedCategory E] (F : C ⥤ D) :
    ((whiskeringLeft C D E).obj F).Braided where
  braided G H := by
    ext X
    exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Whiskering on the right with a lax braided functor is lax braided for the pointwise
braidings on the functor categories. -/
instance LaxBraided.whiskeringRight (E : Type u₃) [Category.{v₃} E] [MonoidalCategory D]
    [MonoidalCategory E] [BraidedCategory D] [BraidedCategory E] (L : D ⥤ E) [L.LaxBraided] :
    ((whiskeringRight C D E).obj L).LaxBraided where
  braided G H := by ext X; exact Functor.LaxBraided.braided _ _

/-- Whiskering on the right with a braided functor is braided for the pointwise braidings
on the functor categories. -/
instance Braided.whiskeringRight (E : Type u₃) [Category.{v₃} E] [MonoidalCategory D]
    [MonoidalCategory E] [BraidedCategory D] [BraidedCategory E] (L : D ⥤ E) [L.Braided] :
    ((whiskeringRight C D E).obj L).Braided where
  braided G H := by ext X; exact Functor.LaxBraided.braided _ _

end Functor

end WhiskeringBraided

end CategoryTheory
