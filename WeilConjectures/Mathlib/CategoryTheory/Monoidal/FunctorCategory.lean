/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# The constant functor into a functor category is monoidal

When `C` is any category and `D` is a monoidal category, the functor category `C ⥤ D`
carries the pointwise monoidal structure (`CategoryTheory.Monoidal.functorCategoryMonoidal`).
The tensor unit and tensor products of constant functors are computed objectwise, so the
constant functor `Functor.const C : D ⥤ C ⥤ D` is a monoidal functor, with structure
isomorphisms whose components are identities. We record this as an instance
`(Functor.const C).Monoidal`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

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

end CategoryTheory.Functor
