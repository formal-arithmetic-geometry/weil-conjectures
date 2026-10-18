/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF stage-2 worker Q112
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Inserters of parallel functors

Source: Ching--Riehl, *Coalgebraic models for combinatorial model categories*, Appendix A,
Definition A.3, printed p. 10 (blueprint: def-coef-inserter).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-- The inserter of parallel functors: an object with an arrow between its two images.
Source: Ching--Riehl, Appendix A, Definition A.3 (blueprint: def-coef-inserter). -/
structure Inserter {A : Type u₁} [Category.{v₁} A] {B : Type u₂}
    [Category.{v₂} B] (F G : A ⥤ B) where
  /-- The underlying object of the source category. -/
  obj : A
  /-- The specified arrow between its two images. -/
  hom : F.obj obj ⟶ G.obj obj

namespace Inserter

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {F G : A ⥤ B}

/-- The compatible arrows between two inserter objects.
Source: Ching--Riehl, Appendix A, Definition A.3 (blueprint: def-coef-inserter). -/
@[ext]
structure Hom (X Y : Inserter F G) where
  /-- The underlying arrow in the source category. -/
  hom : X.obj ⟶ Y.obj
  /-- The naturality square commutes. -/
  w : F.map hom ≫ Y.hom = X.hom ≫ G.map hom

/-- The category of inserter objects, with identities and composition from the source category.
Source: Ching--Riehl, Appendix A, Definition A.3 (blueprint: def-coef-inserter). -/
instance category : Category (Inserter F G) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 X.obj, by simp⟩
  comp {X} {Y} {Z} f g := ⟨f.hom ≫ g.hom, by
    calc
      F.map (f.hom ≫ g.hom) ≫ Z.hom = F.map f.hom ≫ (F.map g.hom ≫ Z.hom) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = F.map f.hom ≫ (Y.hom ≫ G.map g.hom) := by rw [g.w]
      _ = (F.map f.hom ≫ Y.hom) ≫ G.map g.hom := by simp only [Category.assoc]
      _ = (X.hom ≫ G.map f.hom) ≫ G.map g.hom := by rw [f.w]
      _ = X.hom ≫ G.map (f.hom ≫ g.hom) := by
        simp only [Functor.map_comp, Category.assoc]⟩
  id_comp f := by apply Hom.ext; simp
  comp_id f := by apply Hom.ext; simp
  assoc f g h := by apply Hom.ext; simp [Category.assoc]

/-- The canonical inserter projection, forgetting the specified arrow.
Source: Ching--Riehl, Appendix A, Definition A.3 (blueprint: def-coef-inserter). -/
def forget (F G : A ⥤ B) : Inserter F G ⥤ A where
  obj X := X.obj
  map f := f.hom

end Inserter

end CategoryTheory
