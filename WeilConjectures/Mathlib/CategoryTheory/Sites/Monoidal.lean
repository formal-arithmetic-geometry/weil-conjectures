/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# The constant sheaf functor is monoidal

For a site `(C, J)` and a monoidal category `A` such that `Sheaf J A` carries the
localized monoidal category structure `Sheaf.monoidalCategory`, the constant sheaf
functor `constantSheaf J A : A ⥤ Sheaf J A` is monoidal: it is the composition of the
constant presheaf functor (monoidal for the pointwise monoidal structure on presheaves,
see `WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory`) with the
sheafification functor `presheafToSheaf J A` (monoidal by the monoidal localization
theory, see `Mathlib.CategoryTheory.Sites.Monoidal`).

Consequently the constant sheaf of an object with a (left/right) dual has a (left/right)
dual, given by the constant sheaf of the dual
(`CategoryTheory.constantSheafObjHasRightDual`,
`CategoryTheory.constantSheafObjHasLeftDual`).

This file imports both `Mathlib.CategoryTheory.Sites.ConstantSheaf` and
`Mathlib.CategoryTheory.Sites.Monoidal` since neither imports the other.
-/

@[expose] public section

universe v₁ v₃ u₁ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A]
  [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

noncomputable instance : (constantSheaf J A).Monoidal :=
  inferInstanceAs (Functor.const Cᵒᵖ ⋙ presheafToSheaf J A).Monoidal

/-- The constant sheaf of an object with a right dual has a right dual, given by the
constant sheaf of the dual, since the constant sheaf functor is monoidal. -/
@[implicit_reducible]
noncomputable def constantSheafObjHasRightDual (X : A) [HasRightDual X] :
    HasRightDual ((constantSheaf J A).obj X) :=
  HasRightDual.map (constantSheaf J A) X

/-- The constant sheaf of an object with a left dual has a left dual, given by the
constant sheaf of the dual, since the constant sheaf functor is monoidal. -/
@[implicit_reducible]
noncomputable def constantSheafObjHasLeftDual (Y : A) [HasLeftDual Y] :
    HasLeftDual ((constantSheaf J A).obj Y) :=
  HasLeftDual.map (constantSheaf J A) Y

end CategoryTheory
