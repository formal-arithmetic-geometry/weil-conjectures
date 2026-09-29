/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Currying in a preadditive monoidal closed category

In a monoidal closed category `C` whose monoidal structure is compatible with a preadditive
structure (`MonoidalPreadditive C`), the internal hom functors `ihom A` are additive, and
currying and uncurrying are compatible with sums, differences and multiplication by units
of `ℤ`.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] {A B X Y : C}

instance (A : C) : (ihom A).Additive := (ihom.adjunction A).right_adjoint_additive

lemma uncurry_add (f g : X ⟶ (ihom A).obj Y) : uncurry (f + g) = uncurry f + uncurry g := by
  simp [uncurry_eq]

lemma uncurry_sub (f g : X ⟶ (ihom A).obj Y) : uncurry (f - g) = uncurry f - uncurry g := by
  simp only [uncurry_eq]
  rw [show A ◁ (f - g) = (tensorLeft A).map (f - g) from rfl, Functor.map_sub]
  simp

lemma uncurry_units_smul (k : ℤˣ) (f : X ⟶ (ihom A).obj Y) :
    uncurry (k • f) = k • uncurry f := by
  simp only [uncurry_eq]
  rw [show A ◁ (k • f) = (tensorLeft A).map (k • f) from rfl, Units.smul_def,
    Functor.map_zsmul]
  simp [Units.smul_def]

lemma curry_add (f g : A ⊗ X ⟶ Y) : curry (f + g) = curry f + curry g :=
  uncurry_injective (by simp [uncurry_add])

lemma curry_sub (f g : A ⊗ X ⟶ Y) : curry (f - g) = curry f - curry g :=
  uncurry_injective (by simp [uncurry_sub])

lemma curry_units_smul (k : ℤˣ) (f : A ⊗ X ⟶ Y) : curry (k • f) = k • curry f :=
  uncurry_injective (by simp [uncurry_units_smul])

@[simp]
lemma pre_zero_app (X : C) : (pre (0 : B ⟶ A)).app X = 0 :=
  uncurry_injective (by simp [uncurry_eq])

end CategoryTheory.MonoidalClosed
