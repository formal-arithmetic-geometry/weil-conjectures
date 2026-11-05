/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Whiskering with an object isomorphic to the unit

In a monoidal category, whiskering with an object `B ≅ 𝟙_` is a bijection on morphisms. This is
used to eliminate Tate twists over a separably closed field, where the twisting objects are
isomorphic to the unit.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C]

/-- Composing on both sides with isomorphisms is a bijection on morphisms. -/
lemma _root_.CategoryTheory.bijective_conj {W W' Z Z' : C} (e : W ≅ W') (f : Z ≅ Z') :
    Function.Bijective (fun z : W' ⟶ Z ↦ e.hom ≫ z ≫ f.hom) :=
  ⟨fun a b hab ↦ by simpa using congrArg (fun z ↦ e.inv ≫ z ≫ f.inv) hab,
    fun z ↦ ⟨e.inv ≫ z ≫ f.inv, by simp⟩⟩

variable [MonoidalCategory C]

end CategoryTheory.MonoidalCategory
