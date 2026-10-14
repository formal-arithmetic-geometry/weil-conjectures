/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Filtered objects in an abelian category

A *decreasing filtration* of an object `A` of an abelian category is a family of subobjects
`Fⁿ A ⊆ A`, `n ∈ ℤ`, with `Fⁿ⁺¹ A ⊆ Fⁿ A`. Its *graded pieces* are `grⁿ A = Fⁿ A / Fⁿ⁺¹ A`. The
image of a filtration of `A` along a morphism `A ⟶ B` is a filtration of `B`.

## Main definitions

- `CategoryTheory.DecreasingFiltration`: decreasing filtrations of an object.
- `CategoryTheory.DecreasingFiltration.gr`: the graded pieces.
- `CategoryTheory.DecreasingFiltration.IsFiniteSeparated`: finite separated filtrations.
- `CategoryTheory.DecreasingFiltration.image`: the image filtration.
- `CategoryTheory.DecreasingFiltration.IsFinite`: finite filtrations.
- `CategoryTheory.FilteredObject`: objects equipped with a decreasing filtration.
- `CategoryTheory.FilteredObject.Hom`: morphisms of filtered objects.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an abelian category, precomposing with an epimorphism does not change the image. -/
lemma imageSubobject_comp_eq_of_epi {X' X Y : C} (h : X' ⟶ X) [Epi h] (f : X ⟶ Y) :
    imageSubobject (h ≫ f) = imageSubobject f := by
  refine le_antisymm (imageSubobject_comp_le h f) ?_
  have : IsIso (Subobject.ofLE _ _ (imageSubobject_comp_le h f)) :=
    isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ (imageSubobject_comp_le h f))) (by simp)

variable (A : C)

/-- A *decreasing filtration* `F` of an object `A` of an abelian category: subobjects
`Fⁿ A ⊆ A` for `n ∈ ℤ` with `Fⁿ⁺¹ A ⊆ Fⁿ A`. A *filtered object* is a pair `(A, F)`.

(blueprint: `def-sp-filtration`) -/
structure DecreasingFiltration where
  /-- The subobject `Fⁿ A`. -/
  F : ℤ → Subobject A
  F_succ_le (n : ℤ) : F (n + 1) ≤ F n

namespace DecreasingFiltration

variable {A} (F : DecreasingFiltration A)

omit [Abelian C] in
lemma antitone : Antitone F.F :=
  antitone_int_of_succ_le F.F_succ_le

/-- The graded piece `grⁿ A = Fⁿ A / Fⁿ⁺¹ A` of a filtered object.

(blueprint: `def-sp-filtration`) -/
noncomputable def gr (n : ℤ) : C :=
  cokernel (Subobject.ofLE _ _ (F.F_succ_le n))

/-- A filtration is *finite and separated* if `F⁰ A = A`, `Fᴺ A = 0` for some `N`, and the
intersection of all `Fⁿ A` is `0`.

(blueprint: `def-sp-filtration`) -/
def IsFiniteSeparated : Prop :=
  F.F 0 = ⊤ ∧ (∃ N, F.F N = ⊥) ∧ ∀ P : Subobject A, (∀ n, P ≤ F.F n) → P = ⊥

/-- The *image filtration* on `B` of a filtration `F` of `A` along a morphism `φ : A ⟶ B`:
`Fⁿ B = im (Fⁿ A ⟶ B)`.

(blueprint: `def-sp-image-filtration`) -/
noncomputable def image {B : C} (φ : A ⟶ B) : DecreasingFiltration B where
  F n := imageSubobject ((F.F n).arrow ≫ φ)
  F_succ_le n := by
    rw [← Subobject.ofLE_arrow (F.F_succ_le n), Category.assoc]
    exact imageSubobject_comp_le _ _

lemma image_F {B : C} (φ : A ⟶ B) (n : ℤ) :
    (F.image φ).F n = imageSubobject ((F.F n).arrow ≫ φ) :=
  rfl

/-- A filtration is *finite* if `Fⁿ A = A` and `Fᵐ A = 0` for some `n` and `m`; this is weaker
than (implied by) `DecreasingFiltration.IsFiniteSeparated`.

(blueprint: `def-sp-filtration`) -/
def IsFinite : Prop :=
  ∃ n m : ℤ, F.F n = ⊤ ∧ F.F m = ⊥

end DecreasingFiltration

variable (C) in
/-- A *filtered object*: an object of an abelian category with a decreasing `ℤ`-filtration.

(blueprint: `def-sp-filtration`) -/
structure FilteredObject where
  /-- The underlying object. -/
  obj : C
  /-- The decreasing filtration of the underlying object. -/
  filtration : DecreasingFiltration obj

namespace FilteredObject

/-- A morphism of filtered objects: a morphism compatible with the filtrations, i.e. mapping
`Fⁱ A` into `Fⁱ B` for every `i`.

(blueprint: `def-sp-filtration`) -/
structure Hom (A B : FilteredObject C) where
  /-- The underlying morphism. -/
  hom : A.obj ⟶ B.obj
  /-- The underlying morphism maps `Fⁱ A` into `Fⁱ B` for every `i`. -/
  preserves : ∀ i : ℤ, ∃ lift : (A.filtration.F i : C) ⟶ (B.filtration.F i : C),
    lift ≫ (B.filtration.F i).arrow = (A.filtration.F i).arrow ≫ hom

end FilteredObject

end CategoryTheory
