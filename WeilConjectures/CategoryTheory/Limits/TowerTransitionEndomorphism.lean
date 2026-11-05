/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The transition endomorphism of a tower product

Source: Stacks Project, Derived Categories, Definition 13.34.1 (Tag 08TC)
(blueprint: def-weil-tower-transition-endomorphism).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

/-- The shift on the product of an inverse system: its `n`-th component is the
`(n + 1)`-st projection followed by the transition map. Stacks, Tag 08TC
(blueprint: def-weil-tower-transition-endomorphism). -/
noncomputable def towerProductShift {C : Type u} [Category.{v} C] {K : ℕ → C}
    [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n) : ∏ᶜ K ⟶ ∏ᶜ K :=
  Pi.lift (fun n => Pi.π K (n + 1) ≫ f n)

/-- The transition endomorphism `1 - s` of the product of an inverse system.
Its `n`-th component is `pr n - pr (n + 1) ≫ f n`. Stacks, Tag 08TC
(blueprint: def-weil-tower-transition-endomorphism). -/
noncomputable def towerTransitionEndomorphism {C : Type u} [Category.{v} C]
    [Preadditive C] {K : ℕ → C} [HasProduct K]
    (f : ∀ n, K (n + 1) ⟶ K n) : ∏ᶜ K ⟶ ∏ᶜ K :=
  𝟙 _ - towerProductShift f

/-- The projection equations uniquely characterize `1 - s`: compose the defining
difference with each projection, then use product extensionality. Stacks, Tag 08TC
(blueprint: def-weil-tower-transition-endomorphism). -/
theorem towerTransitionEndomorphism_eq_iff {C : Type u} [Category.{v} C]
    [Preadditive C] {K : ℕ → C} [HasProduct K]
    (f : ∀ n, K (n + 1) ⟶ K n) (t : ∏ᶜ K ⟶ ∏ᶜ K) :
    t = towerTransitionEndomorphism f ↔
      ∀ n, t ≫ Pi.π K n = Pi.π K n - Pi.π K (n + 1) ≫ f n := by
  constructor
  · intro h n
    subst t
    simp [towerTransitionEndomorphism, towerProductShift]
  · intro h
    apply Pi.hom_ext
    intro n
    simpa [towerTransitionEndomorphism, towerProductShift] using h n

theorem towerTransitionEndomorphism_natural_backward {C : Type u} [Category.{v} C]
    [Preadditive C] {K K' : ℕ → C} [HasProduct K] [HasProduct K']
    (f : ∀ n, K (n + 1) ⟶ K n) (f' : ∀ n, K' (n + 1) ⟶ K' n)
    (φ : ∀ n, K n ⟶ K' n)
    (h : ∀ n, φ (n + 1) ≫ f' n = f n ≫ φ n) :
    Limits.Pi.map φ ≫ towerTransitionEndomorphism f' =
      towerTransitionEndomorphism f ≫ Limits.Pi.map φ := by
  apply Pi.hom_ext
  intro n
  simp [towerTransitionEndomorphism, towerProductShift, Pi.map_π,
    Category.assoc, h n]

end CategoryTheory
