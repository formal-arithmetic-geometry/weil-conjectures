/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism

/-!
# Derived limits of inverse systems

Source: Stacks Project, Derived Categories, Definition 13.34.1 (Tag 08TC)
(blueprint: def-weil-derived-limit).

## Main definitions

- `CategoryTheory.IsDerivedLimitTriangle`: a specified Roos triangle is distinguished.
- `CategoryTheory.IsDerivedLimit`: an object admits a Roos triangle.
-/

@[expose] public section

universe u v

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- A specified triple `(K, p, δ)` is a derived limit triangle when its Roos triangle
`K ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ K⟦1⟧`, with middle arrow `1 - s`, is distinguished.
The shift `s` uses the transition maps `f n : K (n + 1) ⟶ K n`.
Stacks Project, Definition 13.34.1 (Tag 08TC)
(blueprint: def-weil-derived-limit). -/
def IsDerivedLimitTriangle {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K : ℕ → C} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧) : Prop :=
  Triangle.mk p (towerTransitionEndomorphism f) δ ∈ distTriang C

/-- An object is a derived (homotopy) limit of the inverse system if there are maps
`p` and `δ` making its Roos triangle distinguished. No object or maps are chosen.
Stacks Project, Definition 13.34.1 (Tag 08TC)
(blueprint: def-weil-derived-limit). -/
def IsDerivedLimit {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K : ℕ → C} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n) (L : C) : Prop :=
  ∃ (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧),
    IsDerivedLimitTriangle f L p δ

end CategoryTheory
