/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism

/-!
# Derived limits of towers

We define derived limit triangles and derived limits of towers in a pretriangulated category.
-/

@[expose] public section

universe u v

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- The triangle `L ⟶ ∏ K ⟶ ∏ K ⟶ L⟦1⟧`, whose middle map is the transition endomorphism of the
tower `(K, f)`, is distinguished. -/
def IsDerivedLimitTriangle {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K : ℕ → C} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧) : Prop :=
  Triangle.mk p (towerTransitionEndomorphism f) δ ∈ distTriang C

/-- `L` is a derived limit of the tower `(K, f)`: there are maps `p` and `δ` such that
`L ⟶ ∏ K ⟶ ∏ K ⟶ L⟦1⟧` is a derived limit triangle. -/
def IsDerivedLimit {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {K : ℕ → C} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n) (L : C) : Prop :=
  ∃ (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧),
    IsDerivedLimitTriangle f L p δ

end CategoryTheory
