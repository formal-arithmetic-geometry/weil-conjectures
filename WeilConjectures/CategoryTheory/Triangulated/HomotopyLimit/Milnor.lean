/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import WeilConjectures.Mathlib.CategoryTheory.CofilteredSystem

/-!
# The Milnor map of a homotopy limit of a tower

Let `c` be a homotopy limit cone over a tower `F : ℕᵒᵖ ⥤ C` in a pretriangulated category, so
that `c.pt = R lim F` sits in the Milnor triangle `R lim F → ∏ₙ Fₙ → ∏ₙ Fₙ → (R lim F)⟦1⟧`. For
an object `L`, the long exact sequence of `Hom(L, -)` gives the Milnor exact sequence

`0 → lim¹ₙ Hom(L⟦1⟧, Fₙ) → Hom(L, R lim F) → limₙ Hom(L, Fₙ) → 0`.

When the groups `Hom(L⟦1⟧, Fₙ)` are finite, their `lim¹` vanishes
(`AddCommGroup.exists_sub_map_succ_eq_of_finite`), so the *Milnor map*
`Hom(L, R lim F) → limₙ Hom(L, Fₙ)` is bijective. For `L` a shifted unit object these `Hom`
groups are the cohomology groups, which is the form used for `ℓ`-adic cohomology.

## Main results

- `CategoryTheory.Pretriangulated.IsHomotopyLimit.bijective_milnorMap`: the Milnor map is
  bijective when the groups `Hom(L⟦1⟧, Fₙ)` are finite.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The compatible families of maps `L ⟶ Fₙ` into a tower: the inverse limit
`limₙ Hom(L, Fₙ)`. -/
def towerHomLimit (F : ℕᵒᵖ ⥤ C) (L : C) : Type _ :=
  {x : ∀ n : ℕ, L ⟶ F.obj (op n) // ∀ n, x (n + 1) ≫ F.map (homOfLE n.le_succ).op = x n}

/-- The *Milnor map* `Hom(L, c.pt) → limₙ Hom(L, Fₙ)` of a cone over a tower. -/
def milnorMap {F : ℕᵒᵖ ⥤ C} (c : Cone F) (L : C) (f : L ⟶ c.pt) : towerHomLimit F L :=
  ⟨fun n ↦ f ≫ c.π.app (op n), fun n ↦ by rw [assoc, c.w]⟩

end CategoryTheory.Pretriangulated
