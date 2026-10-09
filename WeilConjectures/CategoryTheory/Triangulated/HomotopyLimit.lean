/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Homotopy limits of towers in a pretriangulated category

Let `F : ℕᵒᵖ ⥤ C` be a tower `⋯ ⟶ F₂ ⟶ F₁ ⟶ F₀` in a pretriangulated category. A categorical
limit of `F` rarely exists in a triangulated category, and when it does it is not the derived
limit. The *homotopy limit* `R lim F` is instead characterised, up to non-unique isomorphism,
by the Milnor (or Roos) triangle

```
  R lim F ⟶ ∏ₙ Fₙ ──1 - t──▶ ∏ₙ Fₙ ⟶ (R lim F)[1]
```

where `t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` has components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`. In the derived category of an
abelian category with exact countable products, such as sheaves on a replete topos, this is
the derived functor of `lim` applied to the tower.

## Main definitions

- `CategoryTheory.Pretriangulated.towerShift`: the map `t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ`.
- `CategoryTheory.Pretriangulated.IsHomotopyLimit`: a cone over a tower is a homotopy limit
  cone if its legs fit into a distinguished Milnor triangle.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The transition endomorphism `t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` of a product of the terms of a tower
`F : ℕᵒᵖ ⥤ C`, with components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`. -/
noncomputable def towerShift {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)}
    (hP : IsLimit P) : P.pt ⟶ P.pt :=
  Fan.IsLimit.lift hP fun n ↦ P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op

/-- A cone `c` over a tower `F : ℕᵒᵖ ⥤ C` is a *homotopy limit* cone if, for a product
`∏ₙ Fₙ`, the Milnor triangle

```
  c.pt ──(c.π n)ₙ──▶ ∏ₙ Fₙ ──1 - t──▶ ∏ₙ Fₙ ──δ──▶ c.pt⟦1⟧
```

is distinguished for some `δ`, where `t` is `towerShift`. The point of a homotopy limit cone is
then the derived limit `R lim F`, determined up to non-unique isomorphism. -/
def IsHomotopyLimit {F : ℕᵒᵖ ⥤ C} (c : Cone F) : Prop :=
  ∃ (P : Fan fun n : ℕ ↦ F.obj (op n)) (hP : IsLimit P) (δ : P.pt ⟶ c.pt⟦(1 : ℤ)⟧),
    Triangle.mk (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) (𝟙 P.pt - towerShift hP) δ ∈
      distTriang C

end CategoryTheory.Pretriangulated
