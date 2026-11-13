/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Limits.Types.Images

/-!
# Nonempty limit of a Mittag-Leffler tower of sets

## Implementation details

The tower `(E_i, f_i)_{i ≥ 1}` is a functor `F : ℕᵒᵖ ⥤ Type u`, the index `n : ℕ` denoting
the positive index `n + 1`. The Mittag-Leffler condition is Mathlib's `Functor.IsMittagLeffler`
and the limit is the set `F.sections` of compatible families.

## References

* [Stacks, Algebra, Tag 0597](https://stacks.math.columbia.edu/tag/0597), with Tags 0595
  and 0596
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.Functor

/-- A tower of nonempty sets satisfying the Mittag-Leffler condition has a nonempty limit.
(Stacks, Tags 0597, 0595, 0596) -/
theorem nonempty_sections_of_isMittagLeffler (F : ℕᵒᵖ ⥤ Type u)
    [∀ n : ℕᵒᵖ, Nonempty (F.obj n)] (hF : F.IsMittagLeffler) :
    F.sections.Nonempty := by
  let G := F.toEventualRanges
  have hsurj : ∀ n, Function.Surjective
      (G.map (CategoryTheory.homOfLE (Nat.le_succ n)).op) := by
    intro n
    exact F.surjective_toEventualRanges hF _
  have hproj : Function.Surjective
      ((CategoryTheory.Limits.Types.limitCone G).π.app ⟨0⟩) :=
    CategoryTheory.Limits.Types.surjective_π_app_zero_of_surjective_map
      (CategoryTheory.Limits.Types.limitConeIsLimit G) hsurj
  obtain ⟨x, hx⟩ := hproj (Classical.choice (F.toEventualRanges_nonempty hF ⟨0⟩))
  let y := (F.toEventualRangesSectionsEquiv) x
  exact ⟨y, y.property⟩

end CategoryTheory.Functor
