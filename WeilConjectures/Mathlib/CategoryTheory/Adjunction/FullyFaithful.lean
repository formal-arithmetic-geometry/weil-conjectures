/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# The unit of an adjunction whose counit is an isomorphism

For an adjunction `L ⊣ R` whose counit is an isomorphism at `L X`, the two maps
`R (L X) ⟶ R (L (R (L X)))` given by `R (L (η X))` and by `η (R (L X))` agree: both are right
inverse to the isomorphism `R (ε (L X))`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

/-- For an adjunction whose counit is an isomorphism at `L X`, the image of the unit at `X`
under `L ⋙ R` is the unit at `R (L X)`. -/
lemma map_map_unit_app_eq {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) (X : C) [IsIso (adj.counit.app (L.obj X))] :
    R.map (L.map (adj.unit.app X)) = adj.unit.app (R.obj (L.obj X)) := by
  rw [← cancel_mono (R.map (adj.counit.app (L.obj X)))]
  simp [← R.map_comp]

end CategoryTheory.Adjunction
