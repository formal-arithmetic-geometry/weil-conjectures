/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Left adjoints at objects where the unit is invertible

For an adjunction `L ⊣ R` and an object `B` at which the unit `η_B : B ⟶ R (L B)` is an
isomorphism, `L` is bijective on morphisms `A ⟶ B` into `B`: under the adjunction bijection,
`L f` corresponds to `f ≫ η_B`.

## Main statements

- `CategoryTheory.Adjunction.map_bijective_of_isIso_unit_app`
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}

/-- Under the adjunction bijection, `L f` corresponds to `f ≫ η_B`. -/
lemma homEquiv_map (adj : L ⊣ R) {A B : C} (f : A ⟶ B) :
    adj.homEquiv A (L.obj B) (L.map f) = f ≫ adj.unit.app B := by
  rw [adj.homEquiv_unit, adj.unit_naturality]

/-- If the unit `η_B` of `L ⊣ R` is an isomorphism, then `L` is bijective on morphisms with
target `B`. -/
lemma map_bijective_of_isIso_unit_app (adj : L ⊣ R) (A : C) {B : C}
    [IsIso (adj.unit.app B)] :
    Function.Bijective (L.map : (A ⟶ B) → (L.obj A ⟶ L.obj B)) := by
  have h : (L.map : (A ⟶ B) → (L.obj A ⟶ L.obj B)) =
      (adj.homEquiv A (L.obj B)).symm ∘ fun f ↦ f ≫ adj.unit.app B := by
    ext1 f
    exact ((adj.homEquiv _ _).symm_apply_apply _).symm.trans (congrArg _ (homEquiv_map adj f))
  rw [h]
  exact (adj.homEquiv A (L.obj B)).symm.bijective.comp
    ((asIso (adj.unit.app B)).homToEquiv (Z := A)).bijective

end CategoryTheory.Adjunction
