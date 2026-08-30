/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!

# Transposing the image of a counit under a composed adjunction

Let `adj : L ⊣ R` and `adjS : S ⊣ S'` be adjunctions with `L : D ⥤ C`, `R : C ⥤ D`,
`S : C ⥤ E` and `S' : E ⥤ C`, so that `adj.comp adjS : L ⋙ S ⊣ S' ⋙ R`. For an object `Y`
of `C` the counit `adj.counit.app Y : L (R Y) ⟶ Y` gives, after applying `S`, a morphism
`S (L (R Y)) ⟶ S Y` out of `(L ⋙ S) (R Y)`, and this file computes its transpose along
`adj.comp adjS`: it is the image under `R` of the transpose along `adjS`.

## Main results

- `CategoryTheory.Adjunction.comp_homEquiv_map_counit_app_comp`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
  {S : C ⥤ E} {S' : E ⥤ C} (adjS : S ⊣ S')

/-- The transpose along `adj.comp adjS : L ⋙ S ⊣ S' ⋙ R` of the morphism
`S (ε_Y) ≫ g : S (L (R Y)) ⟶ M` is the image under `R` of the transpose of `g` along
`adjS`, where `ε` is the counit of `adj : L ⊣ R`.

This is the triangle identity of `adj` read through the naturality of the unit of `adjS`. -/
theorem comp_homEquiv_map_counit_app_comp (Y : C) (M : E) (g : S.obj Y ⟶ M) :
    (adj.comp adjS).homEquiv (R.obj Y) M (S.map (adj.counit.app Y) ≫ g) =
      R.map (adjS.homEquiv Y M g) := by
  have h := adjS.unit.naturality (adj.counit.app Y)
  dsimp at h
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
  rw [S'.map_comp, ← Category.assoc, ← h, Category.assoc, R.map_comp, ← Category.assoc,
    adj.right_triangle_components, Category.id_comp]

end CategoryTheory.Adjunction
