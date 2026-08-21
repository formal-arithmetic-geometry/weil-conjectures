/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The left adjoint of a lax braided functor is braided

Let `adj : F ⊣ G` be an adjunction between braided monoidal categories, where `F` is
monoidal, `G` is lax braided, and the adjunction is compatible with the (lax) monoidal
structures (`adj.IsMonoidal`). Then `F` is a braided functor: the strong monoidal
structure on the left adjoint automatically preserves the braiding. This is an instance
of doctrinal adjunction; the braided axiom for `F` follows from the one for `G` by
transposition through the adjunction.

## Main definitions

- `CategoryTheory.Adjunction.leftAdjointBraided`: the braided structure on the left
  adjoint of a lax braided functor.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxBraided] [adj.IsMonoidal]

/-- If `adj : F ⊣ G` is an adjunction between braided categories, `F` is monoidal, `G` is
lax braided, and the adjunction is compatible with the monoidal structures, then `F` is
braided: transposing the braided axiom for `G` through the adjunction yields the braided
axiom for `F`. -/
@[implicit_reducible]
def leftAdjointBraided : F.Braided where
  braided X Y := by
    have key : F.map (β_ X Y).hom = δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X := by
      apply (adj.homEquiv _ _).injective
      rw [homEquiv_unit, homEquiv_unit, unit_naturality, Functor.map_comp, Functor.map_comp,
        unit_app_tensor_comp_map_δ_assoc, Functor.LaxBraided.braided_assoc,
        BraidedCategory.braiding_naturality_assoc, ← unit_app_tensor_comp_map_δ_assoc adj Y X,
        ← Functor.map_comp, Functor.Monoidal.δ_μ, Functor.map_id, Category.comp_id]
    rw [key, Functor.Monoidal.μ_δ_assoc]

end CategoryTheory.Adjunction
