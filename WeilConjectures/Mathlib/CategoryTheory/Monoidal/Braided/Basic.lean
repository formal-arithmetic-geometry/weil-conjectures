/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braided doctrinal adjunction

Let `adj : F ⊣ G` be an adjunction between braided monoidal categories, compatible with
the (lax) monoidal structures on `F` and `G` (`adj.IsMonoidal`).

If `F` is braided and `G` is lax monoidal, then `G` is lax braided: the lax monoidal
structure on the right adjoint automatically preserves the braiding. Conversely, if `F`
is monoidal and `G` is lax braided, then `F` is a braided functor: the strong monoidal
structure on the left adjoint automatically preserves the braiding. Both are instances
of doctrinal adjunction; the braided axiom for one adjoint follows from the one for the
other by transposition through the adjunction.

## Main definitions

- `CategoryTheory.Adjunction.rightAdjointLaxBraided`: the lax braided structure on the
  right adjoint of a braided functor.
- `CategoryTheory.Adjunction.leftAdjointBraided`: the braided structure on the left
  adjoint of a lax braided functor.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

section

variable [F.Braided] [G.LaxMonoidal] [adj.IsMonoidal]

/-- If `adj : F ⊣ G` is an adjunction between braided categories, `F` is braided, `G` is
lax monoidal, and the adjunction is compatible with the monoidal structures, then `G` is
lax braided: transposing the braided axiom for `F` through the adjunction yields the
braided axiom for `G`. -/
@[implicit_reducible]
def rightAdjointLaxBraided : G.LaxBraided where
  braided X Y := by
    apply (adj.homEquiv _ _).symm.injective
    rw [homEquiv_counit, homEquiv_counit, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc, counit_naturality,
      map_μ_comp_counit_app_tensor_assoc, map_μ_comp_counit_app_tensor,
      BraidedCategory.braiding_naturality, Functor.map_braiding, Category.assoc,
      Category.assoc, Functor.Monoidal.μ_δ_assoc]

end

section

variable [F.Monoidal] [G.LaxBraided] [adj.IsMonoidal]

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

end

end CategoryTheory.Adjunction
