/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The right adjoint of a braided functor is lax braided

Let `adj : F ⊣ G` be an adjunction between braided monoidal categories, where `F` is
monoidal and lax braided (hence braided), `G` is lax monoidal, and the adjunction is
compatible with the (lax) monoidal structures (`adj.IsMonoidal`). Then `G` is lax
braided: the lax monoidal structure on the right adjoint automatically preserves the
braiding. This is an instance of doctrinal adjunction; the braided axiom for `G` follows
from the one for `F` by transposition through the adjunction.

## Main definitions

- `CategoryTheory.Adjunction.rightAdjointLaxBraided`: the lax braided structure on the
  right adjoint of a braided functor.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]

namespace Functor.Braided

variable (F : C ⥤ D) [F.Braided]

/-- The braided axiom of a braided functor, stated for the inverse tensorator `δ`
instead of the tensorator `μ`. -/
@[reassoc]
lemma δ_braiding (X Y : C) :
    δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom = F.map (β_ X Y).hom ≫ δ F Y X := by
  rw [← cancel_epi (μ F X Y), Functor.Monoidal.μ_δ_assoc, LaxBraided.braided_assoc,
    Functor.Monoidal.μ_δ, Category.comp_id]

end Functor.Braided

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Braided] [G.LaxMonoidal]
  [adj.IsMonoidal]

/-- If `adj : F ⊣ G` is an adjunction between braided categories, `F` is braided,
`G` is lax monoidal, and the adjunction is compatible with the monoidal structures,
then `G` is lax braided: transposing the braided axiom for `F` through the adjunction
yields the braided axiom for `G`. -/
@[implicit_reducible]
def rightAdjointLaxBraided : G.LaxBraided where
  braided X Y := by
    apply (adj.homEquiv _ _).symm.injective
    simp only [homEquiv_counit, Functor.map_comp, Category.assoc]
    rw [counit_naturality, map_μ_comp_counit_app_tensor_assoc,
      BraidedCategory.braiding_naturality, Functor.Braided.δ_braiding_assoc,
      map_μ_comp_counit_app_tensor]

end Adjunction

end CategoryTheory
