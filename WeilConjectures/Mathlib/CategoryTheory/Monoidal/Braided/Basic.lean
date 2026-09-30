/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The right adjoint of a braided functor is lax braided

Let `adj : F ⊣ G` be an adjunction between braided monoidal categories, where `F` is
braided, `G` is lax monoidal, and the adjunction is compatible with the (lax) monoidal
structures (`adj.IsMonoidal`). Then `G` is lax braided: the lax monoidal structure on the
right adjoint automatically preserves the braiding. This is an instance of doctrinal
adjunction; the braided axiom for `G` follows from the one for `F` by transposition
through the adjunction.

## Main definitions

- `CategoryTheory.Adjunction.rightAdjointLaxBraided`: the lax braided structure on the
  right adjoint of a braided functor.

## Main results

- `CategoryTheory.BraidedCategory.preservesColimitsOfShape_flip_curriedTensor_obj`: in a
  braided category, tensoring on the right with `X` preserves the colimits of shape `J` that
  tensoring on the left with `X` preserves, the two functors being identified by the braiding.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Braided] [G.LaxMonoidal] [adj.IsMonoidal]

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

end CategoryTheory.Adjunction

namespace CategoryTheory.BraidedCategory

open Limits MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {J : Type*} [Category* J]

/-- In a braided monoidal category, if tensoring on the left with any object preserves
colimits of shape `J`, then so does tensoring on the right, since the braiding identifies
`tensorLeft X` with `tensorRight X`. -/
instance preservesColimitsOfShape_flip_curriedTensor_obj
    [∀ X : C, PreservesColimitsOfShape J (tensorLeft X)] (X : C) :
    PreservesColimitsOfShape J ((curriedTensor C).flip.obj X) :=
  preservesColimitsOfShape_of_natIso (tensorLeftIsoTensorRight X)

end CategoryTheory.BraidedCategory
