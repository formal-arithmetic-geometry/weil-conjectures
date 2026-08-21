/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braided mates: braidedness of adjoints of (lax) braided functors

Let `adj : F ⊣ G` be an adjunction between braided monoidal categories which is
compatible with given (lax) monoidal structures on `F` and `G` (`adj.IsMonoidal`).
This is an instance of doctrinal adjunction: braidedness on one side of the adjunction
transposes to the other side.

We also prove that braidedness descends along an essentially surjective braided functor:
if `H : C ⥤ D` is braided and essentially surjective, `F : D ⥤ E` is lax monoidal and the
composite `H ⋙ F` is lax braided (with respect to the composite lax monoidal structure),
then `F` is lax braided.

## Main definitions

- `CategoryTheory.Adjunction.leftAdjointBraided`: if `F` is monoidal and `G` is lax
  braided, then `F` is braided.
- `CategoryTheory.Adjunction.rightAdjointLaxBraided`: if `F` is braided and `G` is lax
  monoidal, then `G` is lax braided.
- `CategoryTheory.Functor.LaxBraided.ofPrecompEssSurj` (and the strong version
  `CategoryTheory.Functor.Braided.ofPrecompEssSurj`): braidedness descends along an
  essentially surjective braided functor.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Adjunction

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

section LeftAdjoint

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

end LeftAdjoint

section RightAdjoint

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

end RightAdjoint

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]

/-- Braidedness descends along an essentially surjective braided functor: if `H : C ⥤ D`
is braided and essentially surjective, `F : D ⥤ E` is lax monoidal, and the composite
`H ⋙ F` satisfies the lax braided axiom with respect to the composite lax monoidal
structure, then `F` is lax braided. -/
@[implicit_reducible]
def LaxBraided.ofPrecompEssSurj (H : C ⥤ D) (F : D ⥤ E) [H.Braided] [H.EssSurj]
    [F.LaxMonoidal]
    (h : ∀ X Y : C, μ (H ⋙ F) X Y ≫ (H ⋙ F).map (β_ X Y).hom =
      (β_ ((H ⋙ F).obj X) ((H ⋙ F).obj Y)).hom ≫ μ (H ⋙ F) Y X) :
    F.LaxBraided where
  braided X Y := by
    -- the braided axiom for `F` at objects in the image of `H`
    have key : ∀ X' Y' : C,
        μ F (H.obj X') (H.obj Y') ≫ F.map (β_ (H.obj X') (H.obj Y')).hom =
          (β_ (F.obj (H.obj X')) (F.obj (H.obj Y'))).hom ≫ μ F (H.obj Y') (H.obj X') := by
      intro X' Y'
      have h' := h X' Y'
      simp only [comp_map, comp_μ, Category.assoc] at h'
      rw [← F.map_comp, Functor.LaxBraided.braided, F.map_comp] at h'
      rw [← cancel_mono (F.map (μ H Y' X'))]
      simp only [Category.assoc]
      exact h'
    -- transport along the isomorphisms `H.obj (H.objPreimage _) ≅ _`
    rw [← cancel_epi
      (F.map (H.objObjPreimageIso X).hom ⊗ₘ F.map (H.objObjPreimageIso Y).hom),
      μ_natural_assoc, ← F.map_comp, BraidedCategory.braiding_naturality, F.map_comp,
      reassoc_of% key (H.objPreimage X) (H.objPreimage Y),
      BraidedCategory.braiding_naturality_assoc, μ_natural]

/-- Braidedness descends along an essentially surjective braided functor: if `H : C ⥤ D`
is braided and essentially surjective, `F : D ⥤ E` is monoidal, and the composite `H ⋙ F`
satisfies the lax braided axiom with respect to the composite lax monoidal structure,
then `F` is braided. -/
@[implicit_reducible]
def Braided.ofPrecompEssSurj (H : C ⥤ D) (F : D ⥤ E) [H.Braided] [H.EssSurj] [F.Monoidal]
    (h : ∀ X Y : C, μ (H ⋙ F) X Y ≫ (H ⋙ F).map (β_ X Y).hom =
      (β_ ((H ⋙ F).obj X) ((H ⋙ F).obj Y)).hom ≫ μ (H ⋙ F) Y X) :
    F.Braided where
  braided := (LaxBraided.ofPrecompEssSurj H F h).braided

end CategoryTheory.Functor
