/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! Intermediate finite-lifting statement for filtered category colimits. -/

@[expose] public section

universe u

open CategoryTheory.Limits

namespace CategoryTheory

/-- Joint monicity of the image of the two stable stage pullback projections.
Source: Stacks Project, Sites, Tag 09YL, pullback paragraph and Hom calculation.
(blueprint: lem-weil-pbc-filtered-colimit-pullback-hom-ext)

Proof: Lift the two proposed arrows to stage arrows using joint surjectivity
of the arrow colimit. Move their stages and j to a common upper stage. Eventual
equality in the object colimit aligns their sources with each other and their
targets with the transitioned pullback object. After these identifications,
their composites with the transitioned projections have equal colimit images.
Use eventual equality in the arrow colimit twice to enforce these two equalities
at a later stage. The pullback remains preserved by the composite transition
out of j, so its two projections are jointly monic there. The two stage arrows
are equal, and applying the cocone functor proves equality of the original
arrows. This uses no existence of a factorization for an arbitrary cone. -/
theorem filteredColimit_pullback_hom_ext
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (j : J) {X Y Z : F.obj j} (f : Y ⟶ X) (g : Z ⟶ X) [HasPullback f g]
    (hpres : ∀ (k : J) (a : j ⟶ k),
      PreservesLimit (cospan f g) (F.map a).toFunctor) :
    ∀ (W : V.pt) (a b : W ⟶ (V.ι.app j).toFunctor.obj (pullback f g)),
      a ≫ (V.ι.app j).toFunctor.map (pullback.fst f g) =
        b ≫ (V.ι.app j).toFunctor.map (pullback.fst f g) →
      a ≫ (V.ι.app j).toFunctor.map (pullback.snd f g) =
        b ≫ (V.ι.app j).toFunctor.map (pullback.snd f g) → a = b := by sorry

end CategoryTheory
