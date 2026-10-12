/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Pullbacks preserved at every later stage of a filtered category colimit

Source: Stacks Project, Sites, Tag 09YL, pullback paragraph.
-/

@[expose] public section

universe u

open CategoryTheory.Limits

namespace CategoryTheory

/-- A stage pullback preserved by every transition out of that stage is preserved
by the canonical functor to a category whose object and arrow cocones are colimits.
Source: Stacks Project, Sites, Tag 09YL, pullback paragraph and its Hom calculation.
(blueprint: lem-weil-pbc-filtered-colimit-preserves-pullback)

Proof: Take the chosen limiting pullback cone at stage j. To prove its image is
limiting, fix a cone in the colimit category. Joint surjectivity of the object and
arrow colimits lifts its vertex and two legs to stages. Filteredness moves those
representatives and the original stage j to a common stage. Eventual equality in
the object colimit aligns the endpoints; eventual equality in the arrow colimit
makes the cone equation hold after another transition. The composite transition
out of j preserves the original pullback by assumption. Its universal property
therefore supplies a mediating arrow at that later stage. Its image in the
colimit gives the required factorization. For uniqueness, lift two proposed
mediating arrows to a common stage above j, align their endpoints, and enforce
both factorization equations there by eventual equality. The preserved pullback
at that stage identifies the arrows, hence their colimit images agree. This
proves that the canonical functor maps the chosen limiting cone to a limiting
cone; preservation of this limit follows by uniqueness of limiting cones. No
pullbacks elsewhere in the stage categories or in the colimit are needed. -/
theorem filteredColimit_preservesPullback
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (j : J) {X Y Z : F.obj j} (f : Y ⟶ X) (g : Z ⟶ X) [HasPullback f g]
    (hpres : ∀ (k : J) (a : j ⟶ k),
      PreservesLimit (cospan f g) (F.map a).toFunctor) :
    PreservesLimit (cospan f g) (V.ι.app j).toFunctor := by sorry

end CategoryTheory
