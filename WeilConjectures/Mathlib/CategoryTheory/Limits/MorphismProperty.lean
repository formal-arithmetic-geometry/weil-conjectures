/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

/-!
# Left Kan extension along base change on slices of a morphism property

The slice `P.Over ⊤ Y` of a category with pullbacks has finite limits and base change
`P.Over ⊤ Y ⥤ P.Over ⊤ X` along an arbitrary morphism `f : X ⟶ Y` preserves them, hence
base change is representably flat
(`CategoryTheory.MorphismProperty.Over.representablyFlat_pullback`).

For a base category with objects in `Type (u + 1)` and `Hom`-types in `Type u` and a
coefficient category `A` with `Hom`-types in `Type (u + 1)`, this gives the pointwise left
Kan extensions of `A`-valued presheaves along the opposite of base change
(`CategoryTheory.MorphismProperty.Over.hasPointwiseLeftKanExtension_op_pullback`) and their
left exactness (`CategoryTheory.MorphismProperty.Over.preservesFiniteLimits_op_lan_pullback`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty.Over

/-- Base change along an arbitrary morphism `f : X ⟶ Y` is representably flat: the slice
`P.Over ⊤ Y` has finite limits and base change preserves them. -/
instance representablyFlat_pullback {T : Type*} [Category T] [HasPullbacks T]
    (P : MorphismProperty T) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    [P.HasOfPostcompProperty P] {X Y : T} (f : X ⟶ Y) :
    RepresentablyFlat (pullback P ⊤ f) :=
  flat_of_preservesFiniteLimits _

variable {T : Type (u + 1)} [Category.{u} T] [HasPullbacks T]

/-- All pointwise left Kan extensions along the opposite of base change by an *arbitrary*
morphism `f : X ⟶ Y` exist for `A`-valued presheaves on the slices of `P`, provided `A` has
colimits of size `u + 1`. No smallness assumption on the slices themselves is needed. -/
instance hasPointwiseLeftKanExtension_op_pullback (A : Type u') [Category.{u + 1} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] (P : MorphismProperty T) [P.IsStableUnderBaseChange]
    {X Y : T} (f : X ⟶ Y) (F : (P.Over ⊤ Y)ᵒᵖ ⥤ A) :
    (pullback P ⊤ f).op.HasPointwiseLeftKanExtension F := by
  intro V
  -- the indexing comma category has objects in `Type (u + 1)` and `Hom`-types in `Type u`
  have : HasColimitsOfShape (CostructuredArrow (pullback P ⊤ f).op V) A :=
    hasColimitsOfShape_of_essentiallySmall.{u + 1} _ _
  infer_instance

/-- The presheaf-level left Kan extension along the opposite of base change by an
*arbitrary* morphism `f : X ⟶ Y` is left exact for a Grothendieck abelian coefficient
category `A` with `Hom`-types in `Type (u + 1)`.

Here `[P.HasOfPostcompProperty P]` enters only through `MorphismProperty.Over.hasPullbacks`,
which is what makes `P.Over ⊤ Y` finitely complete and hence base change representably
flat. -/
instance preservesFiniteLimits_op_lan_pullback (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] (P : MorphismProperty T) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] {X Y : T} (f : X ⟶ Y) :
    PreservesFiniteLimits ((pullback P ⊤ f).op.lan :
      ((P.Over ⊤ Y)ᵒᵖ ⥤ A) ⥤ (P.Over ⊤ X)ᵒᵖ ⥤ A) :=
  -- `preservesFiniteLimits_op_lan_of_flat` at the size `(u, u + 1)` of the indexing comma
  -- categories, where `A` has exact filtered colimits by AB5
  inferInstance

end CategoryTheory.MorphismProperty.Over
