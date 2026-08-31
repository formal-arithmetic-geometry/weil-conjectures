/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Base change on slices of a morphism property is representably flat

The slice `P.Over ⊤ Y` of a category with pullbacks has finite limits and base change
`P.Over ⊤ Y ⥤ P.Over ⊤ X` along an arbitrary morphism `f : X ⟶ Y` preserves them, hence
base change is representably flat
(`CategoryTheory.MorphismProperty.Over.representablyFlat_pullback`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty.Over

/-- Base change along an arbitrary morphism `f : X ⟶ Y` is representably flat: the slice
`P.Over ⊤ Y` has finite limits and base change preserves them. -/
instance representablyFlat_pullback {T : Type*} [Category T] [HasPullbacks T]
    (P : MorphismProperty T) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    [P.HasOfPostcompProperty P] {X Y : T} (f : X ⟶ Y) :
    RepresentablyFlat (pullback P ⊤ f) :=
  flat_of_preservesFiniteLimits _

end CategoryTheory.MorphismProperty.Over
