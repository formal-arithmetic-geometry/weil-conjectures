/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# The functor of arrows `Cat ⥤ Type`

The functor sending a (small) category `C` to its set `Arrow C` of arrows `(X, Y, f : X ⟶ Y)`
and a functor `v` to `(X, Y, f) ↦ (vX, vY, vf)`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Cat

/-- The functor `Arrows : Cat ⥤ Type` taking a category to its set of arrows and a functor to the
induced map on arrows. (blueprint: `def-weil-pbc-arrows-functor`) -/
@[simps!]
def arrows : Cat.{v, u} ⥤ Type (max u v) where
  obj C := Arrow C
  map v := ↾fun f ↦ v.toFunctor.mapArrow.obj f
  map_id _ := rfl
  map_comp _ _ := rfl

end CategoryTheory.Cat
