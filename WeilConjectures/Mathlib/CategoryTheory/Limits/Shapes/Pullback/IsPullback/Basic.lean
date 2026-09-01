/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Cartesian squares over a terminal object

A cartesian square whose cospan is a pair of morphisms to a terminal object stays cartesian if
the terminal object is replaced by any other terminal object.

## Main declarations

* `CategoryTheory.IsPullback.of_isTerminal`: transport of a cartesian square along a change of
  terminal objects at the tip of its cospan.
-/

@[expose] public section

namespace CategoryTheory.IsPullback

open Limits

variable {C : Type*} [Category* C]

/-- If a square over a terminal object `Z` is cartesian, then the square with the same projections
over any other terminal object `Z'` is cartesian. -/
theorem of_isTerminal {P X Y Z Z' : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (hZ : IsTerminal Z) {f' : X ⟶ Z'} {g' : Y ⟶ Z'}
    (hZ' : IsTerminal Z') :
    IsPullback fst snd f' g' :=
  mk' (hZ'.hom_ext _ _) (fun _ _ _ h₁ h₂ ↦ h.hom_ext h₁ h₂)
    (fun _ a b _ ↦ ⟨h.lift a b (hZ.hom_ext _ _), h.lift_fst .., h.lift_snd ..⟩)

end CategoryTheory.IsPullback
