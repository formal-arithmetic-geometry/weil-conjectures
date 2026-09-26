/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!

# Perfect pairings in a monoidal closed category

A morphism `b : X ⊗ Y ⟶ Z` in a monoidal closed category is *perfect* when the morphism
`Y ⟶ (X ⟶[C] Z)` adjoint to it under the tensor–internal-hom adjunction is an isomorphism,
i.e. when `b` identifies `Y` with the internal hom from `X` to the value object `Z`.

This is the categorical form of "a bilinear map `V × W → k` is perfect if the induced map
`W → V^*` is bijective" (`LinearMap.IsPerfPair`), and it is how perfectness of the derived
Poincaré pairing is expressed.

## Main definitions

- `CategoryTheory.MonoidalClosed.IsPerfectPairing`.

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

/-- A morphism `b : X ⊗ Y ⟶ Z` in a monoidal closed category is a *perfect pairing* if its
tensor–internal-hom adjoint `Y ⟶ (X ⟶[C] Z)` is an isomorphism. -/
def IsPerfectPairing {X Y Z : C} (b : X ⊗ Y ⟶ Z) : Prop :=
  IsIso (curry b)

lemma isPerfectPairing_iff {X Y Z : C} (b : X ⊗ Y ⟶ Z) :
    IsPerfectPairing b ↔ IsIso (curry b) :=
  Iff.rfl

end CategoryTheory.MonoidalClosed
