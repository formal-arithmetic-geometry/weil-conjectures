/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Projective morphisms

A morphism of schemes `f : X ⟶ S` is *projective* if it factors as a closed immersion
`X ⟶ ℙ(α; S)` into a projective space over `S` with finite index type `α`, followed by the
structure morphism `ℙ(α; S) ↘ S`. This is what Stacks calls *H-projective* (`01W8`); over an
affine base, in particular over a field, it agrees with the other common definitions of
projectivity (`0B45`). Mathlib has no such morphism class, so it is introduced here.

## Main definitions

- `AlgebraicGeometry.IsProjective`: projective morphisms of schemes.

## Main results

- `AlgebraicGeometry.IsProjective.isProper`: projective morphisms are proper.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A morphism `f : X ⟶ S` is *projective* if it factors through a closed immersion into a
projective space `ℙ(α; S)` over `S` with finite index type `α`. The index type is called `α`
rather than `ι`, the latter being the token of the inversion notation `ι[A]` for group
schemes. -/
class IsProjective : Prop where
  exists_isClosedImmersion_projectiveSpace :
    ∃ (α : Type u) (_ : Finite α) (j : X ⟶ ℙ(α; S)),
      IsClosedImmersion j ∧ j ≫ ℙ(α; S) ↘ S = f

/-- Projective morphisms are proper: a closed immersion is proper, and so is the structure
morphism of a projective space with finite index type. -/
instance (priority := 900) IsProjective.isProper [IsProjective f] : IsProper f := by
  obtain ⟨α, _, j, _, rfl⟩ := IsProjective.exists_isClosedImmersion_projectiveSpace (f := f)
  infer_instance

end AlgebraicGeometry
