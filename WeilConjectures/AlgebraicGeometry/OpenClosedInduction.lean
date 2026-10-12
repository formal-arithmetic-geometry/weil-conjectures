/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Induction along open-closed decompositions

A property of quasi-compact schemes over a base `S` that holds for affine schemes and that
holds for `X` as soon as it holds for an open subscheme `U` and the complementary closed
subscheme `Z` holds for every quasi-compact scheme over `S`. This is the localization step
(Step 5) of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`: covering `X`
by affine opens `U_1, …, U_N`, the closed complement of `U_1 ∪ ⋯ ∪ U_{i-1}` in
`U_1 ∪ ⋯ ∪ U_i` is closed in the affine `U_i`, hence affine.

## Main results

- `AlgebraicGeometry.Scheme.induction_on_isCompl`: the induction principle.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Induction along open-closed decompositions: let `P` be a property of schemes `X` over `S`
that holds for affine `X`, and that holds for `X` whenever it holds for a quasi-compact open
subscheme `j : U ⟶ X` and the complementary closed subscheme `i : Z ⟶ X`. Then `P` holds for
every quasi-compact scheme over `S`. -/
theorem induction_on_isCompl {S : Scheme.{u}} (P : ∀ {X : Scheme.{u}}, (X ⟶ S) → Prop)
    (affine : ∀ {X : Scheme.{u}} (f : X ⟶ S), IsAffine X → P f)
    (isCompl : ∀ {X U Z : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]
      [IsClosedImmersion i], CompactSpace X → CompactSpace U →
      IsCompl (Set.range j.base) (Set.range i.base) → P (j ≫ f) → P (i ≫ f) → P f)
    {X : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] : P f :=
  sorry

end AlgebraicGeometry.Scheme
