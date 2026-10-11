/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Images of geometrically irreducible schemes

If `a : X ⟶ Y` is a surjective morphism of `S`-schemes and `X` is geometrically irreducible over
`S`, then so is `Y`: every geometric fibre of `Y` is the image of the corresponding geometric
fibre of `X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **The image of a geometrically irreducible scheme is geometrically irreducible.** If
`a : X ⟶ Y` is surjective and `a ≫ g` is geometrically irreducible, then so is `g`: the base
change `X_K ⟶ Y_K` of `a` to a field `K` is surjective, and `X_K` is irreducible. -/
lemma GeometricallyIrreducible.of_surjective {X Y S : Scheme.{u}} (a : X ⟶ Y) (g : Y ⟶ S)
    [Surjective a] [GeometricallyIrreducible (a ≫ g)] : GeometricallyIrreducible g := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have h' : IsPullback (pullback.fst a fst) (pullback.snd a fst ≫ snd) (a ≫ g) y :=
    (IsPullback.of_hasPullback a fst).paste_vert h
  have : IrreducibleSpace (pullback a fst : Scheme.{u}) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ h'
  have : Surjective (pullback.snd a fst) := inferInstance
  exact Function.Surjective.irreducibleSpace (pullback.snd a fst).continuous
    (pullback.snd a fst).surjective

end AlgebraicGeometry
