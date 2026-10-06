/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flatness descends along flat surjections of the source

If `u : X' ⟶ X` is flat and surjective and `u ≫ f` is flat, then `f` is flat: at a point `x`
with preimage `x'`, the local ring map `𝒪_{X,x} ⟶ 𝒪_{X',x'}` is flat and local, hence faithfully
flat, and flatness of `𝒪_{X',x'}` over `𝒪_{S,f(x)}` descends to `𝒪_{X,x}`.

## Main results

- `AlgebraicGeometry.Flat.of_comp_of_flat_of_surjective` (blueprint `lem-pc-flat-source-descent`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Flatness descends along a flat surjection on the source.** If `u : X' ⟶ X` is flat and
surjective and `u ≫ f` is flat, then `f` is flat.

(blueprint: `lem-pc-flat-source-descent`) -/
theorem Flat.of_comp_of_flat_of_surjective {X' X S : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [Flat (u ≫ f)] : Flat f :=
  sorry

end AlgebraicGeometry
