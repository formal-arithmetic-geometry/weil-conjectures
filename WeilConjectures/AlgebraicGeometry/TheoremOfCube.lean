/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# The theorem of the cube

Let `X`, `Y` be proper and geometrically integral over a field `K`, let `Z` be connected, and
let `x`, `y`, `z` be `K`-points of `X`, `Y`, `Z`. An invertible module on `X ×_K Y ×_K Z` is
determined, up to isomorphism, by its restrictions to the three slices `{x} × Y × Z`,
`X × {y} × Z` and `X × Y × {z}` (Stacks, Tag 0BF4).

Products are taken in the cartesian monoidal category `Over (Spec K)`, so that
`((X ⊗ Y) ⊗ Z).left` is the fibre product `(X ×_K Y) ×_K Z`, and the slice inclusions are
written with `CartesianMonoidalCategory.lift`.

## Main statements

- `AlgebraicGeometry.nonempty_iso_of_nonempty_iso_overPullback_slices`: the theorem of the cube.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

variable {K : Type u} [Field K]

/-- **The theorem of the cube** (Stacks, Tag 0BF4, over `S = Spec K` with `K`-rational points).

Let `X`, `Y` be proper and geometrically integral over a field `K`, let `Z` be a connected
`K`-scheme and let `x`, `y`, `z` be `K`-points of `X`, `Y`, `Z`. If two invertible modules `M`,
`N` on `X ×_K Y ×_K Z` become isomorphic on each of the three slices `{x} × Y × Z`,
`X × {y} × Z` and `X × Y × {z}`, then `M ≅ N`.

Stacks states this for one invertible module `L` (if `L` is trivial on the three slices then
`L` is trivial); the form here follows by applying it to `L = M ⊗ N⁻¹`. Over a field the
flatness and finite presentation hypotheses of Tag 0BF4 are automatic. -/
theorem nonempty_iso_of_nonempty_iso_overPullback_slices (X Y Z : Over (Spec (.of K)))
    [IsProper X.hom] [GeometricallyIntegral X.hom] [IsProper Y.hom]
    [GeometricallyIntegral Y.hom] [ConnectedSpace Z.left] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (z : 𝟙_ _ ⟶ Z) (M N : ((X ⊗ Y) ⊗ Z).left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hx : Nonempty (overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) M ≅
      overPullback (lift (lift (toUnit _ ≫ x) (fst Y Z)) (snd Y Z)) N))
    (hy : Nonempty (overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) M ≅
      overPullback (lift (lift (fst X Z) (toUnit _ ≫ y)) (snd X Z)) N))
    (hz : Nonempty (overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) M ≅
      overPullback (lift (𝟙 (X ⊗ Y)) (toUnit _ ≫ z)) N)) :
    Nonempty (M ≅ N) :=
  sorry

end AlgebraicGeometry
