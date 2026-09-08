/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Properness of morphisms of schemes over a base

Cancellation for properness, packaged for the category `Over S` of schemes over a base scheme
`S`: a morphism of `S`-schemes with proper source and separated target is proper.

## Main results

- `AlgebraicGeometry.isProper_left`: a morphism `f : X ⟶ Y` in `Over S` with `X` proper over `S`
  and `Y` separated over `S` is proper.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism `f : X ⟶ Y` of schemes over `S` with `X` proper over `S` and `Y` separated over
`S` is proper.

```
             f.left
    X.left ─────────→ Y.left
         ╲           ╱
   X.hom  ╲         ╱  Y.hom
           ↘       ↙
               S
```
-/
instance (priority := low) isProper_left {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [IsProper X.hom] [IsSeparated Y.hom] : IsProper f.left := by
  have : IsProper (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  exact IsProper.of_comp _ Y.hom

end AlgebraicGeometry
