/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict

/-!

# Quasi-domination

Let `x : X ⟶ S` and `y : Y ⟶ S` be morphisms of schemes with `y` separated. A
*quasi-domination of `X` over `Y`* is a morphism `U ⟶ Y` over `S`, defined on a dense open
`U ⊆ X`, whose graph is closed in the full fibre product `X ×ₛ Y`. Closedness is demanded in
`X ×ₛ Y`, not merely in `U ×ₛ Y`, where it would be automatic from separatedness of `y`; it
is exactly this stronger requirement that is propagated by the partial-section extension
theorem.

## Main definitions

- `AlgebraicGeometry.QuasiDomination`: the data of a quasi-domination of `X` over `Y`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `sk-def-nagata-sketch-quasidomination`: Quasi-domination.

A quasi-domination of `x : X ⟶ S` over a separated `y : Y ⟶ S` is a morphism `hom : U ⟶ Y`
over `S`, defined on a dense open `U ⊆ X`, whose graph `U ⟶ X ×ₛ Y` has closed range. -/
structure QuasiDomination {S X Y : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) where
  /-- The dense open of `X` on which the quasi-domination is defined. -/
  U : X.Opens
  /-- The open `U` is dense in `X`. -/
  dense_coe : Dense (U : Set X)
  /-- The morphism to `Y` defined on `U`. -/
  hom : U.toScheme ⟶ Y
  /-- The morphism `hom` is a morphism over `S`. -/
  ι_comp : U.ι ≫ x = hom ≫ y
  /-- The graph of `hom` is closed in the full fibre product `X ×ₛ Y`. -/
  isClosed_range_graph : IsClosed (Set.range (pullback.lift U.ι hom ι_comp))

end AlgebraicGeometry
