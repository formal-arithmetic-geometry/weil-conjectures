/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometrically connected schemes

## Main statements

- `AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_section`: a connected scheme
  over a field with a rational point is geometrically connected.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A connected scheme `X` over a field `k` with a `k`-rational point, that is, a section `s` of
its structure morphism `f`, is geometrically connected over `k`. -/
@[stacks 04KV]
theorem GeometricallyConnected.of_connectedSpace_of_section {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [ConnectedSpace X] (s : Spec (.of k) ⟶ X)
    (hs : s ≫ f = 𝟙 _) : GeometricallyConnected f :=
  sorry

end AlgebraicGeometry
