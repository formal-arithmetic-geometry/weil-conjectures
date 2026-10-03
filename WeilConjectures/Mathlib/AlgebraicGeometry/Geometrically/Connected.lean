/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Geometrically connected schemes

## Main statements

- `AlgebraicGeometry.GeometricallyConnected.of_geometricallyIrreducible`: a geometrically
  irreducible morphism is geometrically connected.
- `AlgebraicGeometry.GeometricallyConnected.of_isSepClosed`: a connected scheme over a
  separably closed field is geometrically connected.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A geometrically irreducible morphism is geometrically connected, since an irreducible space
is connected. -/
instance (priority := low) GeometricallyConnected.of_geometricallyIrreducible
    {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIrreducible f] : GeometricallyConnected f where
  geometrically_connectedSpace _ _ y _ fst snd h :=
    have := GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd h
    inferInstance

/-- A connected scheme over a separably closed field `k` is geometrically connected over `k`. -/
theorem GeometricallyConnected.of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [ConnectedSpace X] :
    GeometricallyConnected (X ↘ Spec (.of k)) :=
  sorry

end AlgebraicGeometry
