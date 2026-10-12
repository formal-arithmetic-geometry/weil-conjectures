/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Geometrically integral morphisms are geometrically connected

An irreducible space is connected, so a geometrically irreducible morphism, and in particular a
geometrically integral one, is geometrically connected.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A geometrically irreducible morphism is geometrically connected: every geometric fibre is
irreducible, hence connected. -/
lemma GeometricallyIrreducible.geometricallyConnected [GeometricallyIrreducible f] :
    GeometricallyConnected f :=
  ⟨fun _ _ y _ fst snd h ↦
    haveI := GeometricallyIrreducible.geometrically_irreducibleSpace (f := f) y fst snd h
    inferInstance⟩

/-- A geometrically integral morphism is geometrically connected. -/
lemma GeometricallyIntegral.geometricallyConnected [GeometricallyIntegral f] :
    GeometricallyConnected f :=
  GeometricallyIrreducible.geometricallyConnected f

end AlgebraicGeometry
