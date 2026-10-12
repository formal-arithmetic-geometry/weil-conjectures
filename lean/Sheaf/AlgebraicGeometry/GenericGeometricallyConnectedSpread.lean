/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Spreading geometric connectedness of a generic fibre

Source: Stacks Project, Tag 055G (lemma-geometrically-connected-generic-fibre).
(blueprint: lem-sbc-generic-geometrically-connected-spread)
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A finite type family with geometrically connected generic fibre has geometrically
connected fibres on an open neighbourhood of the generic point.

Source: Stacks Project, Tag 055G, lemma-geometrically-connected-generic-fibre.
Proof: after a finite extension of the generic field and shrinking the base, arrange
that the finitely many generic irreducible components are geometrically irreducible.
This change of base is open and surjective over an open, so geometric connectedness
of fibres descends. Reduce the base. Take closures of the generic components.
Shrink so these closures cover the total space and so pairs having empty generic
intersection are disjoint. Shrink again so every component has geometrically
irreducible fibres. For each pair with nonempty generic intersection, generic
flatness makes that intersection flat and finitely presented after further
shrinking; its image is then open and contains the generic point. Intersect these
finitely many images. The graph of nonempty intersections of the generic components
is connected because the generic fibre is connected. On the resulting open, after
any separably closed field extension each component is irreducible and this same
connected graph of intersections persists. Their union is therefore connected.
Descent returns a nonempty open in the original base, which contains its generic
point by irreducibility. The argument also covers a single generic component.

(blueprint: lem-sbc-generic-geometrically-connected-spread) -/
theorem exists_open_geometricallyConnected_fibres_of_generic {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (hη : GeometricallyConnected (f.fiberToSpecResidueField (genericPoint S))) :
    ∃ W : Set S, IsOpen W ∧ genericPoint S ∈ W ∧
      ∀ s ∈ W, GeometricallyConnected (f.fiberToSpecResidueField s) := by sorry

end AlgebraicGeometry
