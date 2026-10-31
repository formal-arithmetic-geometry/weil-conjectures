/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Mathlib.Topology.Order
public import Mathlib.Topology.Compactness.Compact

/-!
# Point images and the topology of an algebraic space

Source: Stacks Project, Properties of Spaces, Tags 03BU and 03BX
(blueprint: def-a1-space-point-topology).

The field-valued point classes `Point F`, their representatives and the scheme point map
`schemePointMap` are those of def-a1-algebraic-space-point-classes. This module adds the
image of a morphism on point classes and the topology on `Point F`, which is final for all
étale scheme-source maps, without choosing an atlas. The atlas criterion is stated in
`AlgebraicSpaceEtaleOpenImage`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Apply a natural transformation to a field-valued representative.
Source: Stacks, Tag 03BU (blueprint: def-a1-space-point-topology). -/
noncomputable def PointRepresentative.map {S : Scheme.{u}} {E F : (Over S)ᵒᵖ ⥤ Type u}
    (f : E ⟶ F) (a : PointRepresentative E) : PointRepresentative F :=
  { K := a.K, base := a.base, value := f.app _ a.value }

/-- Image on point classes, expressed using representatives rather than a choice of them.
Source: Stacks, Tag 03BU (blueprint: def-a1-space-point-topology). -/
def pointImage {S : Scheme.{u}} {E F : (Over S)ᵒᵖ ⥤ Type u}
    (f : E ⟶ F) : Set (Point F) :=
  {p | ∃ a : PointRepresentative E, Quot.mk _ (a.map f) = p}

/-- The final topology for all representable étale scheme-source maps. For an algebraic
space this is the quotient topology of any surjective étale scheme atlas.
Source: Stacks, Tag 03BX (blueprint: def-a1-space-point-topology). -/
noncomputable instance pointTopologicalSpace {S : Scheme.{u}}
    (F : (Over S)ᵒᵖ ⥤ Type u) : TopologicalSpace (Point F) :=
  ⨆ (T : Over S) (a : yoneda.obj T ⟶ F) (_ : IsEtale a),
    TopologicalSpace.coinduced (schemePointMap a) inferInstance

end AlgebraicGeometry.AlgebraicSpace
