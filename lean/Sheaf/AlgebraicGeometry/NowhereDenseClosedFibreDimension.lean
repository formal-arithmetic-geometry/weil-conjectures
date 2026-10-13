/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # NowhereDenseClosedFibreDimension

Source: Stacks Project, Tag 054X, final dimension contradiction; Tags 00OT and 00OS.
(blueprint: lem-sbc-nowhere-dense-closed-fibre-dimension)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A nowhere dense closed fibre has strictly smaller local dimension at each point.
Source: Stacks Project, Tag 054X, final dimension contradiction; Tags 00OT and 00OS.
Proof: a quasi-compact locally finite type fibre over a field is a finite type scheme.
Its irreducible components are finite in number and finite dimensional. For a scheme
locally of finite type over a field, every nonempty open of an irreducible component
has the dimension of that component (Tag 00OS). Consequently the dimension at a point
is the maximum of the dimensions of the components through it. The closed-fibre
immersion identifies its components with closed irreducible subsets of ambient
components through the image point. Empty interior excludes equality with any ambient
component: a component in a noetherian space contains a nonempty open disjoint from
the other components. A proper closed irreducible subset of a finite dimensional
irreducible space has strictly smaller dimension by appending the ambient component
to a maximal chain. Taking the finite maximum gives the asserted strict inequality.
(blueprint: lem-sbc-nowhere-dense-closed-fibre-dimension) -/
theorem fibre_dimension_lt_of_closed_interior_eq_empty
    {Z X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] (t : T)
    (h : interior ((f.fiberι t) ⁻¹' Set.range i) = ∅)
    (z : Z) (hz : (i ≫ f) z = t) :
    topologicalKrullDimAt ((i ≫ f).asFiber z) <
      topologicalKrullDimAt (f.asFiber (i z)) := by sorry

end AlgebraicGeometry
