/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension

/-!
# Component intersections on a Noetherian scheme of dimension at most one

Source: Stacks Project, Varieties, Lemma 33.38.10 (Tag 09NX), proof, first paragraph
and the uniqueness assertion in its final paragraph
(blueprint: lem-sc-component-intersections-finite).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- On a Noetherian scheme of topological dimension at most one, the irreducible components
are finite in number, their distinct pairwise intersections are finite sets of closed points,
and outside their union each point belongs to exactly one component.
Source: Stacks Project, Varieties, Lemma 33.38.10 (Tag 09NX), proof
(blueprint: lem-sc-component-intersections-finite).

Proof: `lem-weil-pbc-noetherian-finitely-many-components` gives finitely many components.
For distinct components, `lem-sc-scheme-sober` gives their unique generic points. The generic
point of one cannot belong to the other, by maximality of irreducible components. The first
component minus the second is therefore a nonempty open in an irreducible T0 space of
dimension at most one. By `lem-sc-dim-one-point-outside-open-closed`, every intersection
point is closed in the first component, hence in the scheme because the component is closed.
The intersection is closed, so `lem-sc-noetherian-closed-points-finite` makes it finite.
Their union over the finitely many distinct component pairs is finite and consists of closed
points. By `lem-sc-irreducible-components-cover` every point lies on a component; a point
outside this union cannot belong to two distinct components, giving uniqueness. -/
theorem component_intersections_finite (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    [CompactSpace Y] (h_dim : topologicalKrullDim Y ≤ 1) :
    let T : Set Y := {y | ∃ Z₁ ∈ irreducibleComponents Y,
      ∃ Z₂ ∈ irreducibleComponents Y, Z₁ ≠ Z₂ ∧ y ∈ Z₁ ∩ Z₂}
    (irreducibleComponents Y).Finite ∧
    (∀ Z₁ ∈ irreducibleComponents Y, ∀ Z₂ ∈ irreducibleComponents Y, Z₁ ≠ Z₂ →
      (Z₁ ∩ Z₂).Finite ∧ ∀ y ∈ Z₁ ∩ Z₂, IsClosed ({y} : Set Y)) ∧
    T.Finite ∧ (∀ y ∈ T, IsClosed ({y} : Set Y)) ∧
    ∀ y : Y, y ∉ T → ∃! Z : Set Y, Z ∈ irreducibleComponents Y ∧ y ∈ Z := by
  sorry

end AlgebraicGeometry
