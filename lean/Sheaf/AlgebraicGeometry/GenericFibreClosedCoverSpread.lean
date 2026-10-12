/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Shrinking near a generic fibre

Source: Stacks Project, Tags 054Y and 054W.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- Two closed subsets covering a fibre cover the family over a neighbourhood in
its base point's closure.

Source: Stacks Project, Tag 054Y (Lemma 37.24.5), applied after the reduction to the
integral base in Tag 055N, proof, first two paragraphs.

Proof: give the closure of `y` its induced reduced closed subscheme structure `Z`.
It is integral with generic point mapping to `y`. Base change `g` to `Z`; this remains
finite type, and the projection identifies its underlying space with the inverse
image of the closure of `y`. Pull back the closed subsets `C` and `D` to this space.
Their traces cover the generic fibre and are closed in it. Tag 054Y applied to the
two traces gives an open neighbourhood of the generic point where their closures
cover the total space. Those closures lie in the pullbacks of `C` and `D`, since
these are closed and contain the original traces. Represent this neighbourhood in
`Z` by the intersection with an ambient open `V` of `T`. Its generic point maps to
`y`, so `y ∈ V`, and the stated inclusion follows under the topological identification.
Neither trace needs to be nonempty; the argument also covers an empty generic fibre.

(blueprint: lem-sbc-generic-fibre-closed-cover-spread) -/
theorem exists_open_generic_fibre_closed_cover {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (C D : Set P)
    (hC : IsClosed C) (hD : IsClosed D) (hcover : g ⁻¹' {y} ⊆ C ∪ D) :
    ∃ V : Set T, IsOpen V ∧ y ∈ V ∧ g ⁻¹' (V ∩ closure {y}) ⊆ C ∪ D := by sorry

end AlgebraicGeometry
