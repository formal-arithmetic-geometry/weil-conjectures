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

/-- A closed subset missing a fibre is absent over a neighbourhood in the closure
of its base point.

Source: Stacks Project, Tag 054W (Lemma 37.24.1), applied after the reduction to the
integral base in Tag 055N, proof, first two paragraphs.

Proof: give the closure of `y` its reduced closed subscheme structure `Z`. This is
integral with generic point over `y`. Base change `g` to `Z` and pull back the closed
set `C`. Give this pullback its reduced closed subscheme structure `W`. A closed
immersion is locally of finite type and quasi-compact, so `W → Z` is finite type.
Its generic fibre is empty by `hempty` and the homeomorphism from the scheme-theoretic
fibre onto the set-theoretic fibre. Tag 054W gives a nonempty open of `Z` over which
`W` is empty. Every nonempty open of the integral `Z` contains its generic point.
Represent this open as `V ∩ closure {y}` with `V` ambient open in `T`; then `y ∈ V`.
The base-change projection is a homeomorphism onto the inverse image of the closure
of `y`, so emptiness of `W` there is exactly the asserted disjointness. If `C` is
empty the conclusion holds with `V = Set.univ`.

(blueprint: lem-sbc-generic-fibre-closed-avoidance) -/
theorem exists_open_generic_fibre_closed_avoidance {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (C : Set P)
    (hC : IsClosed C) (hempty : g ⁻¹' {y} ∩ C = ∅) :
    ∃ V : Set T, IsOpen V ∧ y ∈ V ∧ Disjoint (g ⁻¹' (V ∩ closure {y})) C := by sorry

end AlgebraicGeometry
