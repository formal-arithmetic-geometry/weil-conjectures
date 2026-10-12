/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Generic clopenness of the component selected by a section

Source: Stacks Project, Tag 055N, using Tag 055M.
(blueprint: lem-sbc-section-component-generic-clopen)
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- The section component is clopen over an open neighbourhood of a base point inside
its closure. The topology on the displayed subtype is the subspace topology.

Source: Stacks Project, Tag 055N, proof, using Tag 055M.
Proof: give the closure of y its reduced closed subscheme structure. Base change the
morphism and section to this integral scheme; Tag 055M identifies the section locus
with the inverse image of the original locus. The generic fibre is a finite type scheme
over a field, hence noetherian. Its section component and its complement are clopen.
Take their closures in the total space. Tag 054Y permits shrinking the integral base
so these two closures cover the total space; Tag 054W permits further shrinking to
make their intersection empty. The first closure is now clopen. Its generic fibre is
connected and has the rational point supplied by the section, so it is geometrically
connected by Tag 04KV. Tag 055G permits shrinking the base again so that all its fibres
are geometrically connected. Intersect also with the inverse image under the section
of the first closure; this open contains the generic point. Each fibre of the first
closure is then a nonempty connected clopen subset of the whole fibre containing the
section point, hence is precisely its connected component. This identifies the first
closure with the section locus on the remaining open. A closed immersion and its base
change are homeomorphisms onto their images, so the base-changed total space has the
subspace topology on the inverse image of the closure of y. Express the remaining open
of the closure of y as the intersection with an ambient open V of T. Since y is the
generic point of its closure, V contains y. Transport clopenness along the indicated
homeomorphism to obtain the displayed subtype statement.

(blueprint: lem-sbc-section-component-generic-clopen) -/
theorem exists_open_section_component_clopen {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (y : T) :
    ∃ V : Set T, IsOpen V ∧ y ∈ V ∧
      IsClopen {q : g ⁻¹' (V ∩ closure {y}) |
        (q : P) ∈ connectedComponentIn (g ⁻¹' {g (q : P)}) (σ (g (q : P)))} := by sorry

end AlgebraicGeometry
