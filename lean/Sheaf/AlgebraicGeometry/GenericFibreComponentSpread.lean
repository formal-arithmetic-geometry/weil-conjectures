/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.GenericFibreComponentSpreadCore
import Sheaf.AlgebraicGeometry.GenericFibreComponentSpreadTrace

/-!
# Spreading a connected component of a generic fibre

Source: Stacks Project, Tag 055N, first two paragraphs of the integral-base argument.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A component of the fibre over a point spreads to a clopen subset over an open part
of that point's closure. This does not assert connectedness of any other fibre.

Source: Stacks Project, Tag 055N, proof through the assertion that the closure of the
chosen generic component is open; Tags 054Y and 054W.
Proof: give the closure of y its reduced closed subscheme structure and base change g.
This is an integral base with generic point y. The generic fibre is finite type over
a field, hence noetherian, so the component of x and its complement are clopen.
Take their closures in the base-changed total space. Their generic fibres are the
original subsets. Tag 054Y shrinks the base so the two closures cover the total space.
Their intersection has empty generic fibre; Tag 054W shrinks again so the intersection
is empty. Each closure is now clopen, and its trace on the generic fibre is unchanged.
The base change by the reduced closed immersion is a homeomorphism onto the inverse
image of the closure of y. Represent the open of that closure by an ambient open V,
and represent the chosen closure by a subset A of P under this homeomorphism. The
generic point belongs to V, and the trace of A on its fibre is exactly the component
of x. Empty complements cause no problem: the same closure argument applies.

(blueprint: lem-sbc-generic-fibre-component-spread) -/
theorem exists_open_generic_fibre_component_spread {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (x : P) (hx : g x = y) :
    ∃ (V : Set T) (A : Set P), IsOpen V ∧ y ∈ V ∧
      IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A} ∧
      g ⁻¹' {y} ∩ A = connectedComponentIn (g ⁻¹' {y}) x := by
  obtain ⟨V, A, hV, hy, hcl⟩ :=
    exists_open_generic_fibre_component_spread_core g y x hx
  refine ⟨V, A, hV, hy, hcl, ?_⟩
  apply Set.Subset.antisymm
  · exact generic_fibre_component_spread_trace_reverse g y x hx V A hV hy hcl
  · exact generic_fibre_component_spread_trace g y x hx V A hV hy hcl

end AlgebraicGeometry
