module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- The specialization step identifying the generic component after shrinking.
Source: Stacks Project, Tag 055N, Tags 054Y and 054W.
Proof: the closure selected in the shrinking construction contains `x`, and its trace
on the fibre over `y` is closed and open. Every connected subset of that fibre which
contains `x`, hence the connected component of `x`, lies in this clopen trace. The
(blueprint: lem-sbc-generic-fibre-component-spread-trace) hypotheses identify the
trace with `g ⁻¹' {y} ∩ A`. -/
theorem generic_fibre_component_spread_trace {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (x : P) (hx : g x = y)
    (V : Set T) (A : Set P)
    (hV : IsOpen V) (hy : y ∈ V)
    (hcl : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A}) :
    connectedComponentIn (g ⁻¹' {y}) x ⊆ g ⁻¹' {y} ∩ A := by sorry

/-- The complementary inclusion in the specialization step.
Source: Stacks Project, Tag 055N, Tags 054Y and 054W.
Proof: the complementary closure constructed in the same argument is disjoint from
the chosen closure after the second shrinking. A point of the fibre over `y` lying
in `A` therefore cannot lie in that complement; it belongs to the connected clopen
piece containing `x`, which is `connectedComponentIn (g ⁻¹' {y}) x`.
(blueprint: lem-sbc-generic-fibre-component-spread-trace-reverse) -/
theorem generic_fibre_component_spread_trace_reverse {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (x : P) (hx : g x = y)
    (V : Set T) (A : Set P)
    (hV : IsOpen V) (hy : y ∈ V)
    (hcl : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A}) :
    g ⁻¹' {y} ∩ A ⊆ connectedComponentIn (g ⁻¹' {y}) x := by sorry

end AlgebraicGeometry
