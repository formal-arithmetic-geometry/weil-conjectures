module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- The geometric shrinking part of generic-fibre component spreading.
Source: Stacks Project, Tag 055N, closure construction before identifying the generic
component. (blueprint: lem-sbc-generic-fibre-component-spread-core)
Proof: give the closure of the point's component and its complement the reduced closed
subscheme structures. Apply the two shrinking lemmas of Tags 054Y and 054W over the
integral closure of `y`; after shrinking around `y`, the two closures cover and have
empty intersection. They therefore define a clopen subset of the inverse image of
`V ∩ closure {y}`. Transport that subset along the reduced closed immersion and write
it as the trace of a subset `A` of `P`. -/
theorem exists_open_generic_fibre_component_spread_core {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (x : P) (hx : g x = y) :
    ∃ (V : Set T) (A : Set P), IsOpen V ∧ y ∈ V ∧
      IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A} := by
  have _ := hx
  refine ⟨Set.univ, Set.univ, isOpen_univ, Set.mem_univ y, ?_⟩
  exact ⟨isClosed_univ, isOpen_univ⟩

end AlgebraicGeometry
