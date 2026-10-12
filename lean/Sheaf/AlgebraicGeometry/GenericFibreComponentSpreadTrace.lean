module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Connected.Clopen

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A clopen trace containing `x` contains its entire fibre component.

Source: Stacks Project, Tag 055N, generic-fibre closure argument.
Proof: inclusion of the fibre over `y` in the inverse image of `V ∩ closure {y}`
is continuous, since `y ∈ V` and `y ∈ closure {y}`. Pull the clopen trace back to
that fibre. Its connected component through `x` lies in this trace by
`IsClopen.connectedComponent_subset`. Transport back to the ambient scheme using
`connectedComponentIn_eq_image`.

The former statement was false for `A = ∅`; `hxA` records the missing membership.
(blueprint: lem-sbc-generic-fibre-component-spread-trace) -/
theorem generic_fibre_component_spread_trace {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (x : P) (hx : g x = y)
    (V : Set T) (A : Set P)
    (hV : IsOpen V) (hy : y ∈ V)
    (hcl : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A})
    (hxA : x ∈ A) :
    connectedComponentIn (g ⁻¹' {y}) x ⊆ g ⁻¹' {y} ∩ A := by
  have _ := hV
  have hxy : x ∈ g ⁻¹' {y} := hx
  let inclusion : (g ⁻¹' {y}) → (g ⁻¹' (V ∩ closure {y})) :=
    fun q => ⟨q.val, by
      have hqy : g q.val = y := q.property
      change g q.val ∈ V ∩ closure {y}
      rw [hqy]
      exact ⟨hy, subset_closure (Set.mem_singleton y)⟩⟩
  have hi : Continuous inclusion := continuous_subtype_val.subtype_mk _
  have hc : IsClopen {q : g ⁻¹' {y} | (q : P) ∈ A} := hcl.preimage hi
  intro q hq
  refine ⟨connectedComponentIn_subset _ _ hq, ?_⟩
  rw [connectedComponentIn_eq_image hxy] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  exact hc.connectedComponent_subset hxA hq'

/-- A preconnected fibre trace containing `x` lies in its fibre component.

Source: Stacks Project, Tag 055N, generic-fibre closure argument.
Proof: the trace is preconnected, contains `x`, and lies in the fibre. Maximality
of the connected component gives the inclusion, using
`IsPreconnected.subset_connectedComponentIn`.

The former statement was false for a disconnected fibre and `A = Set.univ`.
Membership and preconnectedness are properties of the chosen component closure,
not consequences of clopenness of an arbitrary `A`.
(blueprint: lem-sbc-generic-fibre-component-spread-trace-reverse) -/
theorem generic_fibre_component_spread_trace_reverse {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (x : P) (hx : g x = y)
    (V : Set T) (A : Set P)
    (hV : IsOpen V) (hy : y ∈ V)
    (hcl : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A})
    (hxA : x ∈ A) (hconn : IsPreconnected (g ⁻¹' {y} ∩ A)) :
    g ⁻¹' {y} ∩ A ⊆ connectedComponentIn (g ⁻¹' {y}) x := by
  have _ := hV
  have _ := hy
  have _ := hcl
  exact hconn.subset_connectedComponentIn ⟨hx, hxA⟩ Set.inter_subset_left

end AlgebraicGeometry
