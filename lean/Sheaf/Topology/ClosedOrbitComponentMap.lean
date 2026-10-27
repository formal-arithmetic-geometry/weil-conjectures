module

public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Components and generic points of a closed orbit map

Source: Stacks Project, Topology, Tags 004V and 004X; the elementary closed-orbit-map
consequence used for Groupoids, Tag 03BL (blueprint: lem-sfb-closed-orbit-component-map).
-/

@[expose] public section

universe u v w

open scoped Pointwise

namespace Topology

/-- A closed orbit map identifies orbits of disjoint clopen irreducible components with
irreducible components of its target and preserves their generic points.
Source: Stacks Project, Topology, Tags 004V (irreducible components) and 004X (generic
points); applied to the point quotient in Groupoids, Tag 03BL.
(blueprint: lem-sfb-closed-orbit-component-map)

Here a component orbit is written as a set `O = MulAction.orbit H C` of subsets of `X`,
and its union is `⋃₀ O`. The action on sets is Mathlib's pointwise image action.

Proof plan:
1. A homeomorphism preserves irreducibility by pulling back relatively closed covers,
   and preserves maximality by applying its inverse. Thus `H` permutes the components
   (def-weil-irreducible-components).
2. Invariance gives `q '' (h • C) = q '' C`, so every component in an orbit has the same
   image. The union of the orbit is stable under `H`. The orbit-fibre hypothesis then
   proves its saturation: any point over its image is a translate of a point in it.
3. The orbit union is clopen, since there are finitely many clopen components. Its image
   and the image of its complement are closed, disjoint by saturation, and cover the
   target by surjectivity. Hence its image is clopen.
4. The image of a component is nonempty and irreducible: pull a relatively closed cover
   back to that component, apply irreducibility, and push forward the resulting equality
   (def-weil-irreducible-components).
5. These images form a disjoint clopen partition. Any irreducible set meeting one part
   lies in that part, by the closed decomposition with its complement. Thus every part
   is maximal irreducible, every target component is a part, and distinct component
   orbits have distinct images (def-weil-irreducible-components).
6. The closed image of a component contains the closure of the image of its generic
   point. Conversely, every closed set containing that image pulls back to a closed set
   containing the original generic point, hence the entire component. This proves the
   opposite inclusion and the generic-point assertion (def-sc-generic-point).
7. A homeomorphism takes a generic point of `C` to a generic point of `h • C` by the same
   closure calculation. Fixing the point fixes its closure; stabilizing the component
   fixes its unique generic point by sobriety (def-sc-generic-point). If `X` is empty,
   surjectivity forces `Z` empty and the component assertions are vacuous.
-/
theorem closed_orbit_component_map
    {X : Type u} {Z : Type v} {H : Type w}
    [TopologicalSpace X] [TopologicalSpace Z]
    [QuasiSober X] [T0Space X] [QuasiSober Z] [T0Space Z]
    [Group H] [Finite H] [MulAction H X] [ContinuousConstSMul H X]
    (hXfinite : (irreducibleComponents X).Finite)
    (hXdisjoint : (irreducibleComponents X).PairwiseDisjoint id)
    (hXclopen : ∀ C ∈ irreducibleComponents X, IsClopen C)
    (hZfinite : (irreducibleComponents Z).Finite)
    (hZdisjoint : (irreducibleComponents Z).PairwiseDisjoint id)
    (hZclopen : ∀ D ∈ irreducibleComponents Z, IsClopen D)
    (q : X → Z) (hqcontinuous : Continuous q) (hqsurjective : Function.Surjective q)
    (hqclosed : IsClosedMap q) (hqinvariant : ∀ (h : H) (x : X), q (h • x) = q x)
    (hqfibres : ∀ x y : X, q x = q y ↔ ∃ h : H, y = h • x) :
    (∀ O : Set (Set X), (∃ C ∈ irreducibleComponents X, O = MulAction.orbit H C) →
      q ⁻¹' (q '' (⋃₀ O)) = ⋃₀ O ∧
      IsClopen (q '' (⋃₀ O)) ∧
      ∀ C ∈ O, q '' (⋃₀ O) = q '' C) ∧
    Set.BijOn (fun O : Set (Set X) ↦ q '' (⋃₀ O))
      {O | ∃ C ∈ irreducibleComponents X, O = MulAction.orbit H C}
      (irreducibleComponents Z) ∧
    (∀ C ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η C →
      IsGenericPoint (q η) (q '' C) ∧
      {h : H | h • η = η} = {h : H | h • C = C}) := by
  sorry

end Topology
