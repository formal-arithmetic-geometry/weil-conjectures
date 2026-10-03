/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Separation.Connected

/-!
# Connected components of a noetherian space

A noetherian topological space has finitely many irreducible components, and every irreducible
component lies in a single connected component. Hence it has finitely many connected
components, and each of them is open, being the complement of the finitely many other ones.

Likewise a point lying in a unique irreducible component has a preirreducible open
neighbourhood (`TopologicalSpace.NoetherianSpace.exists_isOpen_isPreirreducible`).
-/

@[expose] public section

open Topology

variable {α : Type*} [TopologicalSpace α]

namespace TopologicalSpace.NoetherianSpace

variable [NoetherianSpace α]

/-- A noetherian space has finitely many connected components. -/
instance finite_connectedComponents : Finite (ConnectedComponents α) := by
  have : Finite (irreducibleComponents α) := finite_irreducibleComponents.to_subtype
  refine Finite.of_surjective (fun Z : irreducibleComponents α ↦
    (ConnectedComponents.mk (Z.2.1.nonempty.some) : ConnectedComponents α)) fun c ↦ ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  refine ConnectedComponents.coe_eq_coe'.mpr ?_
  exact (irreducibleComponent_property x).1.isPreconnected.subset_connectedComponent
    mem_irreducibleComponent (isIrreducible_irreducibleComponent (x := x)).nonempty.some_mem

/-- Every connected component of a noetherian space is open. -/
theorem isOpen_connectedComponent (x : α) : IsOpen (connectedComponent x) :=
  ConnectedComponents.discreteTopology_iff.mp inferInstance x

/-- In a noetherian space, a point `x` lying in a unique irreducible component has a
preirreducible open neighbourhood, namely the complement of the (finitely many) other
irreducible components. -/
theorem exists_isOpen_isPreirreducible (x : α)
    (h : ∀ Z₁ ∈ irreducibleComponents α, ∀ Z₂ ∈ irreducibleComponents α, x ∈ Z₁ → x ∈ Z₂ →
      Z₁ = Z₂) :
    ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ IsPreirreducible U := by
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  have hopen : IsOpen (⋃ W ∈ irreducibleComponents α \ {irreducibleComponent x}, W)ᶜ :=
    (finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1).isOpen_compl
  refine ⟨_, hopen, ?_, ?_⟩
  · simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun W hW hxW ↦ hW.2 (h W hW.1 _ hZ hxW mem_irreducibleComponent)
  · refine (isIrreducible_irreducibleComponent (x := x)).isPreirreducible.open_subset hopen
      fun y hy ↦ ?_
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hy
    by_contra hyZ
    refine hy _ ⟨irreducibleComponent_mem_irreducibleComponents y, fun h ↦ hyZ ?_⟩
      mem_irreducibleComponent
    rw [← Set.mem_singleton_iff.mp h]
    exact mem_irreducibleComponent

end TopologicalSpace.NoetherianSpace
