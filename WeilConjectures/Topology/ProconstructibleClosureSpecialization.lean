/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Constructible
import WeilConjectures.Topology.SpectralSpace.Constructible

/-!
# Specializations in the closure of an intersection of constructible sets

In a spectral space, every point in the closure of an intersection of constructible sets is a
specialization of a point of that intersection.

## References

* [Stacks Project, Tag 0903](https://stacks.math.columbia.edu/tag/0903), part (1)
-/

@[expose] public section

universe u v

namespace Topology

/-- In a spectral space, every point in the closure of an intersection of constructible sets
is a specialization of a point of that intersection. -/
theorem exists_mem_iInter_closure_singleton {X : Type u} [TopologicalSpace X]
    [SpectralSpace X] {A : Type v} (E : A → Set X)
    (hE : ∀ a : A, IsConstructible (E a)) {x : X} (hx : x ∈ closure (⋂ a : A, E a)) :
    ∃ e : X, e ∈ (⋂ a : A, E a) ∧ x ∈ closure ({e} : Set X) := by
  have hclosed : IsClosed[constructibleTopology X] (⋂ a : A, E a) := by
    exact @isClosed_iInter X A (constructibleTopology X) E (fun a =>
      (hE a).isClopen_constructibleTopology.1)
  obtain ⟨e, he, hsp⟩ :=
    exists_specializes_of_isClosed_constructibleTopology_of_mem_closure hclosed hx
  exact ⟨e, he, specializes_iff_mem_closure.mp hsp⟩

end Topology
