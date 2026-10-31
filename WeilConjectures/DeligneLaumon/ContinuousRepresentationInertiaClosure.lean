/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-! # Killing a topological normal closure in a continuous representation

Source: Stacks 0BTD, the closed-normal-kernel argument in proof step 3 of
lem-dl-a1-condensed-lisse-extension-inertia.
(blueprint: lem-dl-a1-continuous-representation-inertia-closure).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Representation

/-- A continuous action on a Hausdorff module kills a subgroup exactly when it
kills its closed normal closure.

Source: Stacks 0BTD and the elementary kernel argument in proof step 3 of
lem-dl-a1-condensed-lisse-extension-inertia.
(blueprint: lem-dl-a1-continuous-representation-inertia-closure).

Proof: the representation kernel is the intersection, over all vectors v, of
closed sets rho(g)v = v, so is closed. It is normal as the kernel of the action
homomorphism into the units of the endomorphism monoid. If it contains S, it
contains the normal closure and then its topological closure. The converse
uses S contained in both closures. This includes the zero module and S = bottom.
-/
theorem kills_topological_normalClosure_iff
    {k : Type u} [CommSemiring k] {G : Type v} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type w} [AddCommMonoid V] [Module k V]
    [TopologicalSpace V] [T2Space V]
    (ρ : Representation k G V) (hc : ∀ v : V, Continuous (fun g : G ↦ ρ g v))
    (S : Subgroup G) :
    (∀ g ∈ (Subgroup.normalClosure (S : Set G)).topologicalClosure, ρ g = 1) ↔
      ∀ g ∈ S, ρ g = 1 := by
  let K := ρ.asGroupHom.ker
  have hK {g : G} : g ∈ K ↔ ρ g = 1 := by
    constructor
    · intro h
      exact congrArg Units.val h
    · intro h
      exact Units.ext h
  have hset : (K : Set G) = ⋂ v : V, {g : G | ρ g v = v} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    change (g ∈ K) ↔ ∀ v : V, ρ g v = v
    rw [hK]
    constructor
    · intro h v
      rw [h]
      rfl
    · intro h
      exact LinearMap.ext h
  have hclosed : IsClosed (K : Set G) := by
    rw [hset]
    exact isClosed_iInter fun v ↦ isClosed_eq (hc v) continuous_const
  constructor
  · intro h g hg
    exact h g ((Subgroup.le_topologicalClosure _)
      (Subgroup.subset_normalClosure hg))
  · intro h
    have hn : Subgroup.normalClosure (S : Set G) ≤ K :=
      Subgroup.normalClosure_le_normal (fun g hg ↦ hK.mpr (h g hg))
    exact fun g hg ↦ hK.mp
      ((Subgroup.topologicalClosure_minimal _ hn hclosed) hg)

end Representation
