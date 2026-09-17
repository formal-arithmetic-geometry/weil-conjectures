/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sober

/-!
# Generic points of the maximal irreducible subsets of a closed set

In a sober space a maximal irreducible subset `T` of a closed set `S` is itself closed, so it
has a generic point; that point is the unique point of `S` below which `T` lies, and it is
minimal for specialization among the points of `S`.

## Main results

* `exists_mem_minimal_specializes_of_maximal_isIrreducible`: a maximal irreducible subset of a
  closed subset `S` of a sober `T₀` space contains a point `x ∈ S` such that the only point of
  `S` specializing to `x` is `x` itself.
-/

@[expose] public section

open Set

variable {X : Type*} [TopologicalSpace X] {S T : Set X}

/-- A maximal irreducible subset of a closed set is closed. -/
theorem IsClosed.of_maximal_isIrreducible (hS : IsClosed S)
    (hT : Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) T) : IsClosed T :=
  closure_eq_iff_isClosed.1 (subset_antisymm
    (hT.2 ⟨hT.1.1.closure, hS.closure_subset_iff.2 hT.1.2⟩ subset_closure) subset_closure)

/-- **A maximal irreducible subset of a closed set is the closure of a minimal point.** In a
sober `T₀` space, a maximal irreducible subset `T` of a closed set `S` contains a point `x` —
its generic point — such that every point of `S` specializing to `x` equals `x`. -/
theorem exists_mem_minimal_specializes_of_maximal_isIrreducible [QuasiSober X] [T0Space X]
    (hS : IsClosed S) (hT : Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ S) T) :
    ∃ x ∈ T, ∀ y ∈ S, y ⤳ x → y = x := by
  have hgen : IsGenericPoint hT.1.1.genericPoint T :=
    hT.1.1.isGenericPoint_genericPoint (hS.of_maximal_isIrreducible hT)
  refine ⟨_, hgen.mem, fun y hy hyx ↦ ?_⟩
  have hTy : T ⊆ closure {y} := hgen.def ▸ hyx.closure_subset
  have hyT : closure ({y} : Set X) ⊆ T :=
    hT.2 ⟨isIrreducible_singleton.closure, hS.closure_subset_iff.2 (singleton_subset_iff.2 hy)⟩ hTy
  exact (hyx.antisymm (hgen.specializes (hyT (subset_closure rfl)))).eq
