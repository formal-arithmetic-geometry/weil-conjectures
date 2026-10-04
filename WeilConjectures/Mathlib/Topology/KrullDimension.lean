/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# Complements of dense opens in spaces of dimension one

In an irreducible `T₀` space of dimension at most one, every point outside a nonempty open subset
is closed; if the space is moreover quasi-sober and noetherian, there are only finitely many such
points.

## Main statements

- `IsOpen.finite_compl_of_topologicalKrullDim_le_one`: the complement of a nonempty open subset
  is finite.
- `IsOpen.isClosed_singleton_of_mem_compl`: each point of that complement is closed.
-/

@[expose] public section

open Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [IrreducibleSpace X] [T0Space X]

/-- In an irreducible `T₀` space of dimension at most one, every point outside a
nonempty open subset `U` is closed: it is not the generic point, so a proper specialization of it
would give a chain of three irreducible closed subsets. -/
theorem IsOpen.isClosed_singleton_of_mem_compl (h : topologicalKrullDim X ≤ 1) {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) {x : X} (hx : x ∉ U) : IsClosed {x} := by
  obtain ⟨u, hu⟩ := hne
  by_contra hcl
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ closure {x}, y ≠ x := by
    by_contra! H
    exact hcl (closure_subset_iff_isClosed.mp fun y hy ↦ H y hy)
  let Y : IrreducibleCloseds X := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  let Z : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h₁ : Y < Z := by
    refine lt_of_le_of_ne (show closure {y} ⊆ closure {x} from
      closure_minimal (by simpa using hy) isClosed_closure) fun h ↦ hyx ?_
    exact (inseparable_iff_closure_eq.mpr congr(($h : Set X))).eq
  have h₂ : Z < T := by
    refine lt_of_le_of_ne (show closure {x} ⊆ Set.univ from Set.subset_univ _) fun h ↦ hx ?_
    have hu' : u ∈ closure ({x} : Set X) := by
      rw [show closure ({x} : Set X) = Set.univ from congr(($h : Set X))]; trivial
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hu' U hU hu
    rwa [Set.mem_singleton_iff.mp hz] at hzU
  let q₁ : LTSeries (IrreducibleCloseds X) := (RelSeries.singleton _ Y).snoc Z h₁
  let q : LTSeries (IrreducibleCloseds X) :=
    q₁.snoc T (by rw [show q₁.last = Z from RelSeries.last_snoc _ _ _]; exact h₂)
  have hq : q.length = 2 := rfl
  have := Order.LTSeries.length_le_krullDim q
  rw [hq] at this
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := this.trans h
  exact absurd h2 (by decide)

/-- In an irreducible quasi-sober noetherian `T₀` space of dimension at most one, the complement
of a nonempty open subset is finite: it is a closed subset all of whose points are closed, so its
finitely many irreducible components are points. -/
theorem IsOpen.finite_compl_of_topologicalKrullDim_le_one [QuasiSober X] [NoetherianSpace X]
    (h : topologicalKrullDim X ≤ 1) {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    Uᶜ.Finite := by
  obtain ⟨S, hSf, hSc, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    hU.isClosed_compl
  have key : ∀ t ∈ S, ∃ z, t = {z} := by
    intro t ht
    obtain ⟨z, hz⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    have hzU : z ∉ U := by
      have : z ∈ Uᶜ := hS ▸ Set.mem_sUnion_of_mem hz.mem ht
      exact this
    exact ⟨z, by rw [← hz.def, (hU.isClosed_singleton_of_mem_compl h hne hzU).closure_eq]⟩
  rw [hS]
  refine hSf.sUnion fun t ht ↦ ?_
  obtain ⟨z, rfl⟩ := key t ht
  exact Set.finite_singleton z
