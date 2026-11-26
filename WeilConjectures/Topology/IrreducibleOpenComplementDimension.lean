/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.KrullDimension

/-! # Dimension of a proper closed complement

The complement of a nonempty open in an irreducible space of dimension at most `d` is empty or
has dimension at most some `e < d`.

## References

* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ), final induction step.
-/

@[expose] public section

set_option autoImplicit false
universe u
open TopologicalSpace

/-- In an irreducible space of dimension at most `d`, the complement of a nonempty open `U` is
either empty or has dimension at most some `e < d`. -/
theorem irreducible_open_complement_dimension
    (X : Type u) [TopologicalSpace X] [IrreducibleSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (U : Opens X) (hU : U ≠ ⊥) :
    IsEmpty ↥((U : Set X)ᶜ) ∨
      ∃ e : ℕ, e < d ∧ topologicalKrullDim ↥((U : Set X)ᶜ) ≤ (e : WithBot ℕ∞) := by
  let Z := ↥((U : Set X)ᶜ)
  let full : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  let f := IrreducibleCloseds.map (Subtype.val : Z → X) continuous_subtype_val
  have hf : StrictMono f :=
    IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal
  have hproper (c : IrreducibleCloseds Z) : f c < full := by
    refine lt_of_le_of_ne (fun _ _ ↦ Set.mem_univ _) ?_
    intro heq
    obtain ⟨x, hx⟩ := U.ne_bot_iff_nonempty.mp hU
    have hxc : x ∈ (f c : Set X) := by rw [heq]; trivial
    have hsub : (f c : Set X) ⊆ (U : Set X)ᶜ :=
      closure_minimal (by rintro _ ⟨z, _, rfl⟩; exact z.property)
        U.isOpen.isClosed_compl
    exact hsub hxc hx
  have hchain (p : LTSeries (IrreducibleCloseds Z)) : p.length + 1 ≤ d := by
    have h := (Order.LTSeries.length_le_krullDim
      ((p.map f hf).snoc full (hproper _))).trans hdim
    have h' : ((p.length + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      simpa using h
    exact ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp h')
  cases d with
  | zero =>
    left
    refine ⟨fun z ↦ ?_⟩
    let c : IrreducibleCloseds Z :=
      ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    have h := hchain (.singleton _ c)
    simp at h
  | succ e =>
    right
    refine ⟨e, Nat.lt_succ_self e, ?_⟩
    change Order.krullDim (IrreducibleCloseds Z) ≤ (e : WithBot ℕ∞)
    apply iSup_le
    intro p
    have h := Nat.le_of_succ_le_succ (hchain p)
    exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr h)
