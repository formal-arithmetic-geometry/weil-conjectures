/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Logic.Relation
public import Mathlib.LinearAlgebra.Span.Defs
import WeilConjectures.RingTheory.LocalGeneratingTuples
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! # Elementary chains for tuples with equal spans

Source: the local-ring paragraph of lem-pur-frame-independence.proof.md.
-/

@[expose] public section
set_option autoImplicit false

universe u v

namespace Module

/-- One invertible elementary operation on an ordered tuple.
Source: the local-ring paragraph of frame independence
(blueprint: lem-pur-generating-tuple-chain). -/
def GeneratingTupleStep {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] {c : ℕ} (f g : Fin c → M) : Prop :=
  (∃ (i : Fin c) (a : Rˣ),
    ∀ k, g k = if k = i then (a : R) • f i else f k) ∨
  (∃ (i j : Fin c), i ≠ j ∧
    ∀ k, g k = if k = i then f j else if k = j then f i else f k) ∨
  (∃ (i j : Fin c) (a : R), i ≠ j ∧
    ∀ k, g k = if k = i then f i + a • f j else f k)

/-- Tuples with equal spans over a local ring are joined by elementary operations,
without requiring the ambient module to be finite.
Source: Stacks Tags 00DV and 00E9, and the local-ring paragraph of the blueprint
(blueprint: lem-pur-generating-tuple-chain).
Proof: work in the common span, which is finite because the tuple is finite.
Both lifted tuples generate that module. Apply the stated local generator theorem,
discard its matrix witnesses, then map each elementary step through the inclusion. -/
theorem generatingTupleChain {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (c : ℕ) (f g : Fin c → M)
    (hfg : Submodule.span R (Set.range f) = Submodule.span R (Set.range g)) :
    Relation.ReflTransGen (GeneratingTupleStep (R := R)) f g := by
  classical
  let I := Submodule.span R (Set.range f)
  have hfinite : _root_.Module.Finite R I :=
    _root_.Module.Finite.span_of_finite R (Set.finite_range f)
  let f' : Fin c → I := fun k ↦ ⟨f k, Submodule.subset_span ⟨k, rfl⟩⟩
  let g' : Fin c → I := fun k ↦
    ⟨g k, by
      change g k ∈ Submodule.span R (Set.range f)
      rw [hfg]
      exact Submodule.subset_span ⟨k, rfl⟩⟩
  have hf : Submodule.span R (Set.range f') = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff I _).mpr rfl
  have hg : Submodule.span R (Set.range g') = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff I _).mpr hfg.symm
  obtain ⟨s, x, A, hx0, hxs, hstep, _⟩ :=
    exists_elementary_generating_tuple_change c f' g' hf hg
  have hs (t : ℕ) (ht : t < s) :
      GeneratingTupleStep (R := R) (fun k ↦ (x t k : M))
        (fun k ↦ (x (t + 1) k : M)) := by
    rcases hstep t ht with ⟨i, a, h, _⟩ | ⟨i, j, hij, h, _⟩ |
      ⟨i, j, a, hij, h, _⟩
    · left
      refine ⟨i, a, fun k ↦ ?_⟩
      by_cases hk : k = i
      · simpa only [if_pos hk, Submodule.coe_smul] using congrArg Subtype.val (h k)
      · simpa only [if_neg hk] using congrArg Subtype.val (h k)
    · right; left
      refine ⟨i, j, hij, fun k ↦ ?_⟩
      by_cases hk : k = i
      · simpa only [if_pos hk] using congrArg Subtype.val (h k)
      · by_cases hk' : k = j
        · simpa only [if_neg hk, if_pos hk'] using congrArg Subtype.val (h k)
        · simpa only [if_neg hk, if_neg hk'] using congrArg Subtype.val (h k)
    · right; right
      refine ⟨i, j, a, hij, fun k ↦ ?_⟩
      by_cases hk : k = i
      · simpa only [if_pos hk, Submodule.coe_add, Submodule.coe_smul] using
          congrArg Subtype.val (h k)
      · simpa only [if_neg hk] using congrArg Subtype.val (h k)
  have hchain (t : ℕ) (ht : t ≤ s) :
      Relation.ReflTransGen (GeneratingTupleStep (R := R))
        (fun k ↦ (x 0 k : M)) (fun k ↦ (x t k : M)) := by
    induction t with
    | zero => exact .refl
    | succ t ih => exact (ih (by omega)).tail (hs t (by omega))
  simpa only [hx0, hxs, f', g'] using hchain s le_rfl

end Module
