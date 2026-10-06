/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension

/-!
# Topological Krull dimension and closed embeddings

## Main statements

- `Topology.IsInducing.surjective_of_topologicalKrullDim_eq`: an inducing map with closed range
  into an irreducible space of finite dimension, from a space of the same dimension, is
  surjective.
-/

@[expose] public section

open Topology TopologicalSpace Order

section Inducing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An inducing map with closed range into an irreducible space of finite dimension, whose
source has the same dimension as the target, is surjective: otherwise a maximal chain of
irreducible closed subsets of the source, pushed forward and followed by the whole space, would be
longer than any chain of the target. -/
theorem Topology.IsInducing.surjective_of_topologicalKrullDim_eq [IrreducibleSpace X]
    {f : Y → X} (hf : IsInducing f) (hc : IsClosed (Set.range f))
    (hfin : topologicalKrullDim X ≠ ⊤) (h : topologicalKrullDim Y = topologicalKrullDim X) :
    Function.Surjective f := by
  by_contra hns
  have hne : Set.range f ≠ Set.univ := fun h ↦ hns (Set.range_eq_univ.1 h)
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    rw [topologicalKrullDim, Ne, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    exact ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 hbot
  have hm' : m ≠ ⊤ := by
    rintro rfl
    exact hfin hm.symm
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hm'
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 (show ((n : ℕ∞) : WithBot ℕ∞) ≤
    topologicalKrullDim Y from h ▸ hm.le)
  let top : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  let l₀ := l.map _ (IrreducibleCloseds.map_strictMono_of_isInducing hf)
  have hlast : l₀.last < top := by
    refine lt_of_le_of_ne (fun x _ ↦ Set.mem_univ x) fun heq ↦ hne ?_
    refine Set.eq_univ_of_univ_subset ?_
    have : (top : Set X) ⊆ closure (f '' l.last) := by
      rw [← heq]
      rfl
    exact this.trans (closure_minimal (Set.image_subset_range _ _) hc)
  let l' := l₀.snoc top hlast
  have := Order.LTSeries.length_le_krullDim l'
  rw [show l'.length = n + 1 by simp [l', l₀, hl]] at this
  change _ ≤ topologicalKrullDim X at this
  rw [← hm] at this
  norm_cast at this
  omega

end Inducing
