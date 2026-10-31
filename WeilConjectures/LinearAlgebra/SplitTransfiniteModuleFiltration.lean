/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Split transfinite module filtrations

Source: Stacks Project, Tags 058U and 058V, Definition `definition-devissage` and Lemma
`lemma-direct-sum-devissage` (blueprint: lem-trf-split-transfinite-module-filtration).
-/

@[expose] public section

universe u v w

open scoped DirectSum

namespace Module

/-- A continuous split transfinite filtration is a direct sum of its successive quotients.

Source: Stacks Project, Tags 058U and 058V, Definition `definition-devissage` and Lemma
`lemma-direct-sum-devissage`, with the endpoint included by indexing the source filtration
by the successor ordinal of `κ` (blueprint: lem-trf-split-transfinite-module-filtration).

Proof, following the five steps of the node:
1. Choose a linear retraction `rα` of each successor inclusion `jα`. For the quotient
   map `qα`, define a section by `sα(qα(x)) = x - jα(rα(x))`. Changing the representative
   by `jα(a)` changes this expression by zero, so it is well defined and linear.
   Moreover `qα(sα(z)) = z`, every successor element is the sum of a predecessor
   element and a section value, and a section value in the predecessor is zero.
   This uses `def-weil-pbc-quotient-module`.
2. Using `def-weil-pbc-direct-sum-modules`, define a linear map `f` from the direct sum
   of the quotients to `X` by summing the section values on the finite support.
   Families supported below `β` map into `F β` because the filtration is increasing.
3. If surjectivity onto a stage first failed at `β`, then `β` is neither zero (both
   sides are zero), nor a successor (split off its last quotient and use the earlier
   stage), nor a nonzero limit (continuity places each element in an earlier stage).
   Thus all stages are in the image; the endpoint is all of `X`.
4. A nonzero element in the kernel has a finite nonempty support with largest index
   `γ`. All lower section values lie in `F γ`, so its last section value lies there
   too. Applying the quotient map forces its `γ`-component to vanish, a contradiction.
   This uses the finite-support and quotient constructions of the two dependency nodes
   and works at a limit endpoint as well.
5. The bijective linear map has a linear inverse, giving the asserted equivalence in
   the orientation `X` to the direct sum. When `κ = 0`, both modules are zero and the
   direct sum is empty. No generation or projectivity assumption is used.
-/
theorem nonempty_linearEquiv_directSum_of_split_transfinite_filtration
    (R : Type u) [CommRing R] (X : Type v) [AddCommGroup X] [Module R X]
    (κ : Ordinal.{w}) (F : Set.Iic κ → Submodule R X) (hmono : Monotone F)
    (hzero : F ⟨0, bot_le (a := κ)⟩ = ⊥) (htop : F ⟨κ, le_refl κ⟩ = ⊤)
    (hcont : ∀ l : Set.Iic κ, Order.IsSuccLimit l.val →
      ∀ x : X, x ∈ F l ↔ ∃ β : Set.Iic κ, β < l ∧ x ∈ F β)
    (hsplit : ∀ (α : Set.Iic κ) (hα : α.val < κ),
      ∃ r : F ⟨Order.succ α.val, Order.succ_le_of_lt hα⟩ →ₗ[R] F α,
        ∀ x : F α,
          r (Submodule.inclusion
            (hmono (a := α) (b := ⟨Order.succ α.val, Order.succ_le_of_lt hα⟩)
              (Order.le_succ α.val)) x) = x) :
    Nonempty (X ≃ₗ[R] (⨁ α : Set.Iio κ,
      (F ⟨Order.succ α.val, Order.succ_le_of_lt (a := α.val) (b := κ) α.property⟩ ⧸
        (F ⟨α.val, le_of_lt (a := α.val) (b := κ) α.property⟩).comap
          (F ⟨Order.succ α.val,
            Order.succ_le_of_lt (a := α.val) (b := κ) α.property⟩).subtype))) := by
  sorry

end Module
