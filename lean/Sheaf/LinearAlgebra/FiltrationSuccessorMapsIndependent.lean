/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Independence of maps into successive filtration stages

Source: Stacks Project, Tag 058V, Lemma `lemma-direct-sum-devissage`, injectivity
paragraph, in its maximal finite-support formulation
(blueprint: lem-trf-filtration-successor-maps-independent).
-/

@[expose] public section

universe u v w z

namespace Module

/-- Successor maps injective modulo the preceding stage have an injective sum.

Source: Stacks Project, Tag 058V, Lemma `lemma-direct-sum-devissage`, injectivity
paragraph, using only independence modulo the preceding stage
(blueprint: lem-trf-filtration-successor-maps-independent).

The sum map is `DirectSum.toModule` applied to each successor map followed by the
submodule inclusion into `X`. Its value is the sum over the finite support.
There is no assumption on the initial stage, exhaustion, limit-stage continuity,
or generation of successor stages.

Proof, following the five steps of the node:
1. By `def-weil-pbc-direct-sum-modules`, each element has finite support. Summing
   the linear maps into `X` gives a linear map: addition can be checked on the
   finite union of supports, and scalar multiplication preserves finite support.
2. If an element of its kernel has nonempty support, choose its largest index
   `γ`; such an index exists by induction on a nonempty finite linearly ordered
   set, replacing the maximum by the larger element when adjoining a new index.
3. For every support index `α < γ`, one has `α + 1 ≤ γ`, so monotonicity puts
   `t α (a α)` in `F γ`. Closure of `F γ` under finite sums and negation puts
   the negative sum of these earlier terms in `F γ` as well.
4. The zero sum identifies the last term `t γ (a γ)` with that negative sum.
   Independence modulo `F γ` forces `a γ = 0`, contradicting membership in the
   support. Thus the support is empty and every coordinate is zero.
5. Apply the kernel argument to the difference of two elements with the same
   image to obtain injectivity. When `κ = 0`, the direct sum has no coordinates.
   Only monotonicity, finite support, and the stated implication were used.
-/
theorem directSum_toModule_injective_of_filtration_successor_maps
    (R : Type u) [CommRing R] (X : Type v) [AddCommGroup X] [Module R X]
    (κ : Ordinal.{w}) (F : Set.Iic κ → Submodule R X) (hmono : Monotone F)
    (A : Set.Iio κ → Type z) [∀ α, AddCommGroup (A α)] [∀ α, Module R (A α)]
    (t : ∀ α : Set.Iio κ,
      A α →ₗ[R] F ⟨Order.succ α.val,
        Order.succ_le_of_lt (a := α.val) (b := κ) α.property⟩)
    (hind : ∀ (α : Set.Iio κ) (a : A α),
      (t α a : X) ∈ F ⟨α.val, le_of_lt (a := α.val) (b := κ) α.property⟩ → a = 0) :
    Function.Injective (DirectSum.toModule R (Set.Iio κ) X
      (fun α ↦ (F ⟨Order.succ α.val,
        Order.succ_le_of_lt (a := α.val) (b := κ) α.property⟩).subtype.comp (t α))) := by
  sorry

end Module
