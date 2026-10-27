/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.RingTheory.CoordinateSubmodule
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.Set.Countable
public import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.RelClasses

/-!
# Exhaustive coordinate filtrations with projective successive quotients

Source: Stacks Project, Algebra, Tag 05A9, `theorem-ffdescent-projectivity`,
initial, limit, least-missing-element and exhaustion paragraphs, abstracting the
successor enlargement property (blueprint: lem-trf-coordinate-projective-exhaustion).
-/

@[expose] public section

set_option autoImplicit false

universe u v w s t

open scoped TensorProduct DirectSum

namespace Module

/-- The successor enlargement property gives a continuous exhaustive coordinate filtration.

The chosen well-order and its enumeration are represented by `LinearOrder M` and the
order isomorphism `e` from the ordinals below `κ`; the latter also certifies well-foundedness.
For a submodule `U`, `(U.baseChange B).map θ.toLinearMap` is exactly the image of
`B ⊗[A] U → B ⊗[A] M` transported by `θ`. Quotients use the inverse image of the
preceding submodule under the successor submodule's inclusion into `M`.

Source: Stacks Project, Algebra, Tag 05A9, `theorem-ffdescent-projectivity`,
initial, limit, least-missing-element and exhaustion paragraphs, abstracting only the
successor property (blueprint: lem-trf-coordinate-projective-exhaustion).

Proof:
1. Use `lem-weil-pbc-well-ordering-theorem` to well-order pairs of a submodule and an
   index subset. For each valid proper pair choose the least successor-property witness
   for its least missing element. Use `lem-weil-pbc-transfinite-recursion` on ordinals
   at most `κ`: start at `(0, ∅)`, use that witness at a valid proper successor, keep a
   stationary or invalid pair unchanged, and at nonzero limits take unions when the
   earlier modules form a chain, using `(0, ∅)` otherwise. Increasing unions are
   submodules since finitely many elements lie together in their largest stage.
2. A least failure of increasingness is impossible: successors contain their predecessor
   and, when all preceding stages increase, the limit rule is their union. Thus both
   families increase and both asserted limit union identities hold.
3. Inductively prove the coordinate-image identity. At zero all tensors from the zero
   module vanish by `def-weil-pbc-module-tensor-product`; a family supported in the empty
   set is zero by `def-trf-coordinate-submodule`. At proper successors the selected
   witness supplies the identity and the least missing element. At stationary successors
   the preceding identity persists.
4. At a nonzero limit, each tensor is a finite sum of pure tensors, by
   `def-weil-pbc-module-tensor-product`. Their module entries lie in one earlier stage,
   taking the finite maximum of their witness stages, or zero for an empty sum.
   Functoriality of the inclusion-induced maps gives the reverse inclusion. Likewise,
   by `def-weil-pbc-direct-sum-modules` and `def-trf-coordinate-submodule`, finite
   coordinate support in the union of the index sets lies in one earlier index set.
   Therefore both tensor images and coordinate submodules commute with these unions,
   completing the invariant's induction. No invalid successor branch occurs.
5. At a proper successor the witness supplies countable generation and projectivity of
   the quotient. At a stationary successor the quotient is zero by
   `def-weil-pbc-quotient-module`, is spanned by the empty set, and is projective by
   the zero-map lifting characterization in `def-weil-pbc-projective-module`.
6. Induct on the stage to prove all earlier enumerated elements are present. At a
   successor, the current enumerated element either already belongs or is the least
   missing one, since all its predecessors belong. At a nonzero limit, every earlier
   index has its successor still below the limit. Surjectivity of `e` gives exhaustion
   at `κ`. Only finite tensor expressions and finite coordinate supports are used;
   neither flatness nor countable generation or projectivity of the summands is used.
-/
theorem exists_coordinate_projective_exhaustion
    (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
    (M : Type w) [AddCommGroup M] [Module A M]
    (I : Type s) (Q : I → Type t) [∀ i, AddCommGroup (Q i)] [∀ i, Module B (Q i)]
    (θ : (B ⊗[A] M) ≃ₗ[B] DirectSum I Q)
    (henlarge : ∀ (U : Submodule A M) (H : Set I),
      (U.baseChange B).map θ.toLinearMap = DirectSum.coordinateSubmodule B I Q H →
      ∀ x : M, x ∉ U → ∃ (V : Submodule A M) (H' : Set I),
        U ≤ V ∧ x ∈ V ∧ H ⊆ H' ∧
        (V.baseChange B).map θ.toLinearMap = DirectSum.coordinateSubmodule B I Q H' ∧
        (∃ S : Set (V ⧸ U.comap V.subtype), S.Countable ∧ Submodule.span A S = ⊤) ∧
        Module.Projective A (V ⧸ U.comap V.subtype))
    [LinearOrder M] (κ : Ordinal.{w}) (e : Set.Iio κ ≃o M) :
    ∃ (F : Set.Iic κ → Submodule A M) (H : Set.Iic κ → Set I),
      Monotone F ∧ Monotone H ∧
      F ⟨0, bot_le (a := κ)⟩ = ⊥ ∧ H ⟨0, bot_le (a := κ)⟩ = ∅ ∧
      F ⟨κ, le_refl κ⟩ = ⊤ ∧
      (∀ α : Set.Iic κ,
        ((F α).baseChange B).map θ.toLinearMap = DirectSum.coordinateSubmodule B I Q (H α)) ∧
      (∀ l : Set.Iic κ, Order.IsSuccLimit l.val →
        (F l : Set M) = ⋃ (α : Set.Iic κ) (_ : α < l), (F α : Set M)) ∧
      (∀ l : Set.Iic κ, Order.IsSuccLimit l.val →
        H l = ⋃ (α : Set.Iic κ) (_ : α < l), H α) ∧
      (∀ (α : Set.Iic κ) (hα : α.val < κ),
        (∃ S : Set (F ⟨Order.succ α.val, Order.succ_le_of_lt hα⟩ ⧸
            (F α).comap (F ⟨Order.succ α.val, Order.succ_le_of_lt hα⟩).subtype),
          S.Countable ∧ Submodule.span A S = ⊤) ∧
        Module.Projective A (F ⟨Order.succ α.val, Order.succ_le_of_lt hα⟩ ⧸
          (F α).comap (F ⟨Order.succ α.val, Order.succ_le_of_lt hα⟩).subtype) ∧
        (F α ≠ ⊤ → ∃ x : M, x ∉ F α ∧ (∀ y : M, y < x → y ∈ F α) ∧
          x ∈ F ⟨Order.succ α.val, Order.succ_le_of_lt hα⟩) ∧
        (F α = ⊤ → F ⟨Order.succ α.val, Order.succ_le_of_lt hα⟩ = F α ∧
          H ⟨Order.succ α.val, Order.succ_le_of_lt hα⟩ = H α)) ∧
      (∀ (α : Set.Iic κ) (β : Set.Iio κ), β.val < α.val → e β ∈ F α) := by
  sorry

end Module
