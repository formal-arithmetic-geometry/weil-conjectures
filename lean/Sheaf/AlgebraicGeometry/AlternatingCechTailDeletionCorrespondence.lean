/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators

/-!
# Unsigned correspondence for tail deletions

Source: Stacks Project, Tag 01FM, verification of equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-correspondence)
-/

@[expose] public section

set_option autoImplicit false

universe v

namespace AlgebraicGeometry.Scheme

/-- Filtered outgoing tail indices, retaining original labels.
Source: Stacks 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-correspondence) -/
abbrev cechTailOutgoingIndex {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :=
  {x : Equiv.Perm (Fin (p + 2)) × Fin (p + 2) ×
      Equiv.Perm (Fin (p + 2)) × Fin (p + 3) //
    ((cechStableSort t x.1 ∧ cechPartialSort x.1 x.2.2.1 x.2.1) ∧
      cechJunction x.1 x.2.2.1 x.2.1 x.2.2.2 ≠ x.1 x.2.1) ∧
      ¬ x.2.2.2.val < x.2.1.val}

/-- Filtered incoming indices whose omitted label follows the junction in stable order.
Source: Stacks 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-correspondence) -/
abbrev cechTailIncomingIndex {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :=
  {y : Fin (p + 2) × Equiv.Perm (Fin (p + 1)) × Fin (p + 1) ×
      Equiv.Perm (Fin (p + 1)) //
    (cechStableSort (t ∘ y.1.succAbove) y.2.1 ∧
      cechPartialSort y.2.1 y.2.2.2 y.2.2.1) ∧
      ¬ (t y.1 < t (y.1.succAbove (y.2.1 y.2.2.1)) ∨
        (t y.1 = t (y.1.succAbove (y.2.1 y.2.2.1)) ∧
          y.1 < y.1.succAbove (y.2.1 y.2.2.1)))}

/-- The deletion correspondence with the rank, restriction, and prefix identities.
Proof: construct deletion and insertion maps on the finite permutations and verify their
properties by the defining cases of stable and partial sorting.
Source: Stacks Project, Tag 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-basic) -/
theorem cechTailDeletionBasic {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :
    ∃ e : cechTailOutgoingIndex p t ≃ cechTailIncomingIndex p t,
      ∀ x, ∃ k : Fin (p + 2),
        k.val + 1 = x.val.2.2.2.val ∧
        x.val.2.2.1 k = (e x).val.1 ∧
        (∀ z, x.val.2.2.1 (k.succAbove z) =
          (e x).val.1.succAbove ((e x).val.2.2.2 z)) ∧
        x.val.2.1.val = (e x).val.2.2.1.val := by sorry

/-- The junction-map identity for the basic tail deletion correspondence.
Proof: use the deletion identities to check the two cases in the definition of the
junction map, giving equality on every finite position.
Source: Stacks Project, Tag 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-tail-deletion-junction) -/
theorem cechTailDeletionJunction {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) (e : cechTailOutgoingIndex p t ≃ cechTailIncomingIndex p t)
    (he : ∀ x, ∃ k : Fin (p + 2),
      k.val + 1 = x.val.2.2.2.val ∧
      x.val.2.2.1 k = (e x).val.1 ∧
      (∀ z, x.val.2.2.1 (k.succAbove z) =
        (e x).val.1.succAbove ((e x).val.2.2.2 z)) ∧
      x.val.2.1.val = (e x).val.2.2.1.val)
    (x : cechTailOutgoingIndex p t) :
    cechJunction x.val.1 x.val.2.2.1 x.val.2.1 ∘ x.val.2.2.2.succAbove =
      (e x).val.1.succAbove ∘
        cechJunction (e x).val.2.1 (e x).val.2.2.2 (e x).val.2.2.1 := by sorry

theorem cechTailDeletionCorrespondence {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) :
    ∃ e : cechTailOutgoingIndex p t ≃ cechTailIncomingIndex p t,
      ∀ x, ∃ k : Fin (p + 2),
        k.val + 1 = x.val.2.2.2.val ∧
        x.val.2.2.1 k = (e x).val.1 ∧
        (∀ z, x.val.2.2.1 (k.succAbove z) =
          (e x).val.1.succAbove ((e x).val.2.2.2 z)) ∧
        x.val.2.1.val = (e x).val.2.2.1.val ∧
        cechJunction x.val.1 x.val.2.2.1 x.val.2.1 ∘ x.val.2.2.2.succAbove =
          (e x).val.1.succAbove ∘
      cechJunction (e x).val.2.1 (e x).val.2.2.2 (e x).val.2.2.1 := by
  obtain ⟨e, he⟩ := cechTailDeletionBasic p t
  refine ⟨e, ?_⟩
  intro x
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := he x
  have hk5 := cechTailDeletionJunction p t e he x
  exact ⟨k, hk1, hk2, hk3, hk4, hk5⟩


end AlgebraicGeometry.Scheme
