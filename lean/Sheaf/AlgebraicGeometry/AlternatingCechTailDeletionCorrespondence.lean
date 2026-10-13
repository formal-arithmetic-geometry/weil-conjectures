/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Fin.Basic

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

private def deletePerm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) : Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv k).trans
    ((σ.subtypeEquiv (p := fun i => i ≠ k) (q := fun j => j ≠ σ k)
      (fun _ => σ.injective.ne_iff.symm)).trans (finSuccAboveEquiv (σ k)).symm)

private theorem deletePerm_spec {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) (z : Fin n) :
    (σ k).succAbove (deletePerm σ k z) = σ (k.succAbove z) := by
  have h := (finSuccAboveEquiv (σ k)).apply_symm_apply
    ((σ.subtypeEquiv (p := fun i => i ≠ k) (q := fun j => j ≠ σ k)
      (fun _ => σ.injective.ne_iff.symm)) (finSuccAboveEquiv k z))
  exact congrArg Subtype.val h

private theorem stable_delete {I : Type v} [LinearOrder I] {n : ℕ}
    (t : Fin (n + 1) → I) (σ : Equiv.Perm (Fin (n + 1)))
    (hs : cechStableSort t σ) (k : Fin (n + 1)) :
    cechStableSort (t ∘ (σ k).succAbove) (deletePerm σ k) := by
  constructor
  · intro i j hij
    change t ((σ k).succAbove (deletePerm σ k i)) ≤
      t ((σ k).succAbove (deletePerm σ k j))
    rw [deletePerm_spec, deletePerm_spec]
    exact hs.1 ((Fin.strictMono_succAbove k).monotone hij)
  · intro i j hij ht
    apply (Fin.strictMono_succAbove (σ k)).lt_iff_lt.mp
    rw [deletePerm_spec, deletePerm_spec]
    apply hs.2 _ _ ((Fin.strictMono_succAbove k) hij)
    simpa only [Function.comp_apply, deletePerm_spec] using ht

private theorem stable_unique {I : Type v} [LinearOrder I] {n : ℕ}
    (t : Fin n → I) (σ ρ : Equiv.Perm (Fin n))
    (hσ : cechStableSort t σ) (hρ : cechStableSort t ρ) : σ = ρ :=
  (Tuple.eq_sort_iff.mpr hσ).trans (Tuple.eq_sort_iff.mpr hρ).symm

private theorem outgoing_rank {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I) (x : cechTailOutgoingIndex p t)
    (k : Fin (p + 2)) (hk : k.val + 1 = x.val.2.2.2.val) :
    x.val.2.1.val ≤ k.val ∧ x.val.2.1 < x.val.1.symm (x.val.2.2.1 k) := by
  rcases x with ⟨⟨σ, a, τ, r⟩, ⟨⟨hs, ht⟩, hn⟩, hr⟩
  dsimp only at hk hn hr hs ht ⊢
  have har : a.val < r.val := by
    have hne : a.val ≠ r.val := by
      intro he
      apply hn
      simp only [cechJunction]
      rw [dif_pos (by omega)]
      congr 1
      exact Fin.ext he.symm
    omega
  have hka : a.val ≤ k.val := by omega
  have hnk : τ k ≠ σ a := by
    intro he
    apply hn
    simp only [cechJunction]
    rw [dif_neg (by omega)]
    convert he using 1
    congr 1
    apply Fin.ext
    change r.val - 1 = k.val
    omega
  refine ⟨hka, ?_⟩
  by_contra hd
  have hd' : (σ.symm (τ k)).val ≤ a.val := le_of_not_gt hd
  rcases hd'.eq_or_lt with he | hl
  · apply hnk
    have he' : σ.symm (τ k) = a := Fin.ext he
    exact σ.symm_apply_eq.mp he'
  · have ht' := ht.1 (σ.symm (τ k)) hl
    rw [σ.apply_symm_apply] at ht'
    have he := τ.injective ht'
    have hev := congrArg Fin.val he
    omega

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
        cechJunction (e x).val.2.1 (e x).val.2.2.2 (e x).val.2.2.1 := by
  obtain ⟨k, hk, hj, hτ, ha⟩ := he x
  obtain ⟨hka, hda⟩ := outgoing_rank p t x k hk
  let σ := x.val.1
  let τ := x.val.2.2.1
  let a := x.val.2.1
  let r := x.val.2.2.2
  let y := e x
  let j := y.val.1
  let ρ := y.val.2.1
  let b := y.val.2.2.1
  let η := y.val.2.2.2
  let d := σ.symm j
  have hdj : σ d = j := σ.apply_symm_apply j
  have hdb : a.val < d.val := by
    dsimp only [a, d, σ, j, y]
    rwa [← hj]
  have hρ : deletePerm σ d = ρ := by
    apply stable_unique (t ∘ j.succAbove)
    · simpa only [hdj] using stable_delete t σ x.property.1.1.1 d
    · exact y.property.1.1
  have hp (z : Fin (p + 1)) (hz : z.val ≤ b.val) :
      σ ⟨z.val, by omega⟩ = j.succAbove (ρ z) := by
    have hs := deletePerm_spec σ d z
    have hdz : d.succAbove z = ⟨z.val, by omega⟩ := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by
        simp only [Fin.lt_def, Fin.val_castSucc]
        dsimp only [a, b, y] at hdb hz
        omega)]
      rfl
    rw [hdj, hρ, hdz] at hs
    exact hs.symm
  funext z
  change cechJunction σ τ a (r.succAbove z) = j.succAbove (cechJunction ρ η b z)
  by_cases hz : z.val ≤ b.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by
      simp only [Fin.lt_def, Fin.val_castSucc]
      dsimp only [r, b, y, a] at *
      omega)]
    simp only [cechJunction, Fin.val_castSucc]
    rw [dif_pos (by dsimp only [a, b, y] at *; omega), dif_pos hz]
    exact hp ⟨z.val, by omega⟩ hz
  · simp only [cechJunction]
    rw [dif_neg hz]
    by_cases hzr : z.val < r.val
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by exact hzr)]
      simp only [Fin.val_castSucc]
      rw [dif_neg (by dsimp only [a, b, y] at *; omega)]
      have h := hτ ⟨z.val - 1, by omega⟩
      rw [Fin.succAbove_of_castSucc_lt _ _ (by
        simp only [Fin.lt_def, Fin.val_castSucc]
        dsimp only [r] at hzr
        omega)] at h
      exact h
    · rw [Fin.succAbove_of_le_castSucc _ _ (by exact le_of_not_gt hzr)]
      simp only [Fin.val_succ]
      rw [dif_neg (by dsimp only [a, b, y] at *; omega)]
      have h := hτ ⟨z.val - 1, by omega⟩
      rw [Fin.succAbove_of_le_castSucc _ _ (by
        simp only [Fin.le_def, Fin.val_castSucc]
        dsimp only [r] at hzr
        omega)] at h
      convert h using 1
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega


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
