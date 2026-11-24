/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import Mathlib.Data.Fin.Tuple.Sort
import WeilConjectures.AlgebraicGeometry.AlternatingCechPartialSortUnique

@[expose] public section
set_option autoImplicit false
universe v
namespace AlgebraicGeometry.Scheme

private theorem restrict_perm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (r j : Fin (n + 1)) (h : σ r = j) :
    ∃ ρ : Equiv.Perm (Fin n), ∀ k, σ (r.succAbove k) = j.succAbove (ρ k) := by
  let hne : ∀ a, a ≠ r ↔ σ a ≠ j := fun a ↦ by
    rw [← h, σ.injective.ne_iff]
  let ρ := ((finSuccAboveEquiv r).trans (σ.subtypeEquiv hne)).trans
    (finSuccAboveEquiv j).symm
  refine ⟨ρ, ?_⟩
  intro k
  have he := (finSuccAboveEquiv j).apply_symm_apply
    ((σ.subtypeEquiv hne) ((finSuccAboveEquiv r) k))
  exact (congrArg Subtype.val he).symm

private theorem stable_restrict {I : Type v} [LinearOrder I] {n : ℕ}
    (t : Fin (n + 1) → I) (σ : Equiv.Perm (Fin (n + 1)))
    (ρ : Equiv.Perm (Fin n)) (r j : Fin (n + 1))
    (hs : cechStableSort t σ)
    (hr : ∀ k, σ (r.succAbove k) = j.succAbove (ρ k)) :
    cechStableSort (t ∘ j.succAbove) ρ := by
  constructor
  · intro k l hkl
    have he := hs.1 ((Fin.strictMono_succAbove r).monotone hkl)
    simpa only [Function.comp_apply, hr] using he
  · intro k l hkl he
    apply (Fin.strictMono_succAbove j).lt_iff_lt.mp
    rw [← hr k, ← hr l]
    apply hs.2 _ _ ((Fin.strictMono_succAbove r) hkl)
    simpa only [hr, Function.comp_apply] using he

/-- Restriction identities for a prefix-deletion equivalence satisfying its base facts
(Stacks, Tag 01FM). -/
theorem prefixDeletionRestrictions {I : Type v} [LinearOrder I] (p : ℕ)
    (t : Fin (p + 2) → I)
    (e : ({x : Equiv.Perm (Fin (p + 2)) × Fin (p + 2) ×
      Equiv.Perm (Fin (p + 2)) × Fin (p + 3) //
    (cechStableSort t x.1 ∧ cechPartialSort x.1 x.2.2.1 x.2.1) ∧
      x.2.2.2.val < x.2.1.val}) ≃
      ({y : Fin (p + 2) × Equiv.Perm (Fin (p + 1)) × Fin (p + 1) ×
      Equiv.Perm (Fin (p + 1)) //
    (cechStableSort (t ∘ y.1.succAbove) y.2.1 ∧
      cechPartialSort y.2.1 y.2.2.2 y.2.2.1) ∧
    (t y.1 < t (y.1.succAbove (y.2.1 y.2.2.1)) ∨
      (t y.1 = t (y.1.succAbove (y.2.1 y.2.2.1)) ∧
        y.1 < y.1.succAbove (y.2.1 y.2.2.1)))}))
    (h : ∀ x, let y := e x
      x.1.2.1.val = y.1.2.2.1.val + 1 ∧
      ∃ hr : x.1.2.2.2.val < p + 2,
        x.1.2.2.1 ⟨x.1.2.2.2.val, hr⟩ = y.1.1) :
    ∀ x,
      let y := e x
      ∃ hr : x.1.2.2.2.val < p + 2,
        (∀ k : Fin (p + 1),
          x.1.1 ((⟨x.1.2.2.2.val, hr⟩ : Fin (p + 2)).succAbove k) =
            y.1.1.succAbove (y.1.2.1 k)) ∧
        (∀ k : Fin (p + 1),
          x.1.2.2.1 ((⟨x.1.2.2.2.val, hr⟩ : Fin (p + 2)).succAbove k) =
            y.1.1.succAbove (y.1.2.2.2 k)) := by
  intro x
  obtain ⟨ha, hr, hj⟩ := h x
  let r : Fin (p + 2) := ⟨x.1.2.2.2.val, hr⟩
  have hσr : x.1.1 r = (e x).1.1 := by
    rw [← hj]
    exact (x.2.1.2.1 r x.2.2).symm
  obtain ⟨ρ, hρ⟩ := restrict_perm x.1.1 r (e x).1.1 hσr
  have hsρ := stable_restrict t x.1.1 ρ r (e x).1.1 x.2.1.1 hρ
  have heρ : ρ = (e x).1.2.1 :=
    (Tuple.eq_sort_iff.mpr hsρ).trans (Tuple.eq_sort_iff.mpr (e x).2.1.1).symm
  subst ρ
  obtain ⟨η, hη⟩ := restrict_perm x.1.2.2.1 r (e x).1.1 hj
  have hsη : cechPartialSort (e x).1.2.1 η (e x).1.2.2.1 := by
    constructor
    · intro k hk
      apply (Fin.strictMono_succAbove (e x).1.1).injective
      rw [← hη k, ← hρ k]
      apply x.2.1.2.1
      dsimp only [r]
      simp only [Fin.succAbove]
      split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ, Fin.lt_def] at * <;> omega
    · intro k l hk hkl
      apply (Fin.strictMono_succAbove (e x).1.1).lt_iff_lt.mp
      rw [← hη k, ← hη l]
      apply x.2.1.2.2 _ _ ?_ ((Fin.strictMono_succAbove r) hkl)
      dsimp only [r]
      simp only [Fin.succAbove]
      split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ, Fin.lt_def] at * <;> omega
  obtain ⟨η₀, _, hu⟩ := cechPartialSort_existsUnique (p + 1) (e x).1.2.1
    (e x).1.2.2.1.val (Nat.le_of_lt (e x).1.2.2.1.isLt)
  have heη : η = (e x).1.2.2.2 := (hu η hsη).trans (hu _ (e x).2.1.2).symm
  subst η
  exact ⟨hr, hρ, hη⟩

end AlgebraicGeometry.Scheme
