/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Uniqueness of a permutation with prescribed prefix and increasing tail

Source: Stacks Project, Tag 01FM, definition of sigma_a preceding
`cohomology-equation-first-homotopy`.
-/

@[expose] public section
set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-- The partial sorting filter has exactly one solution, including the empty tail
(Stacks, Tag 01FM). -/
theorem cechPartialSort_existsUnique (n : ℕ) (σ : Equiv.Perm (Fin n))
    (a : ℕ) (_ha : a ≤ n) :
    ∃! τ : Equiv.Perm (Fin n),
      (∀ k, k.val < a → τ k = σ k) ∧
      (∀ i j, a ≤ i.val → i < j → τ i < τ j)  := by
  classical
  let f : Fin n → ℕ := fun k =>
    if (σ.symm k).val < a then (σ.symm k).val else n + k.val
  have hf : Function.Injective f := by
    intro i j hij
    dsimp only [f] at hij
    split_ifs at hij with hi hj hj
    · apply σ.symm.injective
      exact Fin.ext hij
    · omega
    · omega
    · exact Fin.ext (by omega)
  let τ := Tuple.sort f
  have hm : Monotone (f ∘ τ) := Tuple.monotone_sort f
  have hp : ∀ k : Fin n, k.val < a → τ k = σ k := by
    intro k
    have aux : ∀ m, ∀ k : Fin n, k.val = m → k.val < a → τ k = σ k := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro k hkm hka
        let b := τ.symm (σ k)
        have hbk : k ≤ b := by
          by_contra h
          have hb : b.val < k.val := lt_of_not_ge h
          have he : τ b = σ b := ih b.val (by omega) b rfl (by omega)
          have he' : τ b = σ k := τ.apply_symm_apply (σ k)
          have := σ.injective (he.symm.trans he')
          have hv := congrArg Fin.val this
          omega
        have hfk : f (τ k) ≤ k.val := by
          have := hm hbk
          simpa only [Function.comp_apply, b, τ.apply_symm_apply, f,
            σ.symm_apply_apply, hka, ite_true] using this
        have hpre : (σ.symm (τ k)).val < a := by
          by_contra hn
          simp only [f, hn, ite_false] at hfk
          omega
        have hrank : (σ.symm (τ k)).val ≤ k.val := by
          simpa only [f, hpre, ite_true] using hfk
        have heq : σ.symm (τ k) = k := by
          by_contra hne
          have hl : (σ.symm (τ k)).val < k.val :=
            lt_of_le_of_ne hrank (fun he => hne (Fin.ext he))
          have he := ih (σ.symm (τ k)).val (by omega) _ rfl (by omega)
          rw [σ.apply_symm_apply] at he
          have := τ.injective he
          have hv := congrArg Fin.val this
          omega
        exact σ.symm_apply_eq.mp heq
    exact aux k.val k rfl
  have tail_rank (π : Equiv.Perm (Fin n))
      (hπ : ∀ k : Fin n, k.val < a → π k = σ k)
      (i : Fin n) (hi : a ≤ i.val) : a ≤ (σ.symm (π i)).val := by
    by_contra h
    have hl : (σ.symm (π i)).val < a := lt_of_not_ge h
    have he := hπ _ hl
    rw [σ.apply_symm_apply] at he
    have := π.injective he
    have hv := congrArg Fin.val this
    omega
  have ht : ∀ i j : Fin n, a ≤ i.val → i < j → τ i < τ j := by
    intro i j hi hij
    have hi' := tail_rank τ hp i hi
    have hj' := tail_rank τ hp j (by omega)
    have hl := hm hij.le
    simp only [Function.comp_apply, f, not_lt.mpr hi', not_lt.mpr hj', ite_false] at hl
    have hle : τ i ≤ τ j := by change (τ i).val ≤ (τ j).val; omega
    exact lt_of_le_of_ne hle (τ.injective.ne hij.ne)
  refine ⟨τ, ⟨hp, ht⟩, ?_⟩
  intro π hπ
  apply Tuple.eq_sort_iff.mpr
  refine ⟨?_, ?_⟩
  · intro i j hij
    change f (π i) ≤ f (π j)
    by_cases hi : i.val < a
    · rw [hπ.1 i hi]
      simp only [f, σ.symm_apply_apply, hi, ite_true]
      by_cases hj : j.val < a
      · rw [hπ.1 j hj]
        simp only [σ.symm_apply_apply, hj, ite_true]
        exact hij
      · have hj' := tail_rank π hπ.1 j (by omega)
        simp only [not_lt.mpr hj', ite_false]
        omega
    · have hi' := tail_rank π hπ.1 i (by omega)
      have hj' := tail_rank π hπ.1 j (by omega)
      simp only [f, not_lt.mpr hi', not_lt.mpr hj', ite_false]
      rcases hij.eq_or_lt with he | hl
      · subst j; rfl
      · have := hπ.2 i j (by omega) hl
        change n + (π i).val ≤ n + (π j).val
        omega
  · intro i j hij he
    exact (hij.ne (π.injective (hf he))).elim

end AlgebraicGeometry.Scheme
