/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet

/-!
# Difference of two basic constructible subsets of an affine spectrum

Source: Étale Cohomology, Lemma 59.72.1 (Tag 03S0), proof (the refinement is asserted there),
with the basic sets of Algebra, Lemma 10.29.3 (Tag 0G1P)
(blueprint: `lem-weil-pbc-affine-basic-set-difference`).
-/

@[expose] public section

universe u

open Set

namespace PrimeSpectrum

private lemma mem_basic {A : Type u} [CommRing A] (f : A) (n : ℕ)
    (g : Fin n → A) (p : PrimeSpectrum A) :
    p ∈ (⟨f, n, g⟩ : BasicConstructibleSetData A).toSet ↔
      (∀ i, g i ∈ p.asIdeal) ∧ f ∉ p.asIdeal := by
  simp [BasicConstructibleSetData.toSet, mem_zeroLocus, Set.range_subset_iff]

/-- (blueprint: `lem-weil-pbc-affine-basic-set-difference`)
For a commutative ring `A`, the difference `B \ C` of two basic subsets
`B = D(f) ∩ V(g₁, ..., gᵣ)` and `C = D(h) ∩ V(k₁, ..., kₛ)` of its prime spectrum is a finite
pairwise-disjoint union of basic subsets (the empty union is allowed).
`BasicConstructibleSetData.toSet` represents `D(f) ∩ V(g₁, ..., gᵣ)` as `V(g₁, ..., gᵣ) \ V(f)`.

Source: Étale Cohomology, Lemma 59.72.1 (Tag 03S0), proof; Algebra, Lemma 10.29.3 (Tag 0G1P). -/
theorem exists_disjoint_basicConstructibleSetData_diff {A : Type u} [CommRing A]
    (f h : A) (r s : ℕ) (g : Fin r → A) (k : Fin s → A) :
    ∃ (n : ℕ) (S : Fin n → BasicConstructibleSetData A),
      (Pairwise fun i j => Disjoint ((S i).toSet) ((S j).toSet)) ∧
      (⟨f, r, g⟩ : BasicConstructibleSetData A).toSet \
          (⟨h, s, k⟩ : BasicConstructibleSetData A).toSet = ⋃ i, (S i).toSet := by
  classical
  induction s with
  | zero =>
    refine ⟨1, fun _ => ⟨f, r + 1, Fin.snoc g h⟩, ?_, ?_⟩
    · intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
    · ext p
      simp [mem_basic, Fin.forall_fin_succ']
      aesop
  | succ s ih =>
    let k' : Fin s → A := fun i => k i.castSucc
    let a : A := k (Fin.last s)
    obtain ⟨n, S, hS, hU⟩ := ih k'
    let E : BasicConstructibleSetData A := ⟨f * h * a, r + s, Fin.append g k'⟩
    have hE (p : PrimeSpectrum A) :
        p ∈ E.toSet ↔
          p ∈ (⟨f, r, g⟩ : BasicConstructibleSetData A).toSet ∧
          p ∈ (⟨h, s, k'⟩ : BasicConstructibleSetData A).toSet ∧
          a ∉ p.asIdeal := by
      simp [E, mem_basic, Fin.forall_fin_add,
        p.isPrime.mul_mem_iff_mem_or_mem]
      aesop
    have hC (p : PrimeSpectrum A) :
        p ∈ (⟨h, s + 1, k⟩ : BasicConstructibleSetData A).toSet ↔
          p ∈ (⟨h, s, k'⟩ : BasicConstructibleSetData A).toSet ∧ a ∈ p.asIdeal := by
      simp [mem_basic, Fin.forall_fin_succ', k', a]
      aesop
    refine ⟨n + 1, Fin.cons E S, ?_, ?_⟩
    · rw [pairwise_fin_succ_iff]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hD (i : Fin n) : Disjoint E.toSet (S i).toSet := by
        rw [Set.disjoint_left]
        intro p hp hpi
        have hpC := (hE p).mp hp
        have hpU : p ∈ ⋃ j, (S j).toSet := Set.mem_iUnion.mpr ⟨i, hpi⟩
        rw [← hU] at hpU
        exact hpU.2 hpC.2.1
      exact ⟨fun i => (hD i).symm, hD, hS⟩
    · ext p
      simp only [Set.mem_sdiff, Set.mem_iUnion, Fin.exists_fin_succ,
        Fin.cons_zero, Fin.cons_succ]
      have hUp := Set.ext_iff.mp hU p
      simp only [Set.mem_sdiff, Set.mem_iUnion] at hUp
      rw [hE, hC]
      by_cases hc : p ∈ (⟨h, s, k'⟩ : BasicConstructibleSetData A).toSet
      · simp only [hc, true_and, not_true_eq_false, and_false, false_iff] at hUp ⊢
        aesop
      · simp only [hc, false_and, not_false_eq_true, and_true] at hUp ⊢
        aesop

end PrimeSpectrum
