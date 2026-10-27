/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.RingTheory.FittingIdealZero
import Mathlib.RingTheory.Ideal.Operations

/-!
# Zeroth Fitting ideal of a direct sum

Source: Stacks Project, More on Algebra, Lemma Tag 07ZA(2)
(blueprint: lem-trf-fitting-ideal-direct-sum).
-/

@[expose] public section

universe u v w

namespace LinearMap

private theorem presentationFittingIdeal_zero_eq {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) :
    π.presentationFittingIdeal 0 =
      Ideal.span {a | ∃ A : Matrix (Fin n) (Fin n) R,
        (∀ i, π (A i) = 0) ∧ A.det = a} := by
  classical
  by_cases hn : n = 0
  · subst n
    simp only [presentationFittingIdeal, Nat.le_refl, ↓reduceIte]
    symm
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨0, fun i ↦ Fin.elim0 i, Matrix.det_isEmpty⟩
  · simp only [presentationFittingIdeal, Nat.sub_zero, Nat.le_zero, hn, ↓reduceIte]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro a ⟨A, c, hA, rfl⟩
      let e : Fin n ≃ Fin n := Equiv.ofBijective c
        ((Finite.injective_iff_bijective).mp c.injective)
      have hdet : (A.submatrix (fun i ↦ i) c).det = (Equiv.Perm.sign e : R) * A.det :=
        Matrix.det_permute' e A
      rw [hdet]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨A, hA, rfl⟩)
    · apply Ideal.span_le.mpr
      rintro a ⟨A, hA, rfl⟩
      exact Ideal.subset_span ⟨A, Function.Embedding.refl _, hA, rfl⟩

private theorem det_mem_presentationFittingIdeal_zero {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i, π (A i) = 0) : A.det ∈ π.presentationFittingIdeal 0 := by
  rw [presentationFittingIdeal_zero_eq]
  exact Ideal.subset_span ⟨A, hA, rfl⟩

private theorem block_rows_det_mem {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] {n m : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (ρ : (Fin m → R) →ₗ[R] N)
    (B : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) R)
    (hπ : ∀ i, π (fun j ↦ B i (.inl j)) = 0)
    (hρ : ∀ i, ρ (fun j ↦ B i (.inr j)) = 0) :
    B.det ∈ π.presentationFittingIdeal 0 * ρ.presentationFittingIdeal 0 := by
  classical
  let X : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) R :=
    fun i ↦ Sum.elim (fun j ↦ B i (.inl j)) (fun _ ↦ 0)
  let Y : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) R :=
    fun i ↦ Sum.elim (fun _ ↦ 0) (fun j ↦ B i (.inr j))
  have hB : B = X + Y := by ext i (j | j) <;> simp [X, Y]
  change Matrix.detRowAlternating B ∈ _
  rw [hB, Matrix.detRowAlternating.map_add_univ]
  apply Submodule.sum_mem
  intro s _
  let C : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) R := s.piecewise X Y
  change C.det ∈ _
  by_cases hc : C.det = 0
  · rw [hc]; exact Ideal.zero_mem _
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show (∑ σ : Equiv.Perm (Fin n ⊕ Fin m),
      Equiv.Perm.sign σ • ∏ j, C (σ j) j) ≠ 0 by rwa [← Matrix.det_apply])
  have hp : ∀ j, C (σ j) j ≠ 0 := by
    intro j hj
    apply hσ
    rw [Finset.prod_eq_zero (f := fun j ↦ C (σ j) j) (Finset.mem_univ j) hj,
      smul_zero]
  have hl : ∀ j : Fin n, σ (.inl j) ∈ s := by
    intro j
    by_contra hj
    exact hp (.inl j) (by simp [C, hj, Y])
  have hr : ∀ j : Fin m, σ (.inr j) ∉ s := by
    intro j hj
    exact hp (.inr j) (by simp [C, hj, X])
  let A : Matrix (Fin n) (Fin n) R := fun i j ↦ B (σ (.inl i)) (.inl j)
  let D : Matrix (Fin m) (Fin m) R := fun i j ↦ B (σ (.inr i)) (.inr j)
  have hblocks : C.submatrix σ (fun i ↦ i) = Matrix.fromBlocks A 0 0 D := by
    ext (i | i) (j | j) <;> simp [C, Finset.piecewise, hl, hr, X, Y, A, D]
  have hmem : (C.submatrix σ (fun i ↦ i)).det ∈
      π.presentationFittingIdeal 0 * ρ.presentationFittingIdeal 0 := by
    rw [hblocks, Matrix.det_fromBlocks_zero₂₁]
    exact Ideal.mul_mem_mul
      (det_mem_presentationFittingIdeal_zero π A (fun i ↦ hπ _))
      (det_mem_presentationFittingIdeal_zero ρ D (fun i ↦ hρ _))
  rw [show (C.submatrix σ (fun i ↦ i)).det =
    (Equiv.Perm.sign σ : R) * C.det from Matrix.det_permute σ C] at hmem
  exact (Ideal.unit_mul_mem_iff_mem _
    ((Equiv.Perm.sign σ).isUnit.map (Int.castRingHom R))).mp hmem

private theorem fittingIdealZero_eq_presentation {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {n : ℕ} (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π) :
    fittingIdealZero (R := R) (M := M) = π.presentationFittingIdeal 0 := by
  classical
  unfold fittingIdealZero
  exact (presentationFittingIdeal_independence_baseChange.{u, v, u} 0 _
    (Classical.choose_spec (Classical.choose_spec
      (Module.Finite.exists_fin' R M)))).1 n π hπ

/-- For finitely generated modules, the zeroth Fitting ideal of their binary direct sum is the
product of their zeroth Fitting ideals.  Binary direct sums of modules are represented by the
product module `M × N`.  The proof chooses finite free surjections for both modules, forms their
block direct-sum presentation, expands its kernel-row determinants by the Leibniz formula, and
uses presentation independence.  Empty presentations are included by the empty determinant
convention. (blueprint: lem-trf-fitting-ideal-direct-sum) -/
theorem fittingIdealZero_prod {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N] :
    fittingIdealZero (R := R) (M := M × N) =
      fittingIdealZero (R := R) (M := M) * fittingIdealZero (R := R) (M := N) := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  obtain ⟨m, ρ, hρ⟩ := Module.Finite.exists_fin' R N
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let q : (Fin (n + m) → R) →ₗ[R] M × N :=
    { toFun := fun x ↦ (π (fun i ↦ x (e (.inl i))), ρ (fun j ↦ x (e (.inr j))))
      map_add' := fun x y ↦ Prod.ext (π.map_add _ _) (ρ.map_add _ _)
      map_smul' := fun r x ↦ Prod.ext (π.map_smul r _) (ρ.map_smul r _) }
  have hq : Function.Surjective q := by
    rintro ⟨a, b⟩
    obtain ⟨x, hx⟩ := hπ a
    obtain ⟨y, hy⟩ := hρ b
    refine ⟨fun i ↦ Sum.elim x y (e.symm i), ?_⟩
    change (π _, ρ _) = (a, b)
    simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, hx, hy]
  rw [fittingIdealZero_eq_presentation q hq,
    fittingIdealZero_eq_presentation π hπ, fittingIdealZero_eq_presentation ρ hρ]
  apply le_antisymm
  · rw [presentationFittingIdeal_zero_eq]
    apply Ideal.span_le.mpr
    rintro a ⟨A, hA, rfl⟩
    rw [← Matrix.det_submatrix_equiv_self e A]
    apply block_rows_det_mem π ρ
    · intro i
      exact congrArg Prod.fst (hA (e i))
    · intro i
      exact congrArg Prod.snd (hA (e i))
  · rw [presentationFittingIdeal_zero_eq π, presentationFittingIdeal_zero_eq ρ,
      Ideal.span_mul_span]
    apply Ideal.span_le.mpr
    rintro a ⟨b, ⟨A, hA, rfl⟩, c, ⟨D, hD, rfl⟩, rfl⟩
    let B : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) R :=
      Matrix.fromBlocks A 0 0 D
    have hrows : ∀ i, q ((B.submatrix e.symm e.symm) i) = 0 := by
      intro i
      change (π _, ρ _) = (0, 0)
      rcases hi : e.symm i with k | k
      · simp only [Matrix.submatrix_apply, hi, Equiv.symm_apply_apply, B,
          Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
          hA]
        change (0, ρ 0) = (0, 0)
        rw [map_zero]
      · simp only [Matrix.submatrix_apply, hi, Equiv.symm_apply_apply, B,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
          hD]
        change (π 0, 0) = (0, 0)
        rw [map_zero]
    have hb := det_mem_presentationFittingIdeal_zero q
      (B.submatrix e.symm e.symm) hrows
    rw [Matrix.det_submatrix_equiv_self] at hb
    change (Matrix.fromBlocks A 0 0 D).det ∈ _ at hb
    rwa [Matrix.det_fromBlocks_zero₂₁] at hb

end LinearMap
