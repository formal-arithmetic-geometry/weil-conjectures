/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Sort

/-!
# The Cauchy–Binet formula

For an `m × n` matrix `A` and an `n × m` matrix `B` over a commutative ring,
`det (A * B) = ∑_{S ⊆ {1,…,n}, |S| = m} det (A^S) det (B_S)`, where `A^S` (resp. `B_S`) is the
`m × m` submatrix of `A` formed by the columns (resp. of `B` formed by the rows) indexed by `S`,
in increasing order.
-/

@[expose] public section

open Finset Equiv

namespace Matrix

variable {R : Type*} [CommRing R]

/-- Expansion of `det (A * B)` as a sum over all maps `f : Fin m → Fin n`. -/
private lemma det_mul_eq_sum_fun {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ f : Fin m → Fin n, (A.submatrix id f).det * ∏ k, B (f k) k := by
  simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id_eq, sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ ↦ Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]

/-- **Cauchy–Binet formula**: `det (A * B) = ∑_{|S| = m} det (A^S) det (B_S)`, the sum running
over the `m`-element subsets `S` of `Fin n`, with columns of `A` (resp. rows of `B`) taken in
increasing order. (blueprint: `lem-weil-pbc-cauchy-binet`) -/
theorem det_mul_eq_sum_det_submatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ S : {S : Finset (Fin n) // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  rw [det_mul_eq_sum_fun]
  set g : (Fin m → Fin n) → R := fun f ↦ (A.submatrix id f).det * ∏ k, B (f k) k with hg
  -- expand `det (B_S)` and reindex by pairs `(S, τ)`
  have hS : ∀ S : {S : Finset (Fin n) // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) id).det =
      ∑ τ : Perm (Fin m), g (S.1.orderEmbOfFin S.2 ∘ τ) := by
    intro S
    simp only [hg]
    rw [det_apply' (B.submatrix _ id), mul_sum]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [show A.submatrix id (S.1.orderEmbOfFin S.2 ∘ τ) =
      (A.submatrix id (S.1.orderEmbOfFin S.2)).submatrix id τ from rfl, det_permute']
    simp only [submatrix_apply, id_eq, Function.comp_apply]
    ring
  rw [Fintype.sum_congr _ _ hS]
  refine (Fintype.sum_of_injective (fun p : (Σ _ : {S : Finset (Fin n) // S.card = m},
    Perm (Fin m)) ↦ (p.1.1.orderEmbOfFin p.1.2 ∘ p.2 : Fin m → Fin n)) ?_ _ g ?_
      fun _ ↦ rfl).symm.trans (Fintype.sum_sigma _)
  · rintro ⟨⟨S, hS⟩, τ⟩ ⟨⟨S', hS'⟩, τ'⟩ h
    have himg : S = S' := by
      have h1 : Set.range (S.orderEmbOfFin hS ∘ τ) = S := by
        rw [Set.range_comp, τ.range_eq_univ, Set.image_univ, Finset.range_orderEmbOfFin]
      have h2 : Set.range (S'.orderEmbOfFin hS' ∘ τ') = S' := by
        rw [Set.range_comp, τ'.range_eq_univ, Set.image_univ, Finset.range_orderEmbOfFin]
      exact_mod_cast h1.symm.trans ((congrArg Set.range h).trans h2)
    subst himg
    have : τ = τ' := by
      ext k
      exact congrArg Fin.val ((S.orderEmbOfFin hS).injective (congrFun h k))
    subst this
    rfl
  · intro f hf
    have hni : ¬ Function.Injective f := by
      intro hinj
      apply hf
      classical
      let S : Finset (Fin n) := Finset.univ.image f
      have hcard : S.card = m := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      have hmem : ∀ k, f k ∈ S := fun k ↦ Finset.mem_image_of_mem f (Finset.mem_univ k)
      let g : Fin m → Fin m := fun k ↦ (S.orderIsoOfFin hcard).symm ⟨f k, hmem k⟩
      have hg : ∀ k, S.orderEmbOfFin hcard (g k) = f k := by
        intro k
        rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
      have hginj : Function.Injective g := by
        intro a b hab
        apply hinj
        rw [← hg a, ← hg b, hab]
      let τ : Perm (Fin m) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj)
      exact ⟨⟨⟨S, hcard⟩, τ⟩, funext fun k ↦ hg k⟩
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
      by_contra hcon
      push Not at hcon
      exact hni hcon
    show (A.submatrix id f).det * _ = 0
    rw [det_zero_of_column_eq hne (fun k ↦ by simp [hij]), zero_mul]

end Matrix
