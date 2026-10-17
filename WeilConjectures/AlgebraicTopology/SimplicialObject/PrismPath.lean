/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer

/-!
# Prisms and combinatorial path data

The product `Δ[m] × Δ[1]` is the union of the `m + 1` simplices of dimension `m + 1` with
vertices `(0, 0), …, (k, 0), (k, 1), …, (m, 1)`. For `θ : ⦋m⦌ ⟶ ⦋n⦌`, the image of the `k`-th
such simplex under `θ × 𝟙` is the image of the `θ k`-th prism simplex of `Δ[n] × Δ[1]` under
the map `prism θ k : ⦋m + 1⦌ ⟶ ⦋n + 1⦌`.

For a simplicial object `V`, a *path family* of degree `n` with values in `T` is a family
`h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌)` of prism simplices glued along their common faces
(`h (j + 1) ≫ V.δ (j + 1) = h j ≫ V.δ (j + 1)`). Path families are contravariantly functorial
in `⦋n⦌` via `pathMap`.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

namespace SimplexCategory

/-- The underlying function of `prism θ k`. -/
def prismFun {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (m + 1)) (i : Fin (m + 2)) : Fin (n + 2) :=
  if h : i.val ≤ k.val then (θ.toOrderHom ⟨i.val, by rw [len_mk]; omega⟩).castSucc
  else (θ.toOrderHom ⟨i.val - 1, by rw [len_mk]; omega⟩).succ

lemma prismFun_monotone {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (m + 1)) :
    Monotone (prismFun θ k) := by
  intro i i' hii'
  have hii'' : i.val ≤ i'.val := hii'
  unfold prismFun
  split_ifs with h₁ h₂ h₂
  · exact Fin.castSucc_le_castSucc_iff.2 (θ.toOrderHom.monotone (by
      rw [Fin.le_iff_val_le_val]; exact hii''))
  · rw [Fin.le_iff_val_le_val, Fin.val_castSucc, Fin.val_succ]
    have := θ.toOrderHom.monotone (show (⟨i.val, by rw [len_mk]; omega⟩ : Fin (m + 1)) ≤ ⟨i'.val - 1, by omega⟩
      by rw [Fin.le_iff_val_le_val]; simp only; omega)
    rw [Fin.le_iff_val_le_val] at this
    omega
  · omega
  · rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_succ]
    have := θ.toOrderHom.monotone (show (⟨i.val - 1, by rw [len_mk]; omega⟩ : Fin (m + 1)) ≤
      ⟨i'.val - 1, by omega⟩ by rw [Fin.le_iff_val_le_val]; simp only; omega)
    rw [Fin.le_iff_val_le_val] at this
    omega

/-- The map `⦋m + 1⦌ ⟶ ⦋n + 1⦌` sending the `k`-th prism simplex of `Δ[m] × Δ[1]` to the
`θ k`-th prism simplex of `Δ[n] × Δ[1]`. -/
def prism {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (m + 1)) : ⦋m + 1⦌ ⟶ ⦋n + 1⦌ :=
  mkHom ⟨prismFun θ k, prismFun_monotone θ k⟩

lemma prism_apply {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (m + 1)) (i : Fin (m + 2)) :
    (prism θ k).toOrderHom i = prismFun θ k i := rfl

lemma prism_id {m : ℕ} (k : Fin (m + 1)) : prism (𝟙 ⦋m⦌) k = 𝟙 _ := by
  ext i : 3
  rw [prism_apply, prismFun]
  split_ifs with h
  · simp
  · simp only [CategoryStruct.id, Fin.val_succ, OrderHom.id_coe, id_eq]
    omega

end SimplexCategory
