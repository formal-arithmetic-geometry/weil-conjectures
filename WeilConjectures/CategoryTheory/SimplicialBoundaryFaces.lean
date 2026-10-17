/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Boundaries of simplices in simplicial objects

Let `Y` be a simplicial object in a category `C` and `T : C`. A family
`x : Fin (n + 2) → (T ⟶ Y _⦋n⦌)` of `n`-simplices of `Y` (with values in `T`) is the
family of faces of a "would-be" `(n + 1)`-simplex when the faces satisfy the simplicial
identities `d_i x_{j+1} = d_j x_i` for `i ≤ j`. We show that such a family extends uniquely
to a compatible family indexed by all maps `θ : Δ ⟶ ⦋n + 1⦌` with `Δ.len < n + 1`, i.e. to a
map to the `(n + 1)`-st matching object (when it exists).

## Main definitions and results

- `CategoryTheory.SimplicialObject.IsBoundaryFamily`: the strong compatibility condition
  `x j ≫ Y.map a.op = x k ≫ Y.map b.op` whenever `a ≫ δ j = b ≫ δ k`.
- `CategoryTheory.SimplicialObject.isBoundaryFamily_zero`: it holds automatically for `n = 0`.
- `CategoryTheory.SimplicialObject.isBoundaryFamily_succ`: it follows from the simplicial
  identities between the faces.
- `CategoryTheory.SimplicialObject.exists_boundary_extension`: a boundary family extends to a
  compatible family over all non-surjective maps to `⦋n + 1⦌`.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type*} [Category* C] (Y : SimplicialObject C) {T : C}

/-- A family of `n`-simplices `x j` (`j : Fin (n + 2)`) is a *boundary family* if
`x j ≫ Y.map a.op = x k ≫ Y.map b.op` whenever `a ≫ δ j = b ≫ δ k`. -/
def IsBoundaryFamily {n : ℕ} (x : Fin (n + 2) → (T ⟶ Y _⦋n⦌)) : Prop :=
  ∀ (Δ : SimplexCategory) (a b : Δ ⟶ ⦋n⦌) (j k : Fin (n + 2)),
    a ≫ SimplexCategory.δ j = b ≫ SimplexCategory.δ k → x j ≫ Y.map a.op = x k ≫ Y.map b.op

/-- Any pair of `0`-simplices is a boundary family. -/
lemma isBoundaryFamily_zero (x : Fin 2 → (T ⟶ Y _⦋0⦌)) : Y.IsBoundaryFamily x := by
  intro Δ a b j k h
  have hab : a = b := by
    ext i : 3
    exact Subsingleton.elim (α := Fin 1) _ _
  subst hab
  have hjk : j = k := by
    have h' := congrArg (fun f : Δ ⟶ ⦋1⦌ ↦ f.toOrderHom 0) h
    have h0 : a.toOrderHom 0 = 0 := Subsingleton.elim (α := Fin 1) _ _
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      h0] at h'
    fin_cases j <;> fin_cases k <;> simp_all [SimplexCategory.δ]
  rw [hjk]

/-- The simplicial identities `d_i x_{j+1} = d_j x_i` (`i ≤ j`) imply that `x` is a boundary
family. -/
lemma isBoundaryFamily_succ {n : ℕ} (x : Fin (n + 3) → (T ⟶ Y _⦋n + 1⦌))
    (hx : ∀ i j : Fin (n + 2), i ≤ j → x j.succ ≫ Y.δ i = x i.castSucc ≫ Y.δ j) :
    Y.IsBoundaryFamily x := by
  intro Δ a b j k h
  wlog hjk : j ≤ k generalizing a b j k
  · exact (this b a k j h.symm (le_of_not_ge hjk)).symm
  rcases hjk.eq_or_lt with rfl | hjk
  · rw [cancel_mono] at h
    rw [h]
  have hk : k ≠ 0 := Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le j) hjk)
  set k' := k.pred hk with hk'
  have hkk : k = k'.succ := (Fin.succ_pred k hk).symm
  have hjn : (j : ℕ) < n + 2 := by
    have := k.isLt
    have : (j : ℕ) < k := hjk
    omega
  set j' : Fin (n + 2) := j.castLT hjn with hj'
  have hjj : j = j'.castSucc := rfl
  have hle : j' ≤ k' := by
    rw [Fin.le_iff_val_le_val]
    simp only [hj', hk', Fin.val_castLT, Fin.val_pred]
    have : (j : ℕ) < k := hjk
    omega
  have ha : ∀ i, a.toOrderHom i ≠ k' := by
    intro i hi
    have h' := congrArg (fun f : Δ ⟶ ⦋n + 2⦌ ↦ f.toOrderHom i) h
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
      hi] at h'
    have h1 : (SimplexCategory.δ j).toOrderHom k' = k := by
      simp only [SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
      rw [hkk, hjj, Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hle)]
    rw [h1] at h'
    have h2 : (SimplexCategory.δ k).toOrderHom (b.toOrderHom i) ≠ k := by
      simp only [SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
      exact Fin.succAbove_ne _ _
    exact h2 h'.symm
  obtain ⟨ψ, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' a k' ha
  have hb : b = ψ ≫ SimplexCategory.δ j' := by
    rw [← cancel_mono (SimplexCategory.δ k), Category.assoc, hkk,
      SimplexCategory.δ_comp_δ hle, ← hkk, ← hjj, ← Category.assoc, h]
  subst hb
  have := hx j' k' hle
  rw [← hkk, ← hjj] at this
  simp only [op_comp, Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ Y.map ψ.op) this.symm

/-- A map `θ : Δ ⟶ ⦋n + 1⦌` with `Δ.len < n + 1` factors through some face `δ i`. -/
lemma _root_.SimplexCategory.exists_eq_comp_δ_of_len_lt {n : ℕ} {Δ : SimplexCategory}
    (h : Δ.len < n + 1) (θ : Δ ⟶ ⦋n + 1⦌) :
    ∃ (i : Fin (n + 2)) (θ' : Δ ⟶ ⦋n⦌), θ = θ' ≫ SimplexCategory.δ i := by
  apply SimplexCategory.eq_comp_δ_of_not_surjective
  intro hs
  have : Epi θ := SimplexCategory.epi_iff_surjective.mpr hs
  have := SimplexCategory.len_le_of_epi θ
  simp only at this
  omega

/-- A boundary family of `n`-simplices extends to a family indexed by all maps
`θ : Δ ⟶ ⦋n + 1⦌` with `Δ.len < n + 1`, compatible with precomposition. -/
theorem exists_boundary_extension {n : ℕ} (x : Fin (n + 2) → (T ⟶ Y _⦋n⦌))
    (hx : Y.IsBoundaryFamily x) :
    ∃ p : ∀ Δ : SimplexCategory, Δ.len < n + 1 → (Δ ⟶ ⦋n + 1⦌) → (T ⟶ Y.obj (op Δ)),
      (∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n + 1) (h' : Δ'.len < n + 1) (α : Δ' ⟶ Δ)
        (θ : Δ ⟶ ⦋n + 1⦌), p Δ h θ ≫ Y.map α.op = p Δ' h' (α ≫ θ)) ∧
      ∀ j : Fin (n + 2), p ⦋n⦌ (by simp) (SimplexCategory.δ j) = x j := by
  choose i θ' hθ using fun (Δ : SimplexCategory) (h : Δ.len < n + 1) (θ : Δ ⟶ ⦋n + 1⦌) ↦
    SimplexCategory.exists_eq_comp_δ_of_len_lt h θ
  refine ⟨fun Δ h θ ↦ x (i Δ h θ) ≫ Y.map (θ' Δ h θ).op, ?_, ?_⟩
  · intro Δ Δ' h h' α θ
    rw [Category.assoc, ← Functor.map_comp, ← op_comp]
    apply hx
    rw [Category.assoc, ← hθ, ← hθ]
  · intro j
    have := hx _ (θ' ⦋n⦌ (by simp) (SimplexCategory.δ j)) (𝟙 _) _ j
      (by rw [← hθ, Category.id_comp])
    simpa using this

end CategoryTheory.SimplicialObject
