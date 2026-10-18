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
    have := θ.toOrderHom.monotone (show (⟨i.val, by omega⟩ : Fin (m + 1)) ≤
      ⟨i'.val - 1, by omega⟩
      by rw [Fin.le_iff_val_le_val]; simp only; omega)
    rw [Fin.le_iff_val_le_val] at this
    omega
  · omega
  · rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_succ]
    have := θ.toOrderHom.monotone (show (⟨i.val - 1, by omega⟩ : Fin (m + 1)) ≤
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
  split_ifs with h <;> (apply Fin.ext; simp); omega

lemma prismFun_of_le {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (m + 1)) (i : Fin (m + 2))
    (h : i.val ≤ k.val) :
    prismFun θ k i = (θ.toOrderHom ⟨i.val, by rw [len_mk]; omega⟩).castSucc := dif_pos h

lemma prismFun_of_lt {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (m + 1)) (i : Fin (m + 2))
    (h : k.val < i.val) :
    prismFun θ k i = (θ.toOrderHom ⟨i.val - 1, by rw [len_mk]; omega⟩).succ :=
  dif_neg (by omega)

lemma toOrderHom_congr {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) {a b : Fin (⦋m⦌.len + 1)} (h : a.val = b.val) :
    θ.toOrderHom a = θ.toOrderHom b := congrArg _ (Fin.ext h)

lemma toOrderHom_val_mono {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) {a b : Fin (⦋m⦌.len + 1)}
    (h : a.val ≤ b.val) : (θ.toOrderHom a).val ≤ (θ.toOrderHom b).val :=
  θ.toOrderHom.monotone h

lemma prism_comp {l m n : ℕ} (θ' : ⦋l⦌ ⟶ ⦋m⦌) (θ : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (l + 1)) :
    prism θ' k ≫ prism θ (θ'.toOrderHom k) = prism (θ' ≫ θ) k := by
  ext i : 3
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, prism_apply]
  by_cases hi : i.val ≤ k.val
  · have h1 : (θ'.toOrderHom ⟨i.val, by simp at *; omega⟩).val ≤ (θ'.toOrderHom k).val :=
      toOrderHom_val_mono θ' (by simp only; omega)
    rw [prismFun_of_le θ' k i hi, prismFun_of_le _ _ _ (by simpa using h1),
      prismFun_of_le _ k i hi]
    rfl
  · have h1 : (θ'.toOrderHom k).val ≤ (θ'.toOrderHom ⟨i.val - 1, by simp at *; omega⟩).val :=
      toOrderHom_val_mono θ' (by simp only; omega)
    rw [prismFun_of_lt θ' k i (by omega), prismFun_of_lt _ _ _ (by simp; omega),
      prismFun_of_lt _ k i (by omega)]
    simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    congr 2

lemma δ_val {n : ℕ} (i : Fin (n + 2)) (x : Fin (n + 1)) :
    ((δ i).toOrderHom x).val = if x.val < i.val then x.val else x.val + 1 := by
  simp only [δ, mkHom, Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
    Fin.succAboveOrderEmb_apply, Fin.succAbove]
  split_ifs with h₁ h₂ h₂ <;> simp_all [Fin.lt_def]

lemma σ_val {n : ℕ} (i : Fin (n + 1)) (x : Fin (n + 2)) :
    ((σ i).toOrderHom x).val = if x.val ≤ i.val then x.val else x.val - 1 := by
  change (i.predAbove x).val = _
  split_ifs with h
  · rw [Fin.predAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simpa using h)]
    simp
  · rw [Fin.predAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp; omega)]
    simp

/-- The faces between consecutive prism simplices agree. -/
lemma δ_comp_prism_succ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (j : Fin m) :
    δ j.succ.castSucc ≫ prism θ j.succ = δ j.succ.castSucc ≫ prism θ j.castSucc := by
  ext x : 3
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, prism_apply]
  have hδ := δ_val j.succ.castSucc x
  simp only [Fin.val_castSucc, Fin.val_succ] at hδ
  by_cases hx : x.val ≤ j.val
  · rw [if_pos (by omega)] at hδ
    rw [prismFun_of_le _ _ _ (by rw [hδ, Fin.val_succ]; omega),
      prismFun_of_le _ _ _ (by rw [hδ, Fin.val_castSucc]; omega)]
  · rw [if_neg (by omega)] at hδ
    rw [prismFun_of_lt _ _ _ (by rw [hδ, Fin.val_succ]; omega),
      prismFun_of_lt _ _ _ (by rw [hδ, Fin.val_castSucc]; omega)]

lemma δ_zero_comp_prism_zero {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    δ 0 ≫ prism θ 0 = θ ≫ δ 0 := by
  ext x : 3
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, prism_apply]
  generalize hy : (δ 0).toOrderHom x = y
  have hyv : y.val = x.val + 1 := by rw [← hy, δ_val]; simp
  rw [prismFun_of_lt _ _ _ (by rw [Fin.val_zero, hyv]; omega)]
  apply Fin.ext
  rw [Fin.val_succ, δ_val, if_neg (by simp)]
  congr 1
  exact congrArg Fin.val (toOrderHom_congr θ (by simp; omega))

lemma δ_last_comp_prism_last {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    δ (Fin.last (m + 1)) ≫ prism θ (Fin.last m) = θ ≫ δ (Fin.last (n + 1)) := by
  ext x : 3
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, prism_apply]
  generalize hy : (δ (Fin.last (m + 1))).toOrderHom x = y
  have hx := x.isLt
  simp only [len_mk] at hx
  have hyv : y.val = x.val := by rw [← hy, δ_val, if_pos (by simp)]
  rw [prismFun_of_le _ _ _ (by rw [hyv, Fin.val_last]; omega)]
  apply Fin.ext
  rw [Fin.val_castSucc, δ_val, if_pos (by simp)]
  exact congrArg Fin.val (toOrderHom_congr θ (by simp; omega))

lemma prism_δ_of_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i.val ≤ j.val) :
    prism (δ i) j = δ i.castSucc := by
  ext x : 3
  apply Fin.ext
  rw [prism_apply]
  by_cases hx : x.val ≤ j.val
  · rw [prismFun_of_le _ _ _ hx, Fin.val_castSucc, δ_val, δ_val, Fin.val_castSucc]
  · rw [prismFun_of_lt _ _ _ (by omega), Fin.val_succ, δ_val, δ_val, Fin.val_castSucc]
    simp only
    split_ifs <;> omega

lemma δ_apply_of_le {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i.val ≤ j.val) :
    (δ i).toOrderHom j = j.succ := by
  apply Fin.ext
  rw [δ_val, if_neg (by omega), Fin.val_succ]

lemma prism_δ_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.val < i.val) :
    prism (δ i) j = δ i.succ := by
  ext x : 3
  apply Fin.ext
  rw [prism_apply]
  by_cases hx : x.val ≤ j.val
  · rw [prismFun_of_le _ _ _ hx, Fin.val_castSucc, δ_val, δ_val, Fin.val_succ]
    simp only
    split_ifs <;> omega
  · rw [prismFun_of_lt _ _ _ (by omega), Fin.val_succ, δ_val, δ_val, Fin.val_succ]
    simp only
    split_ifs <;> omega

lemma δ_apply_of_lt {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.val < i.val) :
    (δ i).toOrderHom j = j.castSucc := by
  apply Fin.ext
  rw [δ_val, if_pos h, Fin.val_castSucc]

lemma prism_σ_of_le {n : ℕ} (i j : Fin (n + 1)) (h : i.val ≤ j.val) :
    prism (σ i) j.succ = σ i.castSucc := by
  ext x : 3
  apply Fin.ext
  rw [prism_apply]
  by_cases hx : x.val ≤ j.val + 1
  · rw [prismFun_of_le _ _ _ (by simpa using hx), Fin.val_castSucc, σ_val, σ_val,
      Fin.val_castSucc]
  · rw [prismFun_of_lt _ _ _ (by simp; omega), Fin.val_succ, σ_val, σ_val, Fin.val_castSucc]
    simp only
    split_ifs <;> omega

lemma σ_apply_succ_of_le {n : ℕ} (i j : Fin (n + 1)) (h : i.val ≤ j.val) :
    (σ i).toOrderHom j.succ = j := by
  apply Fin.ext
  rw [σ_val, if_neg (by simp; omega), Fin.val_succ]
  omega

lemma prism_σ_of_ge {n : ℕ} (i j : Fin (n + 1)) (h : j.val ≤ i.val) :
    prism (σ i) j.castSucc = σ i.succ := by
  ext x : 3
  apply Fin.ext
  rw [prism_apply]
  by_cases hx : x.val ≤ j.val
  · rw [prismFun_of_le _ _ _ (by simpa using hx), Fin.val_castSucc, σ_val, σ_val, Fin.val_succ]
    simp only
    split_ifs <;> omega
  · rw [prismFun_of_lt _ _ _ (by simp; omega), Fin.val_succ, σ_val, σ_val, Fin.val_succ]
    simp only
    split_ifs <;> omega

lemma σ_apply_castSucc_of_ge {n : ℕ} (i j : Fin (n + 1)) (h : j.val ≤ i.val) :
    (σ i).toOrderHom j.castSucc = j := by
  apply Fin.ext
  rw [σ_val, if_pos (by simpa using h), Fin.val_castSucc]

end SimplexCategory

namespace CategoryTheory.SimplicialObject

open SimplexCategory

variable {C : Type*} [Category* C] (V : SimplicialObject C)

/-- A path family of degree `n`: `n + 1` prism simplices glued along their common faces. -/
def IsPathFamily {T : C} {n : ℕ} (h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌)) : Prop :=
  ∀ j : Fin n, h j.succ ≫ V.δ j.succ.castSucc = h j.castSucc ≫ V.δ j.succ.castSucc

variable {V}

lemma IsPathFamily.map_succ_eq {T : C} {n : ℕ} {h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌)}
    (hh : V.IsPathFamily h) (j : Fin n) {Δ : SimplexCategory} (μ : Δ ⟶ ⦋n + 1⦌)
    (hμ : ∀ x, μ.toOrderHom x ≠ j.succ.castSucc) :
    h j.succ ≫ V.map μ.op = h j.castSucc ≫ V.map μ.op := by
  obtain ⟨μ', rfl⟩ := eq_comp_δ_of_not_surjective' μ _ hμ
  simp only [op_comp, Functor.map_comp, ← Category.assoc]
  exact congrArg (· ≫ V.map μ'.op) (hh j)

lemma IsPathFamily.map_eq {T : C} {n : ℕ} {h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌)}
    (hh : V.IsPathFamily h) (a b : Fin (n + 1)) (hab : a.val ≤ b.val) {Δ : SimplexCategory}
    (μ : Δ ⟶ ⦋n + 1⦌) (hμ : ∀ x, ¬ (a.val < (μ.toOrderHom x).val ∧ (μ.toOrderHom x).val ≤ b.val)) :
    h b ≫ V.map μ.op = h a ≫ V.map μ.op := by
  obtain ⟨d, hd⟩ : ∃ d, b.val = a.val + d := ⟨b.val - a.val, by omega⟩
  induction d generalizing b with
  | zero => rw [show b = a from Fin.ext (by omega)]
  | succ d ih =>
    have hb : b.val - 1 < n + 1 := by omega
    let b' : Fin (n + 1) := ⟨b.val - 1, hb⟩
    have hj : b.val - 1 < n := by have := b.isLt; omega
    let j : Fin n := ⟨b.val - 1, hj⟩
    have e1 : j.succ = b := Fin.ext (by simp [j]; omega)
    have e2 : j.castSucc = b' := Fin.ext (by simp [j, b'])
    rw [← e1, hh.map_succ_eq j μ (fun x hx ↦ hμ x ⟨?_, ?_⟩), e2,
      ih b' (by simp [b']; omega) (fun x hx ↦ hμ x ⟨hx.1, by simp [b'] at hx; omega⟩)
      (by simp [b']; omega)]
    · rw [hx]; simp [j]; omega
    · rw [hx]; simp [j]; omega

variable (V) in
/-- The action of `θ : ⦋m⦌ ⟶ ⦋n⦌` on path families. -/
def pathMap {T : C} {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌))
    (k : Fin (m + 1)) : T ⟶ V _⦋m + 1⦌ :=
  h (θ.toOrderHom k) ≫ V.map (prism θ k).op

lemma isPathFamily_pathMap {T : C} {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    {h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌)} (hh : V.IsPathFamily h) :
    V.IsPathFamily (V.pathMap θ h) := by
  intro j
  simp only [pathMap, Category.assoc, SimplicialObject.δ, ← Functor.map_comp, ← op_comp,
    δ_comp_prism_succ]
  have hmono : (θ.toOrderHom j.castSucc).val ≤ (θ.toOrderHom j.succ).val :=
    θ.toOrderHom.monotone (Fin.castSucc_le_succ j)
  refine hh.map_eq _ _ hmono _ fun x ⟨hx₁, hx₂⟩ ↦ ?_
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, prism_apply] at hx₁ hx₂
  generalize hy : (SimplexCategory.δ j.succ.castSucc).toOrderHom x = y at hx₁ hx₂
  have hyv := δ_val j.succ.castSucc x
  rw [hy] at hyv
  simp only [Fin.val_castSucc, Fin.val_succ] at hyv
  by_cases hxj : x.val ≤ j.val
  · rw [if_pos (by omega)] at hyv
    rw [prismFun_of_le _ _ _ (by simp; omega)] at hx₁
    have := θ.toOrderHom.monotone (show (⟨y.val, by simp; omega⟩ : Fin (m + 1)) ≤ j.castSucc
      from by rw [Fin.le_def]; simp; omega)
    rw [Fin.le_def] at this
    simp at hx₁
    omega
  · rw [if_neg (by omega)] at hyv
    rw [prismFun_of_lt _ _ _ (by simp; omega)] at hx₂
    have := θ.toOrderHom.monotone (show j.succ ≤ (⟨y.val - 1, by simp; omega⟩ : Fin (m + 1))
      from by rw [Fin.le_def]; simp; omega)
    rw [Fin.le_def] at this
    simp at hx₂
    omega

lemma pathMap_id {T : C} {n : ℕ} (h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌)) :
    V.pathMap (𝟙 _) h = h := by
  funext k
  simp [pathMap, prism_id]

lemma pathMap_comp {T : C} {l m n : ℕ} (θ' : ⦋l⦌ ⟶ ⦋m⦌) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌)) :
    V.pathMap θ' (V.pathMap θ h) = V.pathMap (θ' ≫ θ) h := by
  funext k
  simp only [pathMap, Category.assoc, ← Functor.map_comp, ← op_comp, prism_comp,
    comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]

lemma pathMap_zero_δ_zero {T : C} {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    {h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌)} (hh : V.IsPathFamily h) :
    V.pathMap θ h 0 ≫ V.δ 0 = h 0 ≫ V.δ 0 ≫ V.map θ.op := by
  simp only [pathMap, Category.assoc, SimplicialObject.δ, ← Functor.map_comp, ← op_comp,
    δ_zero_comp_prism_zero]
  refine hh.map_eq _ _ (Nat.zero_le _) _ fun x ⟨hx₁, hx₂⟩ ↦ ?_
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply] at hx₁ hx₂
  rw [δ_val, if_neg (by simp)] at hx₂
  have := θ.toOrderHom.monotone (Fin.zero_le x)
  rw [Fin.le_def] at this
  simp at hx₂ this
  omega

lemma pathMap_last_δ_last {T : C} {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    {h : Fin (n + 1) → (T ⟶ V _⦋n + 1⦌)} (hh : V.IsPathFamily h) :
    V.pathMap θ h (Fin.last m) ≫ V.δ (Fin.last (m + 1)) =
      h (Fin.last n) ≫ V.δ (Fin.last (n + 1)) ≫ V.map θ.op := by
  simp only [pathMap, Category.assoc, SimplicialObject.δ, ← Functor.map_comp, ← op_comp,
    δ_last_comp_prism_last]
  refine (hh.map_eq _ _ (Fin.le_last _) _ fun x ⟨hx₁, hx₂⟩ ↦ ?_).symm
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply] at hx₁ hx₂
  rw [δ_val, if_pos (by simp)] at hx₁
  have := θ.toOrderHom.monotone (Fin.le_last x)
  rw [Fin.le_def] at this
  simp at hx₁ this
  omega

end CategoryTheory.SimplicialObject
