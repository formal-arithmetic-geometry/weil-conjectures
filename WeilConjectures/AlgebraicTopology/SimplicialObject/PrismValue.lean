/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicTopology.SimplicialObject.HomotopyPathObject

/-!
# Values of path families on simplices of the prism

A simplex of the prism `Δ[r] × Δ[1]` is a pair of maps `f : Δ ⟶ ⦋r⦌` and `g : Δ ⟶ ⦋1⦌`. It
lies in the `k`-th prism simplex if `f x ≤ k` whenever `g x = 0` and `k ≤ f x` whenever
`g x = 1`, and its vertices in this prism simplex are given by `sumHom f g`, `x ↦ f x + g x`.
For a point `z` of the path space `pathSpace a b` in degree `r`, we define the value
`pathValue a b z f g` of the path family of `z` on this simplex; it does not depend on the choice
of `k`, and it is compatible with the simplicial operators.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SimplexCategory

lemma hom_ext_val {Δ Δ' : SimplexCategory} {f g : Δ ⟶ Δ'}
    (h : ∀ x, (f.toOrderHom x).val = (g.toOrderHom x).val) : f = g := by
  ext x : 3
  exact Fin.ext (h x)

lemma val_le_one {Δ : SimplexCategory} (g : Δ ⟶ ⦋1⦌) (x : Fin (Δ.len + 1)) :
    (g.toOrderHom x).val ≤ 1 := by
  have := (g.toOrderHom x).isLt
  simp only [len_mk] at this
  omega

/-- The map `x ↦ f x + g x` to the vertices of a prism simplex. -/
def sumHom {Δ : SimplexCategory} {n : ℕ} (f : Δ ⟶ ⦋n⦌) (g : Δ ⟶ ⦋1⦌) : Δ ⟶ ⦋n + 1⦌ :=
  Hom.mk ⟨fun x ↦ ⟨(f.toOrderHom x).val + (g.toOrderHom x).val, by
      have := (f.toOrderHom x).isLt
      have := val_le_one g x
      simp only [len_mk] at *
      omega⟩, fun x y hxy ↦ by
      have h₁ := f.toOrderHom.monotone hxy
      have h₂ := g.toOrderHom.monotone hxy
      rw [Fin.le_def] at h₁ h₂ ⊢
      simp only
      omega⟩

@[simp]
lemma sumHom_val {Δ : SimplexCategory} {n : ℕ} (f : Δ ⟶ ⦋n⦌) (g : Δ ⟶ ⦋1⦌)
    (x : Fin (Δ.len + 1)) :
    ((sumHom f g).toOrderHom x).val = (f.toOrderHom x).val + (g.toOrderHom x).val := rfl

lemma comp_sumHom {Δ' Δ : SimplexCategory} {n : ℕ} (θ : Δ' ⟶ Δ) (f : Δ ⟶ ⦋n⦌)
    (g : Δ ⟶ ⦋1⦌) : θ ≫ sumHom f g = sumHom (θ ≫ f) (θ ≫ g) :=
  hom_ext_val fun x ↦ by simp

/-- The simplex `(f, g)` of the prism lies in the `k`-th prism simplex. -/
def IsPrismIndex {Δ : SimplexCategory} {n : ℕ} (f : Δ ⟶ ⦋n⦌) (g : Δ ⟶ ⦋1⦌) (k : Fin (n + 1)) :
    Prop :=
  ∀ x, ((g.toOrderHom x).val = 0 → (f.toOrderHom x).val ≤ k.val) ∧
    ((g.toOrderHom x).val = 1 → k.val ≤ (f.toOrderHom x).val)

lemma IsPrismIndex.comp {Δ' Δ : SimplexCategory} {n : ℕ} {f : Δ ⟶ ⦋n⦌} {g : Δ ⟶ ⦋1⦌}
    {k : Fin (n + 1)} (h : IsPrismIndex f g k) (θ : Δ' ⟶ Δ) :
    IsPrismIndex (θ ≫ f) (θ ≫ g) k := fun x ↦ h (θ.toOrderHom x)

/-- A choice of prism simplex containing `(f, g)`. -/
def prismIndex {Δ : SimplexCategory} {n : ℕ} (f : Δ ⟶ ⦋n⦌) (g : Δ ⟶ ⦋1⦌) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun x ↦ (g.toOrderHom x).val = 0).sup fun x ↦ (f.toOrderHom x).val, by
    rw [Finset.sup_lt_iff (by simp)]
    intro x _
    simpa using (f.toOrderHom x).isLt⟩

lemma isPrismIndex_prismIndex {Δ : SimplexCategory} {n : ℕ} (f : Δ ⟶ ⦋n⦌) (g : Δ ⟶ ⦋1⦌) :
    IsPrismIndex f g (prismIndex f g) := by
  intro x
  refine ⟨fun hx ↦ Finset.le_sup (f := fun x ↦ (f.toOrderHom x).val)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩), fun hx ↦ ?_⟩
  show (Finset.univ.filter fun x ↦ (g.toOrderHom x).val = 0).sup (fun x ↦ (f.toOrderHom x).val) ≤ _
  refine Finset.sup_le fun y hy ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
  have hyx : y ≤ x := by
    by_contra h
    have := g.toOrderHom.monotone (le_of_not_ge h)
    rw [Fin.le_def] at this
    omega
  exact f.toOrderHom.monotone hyx

lemma IsPrismIndex.of_one {Δ : SimplexCategory} {n : ℕ} (f : Δ ⟶ ⦋n⦌) {g : Δ ⟶ ⦋1⦌}
    (hg : ∀ x, (g.toOrderHom x).val = 1) : IsPrismIndex f g 0 :=
  fun x ↦ ⟨fun h ↦ by rw [hg x] at h; omega, fun _ ↦ Nat.zero_le _⟩

lemma IsPrismIndex.of_zero {Δ : SimplexCategory} {n : ℕ} (f : Δ ⟶ ⦋n⦌) {g : Δ ⟶ ⦋1⦌}
    (hg : ∀ x, (g.toOrderHom x).val = 0) : IsPrismIndex f g (Fin.last n) :=
  fun x ↦ ⟨fun _ ↦ by simpa [Nat.lt_succ_iff] using (f.toOrderHom x).isLt,
    fun h ↦ by rw [hg x] at h; omega⟩

lemma sumHom_of_one {Δ : SimplexCategory} {n : ℕ} (f : Δ ⟶ ⦋n⦌) {g : Δ ⟶ ⦋1⦌}
    (hg : ∀ x, (g.toOrderHom x).val = 1) : sumHom f g = f ≫ δ 0 :=
  hom_ext_val fun x ↦ by
    simp only [sumHom_val, hg x, comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    rw [δ_val, if_neg (by simp)]

lemma sumHom_of_zero {Δ : SimplexCategory} {n : ℕ} (f : Δ ⟶ ⦋n⦌) {g : Δ ⟶ ⦋1⦌}
    (hg : ∀ x, (g.toOrderHom x).val = 0) : sumHom f g = f ≫ δ (Fin.last (n + 1)) :=
  hom_ext_val fun x ↦ by
    simp only [sumHom_val, hg x, comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    rw [δ_val, if_pos (by simpa [Nat.lt_succ_iff] using (f.toOrderHom x).isLt)]
    rfl

lemma sumHom_comp_prism {Δ : SimplexCategory} {m n : ℕ} {f : Δ ⟶ ⦋m⦌} {g : Δ ⟶ ⦋1⦌}
    {k : Fin (m + 1)} (hk : IsPrismIndex f g k) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    sumHom f g ≫ prism θ k = sumHom (f ≫ θ) g := hom_ext_val fun x ↦ by
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, prism_apply, sumHom_val]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (val_le_one g x) with h | h
  · rw [prismFun_of_le _ _ _ (by simp only [sumHom_val, h]; exact (hk x).1 h), Fin.val_castSucc]
    calc _ = (θ.toOrderHom (f.toOrderHom x)).val :=
          congrArg Fin.val (toOrderHom_congr θ (by simp [h]))
      _ = _ := by simp [h]
  · rw [prismFun_of_lt _ _ _ (by simp only [sumHom_val, h]; have := (hk x).2 h; omega),
      Fin.val_succ]
    calc _ = (θ.toOrderHom (f.toOrderHom x)).val + 1 :=
          congrArg (· + 1) (congrArg Fin.val (toOrderHom_congr θ (by simp [h])))
      _ = _ := by simp [h]

lemma IsPrismIndex.comp_right {Δ : SimplexCategory} {m n : ℕ} {f : Δ ⟶ ⦋m⦌} {g : Δ ⟶ ⦋1⦌}
    {k : Fin (m + 1)} (hk : IsPrismIndex f g k) (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    IsPrismIndex (f ≫ θ) g (θ.toOrderHom k) := fun x ↦
  ⟨fun h ↦ θ.toOrderHom.monotone (Fin.le_def.2 ((hk x).1 h)),
    fun h ↦ θ.toOrderHom.monotone (Fin.le_def.2 ((hk x).2 h))⟩

/-- The map `⦋n⦌ ⟶ ⦋1⦌` switching from `0` to `1` at `s`. -/
def sw {n : ℕ} (s : Fin (n + 2)) : ⦋n⦌ ⟶ ⦋1⦌ :=
  Hom.mk ⟨fun x ↦ if x.val < s.val then 0 else 1, fun x y hxy ↦ by
    rw [Fin.le_def] at hxy
    dsimp only
    split_ifs <;> simp <;> omega⟩

lemma sw_val {n : ℕ} (s : Fin (n + 2)) (x : Fin (n + 1)) :
    ((sw s).toOrderHom x).val = if x.val < s.val then 0 else 1 := by
  change (if x.val < s.val then (0 : Fin 2) else 1).val = _
  split_ifs <;> rfl

/-- The map `⦋n + 1⦌ ⟶ ⦋1⦌` describing the second coordinate of the `k`-th prism simplex. -/
def side {n : ℕ} (k : Fin (n + 1)) : ⦋n + 1⦌ ⟶ ⦋1⦌ :=
  Hom.mk ⟨fun x ↦ if x.val ≤ k.val then 0 else 1, fun x y hxy ↦ by
    rw [Fin.le_def] at hxy
    dsimp only
    split_ifs <;> simp <;> omega⟩

lemma side_val {n : ℕ} (k : Fin (n + 1)) (x : Fin (n + 2)) :
    ((side k).toOrderHom x).val = if x.val ≤ k.val then 0 else 1 := by
  change (if x.val ≤ k.val then (0 : Fin 2) else 1).val = _
  split_ifs <;> rfl

/-- The switching point of a map `⦋n⦌ ⟶ ⦋1⦌`. -/
def switch {n : ℕ} (g : ⦋n⦌ ⟶ ⦋1⦌) : Fin (n + 2) :=
  ⟨(Finset.univ.filter fun x ↦ (g.toOrderHom x).val = 0).sup fun x ↦ x.val + 1, by
    rw [Finset.sup_lt_iff (by simp)]
    intro x _
    have := x.isLt
    simp only [len_mk] at this
    omega⟩

lemma sw_switch {n : ℕ} (g : ⦋n⦌ ⟶ ⦋1⦌) : sw (switch g) = g := hom_ext_val fun x ↦ by
  rw [sw_val]
  have hs : (switch g).val = (Finset.univ.filter fun x ↦ (g.toOrderHom x).val = 0).sup
      fun x : Fin (n + 1) ↦ x.val + 1 := rfl
  rw [hs]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (val_le_one g x) with h | h
  · rw [h, if_pos]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Finset.le_sup (f := fun x : Fin (n + 1) ↦ x.val + 1)
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  · rw [h, if_neg]
    refine not_lt.2 (Finset.sup_le fun y hy ↦ ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    by_contra hxy
    have := g.toOrderHom.monotone (show x ≤ y from Fin.le_def.2 (by omega))
    rw [Fin.le_def] at this
    omega

lemma sw_injective {n : ℕ} : Function.Injective (sw (n := n)) := by
  intro s s' h
  by_contra hne
  wlog hlt : s < s' generalizing s s'
  · exact this h.symm (Ne.symm hne) (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne))
  have hs : s.val < n + 1 := by have := s'.isLt; rw [Fin.lt_def] at hlt; omega
  have := congrArg (fun g : ⦋n⦌ ⟶ ⦋1⦌ ↦ (g.toOrderHom ⟨s.val, hs⟩).val) h
  simp only [sw_val] at this
  rw [Fin.lt_def] at hlt
  rw [if_neg (lt_irrefl _), if_pos hlt] at this
  exact one_ne_zero this

lemma switch_sw {n : ℕ} (s : Fin (n + 2)) : switch (sw s) = s :=
  sw_injective (sw_switch _)

lemma sw_zero_val {n : ℕ} (x : Fin (n + 1)) : ((sw (0 : Fin (n + 2))).toOrderHom x).val = 1 := by
  rw [sw_val, if_neg (by simp)]

lemma sw_last_val {n : ℕ} (x : Fin (n + 1)) :
    ((sw (Fin.last (n + 1))).toOrderHom x).val = 0 := by
  rw [sw_val, if_pos (by simp)]

lemma δ_castSucc_comp_side {n : ℕ} (k : Fin (n + 1)) : δ k.castSucc ≫ side k = sw k.castSucc :=
  hom_ext_val fun x ↦ by
    simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, side_val, sw_val,
      δ_val, Fin.val_castSucc]
    split_ifs <;> omega

lemma δ_succ_comp_side {n : ℕ} (k : Fin (n + 1)) : δ k.succ ≫ side k = sw k.succ :=
  hom_ext_val fun x ↦ by
    simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, side_val, sw_val,
      δ_val, Fin.val_succ]
    split_ifs <;> omega

lemma isPrismIndex_σ_side {n : ℕ} (l : Fin (n + 1)) : IsPrismIndex (σ l) (side l) l := by
  intro x
  rw [side_val, σ_val]
  constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

lemma sumHom_σ_side {n : ℕ} (l : Fin (n + 1)) : sumHom (σ l) (side l) = 𝟙 _ :=
  hom_ext_val fun x ↦ by
    rw [sumHom_val, side_val, σ_val]
    simp only [id_toOrderHom, OrderHom.id_coe, id_eq]
    split_ifs <;> omega

lemma prism_comp_σ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (m + 1)) :
    prism θ k ≫ σ (θ.toOrderHom k) = σ k ≫ θ := hom_ext_val fun x ↦ by
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, prism_apply]
  by_cases hx : x.val ≤ k.val
  · rw [prismFun_of_le _ _ _ hx, σ_val, if_pos (by
      simpa using toOrderHom_val_mono θ (a := ⟨x.val, by simp; omega⟩) (b := k) hx)]
    simp only [Fin.val_castSucc]
    exact congrArg Fin.val (toOrderHom_congr θ (by rw [σ_val, if_pos hx]))
  · rw [prismFun_of_lt _ _ _ (by omega), σ_val, if_neg (by
      have := toOrderHom_val_mono θ (a := k) (b := ⟨x.val - 1, by simp at *; omega⟩)
        (by simp only; omega)
      simp only [Fin.val_succ]
      omega)]
    simp only [Fin.val_succ, Nat.add_sub_cancel]
    exact congrArg Fin.val (toOrderHom_congr θ (by rw [σ_val, if_neg hx]))

lemma prism_comp_side {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (k : Fin (m + 1)) :
    prism θ k ≫ side (θ.toOrderHom k) = side k := hom_ext_val fun x ↦ by
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, prism_apply, side_val]
  by_cases hx : x.val ≤ k.val
  · rw [prismFun_of_le _ _ _ hx, if_pos hx, if_pos (by
      simpa using toOrderHom_val_mono θ (a := ⟨x.val, by simp; omega⟩) (b := k) hx)]
  · rw [prismFun_of_lt _ _ _ (by omega), if_neg hx, if_neg (by
      have := toOrderHom_val_mono θ (a := k) (b := ⟨x.val - 1, by simp at *; omega⟩)
        (by simp only; omega)
      simp only [Fin.val_succ]
      omega)]

lemma not_epi_of_len_lt {Δ : SimplexCategory} {n : ℕ} (θ : Δ ⟶ ⦋n⦌) (h : Δ.len < n) :
    ¬ Epi θ := fun _ ↦ by
  have := len_le_of_epi θ
  simp only [len_mk] at this
  omega

lemma not_epi_comp_of_not_epi {Δ' Δ Δ'' : SimplexCategory} (θ : Δ' ⟶ Δ) (f : Δ ⟶ Δ'')
    (hf : ¬ Epi f) : ¬ Epi (θ ≫ f) := fun _ ↦ hf (epi_of_epi θ f)

end SimplexCategory

namespace CategoryTheory.SimplicialObject

open SimplexCategory

variable {C : Type*} [Category* C] {U V : SimplicialObject C} (a b : U ⟶ V) [HasFiniteLimits C]

/-- The value of the path family of `z` on the simplex `(f, g)` of the prism. -/
noncomputable def pathValue {T : C} {r : ℕ} {Δ : SimplexCategory} (z : T ⟶ pathObj a b r)
    (f : Δ ⟶ ⦋r⦌) (g : Δ ⟶ ⦋1⦌) : T ⟶ V.obj (op Δ) :=
  z ≫ pathH a b r (prismIndex f g) ≫ V.map (sumHom f g).op

variable {a b}

lemma pathValue_eq {T : C} {r : ℕ} {Δ : SimplexCategory} (z : T ⟶ pathObj a b r)
    {f : Δ ⟶ ⦋r⦌} {g : Δ ⟶ ⦋1⦌} {k : Fin (r + 1)} (hk : IsPrismIndex f g k) :
    pathValue a b z f g = z ≫ pathH a b r k ≫ V.map (sumHom f g).op := by
  have key : ∀ k k' : Fin (r + 1), IsPrismIndex f g k → IsPrismIndex f g k' → k ≤ k' →
      pathH a b r k' ≫ V.map (sumHom f g).op = pathH a b r k ≫ V.map (sumHom f g).op := by
    intro k k' hk hk' hle
    refine (isPathFamily_pathH a b r).map_eq k k' hle _ fun x ⟨h₁, h₂⟩ ↦ ?_
    rw [sumHom_val] at h₁ h₂
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (val_le_one g x) with h | h
    · have := (hk x).1 h
      omega
    · have := (hk' x).2 h
      omega
  rw [pathValue]
  rcases le_total (prismIndex f g) k with h | h
  · rw [key _ _ (isPrismIndex_prismIndex f g) hk h]
  · rw [key _ _ hk (isPrismIndex_prismIndex f g) h]

lemma pathValue_precomp {T T' : C} {r : ℕ} {Δ : SimplexCategory} (t : T' ⟶ T)
    (z : T ⟶ pathObj a b r) (f : Δ ⟶ ⦋r⦌) (g : Δ ⟶ ⦋1⦌) :
    pathValue a b (t ≫ z) f g = t ≫ pathValue a b z f g := by
  simp [pathValue]

lemma pathValue_comp {T : C} {r : ℕ} {Δ Δ' : SimplexCategory} (z : T ⟶ pathObj a b r)
    (f : Δ ⟶ ⦋r⦌) (g : Δ ⟶ ⦋1⦌) (θ : Δ' ⟶ Δ) :
    pathValue a b z f g ≫ V.map θ.op = pathValue a b z (θ ≫ f) (θ ≫ g) := by
  rw [pathValue_eq z ((isPrismIndex_prismIndex f g).comp θ), pathValue, Category.assoc,
    Category.assoc, ← V.map_comp, ← op_comp, comp_sumHom]

lemma pathValue_map {T : C} {m n : ℕ} {Δ : SimplexCategory} (z : T ⟶ pathObj a b n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (f : Δ ⟶ ⦋m⦌) (g : Δ ⟶ ⦋1⦌) :
    pathValue a b (z ≫ (pathSpace a b).map θ.op) f g = pathValue a b z (f ≫ θ) g := by
  have hk := isPrismIndex_prismIndex f g
  rw [pathValue_eq z (hk.comp_right θ), pathValue, Category.assoc]
  erw [pathMapObj_pathH_assoc]
  rw [pathMap, Category.assoc, ← V.map_comp, ← op_comp, sumHom_comp_prism hk]
  rfl

lemma pathValue_σ_side {T : C} {r : ℕ} (z : T ⟶ pathObj a b r) (l : Fin (r + 1)) :
    pathValue a b z (SimplexCategory.σ l) (side l) = z ≫ pathH a b r l := by
  rw [pathValue_eq z (isPrismIndex_σ_side l), sumHom_σ_side, op_id, V.map_id,
    Category.comp_id]

lemma pathValue_of_one {T : C} {r : ℕ} {Δ : SimplexCategory} (z : T ⟶ pathObj a b r)
    (f : Δ ⟶ ⦋r⦌) {g : Δ ⟶ ⦋1⦌} (hg : ∀ x, (g.toOrderHom x).val = 1) :
    pathValue a b z f g = z ≫ pathU a b r ≫ U.map f.op ≫ b.app _ := by
  rw [pathValue_eq z (IsPrismIndex.of_one f hg), sumHom_of_one f hg, op_comp, V.map_comp,
    ← Category.assoc (pathH a b r 0), ← SimplicialObject.δ, pathH_zero, Category.assoc,
    b.naturality]

lemma pathValue_of_zero {T : C} {r : ℕ} {Δ : SimplexCategory} (z : T ⟶ pathObj a b r)
    (f : Δ ⟶ ⦋r⦌) {g : Δ ⟶ ⦋1⦌} (hg : ∀ x, (g.toOrderHom x).val = 0) :
    pathValue a b z f g = z ≫ pathU a b r ≫ U.map f.op ≫ a.app _ := by
  rw [pathValue_eq z (IsPrismIndex.of_zero f hg), sumHom_of_zero f hg, op_comp, V.map_comp,
    ← Category.assoc (pathH a b r _), ← SimplicialObject.δ, pathH_last, Category.assoc,
    a.naturality]

end CategoryTheory.SimplicialObject
