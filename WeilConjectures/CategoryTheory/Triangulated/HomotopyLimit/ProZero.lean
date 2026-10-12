/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic

/-!
# Homotopy limits of pro-zero towers

A tower `F : ℕᵒᵖ ⥤ C` is *pro-zero* (`CategoryTheory.Functor.IsProZero`) if for every `n` some
transition map `Fₘ ⟶ Fₙ` with `m ≥ n` vanishes. In a pretriangulated category the homotopy limit
of a pro-zero tower is zero (`CategoryTheory.Pretriangulated.IsHomotopyLimit.isZero_of_isProZero`):
the endomorphism `1 - t` of `∏ₙ Fₙ` is invertible, with inverse `∑ₖ tᵏ`, which is a finite sum
on each factor.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite

variable {C : Type*} [Category C]

section

variable [HasZeroMorphisms C]

/-- A tower `F : ℕᵒᵖ ⥤ C` is *pro-zero* if for every `n` some transition map `Fₘ ⟶ Fₙ`,
`m ≥ n`, vanishes. -/
def Functor.IsProZero (F : ℕᵒᵖ ⥤ C) : Prop :=
  ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), F.map (homOfLE h).op = 0

lemma Functor.IsProZero.map_eq_zero_of_le {F : ℕᵒᵖ ⥤ C} {n m m' : ℕ} (h : n ≤ m) (h' : m ≤ m')
    (hm : F.map (homOfLE h).op = 0) : F.map (homOfLE (h.trans h')).op = 0 := by
  rw [show (homOfLE (h.trans h')).op = (homOfLE h').op ≫ (homOfLE h).op from rfl,
    F.map_comp, hm, comp_zero]

end

namespace Pretriangulated

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section

variable {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P)

/-- The component `∏ₖ Fₖ ⟶ Fₙ₊ₖ ⟶ Fₙ` of `tᵏ`. -/
noncomputable def proZeroTerm (n k : ℕ) : P.pt ⟶ F.obj (op n) :=
  P.proj (n + k) ≫ F.map (homOfLE (Nat.le_add_right n k)).op

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma proj_comp_map_eq_of_eq {a b n : ℕ} (hab : a = b) (f : op a ⟶ op n) (g : op b ⟶ op n) :
    P.proj a ≫ F.map f = P.proj b ≫ F.map g := by
  subst hab
  rw [Subsingleton.elim f g]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma proZeroTerm_zero (n : ℕ) : proZeroTerm (P := P) n 0 = P.proj n := by
  have : F.map (homOfLE (Nat.le_add_right n 0)).op = 𝟙 _ := F.map_id _
  rw [proZeroTerm, this, comp_id]
  rfl

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma proZeroTerm_succ_left (n k : ℕ) :
    proZeroTerm (P := P) (n + 1) k ≫ F.map (homOfLE n.le_succ).op =
      proZeroTerm (P := P) n (k + 1) := by
  simp only [proZeroTerm, assoc, ← F.map_comp]
  exact proj_comp_map_eq_of_eq (by omega) _ _

include hP in
lemma sub_towerShift_comp_proZeroTerm (n k : ℕ) :
    (𝟙 _ - towerShift hP) ≫ proZeroTerm (P := P) n k =
      proZeroTerm (P := P) n k - proZeroTerm (P := P) n (k + 1) := by
  simp only [proZeroTerm, Preadditive.sub_comp, id_comp, towerShift_proj_assoc, ← F.map_comp]
  congr 1
  all_goals exact proj_comp_map_eq_of_eq (by omega) _ _

lemma proZeroTerm_eq_zero {n m : ℕ} (h : n ≤ m) (hm : F.map (homOfLE h).op = 0) (k : ℕ)
    (hk : m ≤ n + k) : proZeroTerm (P := P) n k = 0 := by
  rw [proZeroTerm, Functor.IsProZero.map_eq_zero_of_le h hk hm, comp_zero]

lemma sum_proZeroTerm_eq {n m : ℕ} (h : n ≤ m) (hm : F.map (homOfLE h).op = 0) (M : ℕ)
    (hM : m ≤ n + M) :
    ∑ k ∈ Finset.range M, proZeroTerm (P := P) n k =
      ∑ k ∈ Finset.range (m - n), proZeroTerm (P := P) n k := by
  induction M with
  | zero => rw [show m - n = 0 by omega]
  | succ M ih =>
    by_cases hM' : m ≤ n + M
    · rw [Finset.sum_range_succ, ih hM', proZeroTerm_eq_zero h hm M hM', add_zero]
    · rw [show m - n = M + 1 by omega]

end

/-- **The homotopy limit of a pro-zero tower vanishes.** If `F` is pro-zero, the endomorphism
`1 - t` of `∏ₙ Fₙ` is invertible (its inverse is `∑ₖ tᵏ`, a finite sum on each factor), so the
first term of the Milnor triangle is zero. -/
theorem IsHomotopyLimit.isZero_of_isProZero {F : ℕᵒᵖ ⥤ C} (hF : F.IsProZero) {c : Cone F}
    (hc : IsHomotopyLimit c) : IsZero c.pt := by
  obtain ⟨P, hP, δ, hT⟩ := hc
  choose m hm hm0 using hF
  -- a bound `B n ≥ m n - n` with also `B (n + 1) + 1 ≥ m n - n`
  let B : ℕ → ℕ := fun n ↦ ∑ i ∈ Finset.range (n + 2), m i
  have hB (n : ℕ) : m n ≤ n + B n := by
    have : m n ≤ B n := Finset.single_le_sum (f := m) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
    omega
  have hB' (n : ℕ) : m n ≤ n + (B (n + 1) + 1) := by
    have : m n ≤ B (n + 1) := Finset.single_le_sum (f := m) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
    omega
  let s : P.pt ⟶ P.pt := Fan.IsLimit.lift hP fun n ↦
    ∑ k ∈ Finset.range (B n), proZeroTerm (P := P) n k
  have hs (n : ℕ) : s ≫ P.proj n = ∑ k ∈ Finset.range (B n), proZeroTerm (P := P) n k :=
    Fan.IsLimit.fac hP _ n
  have h₁ : (𝟙 _ - towerShift hP) ≫ s = 𝟙 _ := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
    rw [assoc, hs, Preadditive.comp_sum]
    simp only [sub_towerShift_comp_proZeroTerm hP]
    rw [Finset.sum_range_sub', proZeroTerm_zero,
      proZeroTerm_eq_zero (hm n) (hm0 n) (B n) (hB n), sub_zero, id_comp]
  have h₂ : s ≫ (𝟙 _ - towerShift hP) = 𝟙 _ := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
    rw [assoc, Preadditive.sub_comp, id_comp, towerShift_proj, Preadditive.comp_sub,
      reassoc_of% (hs (n + 1)), hs, Preadditive.sum_comp]
    simp only [proZeroTerm_succ_left]
    rw [sum_proZeroTerm_eq (hm n) (hm0 n) _ (hB n)]
    have e' := sum_proZeroTerm_eq (P := P) (hm n) (hm0 n) (B (n + 1) + 1) (hB' n)
    rw [Finset.sum_range_succ'] at e'
    rw [← e', proZeroTerm_zero]
    abel
  have : IsIso (𝟙 P.pt - towerShift hP) := ⟨s, h₁, h₂⟩
  exact Triangle.isZero₁_of_isIso₂ _ hT this

end Pretriangulated

end CategoryTheory
