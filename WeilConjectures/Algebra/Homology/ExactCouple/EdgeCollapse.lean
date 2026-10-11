/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.Convergence

/-!
# Degenerate spectral sequences of exact couples

If from some page on the spectral sequence of a convergent exact couple is concentrated in the
column `p = 0`, then all later differentials vanish and the abutment is that column
(`CategoryTheory.ExactCouple.edge_collapse`).

## Main statements

- `CategoryTheory.ExactCouple.isZero_derivedIter_E`: vanishing entries stay zero on later pages.
- `CategoryTheory.ExactCouple.nonempty_derivedIter_E_iso`: an entry without incoming and
  outgoing differentials is unchanged on the next page.
- `CategoryTheory.ExactCouple.edge_collapse`: the edge collapse.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace DecreasingFiltration

variable {A : C} (F : DecreasingFiltration A)

/-- If the graded piece `grᵖ` vanishes, then `Fᵖ⁺¹ = Fᵖ`. -/
lemma F_succ_eq_of_isZero_gr (p : ℤ) (h : IsZero (F.gr p)) : F.F (p + 1) = F.F p := by
  refine le_antisymm (F.F_succ_le p) ?_
  have : Epi (Subobject.ofLE _ _ (F.F_succ_le p)) :=
    (ShortComplex.exact_cokernel _).epi_f (h.eq_of_tgt _ _)
  have : IsIso (Subobject.ofLE _ _ (F.F_succ_le p)) := isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ (F.F_succ_le p))) (by simp)

/-- A filtration with `Fᴺ = 0` whose graded pieces vanish in degrees `≥ p` has `Fᵖ = 0`. -/
lemma F_eq_bot_of_isZero_gr (N p : ℤ) (hN : F.F N = ⊥) (h : ∀ k ≥ p, IsZero (F.gr k)) :
    F.F p = ⊥ := by
  by_cases hpN : N ≤ p
  · exact eq_bot_iff.mpr ((F.antitone hpN).trans hN.le)
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, p + k = N := ⟨(N - p).toNat, by omega⟩
    clear hpN
    induction k generalizing p with
    | zero =>
      obtain rfl : p = N := by simpa using hk
      exact hN
    | succ k ih =>
      rw [← F.F_succ_eq_of_isZero_gr p (h p le_rfl)]
      exact ih (p + 1) (fun l hl ↦ h l (by omega)) (by push_cast at hk; omega)

/-- A filtration with `Fᵐ = A` whose graded pieces vanish in degrees `< p` has `Fᵖ = A`. -/
lemma F_eq_top_of_isZero_gr (m p : ℤ) (hm : F.F m = ⊤) (h : ∀ k < p, IsZero (F.gr k)) :
    F.F p = ⊤ := by
  by_cases hmp : p ≤ m
  · exact eq_top_iff.mpr (hm.ge.trans (F.antitone hmp))
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m + k = p := ⟨(p - m).toNat, by omega⟩
    clear hmp
    induction k generalizing p with
    | zero =>
      obtain rfl : p = m := by simpa using hk.symm
      exact hm
    | succ k ih =>
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [F.F_succ_eq_of_isZero_gr q (h q (by omega))]
      exact ih q (fun l hl ↦ h l (by omega)) (by push_cast at hk; omega)

end DecreasingFiltration

namespace ExactCouple

variable {κ : Type w} [AddCommGroup κ] {a b c : κ} (X : ExactCouple C a b c)

/-- Vanishing entries of the spectral sequence of a couple stay zero on the later pages, the
pages being subquotients of the earlier ones. -/
lemma isZero_derivedIter_E (N M : ℕ) (hNM : N ≤ M) (i : κ)
    (h : IsZero ((X.derivedIter N).E i)) : IsZero ((X.derivedIter M).E i) := by
  induction M, hNM using Nat.le_induction with
  | base => exact h
  | succ M _ ih =>
    exact ShortComplex.isZero_homology_of_isZero_X₂ _ ih

/-- An entry of the spectral sequence of a couple which has no incoming and no outgoing
differential is unchanged on the next page. -/
lemma nonempty_derivedIter_E_iso (N : ℕ) (i : κ)
    (hout : (X.derivedIter N).d i (i + (b + degIter a c N)) = 0)
    (hin : (X.derivedIter N).d (i - (b + degIter a c N)) i = 0) :
    Nonempty ((X.derivedIter (N + 1)).E i ≅ (X.derivedIter N).E i) := by
  let K := (X.derivedIter N).dComplex
  have e₁ := K.iCyclesIso i _ (dComplex_next i) hout
  have e₂ := K.isoHomologyπ _ i (dComplex_prev i) hin
  exact ⟨e₂.symm ≪≫ e₁⟩

section Collapse

variable {b : ℤ × ℤ} (X : ExactCouple C ((-1, 0) : ℤ × ℤ) b 0)

lemma degIter_eq' (N : ℕ) : degIter ((-1, 0) : ℤ × ℤ) (0 : ℤ × ℤ) N = ((N : ℤ), 0) := by
  rw [degIter_eq]
  ext <;> simp

/-- If the spectral sequence of a couple is concentrated in the column `p = 0` on some page,
then all the differentials vanish from that page on. -/
lemma d_eq_zero_of_isZero (hb : 0 < b.1) (N₀ : ℕ)
    (h : ∀ p n : ℤ, p ≠ 0 → IsZero ((X.derivedIter N₀).E (p, n))) (N : ℕ) (hN : N₀ ≤ N)
    (i j : ℤ × ℤ) : (X.derivedIter N).d i j = 0 := by
  by_cases hi : i.1 = 0
  · by_cases hj : i + (b + degIter ((-1, 0) : ℤ × ℤ) (0 : ℤ × ℤ) N) = j
    · apply IsZero.eq_of_tgt
      apply X.isZero_derivedIter_E N₀ N hN
      obtain ⟨p, n⟩ := j
      refine h p n ?_
      have := congrArg _root_.Prod.fst hj
      rw [degIter_eq'] at this
      simp at this
      omega
    · exact (X.derivedIter N).shape_d _ _ hj
  · apply IsZero.eq_of_src
    apply X.isZero_derivedIter_E N₀ N hN
    obtain ⟨p, n⟩ := i
    exact h p n hi

/-- **Edge collapse.** Let `X` be an exact couple (with `α` of degree `(-1, 0)`, `g` of degree
`0` and `f` of degree `b` with `b.1 > 0`) whose spectral sequence converges to finite
filtrations of objects `Aⁿ`, and suppose that on some page all the entries `E^{p, n}` with
`p ≠ 0` vanish. Then all later differentials vanish, the later pages agree with that page, and
`Aⁿ` is the entry `E^{0, n}` of that page.

In the bigrading `(p, q)` of the blueprint (`n = p + q`) this is the statement for the column
`p = 0`, with the edge isomorphism `Aⁿ ≅ E^{0, n}`.

(blueprint: `lem-sp-edge-collapse`) -/
theorem edge_collapse (hb : 0 < b.1) {A : ℤ → C} {F : ∀ n, DecreasingFiltration (A n)}
    (hX : X.ConvergesTo A F) (hF : ∀ n, ∃ m M : ℤ, (F n).F m = ⊤ ∧ (F n).F M = ⊥) (N₀ : ℕ)
    (h : ∀ p n : ℤ, p ≠ 0 → IsZero ((X.derivedIter N₀).E (p, n))) :
    (∀ N ≥ N₀, ∀ i j, (X.derivedIter N).d i j = 0) ∧
      (∀ N ≥ N₀, ∀ n : ℤ, Nonempty ((X.derivedIter N).E (0, n) ≅ (X.derivedIter N₀).E (0, n))) ∧
      ∀ n : ℤ, Nonempty (A n ≅ (X.derivedIter N₀).E (0, n)) := by
  have hd := X.d_eq_zero_of_isZero hb N₀ h
  have hstable : ∀ N ≥ N₀, ∀ n : ℤ,
      Nonempty ((X.derivedIter N).E (0, n) ≅ (X.derivedIter N₀).E (0, n)) := by
    intro N hN n
    induction N, hN using Nat.le_induction with
    | base => exact ⟨Iso.refl _⟩
    | succ N hN ih =>
      obtain ⟨e⟩ := X.nonempty_derivedIter_E_iso N (0, n) (hd N hN _ _) (hd N hN _ _)
      exact ⟨e ≪≫ ih.some⟩
  refine ⟨hd, hstable, fun n ↦ ?_⟩
  obtain ⟨m, M, hm, hM⟩ := hF n
  have hgr : ∀ p ≠ 0, IsZero ((F n).gr p) := by
    intro p hp
    obtain ⟨N₁, hN₁⟩ := hX p n
    obtain ⟨-, -, ⟨e⟩⟩ := hN₁ (max N₁ N₀) (le_max_left _ _)
    exact (X.isZero_derivedIter_E N₀ _ (le_max_right _ _) _ (h p n hp)).of_iso e.symm
  have h₁ : (F n).F 1 = ⊥ :=
    (F n).F_eq_bot_of_isZero_gr M 1 hM (fun k hk ↦ hgr k (by omega))
  have h₀ : (F n).F 0 = ⊤ :=
    (F n).F_eq_top_of_isZero_gr m 0 hm (fun k hk ↦ hgr k (by omega))
  obtain ⟨N₁, hN₁⟩ := hX 0 n
  obtain ⟨-, -, ⟨e⟩⟩ := hN₁ (max N₁ N₀) (le_max_left _ _)
  obtain ⟨e'⟩ := hstable (max N₁ N₀) (le_max_right _ _) n
  have key : ∀ (P Q : Subobject (A n)) (hP : P = ⊥) (hQ : Q = ⊤) (hPQ : P ≤ Q),
      Nonempty (cokernel (Subobject.ofLE P Q hPQ) ≅ A n) := by
    intro P Q hP hQ hPQ
    subst hP hQ
    have : Subobject.ofLE (⊥ : Subobject (A n)) ⊤ hPQ = 0 :=
      (Subobject.botCoeIsoZero.isZero_iff.mpr (isZero_zero _)).eq_of_src _ _
    exact ⟨(cokernelIsoOfEq this) ≪≫ cokernelZeroIsoTarget ≪≫
      asIso (⊤ : Subobject (A n)).arrow⟩
  obtain ⟨e''⟩ := key _ _ h₁ h₀ ((F n).F_succ_le 0)
  exact ⟨e''.symm ≪≫ e.symm ≪≫ e'⟩

end Collapse

end ExactCouple

end CategoryTheory
