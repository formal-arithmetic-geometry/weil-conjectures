/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicTopology.OrderedJoinChains

/-! # Single-color identities for ordered join chains

Source: six-functors direct-images proof, paragraph (3), agent-written ordered-join
expansion, calculations 1-4, below local continuous-cocycle descent. These calculations
are not asserted in the blueprint itself
(blueprint: lem-sfb-ordered-join-single-color-identities).

The symbols, specified free integer modules, and explicit maps are the existing
constructions in `AlgebraicTopology.OrderedJoin`. Both identities include the augmented
empty symbol and every integer degree. No equality test on vertices is required.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicTopology.OrderedJoin

open scoped BigOperators

private theorem face_ext {r : ℕ} {X : Fin r → Type u} {σ τ : Face X}
    (h : σ.colors = τ.colors)
    (hv : ∀ i hi, σ.vertex i hi = τ.vertex i (h ▸ hi)) : σ = τ := by
  cases σ
  cases τ
  cases h
  congr
  funext i hi
  exact hv i hi

private theorem erase_erase {r : ℕ} {X : Fin r → Type u}
    (σ : Face X) (i j : Fin r) : erase (erase σ i) j = erase (erase σ j) i := by
  apply face_ext (Finset.erase_right_comm)
  intros
  rfl

private theorem erase_insert_self {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (σ : Face X) (i : Fin r) (hi : i ∉ σ.colors) :
    erase (insert v i σ) i = σ := by
  apply face_ext (Finset.erase_insert hi)
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [erase, insert, hji]

private theorem erase_insert_other {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (σ : Face X) (i j : Fin r) (hij : i ≠ j) :
    erase (insert v i σ) j = insert v i (erase σ j) := by
  apply face_ext (Finset.erase_insert_of_ne hij)
  intro k hk
  by_cases hki : k = i <;> simp [erase, insert, hki]

private theorem insert_erase {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (σ : Face X) (i : Fin r) (hi : i ∈ σ.colors) :
    insert v i (erase σ i) = replaceColors v {i} σ := by
  apply face_ext (Finset.insert_erase hi)
  intro j hj
  by_cases hji : j = i
  · subst j
    simp [insert, replaceColors]
  · simp [insert, erase, replaceColors, hji]

private theorem term_eq {r : ℕ} {X : Fin r → Type u} (q : ℤ) (σ : Face X)
    (h : (σ.colors.card : ℤ) = q + 1) :
    symbolTerm X q σ = Finsupp.single ⟨σ, h⟩ 1 := by
  classical
  simp [symbolTerm, h]

private theorem boundary_term {r : ℕ} {X : Fin r → Type u} (q p : ℤ) (σ : Face X)
    (h : (σ.colors.card : ℤ) = q + 1) :
    boundary X q p (symbolTerm X q σ) =
      ∑ i ∈ σ.colors, positionSign σ.colors i • symbolTerm X p (erase σ i) := by
  classical
  simp [term_eq q σ h, boundary, Finsupp.linearCombination_single]

private theorem insertion_term {r : ℕ} {X : Fin r → Type u} (v : ∀ i, X i)
    (i : Fin r) (q p : ℤ) (σ : Face X) (h : (σ.colors.card : ℤ) = q + 1) :
    insertion v i q p (symbolTerm X q σ) =
      if i ∈ σ.colors then 0
      else positionSign σ.colors i • symbolTerm X p (insert v i σ) := by
  classical
  simp [term_eq q σ h, insertion, Finsupp.linearCombination_single]

private theorem erase_card {r : ℕ} {X : Fin r → Type u} {q : ℤ} (σ : Face X)
    (h : (σ.colors.card : ℤ) = q + 1) (i : Fin r) (hi : i ∈ σ.colors) :
    ((erase σ i).colors.card : ℤ) = (q - 1) + 1 := by
  have hc := Finset.card_erase_add_one hi
  dsimp [erase]
  omega

private theorem insert_card {r : ℕ} {X : Fin r → Type u} {q : ℤ} (v : ∀ i, X i)
    (σ : Face X) (h : (σ.colors.card : ℤ) = q + 1) (i : Fin r) (hi : i ∉ σ.colors) :
    ((insert v i σ).colors.card : ℤ) = (q + 1) + 1 := by
  simp [insert, Finset.card_insert_of_notMem hi, h]

private theorem sign_sq {r : ℕ} (C : Finset (Fin r)) (i : Fin r) :
    positionSign C i * positionSign C i = 1 := by
  unfold positionSign
  rw [← mul_pow]
  norm_num

private theorem sign_insert {r : ℕ} (C : Finset (Fin r)) (i j : Fin r)
    (hi : i ∉ C) :
    positionSign (Insert.insert i C) j =
      if i < j then -positionSign C j else positionSign C j := by
  classical
  unfold positionSign
  by_cases hij : i < j
  · rw [Finset.filter_insert, if_pos hij,
      Finset.card_insert_of_notMem (by simp [hi]), pow_succ]
    simp [hij]
  · simp [Finset.filter_insert, hij]

private theorem sign_erase {r : ℕ} (C : Finset (Fin r)) (i j : Fin r)
    (hi : i ∈ C) :
    positionSign (C.erase i) j =
      if i < j then -positionSign C j else positionSign C j := by
  classical
  have h := sign_insert (C.erase i) i j (Finset.notMem_erase i C)
  rw [Finset.insert_erase hi] at h
  by_cases hij : i < j <;> simp_all

private theorem basis_ext {r : ℕ} {X : Fin r → Type u} {q p : ℤ}
    {f g : Chain X q →ₗ[ℤ] Chain X p}
    (h : ∀ σ, f (Finsupp.single σ 1) = g (Finsupp.single σ 1)) : f = g := by
  apply Finsupp.lhom_ext
  intro σ a
  have he : Finsupp.single σ a = a • Finsupp.single σ (1 : ℤ) := by simp
  rw [he, map_smul, map_smul, h σ]

private theorem boundary_single {r : ℕ} {X : Fin r → Type u} (q p : ℤ)
    (σ : Symbol X q) :
    boundary X q p (Finsupp.single σ 1) =
      ∑ i ∈ σ.val.colors, positionSign σ.val.colors i • symbolTerm X p (erase σ.val i) := by
  simp [boundary]

private theorem double_sum_cancel {r : ℕ} {M : Type u} [AddCommGroup M]
    (C : Finset (Fin r)) (f : Fin r → Fin r → M)
    (h : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → f i j + f j i = 0) :
    ∑ i ∈ C, ∑ j ∈ C.erase i, f i j = 0 := by
  classical
  let S := (C ×ˢ C).filter (fun t ↦ t.1 ≠ t.2)
  have he : (∑ i ∈ C, ∑ j ∈ C.erase i, f i j) = ∑ t ∈ S, f t.1 t.2 := by
    simp only [S, Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_filter, Finset.filter_ne]
  rw [he]
  have hm : ∀ t ∈ S, t.swap ∈ S := by
    intro t ht
    simpa only [S, Finset.mem_filter, Finset.mem_product, Prod.fst_swap,
      Prod.snd_swap, ne_comm, and_comm, and_left_comm] using ht
  refine Finset.sum_involution (fun t _ ↦ t.swap) ?_ ?_ hm ?_
  · intro t ht
    simp only [S, Finset.mem_filter, Finset.mem_product] at ht
    exact h t.1 ht.1.1 t.2 ht.1.2 ht.2
  · intro t ht _ hs
    have hn : t.1 ≠ t.2 := (Finset.mem_filter.mp ht).2
    exact hn (congrArg Prod.snd hs)
  · intros
    rfl

private theorem boundary_boundary {r : ℕ} (X : Fin r → Type u) (q : ℤ) :
    (boundary X (q - 1) (q - 2)).comp (boundary X q (q - 1)) = 0 := by
  classical
  apply basis_ext
  intro σ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, boundary_single, map_sum, map_smul]
  have he : ∀ i ∈ σ.val.colors,
      boundary X (q - 1) (q - 2) (symbolTerm X (q - 1) (erase σ.val i)) =
        ∑ j ∈ σ.val.colors.erase i,
          positionSign (σ.val.colors.erase i) j •
            symbolTerm X (q - 2) (erase (erase σ.val i) j) := by
    intro i hi
    exact boundary_term _ _ _ (erase_card σ.val σ.property i hi)
  simp_rw [Finset.sum_congr rfl (fun i hi ↦ congrArg
    (fun z ↦ positionSign σ.val.colors i • z) (he i hi)),
    Finset.smul_sum, smul_smul]
  apply double_sum_cancel
  intro i hi j hj hij
  rw [erase_erase σ.val j i, ← add_smul]
  have hc : positionSign σ.val.colors i * positionSign (σ.val.colors.erase i) j +
      positionSign σ.val.colors j * positionSign (σ.val.colors.erase j) i = 0 := by
    rw [sign_erase _ i j hi, sign_erase _ j i hj]
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · simp [hlt, not_lt_of_gt hlt, mul_comm]
    · simp [hlt, not_lt_of_gt hlt, mul_comm]
  change (_ : ℤ) • _ = 0
  rw [hc, zero_smul]

private theorem insertion_boundary_present {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (q : ℤ) (σ : Symbol X q) (i : Fin r) (hi : i ∈ σ.val.colors) :
    insertion v i (q - 1) q (boundary X q (q - 1) (Finsupp.single σ 1)) =
      symbolTerm X q (replaceColors v {i} σ.val) := by
  classical
  rw [boundary_single, map_sum]
  have hterm : ∀ j ∈ σ.val.colors,
      insertion v i (q - 1) q
        (positionSign σ.val.colors j • symbolTerm X (q - 1) (erase σ.val j)) =
      if j = i then symbolTerm X q (replaceColors v {i} σ.val) else 0 := by
    intro j hj
    rw [map_smul, insertion_term v i _ _ _ (erase_card σ.val σ.property j hj)]
    by_cases hji : j = i
    · subst j
      have hm : i ∉ (erase σ.val i).colors := Finset.notMem_erase i _
      rw [if_neg hm, if_pos rfl]
      change positionSign σ.val.colors i •
        (positionSign (σ.val.colors.erase i) i •
          symbolTerm X q (insert v i (erase σ.val i))) = _
      rw [sign_erase _ i i hi]
      simp only [lt_self_iff_false, ↓reduceIte, smul_smul, sign_sq, one_smul]
      rw [insert_erase v σ.val i hi]
    · have hm : i ∈ (erase σ.val j).colors := Finset.mem_erase.mpr ⟨Ne.symm hji, hi⟩
      simp [hm, hji]
  simp_rw [Finset.sum_congr rfl hterm]
  simp [hi]

private theorem insertion_boundary_missing {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (q : ℤ) (σ : Symbol X q) (i : Fin r) (hi : i ∉ σ.val.colors) :
    boundary X (q + 1) q (insertion v i q (q + 1) (Finsupp.single σ 1)) +
      insertion v i (q - 1) q (boundary X q (q - 1) (Finsupp.single σ 1)) =
        Finsupp.single σ 1 := by
  classical
  have hins : ((insert v i σ.val).colors.card : ℤ) = (q + 1) + 1 :=
    insert_card v σ.val σ.property i hi
  have hb : boundary X (q + 1) q
      (insertion v i q (q + 1) (Finsupp.single σ 1)) =
      Finsupp.single σ 1 + ∑ j ∈ σ.val.colors,
        (positionSign σ.val.colors i * positionSign (Insert.insert i σ.val.colors) j) •
          symbolTerm X q (insert v i (erase σ.val j)) := by
    simp only [insertion, Finsupp.linearCombination_single, one_smul, if_neg hi,
      map_smul]
    rw [boundary_term _ _ _ hins]
    change positionSign σ.val.colors i •
      (∑ j ∈ Insert.insert i σ.val.colors,
        positionSign (Insert.insert i σ.val.colors) j •
          symbolTerm X q (erase (insert v i σ.val) j)) = _
    rw [Finset.sum_insert hi, smul_add, smul_smul, sign_insert _ i i hi]
    simp only [lt_self_iff_false, ↓reduceIte, sign_sq, one_smul]
    rw [erase_insert_self v σ.val i hi, term_eq q σ.val σ.property]
    congr 1
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_smul, erase_insert_other v σ.val i j (by
      intro he
      exact hi (he ▸ hj))]
  have hc : insertion v i (q - 1) q
      (boundary X q (q - 1) (Finsupp.single σ 1)) =
      ∑ j ∈ σ.val.colors,
        (positionSign σ.val.colors j * positionSign (σ.val.colors.erase j) i) •
          symbolTerm X q (insert v i (erase σ.val j)) := by
    rw [boundary_single, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_smul, insertion_term v i _ _ _ (erase_card σ.val σ.property j hj)]
    have hm : i ∉ (erase σ.val j).colors := fun hm ↦ hi (Finset.mem_of_mem_erase hm)
    simp only [if_neg hm, smul_smul]
    rfl
  rw [hb, hc, add_assoc]
  suffices hs : (∑ j ∈ σ.val.colors,
      (positionSign σ.val.colors i * positionSign (Insert.insert i σ.val.colors) j) •
        symbolTerm X q (insert v i (erase σ.val j))) +
      (∑ j ∈ σ.val.colors,
      (positionSign σ.val.colors j * positionSign (σ.val.colors.erase j) i) •
        symbolTerm X q (insert v i (erase σ.val j))) = 0 by rw [hs, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  rw [← add_smul]
  have hji : j ≠ i := fun he ↦ hi (he ▸ hj)
  have hs : positionSign σ.val.colors i * positionSign (Insert.insert i σ.val.colors) j +
      positionSign σ.val.colors j * positionSign (σ.val.colors.erase j) i = 0 := by
    rw [sign_insert _ i j hi, sign_erase _ j i hj]
    rcases lt_or_gt_of_ne hji with hlt | hlt
    · simp [hlt, not_lt_of_gt hlt, mul_comm]
    · simp [hlt, not_lt_of_gt hlt, mul_comm]
  rw [hs, zero_smul]

/-- Alternating deletion squares to zero, and signed insertion of one chosen vertex
is a homotopy from its remainder map to the identity, in every integer degree.

Source: six-functors direct-images proof, paragraph (3), agent-written ordered-join
expansion, calculations 1-4; these calculations are not asserted in the blueprint
(blueprint: lem-sfb-ordered-join-single-color-identities).

Proof:
1. By def-weil-pbc-free-module, use the specified integer basis of each `Chain X q`.
   Each deletion, insertion, and replacement has finite output, so the formulas extend
   linearly, and equality of maps can be checked on individual symbols.
2. For original positions a<b, the two orders of deletion have signs (-1)^(a+b-1)
   and (-1)^(a+b). Pair these equal output symbols to obtain d squared zero, including
   degree 1, where the output is empty. In degrees 0 and -1 the composite contains
   the zero boundary from the empty face; outside the permitted range its source is zero.
3. If color i is missing, let k count the earlier colors. Deleting the inserted vertex
   from dc_i contributes the original symbol with sign (-1)^(2k)=1. For a<k the
   remaining coefficients are (-1)^(k+a) and (-1)^(a+k-1); for a>=k they are
   (-1)^(k+a+1) and (-1)^(a+k). Each pair cancels between dc_i and c_i d.
   The result is the original symbol, and R_i is zero on it.
4. If color i is present at position k, insertion is zero. Only deleting that vertex
   permits reinsertion in c_i d. Its two signs multiply to 1, leaving T_i of the
   original symbol, which is the original symbol minus R_i of it. This also applies
   when its original vertex already equals the chosen vertex.
5. On the empty face, insertion gives the chosen singleton, whose boundary is the
   empty face, while R_i and the other composite vanish. At top degree every color
   is present and the insertion into degree r is zero, so step 4 applies. Outside
   degrees -1 through r-1 there are no symbols. For r=1 only the empty and singleton
   calculations remain. Extend both equalities to all chains by integer linearity. -/
theorem singleColorIdentities (r : ℕ) (hr : 1 ≤ r) (X : Fin r → Type u)
    (v : ∀ i : Fin r, X i) :
    (∀ q : ℤ, (boundary X (q - 1) (q - 2)).comp (boundary X q (q - 1)) = 0) ∧
    (∀ (q : ℤ) (i : Fin r),
      (boundary X (q + 1) q).comp (insertion v i q (q + 1)) +
        (insertion v i (q - 1) q).comp (boundary X q (q - 1)) =
          LinearMap.id - remainder v i q) := by
  classical
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  constructor
  · exact boundary_boundary X
  · intro q i
    apply basis_ext
    intro σ
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply]
    by_cases hi : i ∈ σ.val.colors
    · have hz : insertion v i q (q + 1) (Finsupp.single σ 1) = 0 := by
        simp [insertion, hi]
      rw [hz, map_zero, zero_add, insertion_boundary_present v q σ i hi]
      simp [remainder, hi, term_eq q σ.val σ.property]
    · rw [insertion_boundary_missing v q σ i hi]
      simp [remainder, hi]

end AlgebraicTopology.OrderedJoin
