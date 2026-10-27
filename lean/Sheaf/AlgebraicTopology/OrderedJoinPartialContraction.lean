/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP, SHEAF group V3
-/
module

public import Sheaf.AlgebraicTopology.OrderedJoinChains
import Sheaf.AlgebraicTopology.OrderedJoinSingleColorIdentities
import Sheaf.AlgebraicTopology.OrderedJoinFunctorialExpansion
import Mathlib.Tactic.Abel

/-! # Partial contraction of ordered join chains

The constructions are in `OrderedJoinChains`, allowing the single-color and
functorial-expansion prerequisites to be imported without a cycle.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace AlgebraicTopology.OrderedJoin

private theorem prefix_list_comp {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (q : ℤ) (L : List ℕ) (P : Chain X q →ₗ[ℤ] Chain X q) :
    L.foldr (fun j Q ↦ if h : j < r then (remainder v ⟨j, h⟩ q).comp Q else Q) P =
      (L.foldr (fun j Q ↦
        if h : j < r then (remainder v ⟨j, h⟩ q).comp Q else Q) LinearMap.id).comp P := by
  induction L with
  | nil => simp
  | cons j L ih =>
    simp only [List.foldr_cons]
    split_ifs with h
    · rw [ih, LinearMap.comp_assoc]
    · exact ih

private theorem prefix_succ {r : ℕ} {X : Fin r → Type u} (v : ∀ i, X i)
    (n : ℕ) (hn : n < r) (q : ℤ) :
    remainderPrefix v (n + 1) q =
      (remainderPrefix v n q).comp (remainder v ⟨n, hn⟩ q) := by
  simp only [remainderPrefix, List.range_succ, List.foldr_append,
    List.foldr_cons, List.foldr_nil, dif_pos hn, LinearMap.comp_id]
  exact prefix_list_comp v q (List.range n) _

private theorem remainder_commutes {r : ℕ} (hr : 1 ≤ r) {X : Fin r → Type u}
    (v : ∀ i, X i) (q : ℤ) (i : Fin r) :
    (boundary X q (q - 1)).comp (remainder v i q) =
      (remainder v i (q - 1)).comp (boundary X q (q - 1)) := by
  obtain ⟨hdd, hc⟩ := singleColorIdentities r hr X v
  have hR (p : ℤ) : remainder v i p = LinearMap.id -
      ((boundary X (p + 1) p).comp (insertion v i p (p + 1)) +
        (insertion v i (p - 1) p).comp (boundary X p (p - 1))) := by
    rw [hc p i]
    abel
  have hd' := hdd (q + 1)
  have he : q + 1 - 2 = q - 1 := by omega
  have he0 : q + 1 - 1 = q := by omega
  rw [he, he0] at hd'
  rw [hR q, hR (q - 1)]
  simp only [LinearMap.comp_sub, LinearMap.comp_add,
    LinearMap.sub_comp, LinearMap.add_comp, LinearMap.id_comp, LinearMap.comp_id]
  have heq : q - 1 + 1 = q := by omega
  rw [heq]
  rw [← LinearMap.comp_assoc, hd', LinearMap.zero_comp]
  have he' : q - 1 - 1 = q - 2 := by omega
  rw [he']
  simp only [LinearMap.comp_assoc, hdd q, LinearMap.comp_zero, zero_add, add_zero]

private theorem prefix_commutes {r : ℕ} (hr : 1 ≤ r) {X : Fin r → Type u}
    (v : ∀ i, X i) (n : ℕ) (hn : n ≤ r) (q : ℤ) :
    (boundary X q (q - 1)).comp (remainderPrefix v n q) =
      (remainderPrefix v n (q - 1)).comp (boundary X q (q - 1)) := by
  induction n with
  | zero => simp [remainderPrefix]
  | succ n ih =>
    have hn' : n < r := by omega
    rw [prefix_succ v n hn' q, prefix_succ v n hn' (q - 1),
      ← LinearMap.comp_assoc, ih (by omega), LinearMap.comp_assoc,
      remainder_commutes hr v q ⟨n, hn'⟩, ← LinearMap.comp_assoc]

private theorem contraction_telescope {r : ℕ} (hr : 1 ≤ r) {X : Fin r → Type u}
    (v : ∀ i, X i) (q : ℤ) :
    (boundary X (q + 1) q).comp (contraction v q (q + 1)) +
      (contraction v (q - 1) q).comp (boundary X q (q - 1)) =
        LinearMap.id - remainderPrefix v r q := by
  have hp (i : Fin r) :
      (boundary X (q + 1) q).comp
          ((remainderPrefix v i.val (q + 1)).comp (insertion v i q (q + 1))) +
        ((remainderPrefix v i.val q).comp (insertion v i (q - 1) q)).comp
          (boundary X q (q - 1)) =
        remainderPrefix v i.val q - remainderPrefix v (i.val + 1) q := by
    have hd := prefix_commutes hr v i.val (Nat.le_of_lt i.isLt) (q + 1)
    have heq : q + 1 - 1 = q := by omega
    rw [heq] at hd
    rw [← LinearMap.comp_assoc, hd, LinearMap.comp_assoc,
      LinearMap.comp_assoc, ← LinearMap.comp_add,
      (singleColorIdentities r hr X v).2 q i,
      LinearMap.comp_sub, LinearMap.comp_id, prefix_succ v i.val i.isLt q]
  have hsum : (∑ i : Fin r,
      (remainderPrefix v i.val q - remainderPrefix v (i.val + 1) q)) =
        LinearMap.id - remainderPrefix v r q := by
    rw [← Finset.sum_range (fun n ↦
      remainderPrefix v n q - remainderPrefix v (n + 1) q), Finset.sum_range_sub']
    simp [remainderPrefix]
  rw [← hsum]
  apply LinearMap.ext
  intro x
  simpa only [contraction, LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    LinearMap.add_apply, ← Finset.sum_add_distrib] using
      Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ ↦ LinearMap.congr_fun (hp i) x)

private theorem remainder_symbolTerm {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (i : Fin r) (q : ℤ) (σ : Face X) :
    remainder v i q (symbolTerm X q σ) =
      if i ∈ σ.colors then symbolTerm X q σ - symbolTerm X q (replaceColors v {i} σ)
      else 0 := by
  classical
  by_cases h : (σ.colors.card : ℤ) = q + 1
  · simp [symbolTerm, remainder, h, replaceColors, Finsupp.linearCombination_single]
  · simp [symbolTerm, h, replaceColors]

private theorem prefix_missing {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (q : ℤ) (n : ℕ) (hn : n ≤ r)
    (σ : Face X) (j : Fin r) (hj : j.val < n) (hm : j ∉ σ.colors) :
    remainderPrefix v n q (symbolTerm X q σ) = 0 := by
  classical
  induction n generalizing σ with
  | zero => omega
  | succ n ih =>
    have hn' : n < r := by omega
    rw [prefix_succ v n hn' q, LinearMap.comp_apply, remainder_symbolTerm]
    split_ifs with hi
    · have hj' : j.val < n := by
        have hne : j.val ≠ n := by
          intro he
          have hje : j = ⟨n, hn'⟩ := Fin.ext he
          exact hm (hje ▸ hi)
        omega
      rw [map_sub, ih (by omega) σ hj' hm,
        ih (by omega) (replaceColors v {⟨n, hn'⟩} σ) hj' hm, sub_self]
    · exact map_zero _

private theorem prefix_zero {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (q : ℤ) (hq : q ≤ (r : ℤ) - 2) :
    remainderPrefix v r q = 0 := by
  classical
  apply Finsupp.lhom_ext
  intro σ z
  have hproper : σ.val.colors ≠ Finset.univ := by
    intro he
    have hh := σ.property
    rw [he, Finset.card_univ, Fintype.card_fin] at hh
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin r, j ∉ σ.val.colors := by
    by_contra! hall
    exact hproper (Finset.eq_univ_of_forall hall)
  have hz : Finsupp.single σ z = z • symbolTerm X q σ.val := by
    simp [symbolTerm, σ.property]
  rw [hz, map_smul, prefix_missing v q r le_rfl σ.val j j.isLt hj, smul_zero]
  rfl

private theorem contraction_minus_two {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) : contraction v (-2) (-1) = 0 := by
  apply Finsupp.lhom_ext
  intro σ z
  have hh := σ.property
  have hc := σ.val.colors.card
  omega

private theorem prefix_natural {r : ℕ} (hr : 1 ≤ r) {X : Fin r → Type u}
    (v : ∀ i, X i) (Y : Fin r → Type v) (f : ∀ i, X i → Y i)
    (n : ℕ) (hn : n ≤ r) (q : ℤ) :
    (chainMap f q).comp (remainderPrefix v n q) =
      (remainderPrefix (fun i ↦ f i (v i)) n q).comp (chainMap f q) := by
  induction n with
  | zero => simp [remainderPrefix]
  | succ n ih =>
    have hn' : n < r := by omega
    rw [prefix_succ v n hn' q, prefix_succ (fun i ↦ f i (v i)) n hn' q,
      ← LinearMap.comp_assoc, ih (by omega), LinearMap.comp_assoc,
      (functorialExpansion r hr X v).1 Y f q ⟨n, hn'⟩ |>.2,
      ← LinearMap.comp_assoc]

private theorem contraction_natural {r : ℕ} (hr : 1 ≤ r) {X : Fin r → Type u}
    (v : ∀ i, X i) (Y : Fin r → Type v) (f : ∀ i, X i → Y i) (q : ℤ) :
    (chainMap f (q + 1)).comp (contraction v q (q + 1)) =
      (contraction (fun i ↦ f i (v i)) q (q + 1)).comp (chainMap f q) := by
  apply LinearMap.ext
  intro x
  simp only [contraction, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((chainMap f (q + 1)).comp
    ((remainderPrefix v i.val (q + 1)).comp (insertion v i q (q + 1)))) x =
    (((remainderPrefix (fun i ↦ f i (v i)) i.val (q + 1)).comp
      (insertion (fun i ↦ f i (v i)) i q (q + 1))).comp (chainMap f q)) x
  rw [← LinearMap.comp_assoc, prefix_natural hr v Y f i.val (Nat.le_of_lt i.isLt),
    LinearMap.comp_assoc, (functorialExpansion r hr X v).1 Y f q i |>.1,
    ← LinearMap.comp_assoc]

private theorem replace_insert {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (A : Finset (Fin r)) (i : Fin r) (σ : Face X) :
    replaceColors v A (insert v i σ) = insert v i (replaceColors v A σ) := by
  unfold replaceColors insert
  congr 1
  funext j hj
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

private theorem sum_flatMap {α M : Type*} [AddCommMonoid M]
    (L : List α) (f : α → List M) :
    (L.flatMap f).sum = (L.map (fun a ↦ (f a).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

private theorem contraction_expansion {r : ℕ} (hr : 1 ≤ r) {X : Fin r → Type u}
    (v : ∀ i, X i) (q : ℤ) (σ : Symbol X q) :
    contraction v q (q + 1) (Finsupp.single σ 1) =
      ((expansionRecipe r σ.val.colors).map (fun t ↦
        t.1 • symbolTerm X (q + 1) (insert v t.2.1 (replaceColors v t.2.2 σ.val)))).sum := by
  classical
  simp only [contraction, LinearMap.sum_apply, LinearMap.comp_apply,
    expansionRecipe, List.map_flatMap, sum_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  have hi := (functorialExpansion.{u, u} r hr X v).2.1 q σ i
  by_cases hm : i ∈ σ.val.colors
  · simp [hm, hi.1 (Or.inl hm)]
  · simp only [hm, if_false]
    by_cases hall : (Finset.univ.filter (fun j : Fin r ↦ j < i)) ⊆ σ.val.colors
    · simp only [hall, if_true]
      have ha : ∀ j : Fin r, j < i → j ∈ σ.val.colors := by
        intro j hj
        exact hall (by simp [hj])
      rw [hi.2 hm ha]
      simp only [summandRecipe, List.map_map]
      apply congrArg List.sum
      apply congrArg (fun f ↦ List.map f
        (Finset.univ.filter (fun j : Fin r ↦ j < i)).powerset.toList)
      funext A
      simp [positionSign, pow_add, replace_insert]
    · have hex : ∃ j : Fin r, j < i ∧ j ∉ σ.val.colors := by
        obtain ⟨j, hj, hnot⟩ := Finset.not_subset.mp hall
        exact ⟨j, (Finset.mem_filter.mp hj).2, hnot⟩
      simp [hall, hi.1 (Or.inr hex)]

/-- The boundary squares to zero, S contracts all degrees below the top,
is natural for arbitrary maps of pointed families, and has the finite
color-dependent expansion specified by `expansionRecipe`.

Source: direct-images paragraph (3), agent ordered-join expansion, calculations
1-8; this is not asserted in the blueprint itself
(blueprint: lem-sfb-ordered-join-partial-contraction).

Proof:
1. Extend each basis formula by finite integer linear combination, using
   def-weil-pbc-free-module. Equality of maps is checked on these bases.
2. In d squared, deleting original positions a<b in the two possible orders
   gives signs (-1)^(a+b-1) and (-1)^(a+b), which cancel. In degrees 0 and -1
   the second boundary is zero. The same holds on all zero chain groups.
3. For a symbol missing color i, let k count its colors less than i. Deleting
   the inserted vertex from dc_i has sign (-1)^(2k)=1. Deletions of original
   vertices cancel with c_i d: for a<k the signs are (-1)^(k+a) and
   (-1)^(a+k-1), and for a>=k they are (-1)^(k+a+1) and (-1)^(a+k).
   Thus dc_i+c_i d=1-R_i, including the empty symbol.
4. For a symbol containing color i in position k, c_i is zero; only the k-th
   face can contribute to c_i d, giving the chosen replacement with sign
   (-1)^(2k)=1. Again dc_i+c_i d=1-R_i, including the top degree.
5. Using d squared zero, deduce dR_i=R_i d. The ordered prefixes P_i commute
   with d, so dS+Sd=sum_i P_i(1-R_i)=sum_i(P_i-P_{i+1})=1-P_r.
6. In degrees -1 through r-2 every symbol misses some color j. Replacement
   preserves the color set, so the factor R_j kills all terms reaching it in
   P_r. Therefore P_r=0. On the empty face only i=0 survives, giving
   S_{-1}[empty]=[(0,v_0)] and dS_{-1}=1; the degree -2 group is zero.
7. Applying f preserves colors, insertion positions, chosen insertions, and
   replacements. It commutes with every c_i and R_i, hence with S. Coincident
   output symbols may cancel, so injectivity of the vertex maps is unnecessary.
8. The i-th summand vanishes if i is present or some predecessor is missing.
   Otherwise distribute the factors R_j=1-T_j for j<i. Each subset A records
   the negative replacement choices, with coefficient
   (-1)^position(i) times (-1)^card(A). These are exactly `expansionRecipe`;
   coincident symbols are left uncollected and no equality of vertices is tested. -/
theorem partialContraction (r : ℕ) (hr : 1 ≤ r) (X : Fin r → Type u)
    (v : ∀ i : Fin r, X i) :
    (∀ q : ℤ, (boundary X (q - 1) (q - 2)).comp (boundary X q (q - 1)) = 0) ∧
    (∀ q : ℤ, -1 ≤ q → q ≤ (r : ℤ) - 2 →
      (boundary X (q + 1) q).comp (contraction v q (q + 1)) +
        (contraction v (q - 1) q).comp (boundary X q (q - 1)) = LinearMap.id) ∧
    contraction v (-2) (-1) = 0 ∧
    (∀ (Y : Fin r → Type v) (f : ∀ i : Fin r, X i → Y i) (q : ℤ),
      (chainMap f (q + 1)).comp (contraction v q (q + 1)) =
        (contraction (fun i ↦ f i (v i)) q (q + 1)).comp (chainMap f q)) ∧
    (∀ (q : ℤ) (σ : Symbol X q),
      contraction v q (q + 1) (Finsupp.single σ 1) =
        ((expansionRecipe r σ.val.colors).map (fun t ↦
          t.1 • symbolTerm X (q + 1) (insert v t.2.1 (replaceColors v t.2.2 σ.val)))).sum) := by
  refine ⟨(singleColorIdentities r hr X v).1, ?_, contraction_minus_two v,
    contraction_natural hr v, contraction_expansion hr v⟩
  intro q _ hq
  rw [contraction_telescope hr v q, prefix_zero v q hq, sub_zero]

end AlgebraicTopology.OrderedJoin
