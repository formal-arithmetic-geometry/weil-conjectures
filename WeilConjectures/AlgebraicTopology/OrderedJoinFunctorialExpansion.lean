/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicTopology.OrderedJoinChains
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Order.Interval.Finset.Fin

/-! # Naturality and individual subset expansions for ordered joins

Source: blueprint/latest, six-functors direct-images proof, paragraph (3), agent
ordered-join expansion, original calculations 7-8. This calculation is an agent
expansion below the continuous-cocycle descent route, not a blueprint assertion
(blueprint: lem-sfb-ordered-join-functorial-expansion).

We reuse the existing ordered-join constructions, not the theorem
`partialContraction`. Their specified integer basis is `Finsupp.basisSingleOne`,
in the sense of `def-weil-pbc-free-module`. Faces encode increasing-color symbols;
the cardinality condition in `Symbol` covers every integer degree.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicTopology.OrderedJoin

open scoped BigOperators

private theorem face_ext {r : ℕ} {X : Fin r → Type u} {σ τ : Face X}
    (hc : σ.colors = τ.colors)
    (hv : ∀ i hi, σ.vertex i hi = τ.vertex i (hc ▸ hi)) : σ = τ := by
  cases σ with | mk C x =>
    cases τ with | mk D y =>
      dsimp at hc
      subst D
      congr
      funext i hi
      exact hv i hi

private theorem replace_empty {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (σ : Face X) : replaceColors v ∅ σ = σ := by
  refine face_ext (σ := replaceColors v ∅ σ) (τ := σ) rfl ?_
  simp [replaceColors]

private theorem replace_replace {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (A B : Finset (Fin r)) (σ : Face X) :
    replaceColors v A (replaceColors v B σ) = replaceColors v (A ∪ B) σ := by
  refine face_ext (σ := replaceColors v A (replaceColors v B σ))
    (τ := replaceColors v (A ∪ B) σ) rfl ?_
  intro i hi
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [replaceColors, ha, hb]

private theorem map_replace {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i, X i → Y i) (v : ∀ i, X i) (A : Finset (Fin r)) (σ : Face X) :
    mapFace f (replaceColors v A σ) =
      replaceColors (fun i ↦ f i (v i)) A (mapFace f σ) := by
  refine face_ext (σ := mapFace f (replaceColors v A σ))
    (τ := replaceColors (fun i ↦ f i (v i)) A (mapFace f σ)) rfl ?_
  intro i hi
  by_cases h : i ∈ A <;> simp [mapFace, replaceColors, h]

private theorem map_insert {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i, X i → Y i) (v : ∀ i, X i) (i : Fin r) (σ : Face X) :
    mapFace f (insert v i σ) = insert (fun j ↦ f j (v j)) i (mapFace f σ) := by
  refine face_ext (σ := mapFace f (insert v i σ))
    (τ := insert (fun j ↦ f j (v j)) i (mapFace f σ)) rfl ?_
  intro j hj
  by_cases h : j = i
  · subst j
    simp [mapFace, insert]
  · simp [mapFace, insert, h]

private theorem chainMap_term {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i, X i → Y i) (q : ℤ) (σ : Face X) :
    chainMap f q (symbolTerm X q σ) = symbolTerm Y q (mapFace f σ) := by
  classical
  by_cases h : (σ.colors.card : ℤ) = q + 1
  · simp [symbolTerm, h, chainMap, Finsupp.linearCombination_single]
  · simp [symbolTerm, mapFace, h]

private theorem remainder_term {r : ℕ} {X : Fin r → Type u}
    (v : ∀ i, X i) (i : Fin r) (q : ℤ) (σ : Face X) :
    remainder v i q (symbolTerm X q σ) =
      if i ∈ σ.colors then symbolTerm X q σ -
        symbolTerm X q (replaceColors v {i} σ) else 0 := by
  classical
  by_cases h : (σ.colors.card : ℤ) = q + 1
  · simp [symbolTerm, h, remainder, Finsupp.linearCombination_single]
  · simp [symbolTerm, replaceColors, h]

private theorem insertion_natural {r : ℕ} {X : Fin r → Type u}
    {Y : Fin r → Type v} (f : ∀ i, X i → Y i) (v : ∀ i, X i)
    (i : Fin r) (q p : ℤ) :
    (chainMap f p).comp (insertion v i q p) =
      (insertion (fun j ↦ f j (v j)) i q p).comp (chainMap f q) := by
  classical
  apply Finsupp.lhom_ext
  intro σ z
  let τ : Symbol Y q := ⟨mapFace f σ.val, σ.property⟩
  have ht : symbolTerm Y q (mapFace f σ.val) = Finsupp.single τ 1 := by
    simp [symbolTerm, τ, show ((mapFace f σ.val).colors.card : ℤ) = q + 1
      from σ.property]
  have hs : chainMap f q (Finsupp.single σ z) = z • Finsupp.single τ 1 := by
    simp only [chainMap, Finsupp.linearCombination_single]
    rw [ht]
  simp only [LinearMap.comp_apply, hs, map_smul]
  simp only [insertion, Finsupp.linearCombination_single, one_smul]
  change chainMap f p (z • (if i ∈ σ.val.colors then 0 else
      positionSign σ.val.colors i • symbolTerm X p (insert v i σ.val))) =
    z • (if i ∈ σ.val.colors then 0 else positionSign σ.val.colors i •
      symbolTerm Y p (insert (fun j ↦ f j (v j)) i (mapFace f σ.val)))
  by_cases hi : i ∈ σ.val.colors <;>
    simp only [hi, if_pos, if_false, map_smul, map_zero, chainMap_term, map_insert]

private theorem remainder_natural {r : ℕ} {X : Fin r → Type u}
    {Y : Fin r → Type v} (f : ∀ i, X i → Y i) (v : ∀ i, X i)
    (i : Fin r) (q : ℤ) :
    (chainMap f q).comp (remainder v i q) =
      (remainder (fun j ↦ f j (v j)) i q).comp (chainMap f q) := by
  classical
  apply Finsupp.lhom_ext
  intro σ z
  simp only [LinearMap.comp_apply, remainder, chainMap,
    Finsupp.linearCombination_single, map_smul]
  change z • chainMap f q
    (if i ∈ σ.val.colors then symbolTerm X q σ.val -
      symbolTerm X q (replaceColors v {i} σ.val) else 0) =
    z • remainder (fun j ↦ f j (v j)) i q (symbolTerm Y q (mapFace f σ.val))
  rw [remainder_term]
  by_cases hi : i ∈ σ.val.colors <;>
    simp only [show (mapFace f σ.val).colors = σ.val.colors from rfl, hi,
      if_pos, if_false, map_sub, map_zero, chainMap_term, map_replace]

private theorem prefix_succ {r : ℕ} {X : Fin r → Type u} (v : ∀ i, X i)
    (n : ℕ) (hn : n < r) (q : ℤ) :
    remainderPrefix v (n + 1) q =
      (remainderPrefix v n q).comp (remainder v ⟨n, hn⟩ q) := by
  unfold remainderPrefix
  rw [List.range_succ, List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil, dif_pos hn, LinearMap.comp_id]
  generalize List.range n = l
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons]
    split <;> simp_all [LinearMap.comp_assoc]

private theorem prefix_missing {r : ℕ} {X : Fin r → Type u} (v : ∀ i, X i)
    (q : ℤ) (n : ℕ) (hn : n ≤ r) (σ : Face X) (j : Fin r)
    (hj : j.val < n) (hm : j ∉ σ.colors) :
    remainderPrefix v n q (symbolTerm X q σ) = 0 := by
  induction n generalizing σ with
  | zero => omega
  | succ n ih =>
    have hnr : n < r := by omega
    rw [prefix_succ v n hnr, LinearMap.comp_apply, remainder_term]
    by_cases hjn : j.val < n
    · split
      · rw [map_sub, ih (by omega) σ hjn hm,
          ih (by omega) (replaceColors v {⟨n, hnr⟩} σ) hjn hm, sub_self]
      · exact map_zero _
    · have he : j = ⟨n, hnr⟩ := by
        apply Fin.ext
        change j.val = n
        omega
      subst j
      rw [if_neg hm, map_zero]

private theorem lower_succ {r n : ℕ} (hn : n < r) :
    (Finset.univ.filter (fun j : Fin r ↦ j.val < n + 1)) =
      Insert.insert ⟨n, hn⟩ (Finset.univ.filter (fun j : Fin r ↦ j.val < n)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    by_cases he : j.val = n
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (by omega)
  · rintro (rfl | h)
    · exact Nat.lt_succ_self n
    · omega

private theorem prefix_expansion {r : ℕ} {X : Fin r → Type u} (v : ∀ i, X i)
    (q : ℤ) (n : ℕ) (hn : n ≤ r) (σ : Face X)
    (hc : ∀ j : Fin r, j.val < n → j ∈ σ.colors) :
    remainderPrefix v n q (symbolTerm X q σ) =
      ∑ A ∈ (Finset.univ.filter (fun j : Fin r ↦ j.val < n)).powerset,
        (-1 : ℤ) ^ A.card • symbolTerm X q (replaceColors v A σ) := by
  classical
  induction n generalizing σ with
  | zero => simp [remainderPrefix, replace_empty]
  | succ n ih =>
    have hnr : n < r := by omega
    let k : Fin r := ⟨n, hnr⟩
    have hk : k ∈ σ.colors := hc k (by dsimp [k]; omega)
    have hlow : ∀ j : Fin r, j.val < n → j ∈ σ.colors :=
      fun j hj ↦ hc j (by omega)
    rw [prefix_succ v n hnr, LinearMap.comp_apply, remainder_term, if_pos hk,
      map_sub, ih (by omega) σ hlow,
      ih (by omega) (replaceColors v {k} σ) hlow, lower_succ hnr]
    have hnot : k ∉ Finset.univ.filter (fun j : Fin r ↦ j.val < n) := by
      simp [k]
    rw [Finset.sum_powerset_insert hnot]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro A hA
    have hka : k ∉ A := fun ha ↦ hnot ((Finset.mem_powerset.mp hA) ha)
    simp [Finset.card_insert_of_notMem hka, pow_succ, replace_replace,
      Finset.union_singleton]

/-- The unreduced subset list for the individual i-th summand. Every subset of
colors less than i occurs once, with its coefficient, insertion color and
replacement set. This recipe depends only on colors; in particular it cannot
test equality of vertices, and does not collect terms that evaluate equally.
It is used only when i is missing and all its predecessors occur in C.

Source: direct-images paragraph (3), agent ordered-join expansion, calculation 8
(blueprint: lem-sfb-ordered-join-functorial-expansion). -/
noncomputable def summandRecipe (r : ℕ) (C : Finset (Fin r)) (i : Fin r) :
    List (ℤ × (Fin r × Finset (Fin r))) :=
  ((Finset.univ.filter (fun j : Fin r ↦ j < i)).powerset.toList).map
    (fun A ↦ ((-1 : ℤ) ^ ((C.filter (fun j ↦ j < i)).card + A.card), (i, A)))

/-- In every integer degree, arbitrary vertex maps commute with each signed
insertion and each remainder. The summand P_i c_i vanishes on a symbol if i is
present or an earlier color is missing. Otherwise it is the sum of the
unreduced subset list `summandRecipe`, which has exactly 2^i terms. Evaluation
inserts the chosen i-vertex and replaces precisely the chosen subset of earlier
vertices. Equal evaluated symbols remain separate entries of the list.

Source: direct-images paragraph (3), agent ordered-join expansion, original
calculations 7-8; not asserted in the blueprint itself
(blueprint: lem-sfb-ordered-join-functorial-expansion).

Proof:
1. By def-weil-pbc-free-module, extend the finite formulas from the specified
   basis by integer linearity; check equality of maps on basis vectors.
2. Applying f preserves colors and their order. On a symbol containing i both
   insertion expressions vanish. Otherwise both insert f_i(v_i) at the same
   position with the same sign. Thus J(f)c_i^v=c_i^(f(v))J(f), without injectivity.
3. On a missing-color symbol both remainder expressions vanish. Otherwise
   f commutes with replacement by v_i, so both expressions are J(f)sigma minus
   its chosen replacement, even if those two terms coincide and cancel.
4. If i is present the insertion is zero. If a predecessor j is absent, every
   factor acting before R_j preserves the color set, and R_j kills every term.
   The remaining factors preserve zero. This respects the rightmost-first order.
5. Otherwise put tau=insert_i(sigma) and Q_m=R_m composed with ... with R_(i-1).
   Descend from m=i, where Q_i is the identity. If Q_(m+1)tau is the signed
   subset sum on {m+1,...,i-1}, R_m sends tau_A to tau_A-tau_(A union {m}).
   The two branches partition the subsets on {m,...,i-1}, with their signs.
   At m=0 multiply by the insertion sign, obtaining (-1)^(k_i+card A).
6. Keep every branch as a list entry; the powerset has 2^i elements because
   exactly i colors precede i. No vertex equality is tested. For the empty
   symbol only i=0 survives; a top-degree symbol contains every i and all
   insertions vanish. Every excluded degree has no symbols and zero chains. -/
theorem functorialExpansion (r : ℕ) (hr : 1 ≤ r) (X : Fin r → Type u)
    (v : ∀ i : Fin r, X i) :
    (∀ (Y : Fin r → Type v) (f : ∀ i : Fin r, X i → Y i) (q : ℤ) (i : Fin r),
      (chainMap f (q + 1)).comp (insertion v i q (q + 1)) =
        (insertion (fun j ↦ f j (v j)) i q (q + 1)).comp (chainMap f q) ∧
      (chainMap f q).comp (remainder v i q) =
        (remainder (fun j ↦ f j (v j)) i q).comp (chainMap f q)) ∧
    (∀ (q : ℤ) (σ : Symbol X q) (i : Fin r),
      ((i ∈ σ.val.colors ∨ ∃ j : Fin r, j < i ∧ j ∉ σ.val.colors) →
        (remainderPrefix v i.val (q + 1))
          (insertion v i q (q + 1) (Finsupp.single σ 1)) = 0) ∧
      (i ∉ σ.val.colors → (∀ j : Fin r, j < i → j ∈ σ.val.colors) →
        (remainderPrefix v i.val (q + 1))
          (insertion v i q (q + 1) (Finsupp.single σ 1)) =
            ((summandRecipe r σ.val.colors i).map (fun t ↦
              t.1 • symbolTerm X (q + 1)
                (replaceColors v t.2.2 (insert v t.2.1 σ.val)))).sum)) ∧
    (∀ (C : Finset (Fin r)) (i : Fin r), (summandRecipe r C i).length = 2 ^ i.val) := by
  classical
  have _hr := hr
  refine ⟨?_, ?_, ?_⟩
  · intro Y f q i
    exact ⟨insertion_natural f v i q (q + 1), remainder_natural f v i q⟩
  · intro q σ i
    constructor
    · rintro (hi | ⟨j, hji, hj⟩)
      · simp [insertion, hi]
      · by_cases hi : i ∈ σ.val.colors
        · simp [insertion, hi]
        · simp only [insertion, Finsupp.linearCombination_single, one_smul, if_neg hi,
            map_smul]
          rw [prefix_missing v (q + 1) i.val (by omega) (insert v i σ.val) j hji]
          · exact smul_zero _
          · simp only [insert, Finset.mem_insert, not_or]
            exact ⟨ne_of_lt hji, hj⟩
    · intro hi hc
      simp only [insertion, Finsupp.linearCombination_single, one_smul, if_neg hi,
        map_smul]
      rw [prefix_expansion v (q + 1) i.val (by omega) (insert v i σ.val)]
      · simp only [summandRecipe, List.map_map, Function.comp_apply,
          Finset.sum_map_toList, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        simp only [positionSign, pow_add, mul_smul]
      · intro j hj
        exact Finset.mem_insert_of_mem (hc j hj)
  · intro C i
    have hset : Finset.univ.filter (fun j : Fin r ↦ j < i) = Finset.Iio i := by
      ext j
      simp
    simp [summandRecipe, hset]

end AlgebraicTopology.OrderedJoin
