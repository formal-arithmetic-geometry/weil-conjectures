/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Sheaf.AlgebraicTopology.OrderedJoinPartialContraction
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Sheaf.AlgebraicTopology.OrderedJoinCosetChains
import Sheaf.AlgebraicTopology.OrderedJoinCosetRecursion
import Sheaf.AlgebraicTopology.OrderedJoinCosetErasureBoundary
import Mathlib.Data.List.InsertIdx

/-! # Uniform equivariant ordered-coset join comparison

Source: six-functors direct-images proof, paragraph (3), agent arithmetic expansion
below local continuous-cocycle descent, calculations 1–7. The current blueprint
paragraph motivates the application but does not assert this arithmetic lemma.
(blueprint: lem-sfb-ordered-join-coset-comparison).

The recursive comparison is indexed by arity: arity k means degree k-1. This
includes the empty tuple at arity zero. Integer-indexed tuple groups also give
zero in degrees below -1. All extensions use the specified Finsupp integer basis.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace AlgebraicTopology.OrderedJoin.CosetComparison

variable {G : Type u} [Group G]

private theorem tupleMap_term {Y : Type u} {Z : Type v} (f : Y → Z)
    (q : ℤ) (l : List Y) :
    tupleMap f q (tupleTerm q l) = tupleTerm q (l.map f) := by
  classical
  by_cases h : (l.length : ℤ) = q + 1
  · simp [tupleTerm, tupleMap, h]
  · simp [tupleTerm, tupleMap, h]

private theorem tupleMap_single {Y : Type u} {Z : Type v} (f : Y → Z)
    (q : ℤ) (σ : TupleSymbol Y q) (m : ℤ) :
    tupleMap f q (Finsupp.single σ m) =
      m • Finsupp.single ⟨σ.val.map f, by simpa using σ.property⟩ 1 := by
  classical
  simp [tupleMap, tupleTerm, σ.property]

private theorem tupleBoundary_natural {Y : Type u} {Z : Type v} (f : Y → Z)
    (q p : ℤ) :
    (tupleBoundary Z q p).comp (tupleMap f q) =
      (tupleMap f p).comp (tupleBoundary Y q p) := by
  classical
  apply Finsupp.lhom_ext
  intro σ m
  simp only [LinearMap.comp_apply, tupleMap_single, map_smul, tupleBoundary,
    Finsupp.linearCombination_single, one_smul, map_list_sum]
  simp only [List.map_map, Function.comp_def, map_smul, tupleMap_term,
    List.length_map, List.eraseIdx_map]

private theorem chainMap_term {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i, X i → Y i) (q : ℤ) (σ : Face X) :
    chainMap f q (symbolTerm X q σ) = symbolTerm Y q (mapFace f σ) := by
  classical
  by_cases h : (σ.colors.card : ℤ) = q + 1
  · simp [symbolTerm, h, chainMap, Finsupp.linearCombination_single]
  · simp [symbolTerm, mapFace, h]

private theorem mapFace_empty {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i, X i → Y i) :
    mapFace f ⟨∅, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩ =
      ⟨∅, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩ := by
  unfold mapFace
  congr 1
  funext i hi
  exact False.elim (Finset.notMem_empty i hi)

private theorem mapFace_insert {r : ℕ} {X : Fin r → Type u} {Y : Fin r → Type v}
    (f : ∀ i, X i → Y i) (v : ∀ i, X i) (i : Fin r) (σ : Face X) :
    mapFace f (insert v i σ) = insert (fun j ↦ f j (v j)) i (mapFace f σ) := by
  unfold mapFace insert
  congr 1
  funext j hj
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

private theorem comparison_equivariant {n : ℕ} (H : Subgroup G)
    (a : Fin (n + 1) → G) (k : ℕ) (g : H) :
    (comparison H a k).comp (tupleMap (fun h : H ↦ g * h) (arityDegree k)) =
      (chainMap (translateVertex H a g) (arityDegree k)).comp (comparison H a k) := by
  classical
  have hv (h : H) :
      (fun i ↦ translateVertex H a g i (vertex H a h i)) = vertex H a (g * h) := by
    funext i
    apply Subtype.ext
    simp [translateVertex, vertex, mul_assoc]
  induction k with
  | zero =>
    apply Finsupp.lhom_ext
    intro σ m
    simp only [LinearMap.comp_apply, tupleMap_single, map_smul, comparison,
      Finsupp.linearCombination_single, one_smul]
    have hb : chainMap (translateVertex H a g) (-1)
        (symbolTerm (Coset H a) (-1)
          ⟨∅, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩) =
        symbolTerm (Coset H a) (-1)
          ⟨∅, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩ := by
      rw [chainMap_term, mapFace_empty]
    exact congrArg (fun z ↦ m • z) hb.symm
  | succ k ih =>
    cases k with
    | zero =>
      apply Finsupp.lhom_ext
      rintro ⟨l, hl⟩ m
      cases l with
      | nil => simp [arityDegree] at hl
      | cons h l =>
        simp only [LinearMap.comp_apply, tupleMap_single, map_smul, comparison,
          Finsupp.linearCombination_single, one_smul]
        simp only [List.map_cons, List.headD_cons]
        have hb : chainMap (translateVertex H a g) 0
            (symbolTerm (Coset H a) 0 (insert (vertex H a h) 0
              ⟨∅, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩)) =
            symbolTerm (Coset H a) 0 (insert (vertex H a (g * h)) 0
              ⟨∅, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩) := by
          rw [chainMap_term, mapFace_insert, mapFace_empty, hv]
        exact congrArg (fun z ↦ m • z) hb.symm
    | succ k =>
      apply Finsupp.lhom_ext
      rintro ⟨l, hl⟩ m
      cases l with
      | nil => simp [arityDegree] at hl; omega
      | cons h l =>
        have hn := (partialContraction (n + 1) (by omega) (Coset H a)
          (vertex H a h)).2.2.2.1 (Coset H a) (translateVertex H a g) (k : ℤ)
        rw [hv] at hn
        simp only [LinearMap.comp_apply, tupleMap_single, map_smul, comparison,
          Finsupp.linearCombination_single, one_smul]
        simp only [List.map_cons, List.headD_cons]
        let σ : TupleSymbol H ((k + 1 : ℕ) : ℤ) := ⟨h :: l, hl⟩
        let τ : TupleSymbol H ((k + 1 : ℕ) : ℤ) :=
          ⟨(h :: l).map (fun h ↦ g * h), by simpa [arityDegree] using hl⟩
        have hm : tupleMap (fun h : H ↦ g * h) ((k + 1 : ℕ) : ℤ)
            (Finsupp.single σ 1) = Finsupp.single τ 1 := by
          simp [tupleMap_single, σ, τ]
        have hd := LinearMap.congr_fun
          (tupleBoundary_natural (fun h : H ↦ g * h) ((k + 1 : ℕ) : ℤ) (k : ℤ))
          (Finsupp.single σ 1)
        simp only [LinearMap.comp_apply, hm] at hd
        have hp := LinearMap.congr_fun ih
          (tupleBoundary H ((k + 1 : ℕ) : ℤ) (k : ℤ) (Finsupp.single σ 1))
        simp only [LinearMap.comp_apply, arityDegree] at hp
        have hs := LinearMap.congr_fun hn
          (comparison H a (k + 1)
            (tupleBoundary H ((k + 1 : ℕ) : ℤ) (k : ℤ) (Finsupp.single σ 1)))
        simp only [LinearMap.comp_apply] at hs
        have he : contraction (vertex H a (g * h)) (k : ℤ) ((k + 1 : ℕ) : ℤ)
            (comparison H a (k + 1)
              (tupleBoundary H ((k + 1 : ℕ) : ℤ) (k : ℤ) (Finsupp.single τ 1))) =
            chainMap (translateVertex H a g) ((k + 1 : ℕ) : ℤ)
              (contraction (vertex H a h) (k : ℤ) ((k + 1 : ℕ) : ℤ)
                (comparison H a (k + 1)
                  (tupleBoundary H ((k + 1 : ℕ) : ℤ) (k : ℤ)
                    (Finsupp.single σ 1)))) := by
          rw [hd]
          exact (congrArg
            (contraction (vertex H a (g * h)) (k : ℤ) ((k + 1 : ℕ) : ℤ)) hp).trans hs.symm
        exact congrArg (fun z ↦ m • z) he

private theorem erasure_symbolTerm {n : ℕ} (H : Subgroup G)
    (a : Fin (n + 1) → G) (q : ℤ) (σ : Face (Coset H a))
    (hσ : (σ.colors.card : ℤ) = q + 1) :
    erasure H a q (symbolTerm (Coset H a) q σ) = tupleTerm q
      ((List.finRange (n + 1)).filterMap (fun i ↦
        if hi : i ∈ σ.colors then some (σ.vertex i hi).val else none)) := by
  classical
  simp [symbolTerm, hσ, erasure]

private theorem erasure_equivariant {n : ℕ} (H : Subgroup G)
    (a : Fin (n + 1) → G) (q : ℤ) (g : H) :
    (erasure H a q).comp (chainMap (translateVertex H a g) q) =
      (tupleMap (fun x : G ↦ (g : G) * x) q).comp (erasure H a q) := by
  classical
  apply Finsupp.lhom_ext
  intro σ m
  simp only [LinearMap.comp_apply, chainMap, Finsupp.linearCombination_single, map_smul]
  rw [erasure_symbolTerm H a q (mapFace (translateVertex H a g) σ.val) σ.property]
  simp only [erasure, Finsupp.linearCombination_single, map_smul, tupleMap_term]
  congr 2
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro i _
  simp only [mapFace, translateVertex]
  split_ifs <;> rfl

private theorem comparison_augmentation {n : ℕ} (H : Subgroup G)
    (a : Fin (n + 1) → G) (z : TupleChain H (-1)) :
    comparison H a 0 z =
      (z.sum (fun _ m ↦ m)) • symbolTerm (Coset H a) (-1)
        ⟨∅, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩ := by
  classical
  simp only [comparison, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_smul]
  rfl

private theorem erasure_augmentation {n : ℕ} (H : Subgroup G)
    (a : Fin (n + 1) → G) (z : Chain (Coset H a) (-1)) :
    erasure H a (-1) z = (z.sum (fun _ m ↦ m)) • tupleTerm (-1) ([] : List G) := by
  classical
  rw [erasure, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro σ _
  have hσ : σ.val.colors = ∅ := by
    apply Finset.card_eq_zero.mp
    have h := σ.property
    omega
  simp [hσ]

private theorem erasure_empty {n : ℕ} (H : Subgroup G) (a : Fin (n + 1) → G) :
    erasure H a (-1) (symbolTerm (Coset H a) (-1)
      ⟨∅, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩) =
        tupleTerm (-1) ([] : List G) := by
  classical
  simp [symbolTerm, erasure]

private theorem erasure_top_mem {n : ℕ} (H : Subgroup G)
    (a : Fin (n + 1) → G) (z : Chain (Coset H a) (n : ℤ)) :
    erasure H a (n : ℤ) z ∈
      Submodule.span ℤ (Set.range (fun h : Fin (n + 1) → H ↦
        tupleTerm (n : ℤ) (List.ofFn (fun i ↦ (h i : G) * a i)))) := by
  classical
  rw [erasure, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro σ _
  apply Submodule.smul_mem
  have hc : σ.val.colors = Finset.univ := by
    apply Finset.eq_univ_of_card
    have h := σ.property
    simp only [Fintype.card_fin]
    omega
  have hi (i : Fin (n + 1)) : i ∈ σ.val.colors := by simp [hc]
  obtain ⟨h, hh⟩ := Classical.axiomOfChoice
    (fun i ↦ (σ.val.vertex i (hi i)).property)
  apply Submodule.subset_span
  refine ⟨h, ?_⟩
  have hl : (List.finRange (n + 1)).filterMap (fun i ↦
      if hj : i ∈ σ.val.colors then some (σ.val.vertex i hj).val else none) =
        List.ofFn (fun i ↦ (h i : G) * a i) := by
    rw [List.ofFn_eq_map]
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro i _
    simp only [dif_pos (hi i)]
    exact congrArg some (hh i)
  rw [hl]

/-- The canonical comparison is an augmented equivariant chain map, its coordinate
formula is a fixed finite list, erasure is an equivariant augmented chain map, and
the top image has the prescribed coset support. In the finite list each formal
symbol has a set of q+1 colors, ordered increasingly, and each color carries an
index in Fin(q+1). Thus repeated terms are permitted and the list is independent
of every value of the input tuple. Integer-linear maps are precisely homomorphisms
of the free abelian groups here.

Source: direct-images (3), agent ordered-coset expansion, calculations 1–7
(blueprint: lem-sfb-ordered-join-coset-comparison).

Proof:
1. Extend the displayed formulas on the specified bases, using
   def-weil-pbc-free-module. Recursion uses only previously constructed values.
2. In the tuple boundary squared, delete positions a<b in either order. The
   signs are (-1)^(a+b-1) and (-1)^(a+b), so the terms cancel, even for repeated
   entries. Deletion commutes with translation; augmentation has trivial action.
3. The degree-zero comparison has boundary 1. Inductively z=P(dx) is a cycle
   by the preceding chain identity and d squared zero. The identity dS+Sd=1 of
   lem-sfb-ordered-join-partial-contraction applies in degree q-1<=n-1, giving
   dP(x)=z. No contraction of degree n is used.
4. Left translation sends the chosen vertices ha_i to (gh)a_i. Naturality in
   lem-sfb-ordered-join-partial-contraction gives gS^h=S^(gh)g. Induct using
   deletion commutation to obtain equivariance, including the empty tuple.
5. Start with coefficient 1, color 0, index 0. For each face copy the preceding
   list, multiply by its deletion sign and reindex the remaining coordinates.
   Expand S using the dependency's color-only insertion/replacement formula;
   retained vertices keep their indices and chosen vertices acquire index 0.
   Concatenate without collecting equal terms. All lists are fixed before inputs.
6. On basis symbols erasure and boundary give the same signed deletion list.
   Erasure also commutes with left multiplication, and fixes the empty symbol.
7. Compose these identities to obtain the assertions for A=eP. A top join face
   has all n+1 colors, so its erased tuple has ith coordinate in Ha_i. Finite
   integer linear combinations give precisely the claimed span containment. -/
theorem orderedJoinCosetComparison (H : Subgroup G) (n : ℕ) (hn : 1 ≤ n)
    (a : Fin (n + 1) → G) :
    (∀ q : ℕ, q ≤ n →
      (boundary (Coset H a) (q : ℤ) (arityDegree q)).comp (comparison H a (q + 1)) =
        (comparison H a q).comp (tupleBoundary H (q : ℤ) (arityDegree q))) ∧
    (∀ (k : ℕ), k ≤ n + 1 → ∀ g : H,
      (comparison H a k).comp (tupleMap (fun h : H ↦ g * h) (arityDegree k)) =
        (chainMap (translateVertex H a g) (arityDegree k)).comp (comparison H a k)) ∧
    (∀ q : ℕ, q ≤ n →
      ∃ L : List (ℤ × Symbol (fun _ : Fin (n + 1) ↦ Fin (q + 1)) (q : ℤ)),
        ∀ h : Fin (q + 1) → H,
          comparison H a (q + 1) (tupleTerm (q : ℤ) (List.ofFn h)) =
            (L.map (fun t ↦ t.1 •
              chainMap (fun i j ↦ vertex H a (h j) i) (q : ℤ)
                (Finsupp.single t.2 1))).sum) ∧
    (∀ q : ℤ,
      (tupleBoundary G q (q - 1)).comp (erasure H a q) =
        (erasure H a (q - 1)).comp (boundary (Coset H a) q (q - 1))) ∧
    (∀ (q : ℤ) (g : H),
      (erasure H a q).comp (chainMap (translateVertex H a g) q) =
        (tupleMap (fun x : G ↦ (g : G) * x) q).comp (erasure H a q)) ∧
    (∀ z : TupleChain H (-1),
      comparison H a 0 z =
        (z.sum (fun _ m ↦ m)) • symbolTerm (Coset H a) (-1)
          ⟨∅, fun i hi ↦ False.elim (Finset.notMem_empty i hi)⟩) ∧
    (∀ z : Chain (Coset H a) (-1),
      erasure H a (-1) z = (z.sum (fun _ m ↦ m)) • tupleTerm (-1) ([] : List G)) ∧
    (∀ q : ℕ, q ≤ n →
      (tupleBoundary G (q : ℤ) (arityDegree q)).comp (erasedComparison H a (q + 1)) =
        (erasedComparison H a q).comp (tupleBoundary H (q : ℤ) (arityDegree q))) ∧
    (∀ (k : ℕ), k ≤ n + 1 → ∀ g : H,
      (erasedComparison H a k).comp (tupleMap (fun h : H ↦ g * h) (arityDegree k)) =
        (tupleMap (fun x : G ↦ (g : G) * x) (arityDegree k)).comp
          (erasedComparison H a k)) ∧
    (∀ z : TupleChain H (-1),
      erasedComparison H a 0 z = (z.sum (fun _ m ↦ m)) • tupleTerm (-1) ([] : List G)) ∧
    LinearMap.range (erasedComparison H a (n + 1)) ≤
      Submodule.span ℤ (Set.range (fun h : Fin (n + 1) → H ↦
        tupleTerm (n : ℤ) (List.ofFn (fun i ↦ (h i : G) * a i)))) := by
  obtain ⟨hchain, hformula⟩ := cosetComparisonRecursion H n hn a
  have hequiv (k : ℕ) (_ : k ≤ n + 1) (g : H) := comparison_equivariant H a k g
  have herasure := cosetErasureBoundary H a
  refine ⟨hchain, hequiv, hformula, herasure, erasure_equivariant H a,
    comparison_augmentation H a, erasure_augmentation H a, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hd (q p : ℤ) (hp : p = q - 1) :
        (tupleBoundary G q p).comp (erasure H a q) =
          (erasure H a p).comp (boundary (Coset H a) q p) := by
      subst p
      exact herasure q
    have he := hd (q : ℤ) (arityDegree q) (by cases q <;> simp [arityDegree])
    change (tupleBoundary G (q : ℤ) (arityDegree q)).comp
        ((erasure H a (q : ℤ)).comp (comparison H a (q + 1))) =
      ((erasure H a (arityDegree q)).comp (comparison H a q)).comp
        (tupleBoundary H (q : ℤ) (arityDegree q))
    rw [← LinearMap.comp_assoc, he, LinearMap.comp_assoc, hchain q hq,
      ← LinearMap.comp_assoc]
  · intro k hk g
    unfold erasedComparison
    rw [LinearMap.comp_assoc, hequiv k hk g, ← LinearMap.comp_assoc,
      erasure_equivariant H a, LinearMap.comp_assoc]
  · intro z
    change erasure H a (-1) (comparison H a 0 z) = _
    rw [comparison_augmentation H a z, map_smul, erasure_empty]
  · rintro _ ⟨z, rfl⟩
    exact erasure_top_mem H a (comparison H a (n + 1) z)

end AlgebraicTopology.OrderedJoin.CosetComparison
