/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Data.List.FinRange

import Mathlib.Algebra.BigOperators.Fin

/-! # Ordered-prefix telescoping for local chain homotopies

Source: six-functors direct-images proof, paragraph (3), agent expansion of
ordered-join calculations 5–6 (blueprint: lem-sfb-ordered-join-prefix-telescope).
The abstract calculation is an agent generalization, not an assertion of the blueprint.

`ChainComplex (ModuleCat ℤ) ℤ` uses the chain convention recorded by
`def-weil-pbc-module-chain-complex-homology`. The canonical `XIsoOfEq` identifies
A_((q-1)+1) with A_q; no periodicity of the graded groups is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped BigOperators

namespace AlgebraicTopology

/-- The first n remainders in increasing color order, with the rightmost acting first.
For n=0 this is the identity, and for n<r the next prefix is P_n composed with R_n.
Source: direct-images paragraph (3), agent ordered-join calculation 5
(blueprint: lem-sfb-ordered-join-prefix-telescope). -/
def orderedRemainderPrefix {r : ℕ} (A : ChainComplex (ModuleCat.{u} ℤ) ℤ)
    (R : ∀ (_i : Fin r) (q : ℤ), A.X q ⟶ A.X q) (n : ℕ) (q : ℤ) : A.X q ⟶ A.X q :=
  ((List.finRange r).take n).foldr (fun i P ↦ P ≫ R i q) (𝟙 (A.X q))

/-- The sum H_q of the prefix P_i in degree q+1 composed with c_i in degree q.
Source: direct-images paragraph (3), agent ordered-join calculation 5
(blueprint: lem-sfb-ordered-join-prefix-telescope). -/
def orderedPrefixHomotopy {r : ℕ} (A : ChainComplex (ModuleCat.{u} ℤ) ℤ)
    (c : ∀ (_i : Fin r) (q : ℤ), A.X q ⟶ A.X (q + 1))
    (R : ∀ (_i : Fin r) (q : ℤ), A.X q ⟶ A.X q) (q : ℤ) : A.X q ⟶ A.X (q + 1) :=
  ∑ i : Fin r, c i q ≫ orderedRemainderPrefix A R i.val (q + 1)

private lemma prefix_zero {r : ℕ} (A : ChainComplex (ModuleCat.{u} ℤ) ℤ)
    (R : ∀ (_i : Fin r) (q : ℤ), A.X q ⟶ A.X q) (q : ℤ) :
    orderedRemainderPrefix A R 0 q = 𝟙 _ := by
  simp [orderedRemainderPrefix]

private lemma fold_prefix {r : ℕ} (A : ChainComplex (ModuleCat.{u} ℤ) ℤ)
    (R : ∀ (_i : Fin r) (q : ℤ), A.X q ⟶ A.X q) (q : ℤ)
    (l : List (Fin r)) (f : A.X q ⟶ A.X q) :
    l.foldr (fun i P ↦ P ≫ R i q) f =
      f ≫ l.foldr (fun i P ↦ P ≫ R i q) (𝟙 _) := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih, Category.assoc]

private lemma prefix_succ {r : ℕ} (A : ChainComplex (ModuleCat.{u} ℤ) ℤ)
    (R : ∀ (_i : Fin r) (q : ℤ), A.X q ⟶ A.X q) (q : ℤ)
    (n : ℕ) (hn : n < r) :
    orderedRemainderPrefix A R (n + 1) q =
      R ⟨n, hn⟩ q ≫ orderedRemainderPrefix A R n q := by
  unfold orderedRemainderPrefix
  rw [List.take_add_one,
    List.getElem?_eq_getElem (show n < (List.finRange r).length by simpa using hn)]
  simp only [List.getElem_finRange, Option.toList_some, List.foldr_append,
    List.foldr_cons, List.foldr_nil, Category.id_comp]
  rw [fold_prefix]
  congr 2

/-- Local identities imply differential commutation, the ordered telescoping identity,
and vanishing of the final product under the proper-color support hypotheses.

Source: direct-images paragraph (3), agent generalization of ordered-join calculations
5–6, not asserted in the blueprint itself
(blueprint: lem-sfb-ordered-join-prefix-telescope).

Proof:
1. Solve the local identity for R_i in degrees q and q-1. Expand d R_i and R_i d.
   The d squared terms vanish by the chain-complex axiom of
   def-weil-pbc-module-chain-complex-homology; both expressions are d-d c_i d.
2. Induct on the prefix length, starting from the identity. Associativity and step 1
   give d P_(i+1)=d P_i R_i=P_i d R_i=P_i R_i d=P_(i+1) d in every degree.
3. Distribute d over H. Step 2 and the local identity give the i-th summand
   P_i (d c_i+c_i d)=P_i(1-R_i)=P_i-P_(i+1).
4. The finite sum telescopes by induction on its length, giving P_0-P_r=1-P_r.
5. Fix a proper color set C and choose j outside C. In P_r, the factors with index
   greater than j act first and preserve its subgroup. The factor R_j kills the result;
   the remaining homomorphisms send zero to zero. Thus P_r kills each support subgroup.
   Write an arbitrary element as the assumed finite sum and use additivity. No factors
   are commuted, and empty composites are identities. -/
theorem orderedJoinPrefixTelescope (r : ℕ) (hr : 1 ≤ r)
    (A : ChainComplex (ModuleCat.{u} ℤ) ℤ)
    (c : ∀ (_i : Fin r) (q : ℤ), A.X q ⟶ A.X (q + 1))
    (R : ∀ (_i : Fin r) (q : ℤ), A.X q ⟶ A.X q)
    (hlocal : ∀ (i : Fin r) (q : ℤ),
      c i q ≫ A.d (q + 1) q +
        A.d q (q - 1) ≫ c i (q - 1) ≫ (A.XIsoOfEq (sub_add_cancel q 1)).hom =
          𝟙 (A.X q) - R i q) :
    (∀ (q : ℤ) (i : Fin r),
      R i q ≫ A.d q (q - 1) = A.d q (q - 1) ≫ R i (q - 1)) ∧
    (∀ (q : ℤ) (n : ℕ), n ≤ r →
      orderedRemainderPrefix A R n q ≫ A.d q (q - 1) =
        A.d q (q - 1) ≫ orderedRemainderPrefix A R n (q - 1)) ∧
    (∀ q : ℤ,
      orderedPrefixHomotopy A c R q ≫ A.d (q + 1) q +
          A.d q (q - 1) ≫ orderedPrefixHomotopy A c R (q - 1) ≫
            (A.XIsoOfEq (sub_add_cancel q 1)).hom =
        ∑ i : Fin r, (orderedRemainderPrefix A R i.val q -
          orderedRemainderPrefix A R (i.val + 1) q)) ∧
    (∀ q : ℤ,
      (∑ i : Fin r, (orderedRemainderPrefix A R i.val q -
        orderedRemainderPrefix A R (i.val + 1) q)) =
          𝟙 (A.X q) - orderedRemainderPrefix A R r q) ∧
    (∀ (q : ℤ) (S : {C : Set (Fin r) // C ⊂ Set.univ} → AddSubgroup (A.X q)),
      (∀ x : A.X q, ∃ (n : ℕ) (f : Fin n → A.X q)
        (C : Fin n → {C : Set (Fin r) // C ⊂ Set.univ}),
          (∀ j : Fin n, f j ∈ S (C j)) ∧ (∑ j : Fin n, f j) = x) →
      (∀ (i : Fin r) (C : {C : Set (Fin r) // C ⊂ Set.univ}) (x : A.X q),
        x ∈ S C → R i q x ∈ S C) →
      (∀ (i : Fin r) (C : {C : Set (Fin r) // C ⊂ Set.univ}) (x : A.X q),
        i ∉ C.val → x ∈ S C → R i q x = 0) →
      orderedRemainderPrefix A R r q = 0) := by
  classical
  have _ := hr
  have hlocal' (i : Fin r) (q p : ℤ) (h : p + 1 = q) :
      c i q ≫ A.d (q + 1) q +
        A.d q p ≫ c i p ≫ (A.XIsoOfEq h).hom = 𝟙 _ - R i q := by
    have hp : p = q - 1 := by omega
    subst p
    exact hlocal i q
  have hR : ∀ (q : ℤ) (i : Fin r),
      R i q ≫ A.d q (q - 1) = A.d q (q - 1) ≫ R i (q - 1) := by
    intro q i
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, q = p + 1 := ⟨q - 1, by omega⟩
    have hshift (a b : ℤ) (hb : b = a - 1) :
        (R i a ≫ A.d a b = A.d a b ≫ R i b) ↔
          (R i a ≫ A.d a (a - 1) = A.d a (a - 1) ≫ R i (a - 1)) := by
      subst b
      rfl
    apply (hshift (p + 1) p (by omega)).mp
    have hu : c i (p + 1) ≫ A.d (p + 1 + 1) (p + 1) +
        A.d (p + 1) p ≫ c i p = 𝟙 _ - R i (p + 1) := by
      simpa only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
        Category.comp_id] using hlocal' i (p + 1) p rfl
    have h₁ := congrArg (fun f ↦ f ≫ A.d (p + 1) p) hu
    have h₂ := congrArg (fun f ↦ A.d (p + 1) p ≫ f) (hlocal i p)
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.assoc, HomologicalComplex.d_comp_d,
      HomologicalComplex.d_comp_d_assoc,
      Limits.comp_zero, Limits.zero_comp, zero_add, add_zero, Category.id_comp,
      Category.comp_id] at h₁ h₂
    have h := h₁.symm.trans h₂
    exact sub_right_inj.mp h
  have hP : ∀ (q : ℤ) (n : ℕ), n ≤ r →
      orderedRemainderPrefix A R n q ≫ A.d q (q - 1) =
        A.d q (q - 1) ≫ orderedRemainderPrefix A R n (q - 1) := by
    intro q n hn
    induction n with
    | zero => simp [prefix_zero]
    | succ n ih =>
      rw [prefix_succ A R q n (by omega), prefix_succ A R (q - 1) n (by omega)]
      rw [Category.assoc, ih (by omega), ← Category.assoc, hR q ⟨n, by omega⟩,
        Category.assoc]
  refine ⟨hR, hP, ?_, ?_, ?_⟩
  · intro q
    have hPu (n : ℕ) (hn : n ≤ r) :
        orderedRemainderPrefix A R n (q + 1) ≫ A.d (q + 1) q =
          A.d (q + 1) q ≫ orderedRemainderPrefix A R n q := by
      have hp (a b : ℤ) (h : b = a - 1) :
          orderedRemainderPrefix A R n a ≫ A.d a b =
            A.d a b ≫ orderedRemainderPrefix A R n b := by
        subst b
        exact hP a n hn
      exact hp (q + 1) q (by omega)
    have htransport (n : ℕ) {a b : ℤ} (h : a = b) :
        orderedRemainderPrefix A R n a ≫ (A.XIsoOfEq h).hom =
          (A.XIsoOfEq h).hom ≫ orderedRemainderPrefix A R n b := by
      subst b
      simp
    unfold orderedPrefixHomotopy
    simp only [Preadditive.sum_comp, Preadditive.comp_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (c i q ≫ A.d (q + 1) q +
          A.d q (q - 1) ≫ c i (q - 1) ≫
            (A.XIsoOfEq (sub_add_cancel q 1)).hom) ≫
              orderedRemainderPrefix A R i.val q := by
        simp only [Preadditive.add_comp, Category.assoc]
        rw [hPu i.val (Nat.le_of_lt i.isLt),
          htransport i.val (sub_add_cancel q 1)]
      _ = _ := by
        rw [hlocal, Preadditive.sub_comp, Category.id_comp, prefix_succ A R q i.val i.isLt]
  · intro q
    simpa only [prefix_zero] using
      (Fin.sum_univ_eq_sum_range (fun n ↦ orderedRemainderPrefix A R n q -
        orderedRemainderPrefix A R (n + 1) q) r).trans (Finset.sum_range_sub' _ r)
  · intro q S hgen hpres hkill
    let F (l : List (Fin r)) : A.X q ⟶ A.X q :=
      l.foldr (fun i P ↦ P ≫ R i q) (𝟙 _)
    have hF (C) (l : List (Fin r)) (x : A.X q) (hx : x ∈ S C) : F l x ∈ S C := by
      induction l with
      | nil => simpa [F] using hx
      | cons i l ih => exact hpres i C (F l x) ih
    have hZ (C) (l : List (Fin r)) (hl : ∃ i ∈ l, i ∉ C.val)
        (x : A.X q) (hx : x ∈ S C) : F l x = 0 := by
      induction l with
      | nil => simp at hl
      | cons i l ih =>
        change R i q (F l x) = 0
        by_cases hi : i ∈ C.val
        · have hl' : ∃ j ∈ l, j ∉ C.val := by
            obtain ⟨j, hj, hjC⟩ := hl
            rcases List.mem_cons.mp hj with h | h
            · subst j; exact (hjC hi).elim
            · exact ⟨j, h, hjC⟩
          rw [ih hl', map_zero]
        · exact hkill i C (F l x) hi (hF C l x hx)
    have hz (C) (x : A.X q) (hx : x ∈ S C) :
        orderedRemainderPrefix A R r q x = 0 := by
      obtain ⟨i, _, hi⟩ := Set.exists_of_ssubset C.property
      have ht : (List.finRange r).take r = List.finRange r := by
        simpa only [List.length_finRange] using (List.take_length (l := List.finRange r))
      simpa only [orderedRemainderPrefix, ht, F] using
        hZ C (List.finRange r) ⟨i, List.mem_finRange i, hi⟩ x hx
    ext x
    obtain ⟨n, f, C, hf, hsum⟩ := hgen x
    rw [← hsum]
    change (orderedRemainderPrefix A R r q).hom (∑ j : Fin n, f j) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    exact hz (C j) (f j) (hf j)

end AlgebraicTopology
