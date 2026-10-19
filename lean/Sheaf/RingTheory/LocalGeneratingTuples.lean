/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module

/-! # Elementary changes between generating tuples over a local ring

Source: Stacks Project, Algebra, Tags 00DV (`lemma-NAK`) and 00E9
(`lemma-characterize-local-ring`); the agent-formulated generating-tuple consequence
used in the local-ring reduction of `lem-pur-frame-independence.proof.md`
(blueprint: lem-pur-local-generating-tuples).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace Module

private inductive TupleOp (R : Type u) [CommRing R] (ι : Type) where
  | scale (i : ι) (a : Rˣ)
  | swap (i j : ι) (h : i ≠ j)
  | shear (i j : ι) (a : R) (h : i ≠ j)

private def TupleOp.act {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module R M] (o : TupleOp R ι) (f : ι → M) : ι → M :=
  match o with
  | .scale i a => fun k ↦ if k = i then (a : R) • f i else f k
  | .swap i j _ => fun k ↦ if k = i then f j else if k = j then f i else f k
  | .shear i j a _ => fun k ↦ if k = i then f i + a • f j else f k

private def TupleOp.inv {R : Type u} [CommRing R] {ι : Type} :
    TupleOp R ι → TupleOp R ι
  | .scale i a => .scale i a⁻¹
  | .swap i j h => .swap i j h
  | .shear i j a h => .shear i j (-a) h

private theorem TupleOp.inv_act {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module R M] (o : TupleOp R ι) (f : ι → M) :
    o.inv.act (o.act f) = f := by
  funext k
  cases o with
  | scale i a => by_cases h : k = i <;> simp [TupleOp.inv, TupleOp.act, h, smul_smul]
  | swap i j hij =>
    by_cases h : k = i <;> by_cases h' : k = j <;>
      simp_all [TupleOp.inv, TupleOp.act]
  | shear i j a hij =>
    by_cases h : k = i <;> simp [TupleOp.inv, TupleOp.act, h, hij.symm]

private def tupleRun {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module R M] (l : List (TupleOp R ι))
    (f : ι → M) : ι → M := l.foldl (fun f o ↦ o.act f) f

private theorem tupleRun_append {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module R M] (l l' : List (TupleOp R ι)) (f : ι → M) :
    tupleRun (l ++ l') f = tupleRun l' (tupleRun l f) := by
  exact List.foldl_append

private theorem TupleOp.span_act {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module R M] (o : TupleOp R ι) (f : ι → M) :
    Submodule.span R (Set.range (o.act f)) = Submodule.span R (Set.range f) := by
  have le (o : TupleOp R ι) (f : ι → M) :
      Submodule.span R (Set.range (o.act f)) ≤ Submodule.span R (Set.range f) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    have hf (i) : f i ∈ Submodule.span R (Set.range f) := Submodule.subset_span ⟨i, rfl⟩
    cases o with
    | scale i a =>
      simp only [TupleOp.act]
      split_ifs
      · exact Submodule.smul_mem _ _ (hf _)
      · exact hf _
    | swap i j h => simp only [TupleOp.act]; split_ifs <;> exact hf _
    | shear i j a h =>
      simp only [TupleOp.act]
      split_ifs
      · exact Submodule.add_mem _ (hf _) (Submodule.smul_mem _ _ (hf _))
      · exact hf _
  apply le_antisymm (le o f)
  simpa only [o.inv_act f] using le o.inv (o.act f)

private theorem tupleRun_span {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]
    {M : Type v} [AddCommGroup M] [Module R M] (l : List (TupleOp R ι)) (f : ι → M) :
    Submodule.span R (Set.range (tupleRun l f)) = Submodule.span R (Set.range f) := by
  induction l generalizing f with
  | nil => rfl
  | cons o l ih => exact (ih (o.act f)).trans (o.span_act f)

section TupleHelpers

variable {R : Type u} [CommRing R] {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem TupleOp.act_map {N : Type*} [AddCommGroup N] [Module R N]
    (o : TupleOp R ι) (q : M →ₗ[R] N) (f : ι → M) :
    q ∘ o.act f = o.act (q ∘ f) := by
  funext k
  cases o <;> simp only [TupleOp.act, Function.comp_apply] <;>
    split_ifs <;> simp [map_add, map_smul]

private theorem tupleRun_map {N : Type*} [AddCommGroup N] [Module R N]
    (l : List (TupleOp R ι)) (q : M →ₗ[R] N) (f : ι → M) :
    q ∘ tupleRun l f = tupleRun l (q ∘ f) := by
  induction l generalizing f with
  | nil => rfl
  | cons o l ih =>
    change q ∘ tupleRun l (o.act f) = tupleRun l (o.act (q ∘ f))
    rw [ih, o.act_map]

private def TupleOp.embed (e : ι ↪ κ) : TupleOp R ι → TupleOp R κ
  | .scale i a => .scale (e i) a
  | .swap i j h => .swap (e i) (e j) (fun H ↦ h (e.injective H))
  | .shear i j a h => .shear (e i) (e j) a (fun H ↦ h (e.injective H))

private theorem TupleOp.embed_act (e : ι ↪ κ) (o : TupleOp R ι) (f : κ → M) :
    (o.embed e).act f ∘ e = o.act (f ∘ e) := by
  funext k
  cases o <;> simp [TupleOp.embed, TupleOp.act, e.injective.eq_iff]

omit [DecidableEq ι] in
private theorem TupleOp.embed_act_fixed (e : ι ↪ κ) (o : TupleOp R ι)
    (f : κ → M) (k : κ) (hk : ∀ i, e i ≠ k) : (o.embed e).act f k = f k := by
  cases o <;> simp [TupleOp.embed, TupleOp.act, (hk _).symm]

private theorem tupleRun_embed (e : ι ↪ κ) (l : List (TupleOp R ι)) (f : κ → M) :
    tupleRun (l.map (TupleOp.embed e)) f ∘ e = tupleRun l (f ∘ e) := by
  induction l generalizing f with
  | nil => rfl
  | cons o l ih =>
    change tupleRun (l.map (TupleOp.embed e)) ((o.embed e).act f) ∘ e = _
    rw [ih, o.embed_act]
    rfl

omit [DecidableEq ι] in
private theorem tupleRun_embed_fixed (e : ι ↪ κ) (l : List (TupleOp R ι))
    (f : κ → M) (k : κ) (hk : ∀ i, e i ≠ k) :
    tupleRun (l.map (TupleOp.embed e)) f k = f k := by
  induction l generalizing f with
  | nil => rfl
  | cons o l ih =>
    change tupleRun (l.map (TupleOp.embed e)) ((o.embed e).act f) k = _
    rw [ih, o.embed_act_fixed e f k hk]

private theorem TupleOp.act_add (o : TupleOp R ι) (f g : ι → M) :
    o.act (f + g) = o.act f + o.act g := by
  funext k
  cases o <;> simp only [TupleOp.act, Pi.add_apply] <;> split_ifs <;>
    simp [smul_add, add_add_add_comm]

private theorem TupleOp.act_smul (o : TupleOp R ι) (a : R) (f : ι → M) :
    o.act (a • f) = a • o.act f := by
  funext k
  cases o <;> simp only [TupleOp.act, Pi.smul_apply] <;> split_ifs <;>
    simp [smul_add, smul_smul, mul_comm]

private def TupleOp.linearEquiv (o : TupleOp R ι) : (ι → R) ≃ₗ[R] (ι → R) where
  toFun := o.act
  invFun := o.inv.act
  left_inv := o.inv_act
  right_inv := by
    have hi : o.inv.inv = o := by cases o <;> simp [TupleOp.inv]
    intro f
    simpa only [hi] using o.inv.inv_act f
  map_add' := o.act_add
  map_smul' := o.act_smul

private def TupleOp.matrix [Fintype ι] (o : TupleOp R ι) :
    Matrix.GeneralLinearGroup ι R :=
  Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv o.linearEquiv)

private theorem TupleOp.matrix_mulVec [Fintype ι] (o : TupleOp R ι) (z : ι → R) :
    (o.matrix : Matrix ι ι R).mulVec z = o.act z := by
  have h := congrArg (fun e : LinearMap.GeneralLinearGroup R (ι → R) ↦ e.toLinearEquiv z)
    (Matrix.GeneralLinearGroup.toLin.apply_symm_apply
      (LinearMap.GeneralLinearGroup.ofLinearEquiv o.linearEquiv))
  exact h

private theorem exists_sum_update (s : Finset ι) (i : ι) (hi : i ∉ s)
    (a : ι → R) (f : ι → M) :
    ∃ l : List (TupleOp R ι),
      tupleRun l f = Function.update f i (f i + ∑ j ∈ s, a j • f j) := by
  induction s using Finset.induction_on generalizing f with
  | empty => exact ⟨[], by simp [tupleRun]⟩
  | @insert j s hj ih =>
    have hji : j ≠ i := by intro h; subst j; simp at hi
    obtain ⟨l, hl⟩ := ih (fun h ↦ hi (Finset.mem_insert_of_mem h)) f
    refine ⟨l ++ [.shear i j (a j) hji.symm], ?_⟩
    rw [tupleRun_append, hl]
    funext k
    by_cases hk : k = i
    · subst k
      simp [tupleRun, TupleOp.act, hji, Finset.sum_insert hj, add_comm, add_left_comm]
    · simp [tupleRun, TupleOp.act, hk]

private theorem exists_adjust (s : Finset ι) (i : ι) (hi : i ∉ s)
    (a : ι → R) (f : ι → M) :
    ∃ l : List (TupleOp R ι), ∀ k,
      tupleRun l f k = if k ∈ s then f k + a k • f i else f k := by
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simp [tupleRun]⟩
  | @insert j s hj ih =>
    have hji : j ≠ i := by intro h; subst j; simp at hi
    obtain ⟨l, hl⟩ := ih (fun h ↦ hi (Finset.mem_insert_of_mem h))
    refine ⟨l ++ [.shear j i (a j) hji], ?_⟩
    intro k
    rw [tupleRun_append]
    change (TupleOp.shear j i (a j) hji).act (tupleRun l f) k = _
    simp only [TupleOp.act]
    by_cases hk : k = j
    · subst k
      simp [hl, hj, show i ∉ s from fun h ↦ hi (Finset.mem_insert_of_mem h)]
    · simp [hk, hl]

private theorem exists_pivot [Fintype ι] (f : ι → M) (a : ι → R)
    (j : ι) (hj : IsUnit (a j)) :
    ∃ l : List (TupleOp R ι), tupleRun l f j = ∑ k, a k • f k := by
  obtain ⟨u, hu⟩ := hj
  let f' := (TupleOp.scale j u).act f
  obtain ⟨l, hl⟩ := exists_sum_update (Finset.univ.erase j) j (by simp) a f'
  refine ⟨.scale j u :: l, ?_⟩
  change tupleRun l f' j = _
  rw [hl, Function.update_self]
  have hs : (∑ k ∈ Finset.univ.erase j, a k • f' k) =
      ∑ k ∈ Finset.univ.erase j, a k • f k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [f', TupleOp.act, (Finset.mem_erase.mp hk).1]
  rw [hs]
  simpa only [f', TupleOp.act, if_pos rfl, hu] using
    (Finset.add_sum_erase Finset.univ (fun k ↦ a k • f k) (Finset.mem_univ j))

omit [DecidableEq ι] in
private theorem quotient_tail_span (f : ι → M)
    (hf : Submodule.span R (Set.range f) = ⊤) (i : ι)
    (p : Submodule R M) (hi : f i ∈ p) :
    Submodule.span R
      (Set.range (fun j : {j : ι // j ≠ i} ↦ p.mkQ (f j))) = ⊤ := by
  let q := p.mkQ
  let S := Submodule.span R (Set.range (fun j : {j : ι // j ≠ i} ↦ q (f j)))
  have hfull : (Submodule.span R (Set.range f)).map q = ⊤ := by
    rw [hf, Submodule.map_top, Submodule.range_mkQ]
  apply top_unique
  rw [← hfull, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  by_cases hj : j = i
  · subst j
    have hz : q (f i) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero p).mpr hi
    rw [hz]
    exact S.zero_mem
  · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

private theorem exists_tuple_ops [IsLocalRing R] (n : ℕ) :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
      (f g : ι → M), Submodule.span R (Set.range f) = ⊤ →
      Submodule.span R (Set.range g) = ⊤ →
      ∃ l : List (TupleOp R ι), tupleRun l f = g := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ι _ _ hn M _ _ _ f g hf hg
    by_cases hM : Subsingleton M
    · exact ⟨[], funext fun k ↦ hM.elim (f k) (g k)⟩
    have : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    let mM : Submodule R M := IsLocalRing.maximalIdeal R • ⊤
    have hm : mM ≠ ⊤ := by
      intro hm
      have hb : (⊥ : Submodule R M) = ⊤ := IsLocalRing.map_mkQ_eq_top.mp (by
        have hz : (⊥ : Submodule R (M ⧸ mM)) = ⊤ :=
          (Submodule.mkQ_map_self mM).symm.trans
            ((congrArg (Submodule.map mM.mkQ) hm).trans (by simp))
        simpa only [Submodule.map_bot] using hz)
      exact bot_ne_top hb
    obtain ⟨i, hi⟩ : ∃ i, g i ∉ mM := by
      by_contra! H
      apply hm
      apply top_unique
      rw [← hg]
      exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact H j)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp
      (show g i ∈ Submodule.span R (Set.range f) by rw [hf]; trivial)
    obtain ⟨j, hj⟩ : ∃ j, IsUnit (a j) := by
      by_contra! H
      apply hi
      rw [← ha]
      exact Submodule.sum_mem _ fun j _ ↦
        Submodule.smul_mem_smul (((IsLocalRing.mem_maximalIdeal (a j)).mpr (H j)))
          (Submodule.mem_top)
    obtain ⟨l₀, hl₀⟩ := exists_pivot f a j hj
    have hfirst : ∃ l : List (TupleOp R ι), tupleRun l f i = g i := by
      by_cases hij : i = j
      · exact ⟨l₀, by simpa only [hij, ha] using hl₀⟩
      · refine ⟨l₀ ++ [.swap i j hij], ?_⟩
        rw [tupleRun_append]
        simpa [tupleRun, TupleOp.act, ha] using hl₀
    obtain ⟨l₁, hl₁⟩ := hfirst
    let h := tupleRun l₁ f
    have hh : Submodule.span R (Set.range h) = ⊤ := (tupleRun_span l₁ f).trans hf
    let p := R ∙ g i
    let q := p.mkQ
    let e : {j : ι // j ≠ i} ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
    have htail : Submodule.span R (Set.range (q ∘ h ∘ e)) = ⊤ := by
      exact quotient_tail_span h hh i p
        (by rw [show h i = g i from hl₁]; exact Submodule.mem_span_singleton_self _)
    have gtail : Submodule.span R (Set.range (q ∘ g ∘ e)) = ⊤ :=
      quotient_tail_span g hg i p (Submodule.mem_span_singleton_self _)
    obtain ⟨l₂, hl₂⟩ := ih (Fintype.card {j : ι // j ≠ i})
      (hn ▸ Fintype.card_subtype_lt (x := i) (not_not.mpr rfl)) rfl
      (q ∘ h ∘ e) (q ∘ g ∘ e) htail gtail
    let l₂' := l₂.map (TupleOp.embed e)
    let k := tupleRun l₂' h
    have hk : k i = g i := by
      exact (tupleRun_embed_fixed e l₂ h i (fun j ↦ j.property)).trans hl₁
    have hq : q ∘ k ∘ e = q ∘ g ∘ e := by
      rw [show q ∘ k ∘ e = q ∘ (k ∘ e) from rfl, tupleRun_embed, tupleRun_map, hl₂]
    have hcoeff : ∀ j, ∃ a : R, g j = k j + a • k i := by
      intro j
      by_cases hji : j = i
      · exact ⟨0, by simp [hji, hk]⟩
      have heq : q (g j) = q (k j) := (congr_fun hq ⟨j, hji⟩).symm
      have hmem : g j - k j ∈ p := (Submodule.Quotient.eq p).mp heq
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
      exact ⟨a, by rw [hk, ha]; abel⟩
    choose a ha using hcoeff
    obtain ⟨l₃, hl₃⟩ := exists_adjust (Finset.univ.erase i) i (by simp) a k
    refine ⟨l₁ ++ l₂' ++ l₃, ?_⟩
    rw [tupleRun_append, tupleRun_append]
    funext j
    rw [hl₃]
    by_cases hji : j = i
    · simpa [hji] using hk
    · simpa [hji] using (ha j).symm

private def tupleMatrixAct [Fintype ι] (A : Matrix ι ι R) (f : ι → M) : ι → M :=
  fun i ↦ ∑ j, A i j • f j

private theorem tupleMatrixAct_one [Fintype ι] (f : ι → M) :
    tupleMatrixAct (1 : Matrix ι ι R) f = f := by
  funext k
  simp [tupleMatrixAct, Matrix.one_apply, ite_smul]

omit [DecidableEq ι] in
private theorem tupleMatrixAct_mul [Fintype ι] (A B : Matrix ι ι R) (f : ι → M) :
    tupleMatrixAct (A * B) f = tupleMatrixAct A (tupleMatrixAct B f) := by
  funext k
  simp_rw [tupleMatrixAct, Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]

private theorem TupleOp.matrix_act [Fintype ι] (o : TupleOp R ι) (f : ι → M) :
    tupleMatrixAct (o.matrix : Matrix ι ι R) f = o.act f := by
  have hA (k j : ι) : (o.matrix : Matrix ι ι R) k j = o.act (Pi.single j 1) k := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using
      congr_fun (o.matrix_mulVec (Pi.single j 1)) k
  funext k
  simp only [tupleMatrixAct, hA]
  cases o with
  | scale i a =>
    by_cases hk : k = i
    · simp [TupleOp.act, hk, Pi.single_apply, ite_smul]
    · simp [TupleOp.act, hk, Pi.single_apply, ite_smul]
  | swap i j hij =>
    by_cases hk : k = i <;> by_cases hk' : k = j <;>
      simp_all [TupleOp.act, Pi.single_apply, ite_smul]
  | shear i j a hij =>
    by_cases hk : k = i
    · simp [TupleOp.act, hk, Pi.single_apply, ite_smul, add_smul,
        Finset.sum_add_distrib]
    · simp [TupleOp.act, hk, Pi.single_apply, ite_smul]

private theorem tupleRun_matrix [Fintype ι] (l : List (TupleOp R ι)) (f : ι → M) :
    tupleRun l f = tupleMatrixAct
      (((l.map TupleOp.matrix).reverse.prod : Matrix.GeneralLinearGroup ι R) :
        Matrix ι ι R) f := by
  induction l generalizing f with
  | nil => exact (tupleMatrixAct_one f).symm
  | cons o l ih =>
    change tupleRun l (o.act f) = _
    rw [ih, ← o.matrix_act f, ← tupleMatrixAct_mul]
    simp only [List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton, Matrix.GeneralLinearGroup.coe_mul]

private theorem tupleRun_take_succ (l : List (TupleOp R ι)) (f : ι → M)
    (t : ℕ) (ht : t < l.length) :
    tupleRun (l.take (t + 1)) f = (l.get ⟨t, ht⟩).act (tupleRun (l.take t) f) := by
  induction l generalizing t f with
  | nil => simp at ht
  | cons o l ih =>
    cases t with
    | zero => rfl
    | succ t =>
      exact ih (o.act f) t (Nat.lt_of_succ_lt_succ ht)

end TupleHelpers


/-- Any two equal-length generating tuples over a commutative local ring differ by
finitely many unit scalings, swaps and shears, with their corresponding matrix product.

Source: Stacks Project, Algebra, Tags 00DV (`lemma-NAK`) and 00E9
(`lemma-characterize-local-ring`), agent-formulated consequence
(blueprint: lem-pur-local-generating-tuples).

Proof, following the six steps of the node:
1. Induct on `c`, uniformly for all finite modules over the fixed ring. If `c = 0`,
   generation forces the module to be zero; take no operations and the identity matrix.
   If the module is zero at any other length, the two tuples are identical as well.
2. Otherwise, Nakayama with the zero submodule (`lem-weil-pbc-nakayama-local-generators`,
   `IsLocalRing.map_mkQ_eq_top`) shows that the quotient by the maximal-ideal multiple
   is nonzero. Some target generator survives there; permute it to the first position.
3. Express this generator as a linear combination of the source tuple. One coefficient
   is outside the maximal ideal, hence a unit (`lem-weil-pbc-local-ring-unit-criterion`,
   `IsLocalRing.notMem_maximalIdeal`). Swap its source entry to the first position,
   scale it by that unit, and add the other coefficient multiples to the first entry.
   This gives a tuple whose first entry agrees with the permuted target. Each operation
   is invertible: inverse unit, the same swap, or the shear with negative coefficient.
4. Quotient by the submodule spanned by that common first entry. Both tails generate
   the quotient, making it finite (`def-weil-finitely-generated-module`). Apply induction
   to these tails of length `c - 1`; for `c = 1` this is the empty quotient-tail case.
5. Lift the tail operations to the module while fixing the first entry. The quotient
   map respects unit scaling, swaps and shears, so induction on the finite operation list
   gives the prescribed quotient tail. The differences from the target are now multiples
   of the fixed first entry. Correct them with shears from that entry to each tail entry,
   and undo the original target permutation. All concatenated operation lists are finite.
6. Record each operation's matrix: a unit diagonal matrix, a swap permutation matrix,
   or `I + a E i j` for distinct indices. Their inverses are the inverse-unit diagonal,
   the same swap, and `I - a E i j`, since `E i j` squares to zero. For chronological
   matrices `A 0, ..., A (s - 1)`, their action on column tuples is the reverse product.
   The converse reads such a product from right to left. At length zero this is the
   empty product. A finitely generated ideal is a specialization of the module statement. -/
theorem exists_elementary_generating_tuple_change
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (c : ℕ) (f g : Fin c → M)
    (hf : Submodule.span R (Set.range f) = ⊤)
    (hg : Submodule.span R (Set.range g) = ⊤) :
    ∃ (s : ℕ) (x : ℕ → Fin c → M)
      (A : Fin s → Matrix.GeneralLinearGroup (Fin c) R),
      x 0 = f ∧ x s = g ∧
      (∀ (t : ℕ) (ht : t < s),
        (∃ (i : Fin c) (u : Rˣ),
          (∀ k, x (t + 1) k = if k = i then (u : R) • x t i else x t k) ∧
          (∀ z : Fin c → R, ∀ k,
            ((A ⟨t, ht⟩ : Matrix (Fin c) (Fin c) R).mulVec z) k =
              if k = i then (u : R) * z i else z k)) ∨
        (∃ (i j : Fin c), i ≠ j ∧
          (∀ k, x (t + 1) k =
            if k = i then x t j else if k = j then x t i else x t k) ∧
          (∀ z : Fin c → R, ∀ k,
            ((A ⟨t, ht⟩ : Matrix (Fin c) (Fin c) R).mulVec z) k =
              if k = i then z j else if k = j then z i else z k)) ∨
        (∃ (i j : Fin c) (a : R), i ≠ j ∧
          (∀ k, x (t + 1) k = if k = i then x t i + a • x t j else x t k) ∧
          (∀ z : Fin c → R, ∀ k,
            ((A ⟨t, ht⟩ : Matrix (Fin c) (Fin c) R).mulVec z) k =
              if k = i then z i + a * z j else z k))) ∧
      ∃ (P : Matrix.GeneralLinearGroup (Fin c) R),
        (∀ i, g i = ∑ j : Fin c, (P : Matrix (Fin c) (Fin c) R) i j • f j) ∧
        P = (List.ofFn A).reverse.prod := by
  classical
  obtain ⟨l, hl⟩ := exists_tuple_ops (R := R) c (ι := Fin c) (by simp) f g hf hg
  let x : ℕ → Fin c → M := fun t ↦ tupleRun (l.take t) f
  let A : Fin l.length → Matrix.GeneralLinearGroup (Fin c) R := fun t ↦ (l.get t).matrix
  refine ⟨l.length, x, A, ?_, ?_, ?_, (l.map TupleOp.matrix).reverse.prod, ?_, ?_⟩
  · rfl
  · simpa only [x, List.take_length] using hl
  · intro t ht
    have hs : x (t + 1) = (l.get ⟨t, ht⟩).act (x t) := tupleRun_take_succ l f t ht
    have hm (z : Fin c → R) :
        ((A ⟨t, ht⟩ : Matrix (Fin c) (Fin c) R).mulVec z) =
          (l.get ⟨t, ht⟩).act z := (l.get ⟨t, ht⟩).matrix_mulVec z
    cases he : l.get ⟨t, ht⟩ with
    | scale i a =>
      left
      refine ⟨i, a, ?_, ?_⟩
      · intro k; exact congr_fun (he ▸ hs) k
      · intro z k; exact congr_fun (he ▸ hm z) k
    | swap i j hij =>
      right; left
      refine ⟨i, j, hij, ?_, ?_⟩
      · intro k; exact congr_fun (he ▸ hs) k
      · intro z k; exact congr_fun (he ▸ hm z) k
    | shear i j a hij =>
      right; right
      refine ⟨i, j, a, hij, ?_, ?_⟩
      · intro k; exact congr_fun (he ▸ hs) k
      · intro z k; exact congr_fun (he ▸ hm z) k
  · intro i
    exact (congr_fun hl.symm i).trans (congr_fun (tupleRun_matrix l f) i)
  · have hA : List.ofFn A = l.map TupleOp.matrix := by
      exact (List.ofFn_comp' l.get TupleOp.matrix).trans
        (congrArg (List.map TupleOp.matrix) (List.ofFn_get l))
    rw [hA]

end Module
