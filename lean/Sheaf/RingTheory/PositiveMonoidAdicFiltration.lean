/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Ideal.Operations

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Choose
import Mathlib.Tactic.SplitIfs

/-!
# Positive monoid finiteness and the mixed ideal filtration

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VI §1.6(i)--(ii),
printed p. 70, for the motivating formal monoid models. The finiteness statements
and coefficient refinement are the agent-supplied argument recorded in the DAG,
not a verbatim theorem of ILO (blueprint: lem-trf-positive-monoid-adic-filtration).

The zero-variable monoid ring of `ToricMonoid.PolynomialRing` is written using its
coefficient ring `AddMonoidAlgebra A P`, so its coefficients are `F.coeff p`.
-/

@[expose] public section

universe u v

namespace AddMonoidAlgebra

private theorem weight_nonneg {G : Type u} [AddCommGroup G] {P : AddSubmonoid G}
    (wgt : G →+ ℤ) (hpos : ∀ p : P, p ≠ 0 → 0 < wgt (p : G)) (p : P) :
    0 ≤ wgt (p : G) := by
  by_cases hp : p = 0
  · simp [hp]
  · exact le_of_lt (hpos p hp)

private theorem decomposition_weight_bound {G : Type u} [AddCommGroup G]
    {P : AddSubmonoid G} (wgt : G →+ ℤ)
    (hpos : ∀ p : P, p ≠ 0 → 0 < wgt (p : G))
    {q : ℕ} (f : Fin q → P) (hf : ∀ i, f i ≠ 0) :
    (q : ℤ) ≤ wgt ((∑ i, f i : P) : G) := by
  calc
    (q : ℤ) = ∑ _i : Fin q, (1 : ℤ) := by simp
    _ ≤ ∑ i : Fin q, wgt (f i : G) :=
      Finset.sum_le_sum fun i _ ↦ hpos (f i) (hf i)
    _ = wgt ((∑ i, f i : P) : G) := by
      simp

private theorem exists_maximal_length {G : Type u} [AddCommGroup G]
    {P : AddSubmonoid G} (wgt : G →+ ℤ)
    (hpos : ∀ p : P, p ≠ 0 → 0 < wgt (p : G)) (p : P) :
    ∃ r : ℕ, IsGreatest {q : ℕ | ∃ f : Fin q → P,
      (∀ i : Fin q, f i ≠ 0) ∧ (∑ i, f i) = p} r := by
  apply BddAbove.exists_isGreatest_of_nonempty
  · refine ⟨(wgt (p : G)).toNat, ?_⟩
    rintro q ⟨f, hf, rfl⟩
    have h := decomposition_weight_bound wgt hpos f hf
    omega
  · by_cases hp : p = 0
    · refine ⟨0, fun _ ↦ 0, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · simp [hp]
    · refine ⟨1, fun _ ↦ p, fun _ ↦ hp, ?_⟩
      simp

-- The coefficient conditions form an ideal because ν increases under addition.
private def lengthCoeffIdeal {P : Type u} [AddCommMonoid P]
    (ν : P → ℕ) (hadd : ∀ a b, ν a + ν b ≤ ν (a + b))
    {A : Type v} [CommRing A] (I : Ideal A) (n : ℕ) : Ideal (AddMonoidAlgebra A P) where
  carrier := {F | ∀ p, F.coeff p ∈ I ^ (n - ν p)}
  zero_mem' := by intro p; simp
  add_mem' := by
    intro F H hF hH p
    exact (I ^ (n - ν p)).add_mem (hF p) (hH p)
  smul_mem' := by
    classical
    intro H F hF p
    change (H * F).coeff p ∈ I ^ (n - ν p)
    simp only [coeff_mul, Finsupp.sum]
    apply Ideal.sum_mem
    intro a _
    apply Ideal.sum_mem
    intro b _
    split_ifs with hab
    · subst p
      have hle : ν b ≤ ν (a + b) := (Nat.le_add_left _ _).trans (hadd a b)
      exact Ideal.pow_le_pow_right (Nat.sub_le_sub_left hle n)
        ((I ^ (n - ν b)).mul_mem_left _ (hF b))
    · exact Ideal.zero_mem _

private theorem lengthCoeffIdeal_mul {P : Type u} [AddCommMonoid P]
    (ν : P → ℕ) (hadd : ∀ a b, ν a + ν b ≤ ν (a + b))
    {A : Type v} [CommRing A] (I : Ideal A) (m n : ℕ) :
    lengthCoeffIdeal ν hadd I m * lengthCoeffIdeal ν hadd I n ≤
      lengthCoeffIdeal ν hadd I (m + n) := by
  classical
  apply Ideal.mul_le.2
  intro F hF H hH p
  simp only [coeff_mul, Finsupp.sum]
  apply Ideal.sum_mem
  intro a _
  apply Ideal.sum_mem
  intro b _
  split_ifs with hab
  · subst p
    have hle : m + n - ν (a + b) ≤ (m - ν a) + (n - ν b) := by
      have := hadd a b
      omega
    apply Ideal.pow_le_pow_right hle
    rw [pow_add]
    exact Ideal.mul_mem_mul (hF a) (hH b)
  · exact Ideal.zero_mem _

private theorem mixed_ideal_filtration {P : Type u} [AddCommMonoid P]
    (ν : P → ℕ)
    (hν : ∀ p, IsGreatest {q : ℕ | ∃ f : Fin q → P,
      (∀ i : Fin q, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p))
    (hzero : ν 0 = 0) (hadd : ∀ a b, ν a + ν b ≤ ν (a + b))
    (A : Type v) [CommRing A] (I : Ideal A) (n : ℕ) (F : AddMonoidAlgebra A P) :
    F ∈ (Ideal.span
      ({f : AddMonoidAlgebra A P | ∃ a : A, a ∈ I ∧ f = single 0 a} ∪
        {f : AddMonoidAlgebra A P | ∃ p : P, p ≠ 0 ∧ f = single p (1 : A)})) ^ n ↔
      ∀ p : P, F.coeff p ∈ I ^ (n - ν p) := by
  classical
  let J : Ideal (AddMonoidAlgebra A P) := Ideal.span
    ({f : AddMonoidAlgebra A P | ∃ a : A, a ∈ I ∧ f = single 0 a} ∪
      {f : AddMonoidAlgebra A P | ∃ p : P, p ≠ 0 ∧ f = single p (1 : A)})
  have hcoeff (a : A) (ha : a ∈ I) : single (0 : P) a ∈ J :=
    Ideal.subset_span (Or.inl ⟨a, ha, rfl⟩)
  have hmon (p : P) (hp : p ≠ 0) : single p (1 : A) ∈ J :=
    Ideal.subset_span (Or.inr ⟨p, hp, rfl⟩)
  have hnonzero (p : P) (hp : p ≠ 0) : 1 ≤ ν p := by
    apply (hν p).2
    exact ⟨fun _ ↦ p, fun _ ↦ hp, by simp⟩
  have hbase : J ≤ lengthCoeffIdeal ν hadd I 1 := by
    apply Ideal.span_le.2
    rintro _ (⟨a, ha, rfl⟩ | ⟨p, hp, rfl⟩) q
    · by_cases hq : q = 0
      · subst q
        simpa [hzero] using ha
      · simp [hq]
    · by_cases hq : q = p
      · subst q
        simp [Nat.sub_eq_zero_of_le (hnonzero p hp)]
      · simp [hq]
  have hforward (k : ℕ) : J ^ k ≤ lengthCoeffIdeal ν hadd I k := by
    induction k with
    | zero => intro H _ q; simp
    | succ k ih =>
      rw [pow_succ]
      exact (mul_le_mul' ih hbase).trans (lengthCoeffIdeal_mul ν hadd I k 1)
  -- The coefficient and exponent factors give the reverse inclusion separately.
  have hconstant (k : ℕ) (a : A) (ha : a ∈ I ^ k) : single (0 : P) a ∈ J ^ k := by
    have hmap : Ideal.map (singleZeroRingHom : A →+* AddMonoidAlgebra A P) I ≤ J := by
      apply Ideal.map_le_iff_le_comap.2
      intro a ha
      exact hcoeff a ha
    have hmem := Ideal.mem_map_of_mem (singleZeroRingHom : A →+* AddMonoidAlgebra A P) ha
    rw [Ideal.map_pow] at hmem
    exact (pow_le_pow_left' hmap k) hmem
  have hdecomp (p : P) : single p (1 : A) ∈ J ^ ν p := by
    obtain ⟨f, hf, hsum⟩ := (hν p).1
    have hprod : (∏ i : Fin (ν p), single (f i) (1 : A)) ∈
        ∏ _i : Fin (ν p), J := Ideal.prod_mem_prod (fun i _ ↦ hmon (f i) (hf i))
    simpa [hsum] using hprod
  change F ∈ J ^ n ↔ _
  constructor
  · exact fun hF ↦ hforward n hF
  · intro hF
    rw [← sum_coeff_single F, Finsupp.sum]
    apply Ideal.sum_mem
    intro p _
    have hterm := Ideal.mul_mem_mul (hconstant (n - ν p) (F.coeff p) (hF p))
      (hdecomp p)
    rw [← pow_add] at hterm
    apply Ideal.pow_le_pow_right (show n ≤ (n - ν p) + ν p by omega)
    simpa using hterm

open Classical in
/-- Maximal decomposition lengths, finite sublevel sets, and the coefficient
criterion for powers of the ideal generated by `I z^0` and all nonzero monomials.

Source: ILO, Exposé VI §1.6(i)--(ii), printed p. 70, motivates the formal monoid
models; the elementary coefficient refinement is supplied by the DAG
(blueprint: lem-trf-positive-monoid-adic-filtration).

`IsGreatest` includes attainment by a tuple of nonzero summands, with the empty
`Fin 0` sum equal to zero. Natural subtraction in the exponent `n - ν p` is exactly
`max (n - ν(p), 0)`. Ideal powers are Mathlib's ordinary algebraic ideal powers,
including `I ^ 0 = ⊤`. The ambient abelian group need not be free or finitely generated,
and the coefficient ring need not be local or Noetherian.

Proof plan:
1. Each nonzero summand has integral weight at least one, so every decomposition
   length of `p` is at most `wgt p`. The empty tuple at zero and the singleton at a
   nonzero exponent show that the set of lengths is nonempty, hence has a maximum.
   Only the empty tuple sums to zero. Concatenating maximal tuples proves
   superadditivity of their lengths.
2. Delete zero from a finite set of generators of `P`. In a generator expression
   of weight at most `M`, every multiplicity is at most `M`. The finite box of such
   multiplicities surjects onto the weight sublevel set. An empty generator set
   gives the zero monoid and a one-element box.
3. In a tuple with sum `p`, each summand has nonnegative weight bounded by `wgt p`.
   The tuples lie in a finite Cartesian power of a weight sublevel set. If `ν p < n`,
   every generator expression has total length less than `n`, so its multiplicities
   lie in another finite box. This proves finiteness of the length sublevel set.
4. For `J` the span of the displayed generators, induction and finite distributivity
   show that `J ^ n` consists of finite sums `H t₁ ... tₙ` with each `tᵢ` a generator.
   For `n = 0`, the empty product gives the whole ring. In the induction step expand
   products of finite sums representing members of `J ^ n` and `J`.
5. Expand each polynomial multiplier into its finitely many monomials. A term with
   `k` nonzero monomial factors has exponent `p` with `ν p ≥ k`; include the multiplier
   exponent as an extra nonzero summand when necessary. Its coefficient is in
   `I ^ (n - k)`, hence in `I ^ (n - ν p)`. Summing proves the forward implication,
   including coefficients outside the finite support, which are zero.
6. Conversely fix an exponent in the finite support of `F`. If `r = ν p < n`, use an
   attained length-`r` decomposition and express its coefficient as a finite sum of
   products of `n - r` elements of `I`. Ring multipliers can be absorbed into the
   first factor because `n - r ≥ 1`. Each monomial is thus a sum of products of `n`
   generators of `J`. If `r ≥ n`, group a maximal decomposition into `n` nonempty
   blocks. Their sums are nonzero by positive weight, so the monomial itself is a
   product of `n` generators. At `r = 0`, the exponent is zero and the monomial
   product is empty. Finally sum over the finite support of `F`.
-/
theorem positiveMonoid_adic_filtration
    (G : Type u) [AddCommGroup G] (P : AddSubmonoid G) (hfg : P.FG)
    (wgt : G →+ ℤ) (hpos : ∀ p : P, p ≠ 0 → 0 < wgt (p : G)) :
    ∃ ν : P → ℕ,
      (∀ p : P, IsGreatest {q : ℕ | ∃ f : Fin q → P,
        (∀ i : Fin q, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p)) ∧
      ν 0 = 0 ∧
      (∀ p : P, (ν p : ℤ) ≤ wgt (p : G)) ∧
      (∀ a b : P, ν a + ν b ≤ ν (a + b)) ∧
      (∀ M : ℤ, 0 ≤ M → Set.Finite {p : P | wgt (p : G) ≤ M}) ∧
      (∀ (p : P) (k : ℕ), 1 ≤ k →
        Set.Finite {f : Fin k → P | (∑ i, f i) = p}) ∧
      (∀ n : ℕ, 1 ≤ n → Set.Finite {p : P | ν p < n}) ∧
      ∀ (A : Type v) [CommRing A] (I : Ideal A) (n : ℕ), 1 ≤ n →
        ∀ F : AddMonoidAlgebra A P,
          F ∈ (Ideal.span
            ({f : AddMonoidAlgebra A P | ∃ a : A, a ∈ I ∧ f = single 0 a} ∪
              {f : AddMonoidAlgebra A P | ∃ p : P, p ≠ 0 ∧ f = single p (1 : A)})) ^ n ↔
            ∀ p : P, F.coeff p ∈ I ^ (n - ν p) := by
  classical
  choose ν hν using exists_maximal_length wgt hpos
  have hbound (p : P) : (ν p : ℤ) ≤ wgt (p : G) := by
    obtain ⟨f, hf, hsum⟩ := (hν p).1
    simpa [hsum] using decomposition_weight_bound wgt hpos f hf
  have hzero : ν 0 = 0 := by
    have h := hbound 0
    simp only [ZeroMemClass.coe_zero, map_zero] at h
    omega
  have hadd (a b : P) : ν a + ν b ≤ ν (a + b) := by
    obtain ⟨f, hf, hfsum⟩ := (hν a).1
    obtain ⟨g, hg, hgsum⟩ := (hν b).1
    apply (hν (a + b)).2
    refine ⟨Fin.append f g, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simpa using hf j
      · simpa using hg j
    · rw [Fin.sum_univ_add]
      simpa using congrArg₂ (· + ·) hfsum hgsum
  have : AddMonoid.FG P := (AddMonoid.fg_iff_addSubmonoid_fg P).2 hfg
  obtain ⟨s, hs⟩ := (inferInstance : AddMonoid.FG P).fg_top
  let S := s.erase (0 : P)
  have hS : AddSubmonoid.closure (S : Set P) = ⊤ := by
    simpa [S, Finset.coe_erase, AddSubmonoid.closure_sdiff_singleton_zero] using hs
  have hexpr (p : P) : ∃ l : List S, (l.map Subtype.val).sum = p := by
    have hp : p ∈ AddSubmonoid.closure (S : Set P) := by rw [hS]; trivial
    induction hp using AddSubmonoid.closure_induction with
    | mem x hx => exact ⟨[⟨x, hx⟩], by simp⟩
    | zero => exact ⟨[], rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨k, rfl⟩ := hy
      exact ⟨l ++ k, by simp⟩
  have hlist (l : List S) : ∃ f : Fin l.length → P,
      (∀ i, f i ≠ 0) ∧ (∑ i, f i) = (l.map Subtype.val).sum := by
    refine ⟨fun i ↦ (l.get i).val, ?_, ?_⟩
    · intro i
      exact Finset.ne_of_mem_erase (l.get i).prop
    · exact Fin.sum_univ_fun_getElem l Subtype.val
  have hweightfinite (M : ℤ) (hM : 0 ≤ M) :
      Set.Finite {p : P | wgt (p : G) ≤ M} := by
    apply ((List.finite_length_le S M.toNat).image
      (fun l : List S ↦ (l.map Subtype.val).sum)).subset
    intro p hp
    obtain ⟨l, hl⟩ := hexpr p
    refine ⟨l, ?_, hl⟩
    obtain ⟨f, hf, hsum⟩ := hlist l
    have hb := decomposition_weight_bound wgt hpos f hf
    rw [hsum, hl] at hb
    dsimp at hp ⊢
    omega
  have htuplefinite (p : P) (k : ℕ) (_hk : 1 ≤ k) :
      Set.Finite {f : Fin k → P | (∑ i, f i) = p} := by
    have hf := hweightfinite (wgt (p : G)) (weight_nonneg wgt hpos p)
    apply (Set.Finite.pi (fun _ : Fin k ↦ hf)).subset
    intro f hsum i _
    change (∑ j, f j) = p at hsum
    change wgt (f i : G) ≤ wgt (p : G)
    calc
      wgt (f i : G) ≤ ∑ j : Fin k, wgt (f j : G) :=
        Finset.single_le_sum (fun j _ ↦ weight_nonneg wgt hpos (f j)) (Finset.mem_univ i)
      _ = wgt (p : G) := by
        rw [← hsum]
        simp
  have hlengthfinite (n : ℕ) (_hn : 1 ≤ n) : Set.Finite {p : P | ν p < n} := by
    apply ((List.finite_length_lt S n).image
      (fun l : List S ↦ (l.map Subtype.val).sum)).subset
    intro p hp
    obtain ⟨l, hl⟩ := hexpr p
    refine ⟨l, ?_, hl⟩
    obtain ⟨f, hf, hsum⟩ := hlist l
    have hb := (hν p).2 ⟨f, hf, hsum.trans hl⟩
    exact lt_of_le_of_lt hb hp
  refine ⟨ν, hν, hzero, hbound, hadd, hweightfinite, htuplefinite, hlengthfinite, ?_⟩
  intro A _ I n _hn F
  exact mixed_ideal_filtration ν hν hzero hadd A I n F

end AddMonoidAlgebra
