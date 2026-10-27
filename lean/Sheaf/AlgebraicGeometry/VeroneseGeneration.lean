/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import Mathlib.Data.PNat.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Generation of sufficiently divisible Veronese rings

Source: Stacks Project, Tag 0EGH.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace GradedAlgebra

private theorem exists_large_exponent {ι : Type*} [Fintype ι] [Nonempty ι]
    (w e : ι → ℕ) (m : ℕ) (hw : ∀ i, 0 < w i) (hm : ∀ i, w i ∣ m)
    (he : Fintype.card ι * m ≤ ∑ i, e i * w i) :
    ∃ i, m / w i ≤ e i := by
  by_contra! h
  have hlt : ∑ i, e i * w i < ∑ _i : ι, m := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    calc
      e i * w i < (m / w i) * w i := Nat.mul_lt_mul_of_pos_right (h i) (hw i)
      _ = m := Nat.div_mul_cancel (hm i)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
  omega

private theorem exists_subexponents {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℕ) (m : ℕ) (hw : ∀ i, 0 < w i) (hm : ∀ i, w i ∣ m)
    (t : ℕ) (e : ι → ℕ) (he : (t + Fintype.card ι) * m ≤ ∑ i, e i * w i) :
    ∃ b : ι → ℕ, (∀ i, b i ≤ e i) ∧ ∑ i, b i * w i = t * m := by
  classical
  induction t generalizing e with
  | zero => exact ⟨fun _ => 0, by simp, by simp⟩
  | succ t ih =>
    obtain ⟨i, hi⟩ := exists_large_exponent w e m hw hm (by nlinarith)
    let a : ι → ℕ := Pi.single i (m / w i)
    have ha : ∀ j, a j ≤ e j := by
      intro j
      by_cases hji : j = i
      · subst j; simpa [a] using hi
      · simp [a, hji]
    have hwa : ∑ j, a j * w j = m := by
      simp [a, Pi.single_apply, Nat.div_mul_cancel (hm i)]
    have hsplit : (∑ j, (e j - a j) * w j) + m = ∑ j, e j * w j := by
      rw [← hwa, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Nat.add_mul, Nat.sub_add_cancel (ha j)]
    obtain ⟨b, hb, hwb⟩ := ih (fun j => e j - a j) (by nlinarith)
    refine ⟨fun j => b j + a j, fun j => ?_, ?_⟩
    · exact (Nat.add_le_add_right (hb j) _).trans_eq (Nat.sub_add_cancel (ha j))
    · simp only [Nat.add_mul, Finset.sum_add_distrib, hwb, hwa, Nat.succ_mul]

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (𝒜 : ℕ → Submodule k R) [GradedRing 𝒜]

private theorem homogeneous_mem_subring {ι : Type*} [Fintype ι]
    (v : ι → R) (w : ι → ℕ) (hv : ∀ i, v i ∈ 𝒜 (w i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤)
    (C : Subring R) (hC : (𝒜 0 : Set R) ⊆ C) (n : ℕ)
    (hmon : ∀ e : ι → ℕ, (∑ i, e i * w i) = n → (∏ i, v i ^ e i) ∈ C)
    (x : R) (hx : x ∈ 𝒜 n) : x ∈ C := by
  have key (y : R) (hy : y ∈ Submodule.span (𝒜 0) (Submonoid.closure (Set.range v))) :
      (DirectSum.decompose 𝒜 y n : R) ∈ C := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, rfl⟩ := Submonoid.exists_of_mem_closure_range _ _ hy
      have hdeg : (∏ i, v i ^ e i) ∈ 𝒜 (∑ i, e i • w i) :=
        SetLike.prod_pow_mem_graded 𝒜 w v e (fun i _ => hv i)
      simp only [smul_eq_mul] at hdeg
      by_cases h : (∑ i, e i * w i) = n
      · rw [DirectSum.decompose_of_mem_same 𝒜 (h ▸ hdeg)]
        exact hmon e h
      · rw [DirectSum.decompose_of_mem_ne 𝒜 hdeg h]
        exact C.zero_mem
    | zero => simp
    | add a b _ _ ha hb =>
      simpa only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
        using C.add_mem ha hb
    | smul c y _ hy =>
      change (DirectSum.decompose 𝒜 ((c : R) * y) n : R) ∈ C
      rw [DirectSum.coe_decompose_mul_of_left_mem_zero 𝒜 c.2]
      exact C.mul_mem (hC c.2) hy
  have hspan : x ∈ Submodule.span (𝒜 0) (Submonoid.closure (Set.range v)) := by
    rw [← Algebra.adjoin_eq_span, hgen]
    trivial
  simpa only [DirectSum.decompose_of_mem_same 𝒜 hx] using key x hspan

private theorem monomial_mem_veronese_generators {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → R) (w : ι → ℕ) (hv : ∀ i, v i ∈ 𝒜 (w i))
    (hw : ∀ i, 0 < w i) (m : ℕ) (hm : ∀ i, w i ∣ m) (n : ℕ) (e : ι → ℕ)
    (he : (∑ i, e i * w i) = n * (Fintype.card ι * m)) :
    (∏ i, v i ^ e i) ∈
      Subring.closure ((𝒜 0 : Set R) ∪ (𝒜 (Fintype.card ι * m) : Set R)) := by
  classical
  let C := Subring.closure ((𝒜 0 : Set R) ∪ (𝒜 (Fintype.card ι * m) : Set R))
  have hdeg (b : ι → ℕ) : (∏ i, v i ^ b i) ∈ 𝒜 (∑ i, b i * w i) := by
    simpa only [smul_eq_mul] using SetLike.prod_pow_mem_graded 𝒜 w v b (fun i _ => hv i)
  induction n generalizing e with
  | zero => exact Subring.subset_closure (Or.inl (by simpa [he] using hdeg e))
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      exact Subring.subset_closure (Or.inr (by simpa [he] using hdeg e))
    obtain ⟨b, hb, hwb⟩ := exists_subexponents w m hw hm (Fintype.card ι) e (by
      rw [he]
      have htwo : 2 ≤ n + 1 := by omega
      calc
        _ = 2 * (Fintype.card ι * m) := by ring
        _ ≤ (n + 1) * (Fintype.card ι * m) := Nat.mul_le_mul_right _ htwo)
    have hrest : (∑ i, (e i - b i) * w i) = n * (Fintype.card ι * m) := by
      have hh : (∑ i, (e i - b i) * w i) + (∑ i, b i * w i) = ∑ i, e i * w i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Nat.add_mul, Nat.sub_add_cancel (hb i)]
      rw [hwb, he] at hh
      nlinarith
    have hprod : (∏ i, v i ^ e i) = (∏ i, v i ^ b i) * ∏ i, v i ^ (e i - b i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [← pow_add, Nat.add_sub_of_le (hb i)]
    rw [hprod]
    exact C.mul_mem (Subring.subset_closure (Or.inr (hwb ▸ hdeg b))) (ih _ hrest)

/-- Sufficiently divisible Veronese rings are generated in degree one over degree zero.
Source: Stacks Project, Tag 0EGH (blueprint: lem-sfb-veronese-generation).

Proof: choose finitely many positive-degree homogeneous generators, padding with zero
of degree one. Let r be their number and l the product of their positive degrees. Set
D = r*l. If d = D*c, put m = l*c. Every monomial of degree at least r*m contains
an m-degree pure-power factor, since otherwise every weighted exponent is below m.
Extract r such factors from a monomial of degree n*d, n at least two; the remainder
has degree (n-1)*d. Induction factors every monomial into degree-d monomials.
Project a polynomial expression for a homogeneous element to its degree to finish. -/
theorem exists_veronese_generators [Algebra.FiniteType (𝒜 0) R] :
    ∃ D : ℕ+, ∀ d : ℕ+, (D : ℕ) ∣ (d : ℕ) →
      ∀ (n : ℕ) (a : R), a ∈ 𝒜 (n * (d : ℕ)) →
        a ∈ Subring.closure ((𝒜 0 : Set R) ∪ (𝒜 (d : ℕ) : Set R)) := by
  classical
  obtain ⟨s, hs, hhom⟩ := exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  choose w hw hv using hhom
  let v : Option s → R := fun i => i.elim 0 Subtype.val
  let weights : Option s → ℕ := fun i => i.elim 1 (fun j => w j j.2)
  have hwpos : ∀ i, 0 < weights i := by
    intro i; cases i with
    | none => exact Nat.zero_lt_one
    | some j => exact Nat.pos_of_ne_zero (hw j j.2)
  have hvdeg : ∀ i, v i ∈ 𝒜 (weights i) := by
    intro i; cases i with
    | none => exact Submodule.zero_mem _
    | some j => exact hv j j.2
  have hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Algebra.adjoin_mono
    intro x hx
    exact ⟨some ⟨x, hx⟩, rfl⟩
  let l := ∏ i, weights i
  let r := Fintype.card (Option s)
  have hlpos : 0 < l := Finset.prod_pos (fun i _ => hwpos i)
  have hrpos : 0 < r := Fintype.card_pos
  refine ⟨⟨r * l, Nat.mul_pos hrpos hlpos⟩, ?_⟩
  intro d hd n a ha
  obtain ⟨c, hc⟩ := hd
  let m := l * c
  have hd' : (d : ℕ) = r * m := by
    change (d : ℕ) = r * l * c at hc
    dsimp [m]
    simpa only [Nat.mul_assoc] using hc
  have hm : ∀ i, weights i ∣ m := fun i =>
    dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem weights (Finset.mem_univ i)) c
  apply homogeneous_mem_subring 𝒜 v weights hvdeg hgen _
    (fun x hx => Subring.subset_closure (Or.inl hx)) (n * (d : ℕ)) ?_ a ha
  intro e he
  rw [hd']
  apply monomial_mem_veronese_generators 𝒜 v weights hvdeg hwpos m hm n e
  simpa only [hd'] using he

end GradedAlgebra
