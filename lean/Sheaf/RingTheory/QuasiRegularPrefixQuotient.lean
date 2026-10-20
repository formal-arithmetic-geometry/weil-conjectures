/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Polynomial associated graded algebras after a prefix quotient

Source: Stacks Project, Algebra, Tags 061R (lemma-truncate-quasi-regular),
061P and 061N, specialized to the ring as its own module
(blueprint: lem-pur-quasi-regular-prefix-quotient).

Polynomial evaluation sends variables to degree-one initial forms and coefficients
into degree zero. Thus bijectivity expresses that this canonical graded algebra
map is an isomorphism. The coefficient identification in the conclusion is specified
on every representative in the original ring.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

/-- The ideal of the first `i` generators, using zero-based indices. Source: Stacks,
Algebra, Tag 061R (blueprint: lem-pur-quasi-regular-prefix-quotient). -/
def quasiRegularPrefixIdeal {A : Type u} [CommRing A] {b : ℕ}
    (f : Fin b → A) (i : ℕ) : Ideal A :=
  Ideal.span (f '' {j : Fin b | j.val < i})

/-- The remaining generators in the quotient by the prefix. Source: Stacks,
Algebra, Tag 061R (blueprint: lem-pur-quasi-regular-prefix-quotient).
The subtype keeps precisely the original indices of the remaining variables. -/
def quasiRegularQuotientTail {A : Type u} [CommRing A] {b : ℕ}
    (f : Fin b → A) (i : ℕ) : {j : Fin b // i ≤ j.val} → A ⧸ quasiRegularPrefixIdeal f i :=
  fun j ↦ Ideal.Quotient.mk (quasiRegularPrefixIdeal f i) (f j.val)

-- The following coefficient calculations generalize the private calculations in
-- `RegularSequenceGradedPolynomial` from `Fin c` to arbitrary variable types. The tail
-- index is a subtype, so those private `Fin c` calculations cannot be invoked here.
private noncomputable def prefixPolynomialMap {R : Type u} [CommRing R]
    {σ : Type*} (f : σ → R) :
    MvPolynomial σ (R ⧸ Ideal.span (Set.range f)) →ₐ[R ⧸ Ideal.span (Set.range f)]
      associatedGraded (Ideal.span (Set.range f)) :=
  MvPolynomial.aeval (fun j ↦ DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) 1
    (Submodule.Quotient.mk
      (⟨f j, by simpa using Ideal.subset_span (Set.mem_range_self j)⟩ :
        (Ideal.span (Set.range f) ^ 1 : Ideal R))))

set_option backward.isDefEq.respectTransparency false in
private theorem monomial_class {R : Type u} [CommRing R] {σ : Type*} (f : σ → R)
    (d : σ →₀ ℕ) :
    ∃ x : (Ideal.span (Set.range f) ^ d.degree : Ideal R),
      x.val = d.prod (fun j k ↦ f j ^ k) ∧
      prefixPolynomialMap f (MvPolynomial.monomial d 1) =
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) d.degree
          (Submodule.Quotient.mk x) := by
  classical
  let J := Ideal.span (Set.range f)
  let P := fun d : σ →₀ ℕ ↦
    ∃ x : (J ^ d.degree : Ideal R),
      x.val = d.prod (fun j k ↦ f j ^ k) ∧
      prefixPolynomialMap f (MvPolynomial.monomial d 1) =
        DirectSum.of (associatedGradedPiece J) d.degree (Submodule.Quotient.mk x)
  have hzero : P 0 := by
    refine ⟨⟨1, by simp⟩, by simp, ?_⟩
    change prefixPolynomialMap f 1 = _
    rw [map_one]
    exact associatedGraded_one J
  have hadd (d e : σ →₀ ℕ) (hd : P d) (he : P e) : P (d + e) := by
    obtain ⟨x, hx, hx'⟩ := hd
    obtain ⟨y, hy, hy'⟩ := he
    dsimp only [P]
    rw [Finsupp.degree.map_add]
    refine ⟨⟨x.val * y.val, by simpa [pow_add] using Ideal.mul_mem_mul x.property y.property⟩,
      ?_, ?_⟩
    · change x.val * y.val = _
      rw [hx, hy, Finsupp.prod_add_index]
      · intro a ha; simp
      · intro a ha b₁ b₂; exact pow_add _ _ _
    · rw [← one_mul (1 : R ⧸ J), ← MvPolynomial.monomial_mul, map_mul, hx', hy']
      exact associatedGraded_mul J _ _ x y
  have hsingle (j : σ) : P (Finsupp.single j 1) := by
    dsimp only [P]
    rw [Finsupp.degree_single]
    refine ⟨⟨f j, by simpa using Ideal.subset_span (Set.mem_range_self j)⟩,
      by simp, ?_⟩
    change prefixPolynomialMap f (MvPolynomial.X j) = _
    exact MvPolynomial.aeval_X (R := R ⧸ J) (S₁ := associatedGraded J) _ j
  change P d
  induction d using Finsupp.induction_linear with
  | zero => exact hzero
  | add d e hd he => exact hadd d e hd he
  | single j k =>
    induction k with
    | zero => simpa using hzero
    | succ k hk =>
      simpa only [Finsupp.single_add] using hadd _ _ hk (hsingle j)

set_option backward.isDefEq.respectTransparency false in
private theorem coeff_monomial_class {R : Type u} [CommRing R] {σ : Type*} (f : σ → R)
    (d : σ →₀ ℕ) (r : R) :
    ∃ x : (Ideal.span (Set.range f) ^ d.degree : Ideal R),
      x.val = r * d.prod (fun j k ↦ f j ^ k) ∧
      prefixPolynomialMap f
          (MvPolynomial.monomial d (Ideal.Quotient.mk (Ideal.span (Set.range f)) r)) =
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) d.degree
          (Submodule.Quotient.mk x) := by
  obtain ⟨x, hx, hx'⟩ := monomial_class f d
  refine ⟨⟨r * x.val, Ideal.mul_mem_left _ r x.property⟩, by dsimp only; rw [hx], ?_⟩
  have hm : MvPolynomial.monomial d (Ideal.Quotient.mk (Ideal.span (Set.range f)) r) =
      Ideal.Quotient.mk (Ideal.span (Set.range f)) r • MvPolynomial.monomial d 1 := by
    simpa only [smul_eq_mul, mul_one] using
      ((MvPolynomial.monomial d).map_smul
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) r) 1)
  rw [hm, map_smul, hx']
  exact associatedGraded_smul _ _ _ x

set_option backward.isDefEq.respectTransparency false in
private theorem homogeneous_class {R : Type u} [CommRing R] {σ : Type*} (f : σ → R)
    (n : ℕ) (p : MvPolynomial σ R) (hp : p.IsHomogeneous n) :
    ∃ x : (Ideal.span (Set.range f) ^ n : Ideal R),
      x.val = p.eval f ∧
      prefixPolynomialMap f
          (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span (Set.range f))) p) =
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n
          (Submodule.Quotient.mk x) := by
  classical
  let J := Ideal.span (Set.range f)
  have hd (d : p.support) : Finsupp.degree d.val = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hp (MvPolynomial.mem_support_iff.mp d.property)
  have hmon (d : p.support) :
      ∃ x : (J ^ n : Ideal R),
        x.val = p.coeff d.val * d.val.prod (fun j k ↦ f j ^ k) ∧
        prefixPolynomialMap f
            (MvPolynomial.monomial d.val (Ideal.Quotient.mk J (p.coeff d.val))) =
          DirectSum.of (associatedGradedPiece J) n (Submodule.Quotient.mk x) := by
    have h := coeff_monomial_class f d.val (p.coeff d.val)
    rw [hd d] at h
    exact h
  choose x hx hx' using hmon
  refine ⟨∑ d : p.support, x d, ?_, ?_⟩
  · simp only [Submodule.coe_sum, hx]
    conv_rhs => rw [p.as_sum, map_sum]
    simp only [MvPolynomial.eval_monomial]
    exact Finset.sum_coe_sort p.support (fun d ↦ p.coeff d * d.prod (fun j k ↦ f j ^ k))
  · conv_lhs => rw [p.as_sum, map_sum, map_sum]
    simp only [MvPolynomial.map_monomial]
    rw [← Finset.sum_coe_sort p.support]
    simp only [map_sum, ← Submodule.mkQ_apply]
    apply Finset.sum_congr rfl
    intro d hd
    exact hx' d

set_option backward.isDefEq.respectTransparency false in
private theorem homogeneous_lift {R : Type u} [CommRing R] {σ : Type*} (f : σ → R)
    (n : ℕ) (p : MvPolynomial σ (R ⧸ Ideal.span (Set.range f)))
    (hp : p.IsHomogeneous n) :
    ∃ q : MvPolynomial σ R, q.IsHomogeneous n ∧
      MvPolynomial.map (Ideal.Quotient.mk (Ideal.span (Set.range f))) q = p := by
  obtain ⟨q, hq⟩ := MvPolynomial.map_surjective _ (Ideal.Quotient.mk_surjective) p
  refine ⟨MvPolynomial.homogeneousComponent n q,
    MvPolynomial.homogeneousComponent_isHomogeneous _ _, ?_⟩
  ext d
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
  split_ifs with h
  · simpa only [MvPolynomial.coeff_map] using congrArg (MvPolynomial.coeff d) hq
  · rw [map_zero]
    exact (hp.coeff_eq_zero h).symm

set_option backward.isDefEq.respectTransparency false in
private theorem component_map {R : Type u} [CommRing R] {σ : Type*} (f : σ → R)
    (n : ℕ) (p : MvPolynomial σ (R ⧸ Ideal.span (Set.range f))) :
    prefixPolynomialMap f (MvPolynomial.homogeneousComponent n p) =
      DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n
        (prefixPolynomialMap f p n) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d b =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨x, hx, hx'⟩ := coeff_monomial_class f d r
    rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial _ rfl)]
    by_cases h : n = d.degree
    · subst n
      simp only [ite_true, hx', DirectSum.of_eq_same]
    · simp only [if_neg h, map_zero, hx', DirectSum.of_eq_of_ne _ _ _ h]
  | add p q hp hq =>
    simp only [map_add, DirectSum.add_apply, hp, hq]

set_option backward.isDefEq.respectTransparency false in
private theorem homogeneous_kernel {R : Type u} [CommRing R] {σ : Type*} (f : σ → R)
    (hrel : ∀ (n : ℕ) (p : MvPolynomial σ R), p.IsHomogeneous n →
      p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) →
        ∀ d, p.coeff d ∈ Ideal.span (Set.range f))
    (n : ℕ) (p : MvPolynomial σ (R ⧸ Ideal.span (Set.range f)))
    (hp : p.IsHomogeneous n) (hz : prefixPolynomialMap f p = 0) : p = 0 := by
  obtain ⟨q, hq, hqp⟩ := homogeneous_lift f n p hp
  obtain ⟨x, hx, hx'⟩ := homogeneous_class f n q hq
  have hzero : Submodule.Quotient.mk x =
      (0 : associatedGradedPiece (Ideal.span (Set.range f)) n) := by
    apply DirectSum.of_injective n
    simpa only [hqp, hz, map_zero] using hx'.symm
  have hmem : q.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) := by
    rw [← hx]
    exact (Submodule.Quotient.mk_eq_zero
      (Submodule.comap (Ideal.span (Set.range f) ^ n : Ideal R).subtype
        (Ideal.span (Set.range f) ^ (n + 1)))).mp hzero
  rw [← hqp]
  ext d
  simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] using
    Ideal.Quotient.eq_zero_iff_mem.mpr (hrel n q hq hmem d)

set_option backward.isDefEq.respectTransparency false in
private theorem bijective_of_relation {R : Type u} [CommRing R] {σ : Type*} (f : σ → R)
    (hrel : ∀ (n : ℕ) (p : MvPolynomial σ R), p.IsHomogeneous n →
      p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) →
        ∀ d, p.coeff d ∈ Ideal.span (Set.range f)) :
    Function.Bijective (prefixPolynomialMap f) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro p hp
    have hc (n : ℕ) : MvPolynomial.homogeneousComponent n p = 0 := by
      apply homogeneous_kernel f hrel n _ (MvPolynomial.homogeneousComponent_isHomogeneous _ _)
      rw [component_map, hp]
      simp
    rw [← MvPolynomial.sum_homogeneousComponent p]
    simp only [hc, Finset.sum_const_zero]
  · intro y
    induction y using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | of n y =>
      induction y using Submodule.Quotient.induction_on with
      | _ x =>
        obtain ⟨p, hp, hpx⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f x.val).mp x.property
        obtain ⟨z, hz, hz'⟩ := homogeneous_class f n p hp
        have he : z = x := Subtype.ext (hz.trans hpx)
        exact ⟨MvPolynomial.map (Ideal.Quotient.mk _) p, by simpa only [he] using hz'⟩
    | add x y hx hy =>
      obtain ⟨p, rfl⟩ := hx
      obtain ⟨q, rfl⟩ := hy
      exact ⟨p + q, map_add _ _ _⟩

-- Injectivity of the graded map is the homogeneous coefficient-relation criterion.
private theorem relation_of_injective {R : Type u} [CommRing R] {σ : Type*}
    (f : σ → R) (hinj : Function.Injective (prefixPolynomialMap f))
    (n : ℕ) (p : MvPolynomial σ R) (hp : p.IsHomogeneous n)
    (hm : p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1)) :
    ∀ d, p.coeff d ∈ Ideal.span (Set.range f) := by
  obtain ⟨x, hx, he⟩ := homogeneous_class f n p hp
  have hz : prefixPolynomialMap f (MvPolynomial.map (Ideal.Quotient.mk _) p) = 0 := by
    rw [he]
    have hxz : (Submodule.Quotient.mk x :
        associatedGradedPiece (Ideal.span (Set.range f)) n) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change x.val ∈ Ideal.span (Set.range f) ^ (n + 1)
      rwa [hx]
    rw [hxz, map_zero]
  have hzero := hinj (hz.trans (map_zero _).symm)
  intro d
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] using
    congrArg (MvPolynomial.coeff d) hzero

private theorem raise_homogeneous {R : Type u} [CommRing R] {σ : Type*}
    [Finite σ] (f : σ → R) (n : ℕ) (p : MvPolynomial σ R)
    (hp : p.IsHomogeneous n) (hc : ∀ d, p.coeff d ∈ Ideal.span (Set.range f)) :
    ∃ q : MvPolynomial σ R, q.IsHomogeneous (n + 1) ∧ q.eval f = p.eval f := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  have hrep (d : p.support) : ∃ a : σ → R, ∑ i, a i * f i = p.coeff d.val :=
    Ideal.mem_span_range_iff_exists_fun.mp (hc d.val)
  choose a ha using hrep
  let q : MvPolynomial σ R :=
    ∑ d : p.support, ∑ i : σ, MvPolynomial.monomial d.val (a d i) * MvPolynomial.X i
  refine ⟨q, ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro d hd
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    have hdeg : d.val.sum (fun _ k ↦ k) = n := by
      change d.val.degree = n
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
        hp (MvPolynomial.mem_support_iff.mp d.property)
    exact (MvPolynomial.isHomogeneous_monomial _ hdeg).mul (MvPolynomial.isHomogeneous_X R i)
  · dsimp only [q]
    rw [map_sum]
    simp only [map_sum, map_mul, MvPolynomial.eval_monomial, MvPolynomial.eval_X]
    conv_rhs => rw [p.as_sum, map_sum]
    simp only [MvPolynomial.eval_monomial]
    rw [← Finset.sum_coe_sort p.support]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← ha d, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring

-- This induction is the finite filtration argument of Stacks 061R; it uses no
-- separatedness. Raising a homogeneous polynomial with coefficients in J moves its
-- evaluation from J^n into J^(n+1).
set_option backward.isDefEq.respectTransparency false in
private theorem mul_generator_strict {R : Type u} [CommRing R] {σ : Type*}
    [Finite σ] (f : σ → R) (hinj : Function.Injective (prefixPolynomialMap f))
    (j : σ) (n : ℕ) (y : R) (hm : f j * y ∈ Ideal.span (Set.range f) ^ (n + 1)) :
    y ∈ Ideal.span (Set.range f) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hy : y ∈ Ideal.span (Set.range f) ^ n :=
      ih (Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + 1 + 1) hm)
    obtain ⟨p, hp, he⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f y).mp hy
    have hh := relation_of_injective f hinj (n + 1) (MvPolynomial.X j * p)
      (by simpa only [Nat.add_comm] using (MvPolynomial.isHomogeneous_X R j).mul hp) (by
        simpa only [map_mul, MvPolynomial.eval_X, he, Nat.add_comm] using hm)
    have hc (d : σ →₀ ℕ) : p.coeff d ∈ Ideal.span (Set.range f) := by
      have hd := hh (Finsupp.single j 1 + d)
      rw [MvPolynomial.coeff_X_mul] at hd
      exact hd
    obtain ⟨q, hq, heq⟩ := raise_homogeneous f n p hp hc
    exact (Ideal.mem_span_pow_iff_exists_isHomogeneous f y).mpr ⟨q, hq, heq.trans he⟩

set_option backward.isDefEq.respectTransparency false in
private theorem relation_of_zero_relation {R : Type u} [CommRing R] {σ : Type*} (f : σ → R)
    (hz : ∀ (n : ℕ) (p : MvPolynomial σ R), p.IsHomogeneous n →
      p.eval f = 0 → ∀ d, p.coeff d ∈ Ideal.span (Set.range f))
    (n : ℕ) (p : MvPolynomial σ R) (hp : p.IsHomogeneous n)
    (hmem : p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1)) :
    ∀ d, p.coeff d ∈ Ideal.span (Set.range f) := by
  classical
  let J := Ideal.span (Set.range f)
  have hrep : ∀ y ∈ J ^ (n + 1), ∃ q : MvPolynomial σ R,
      q.IsHomogeneous n ∧ q.eval f = y ∧ ∀ d, q.coeff d ∈ J := by
    intro y hy
    rw [pow_succ', ← Ideal.smul_eq_mul] at hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨q, hq, he⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f b).mp hb
      refine ⟨MvPolynomial.C a * q, hq.C_mul a, ?_, ?_⟩
      · simp only [map_mul, MvPolynomial.eval_C, he, smul_eq_mul]
      · intro d
        rw [MvPolynomial.coeff_C_mul]
        exact J.mul_mem_right _ ha
    · intro x y hx hy
      obtain ⟨p, hp, he, hc⟩ := hx
      obtain ⟨q, hq, hf, hd⟩ := hy
      exact ⟨p + q, hp.add hq, by rw [map_add, he, hf],
        fun d ↦ by rw [MvPolynomial.coeff_add]; exact J.add_mem (hc d) (hd d)⟩
  obtain ⟨q, hq, he, hc⟩ := hrep _ hmem
  have hh := hz n (p - q) (hp.sub hq) (by rw [map_sub, he, sub_self])
  intro d
  have hd : p.coeff d - q.coeff d ∈ J := by
    simpa only [MvPolynomial.coeff_sub] using hh d
  simpa only [sub_add_cancel] using J.add_mem hd (hc d)

-- A homogeneous zero relation in the quotient lifts to H(f) = f_j*y. The strict
-- filtration lemma lifts y in degree n-1. Subtract X_j*Q and compare coefficients
-- at monomials not containing j. Degree zero is handled separately.
set_option backward.isDefEq.respectTransparency false in
private theorem quotient_one {R S : Type u} [CommRing R] [CommRing S]
    {σ : Type*} {τ : Type*} [Finite σ] (f : σ → R) (g : τ → S)
    (q : R →+* S) (hq : Function.Surjective q) (j : σ)
    (ι : τ → σ) (hι : Function.Injective ι) (hne : ∀ k, ι k ≠ j)
    (hker : RingHom.ker q = Ideal.span {f j})
    (hg : ∀ k, q (f (ι k)) = g k)
    (hmap : (Ideal.span (Set.range f)).map q = Ideal.span (Set.range g))
    (hinj : Function.Injective (prefixPolynomialMap f)) :
    Function.Bijective (prefixPolynomialMap g) := by
  classical
  apply bijective_of_relation g
  apply relation_of_zero_relation g
  intro n p hp hz d
  obtain ⟨P, hP⟩ := MvPolynomial.map_surjective q hq p
  let Pn := MvPolynomial.homogeneousComponent n P
  have hPh : Pn.IsHomogeneous n := MvPolynomial.homogeneousComponent_isHomogeneous _ _
  have hPn : MvPolynomial.map q Pn = p := by
    ext e
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
    split_ifs with he
    · simpa only [MvPolynomial.coeff_map] using congrArg (MvPolynomial.coeff e) hP
    · rw [map_zero]
      exact (hp.coeff_eq_zero he).symm
  let H := MvPolynomial.rename ι Pn
  have hH : H.IsHomogeneous n := hPh.rename_isHomogeneous
  have heval : q (H.eval f) = 0 := by
    rw [MvPolynomial.map_eval, show q ∘ f = fun k ↦ q (f k) from rfl]
    dsimp only [H]
    rw [MvPolynomial.map_rename, MvPolynomial.eval_rename]
    simpa only [Function.comp_def, hg, hPn] using hz
  have hmker : H.eval f ∈ Ideal.span {f j} := by
    rw [← hker]
    exact heval
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmker
  have hc : H.coeff (d.mapDomain ι) ∈ Ideal.span (Set.range f) := by
    cases n with
    | zero =>
      apply relation_of_injective f hinj 0 H hH
      simpa only [Nat.zero_add, pow_one] using
        (((Ideal.span_singleton_le_iff_mem _).mpr
          (Ideal.subset_span (Set.mem_range_self j))) hmker)
    | succ n =>
      have hmul : f j * y ∈ Ideal.span (Set.range f) ^ (n + 1) := by
        rw [mul_comm, hy]
        exact (Ideal.mem_span_pow_iff_exists_isHomogeneous f _).mpr ⟨H, hH, rfl⟩
      have hyJ := mul_generator_strict f hinj j n y hmul
      obtain ⟨Q, hQ, heQ⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous f y).mp hyJ
      have hhom : (H - MvPolynomial.X j * Q).IsHomogeneous (n + 1) :=
        hH.sub (by simpa only [Nat.add_comm] using (MvPolynomial.isHomogeneous_X R j).mul hQ)
      have hzero : (H - MvPolynomial.X j * Q).eval f = 0 := by
        simp only [map_sub, map_mul, MvPolynomial.eval_X, heQ, ← hy]
        ring
      have hrel := relation_of_injective f hinj (n + 1) _ hhom (by
        rw [hzero]; exact zero_mem _) (d.mapDomain ι)
      have hnot : j ∉ (d.mapDomain ι).support := by
        rw [Finsupp.mapDomain_support_of_injective hι]
        simp only [Finset.mem_image, not_exists, not_and]
        intro k hk he
        exact hne k he
      simpa only [MvPolynomial.coeff_sub, MvPolynomial.coeff_X_mul', if_neg hnot, sub_zero]
        using hrel
  have hcP : Pn.coeff d ∈ Ideal.span (Set.range f) := by
    simpa only [H, MvPolynomial.coeff_rename_mapDomain ι hι] using hc
  rw [← hPn, MvPolynomial.coeff_map]
  rw [← hmap]
  exact Ideal.mem_map_of_mem q hcP

set_option backward.isDefEq.respectTransparency false in
private theorem transport_polynomial {R S : Type u} [CommRing R] [CommRing S]
    {σ : Type*} {τ : Type*} (f : σ → R) (g : τ → S)
    (q : R →+* S) (hq : Function.Bijective q)
    (ι : τ → σ) (hι : Function.Injective ι)
    (hg : ∀ k, q (f (ι k)) = g k)
    (hmap : (Ideal.span (Set.range f)).map q = Ideal.span (Set.range g))
    (hinj : Function.Injective (prefixPolynomialMap f)) :
    Function.Bijective (prefixPolynomialMap g) := by
  apply bijective_of_relation g
  apply relation_of_zero_relation g
  intro n p hp hz d
  obtain ⟨P, hP⟩ := MvPolynomial.map_surjective q hq.2 p
  let Pn := MvPolynomial.homogeneousComponent n P
  have hPh : Pn.IsHomogeneous n := MvPolynomial.homogeneousComponent_isHomogeneous _ _
  have hPn : MvPolynomial.map q Pn = p := by
    ext e
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
    split_ifs with he
    · simpa only [MvPolynomial.coeff_map] using congrArg (MvPolynomial.coeff e) hP
    · rw [map_zero]
      exact (hp.coeff_eq_zero he).symm
  let H := MvPolynomial.rename ι Pn
  have hH : H.IsHomogeneous n := hPh.rename_isHomogeneous
  have heval : H.eval f = 0 := by
    apply hq.1
    rw [map_zero, MvPolynomial.map_eval]
    dsimp only [H]
    rw [MvPolynomial.map_rename, MvPolynomial.eval_rename]
    simpa only [Function.comp_def, hg, hPn] using hz
  have hc := relation_of_injective f hinj n H hH (by
    rw [heval]; exact zero_mem _) (d.mapDomain ι)
  have hcP : Pn.coeff d ∈ Ideal.span (Set.range f) := by
    simpa only [H, MvPolynomial.coeff_rename_mapDomain ι hι] using hc
  rw [← hPn, MvPolynomial.coeff_map, ← hmap]
  exact Ideal.mem_map_of_mem q hcP

private theorem prefix_le {A : Type u} [CommRing A] {b : ℕ}
    (f : Fin b → A) (i : ℕ) : quasiRegularPrefixIdeal f i ≤ Ideal.span (Set.range f) := by
  apply Ideal.span_mono
  rintro x ⟨j, hj, rfl⟩
  exact Set.mem_range_self j

private theorem prefix_mono {A : Type u} [CommRing A] {b : ℕ}
    (f : Fin b → A) (i : ℕ) : quasiRegularPrefixIdeal f i ≤ quasiRegularPrefixIdeal f (i + 1) := by
  apply Ideal.span_mono
  rintro x ⟨j, hj, rfl⟩
  change j.val < i at hj
  exact ⟨j, by change j.val < i + 1; omega, rfl⟩

private theorem prefix_succ {A : Type u} [CommRing A] {b : ℕ}
    (f : Fin b → A) (i : ℕ) (hi : i < b) :
    quasiRegularPrefixIdeal f (i + 1) =
      quasiRegularPrefixIdeal f i ⊔ Ideal.span {f ⟨i, hi⟩} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    by_cases h : j.val < i
    · exact (le_sup_left : quasiRegularPrefixIdeal f i ≤ _)
        (Ideal.subset_span ⟨j, h, rfl⟩)
    · have he : j = ⟨i, hi⟩ := Fin.ext (by change j.val < i + 1 at hj; dsimp only; omega)
      rw [he]
      exact (le_sup_right : Ideal.span {f ⟨i, hi⟩} ≤ _) (Ideal.mem_span_singleton_self _)
  · apply sup_le (prefix_mono f i)
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.subset_span ⟨⟨i, hi⟩, by change i < i + 1; omega, rfl⟩

private theorem tail_map {A : Type u} [CommRing A] {b : ℕ}
    (f : Fin b → A) (i : ℕ) :
    (Ideal.span (Set.range f)).map (Ideal.Quotient.mk (quasiRegularPrefixIdeal f i)) =
      Ideal.span (Set.range (quasiRegularQuotientTail f i)) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro x ⟨j, rfl⟩
    change Ideal.Quotient.mk (quasiRegularPrefixIdeal f i) (f j) ∈
      Ideal.span (Set.range (quasiRegularQuotientTail f i))
    by_cases h : i ≤ j.val
    · exact Ideal.subset_span ⟨⟨j, h⟩, rfl⟩
    · have hz : Ideal.Quotient.mk (quasiRegularPrefixIdeal f i) (f j) = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact Ideal.subset_span ⟨j, by change j.val < i; omega, rfl⟩
      rw [hz]
      exact zero_mem _
  · apply Ideal.span_le.mpr
    rintro x ⟨j, rfl⟩
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self j.val))

set_option backward.isDefEq.respectTransparency false in
private theorem tail_step {A : Type u} [CommRing A] {b : ℕ}
    (f : Fin b → A) (i : ℕ) (hi : i < b)
    (h : Function.Injective (prefixPolynomialMap (quasiRegularQuotientTail f i))) :
    Function.Bijective (prefixPolynomialMap (quasiRegularQuotientTail f (i + 1))) := by
  classical
  let q := Ideal.Quotient.factor (prefix_mono f i)
  let j : {j : Fin b // i ≤ j.val} := ⟨⟨i, hi⟩, le_refl i⟩
  let ι : {j : Fin b // i + 1 ≤ j.val} → {j : Fin b // i ≤ j.val} :=
    fun k ↦ ⟨k.val, by have := k.property; omega⟩
  have hι : Function.Injective ι := by
    intro k l h
    apply Subtype.ext
    exact congrArg (fun x : {j : Fin b // i ≤ j.val} ↦ x.val) h
  have hne (k) : ι k ≠ j := by
    intro he
    have heval := congrArg (fun x : {j : Fin b // i ≤ j.val} ↦ x.val.val) he
    have := k.property
    dsimp only [ι, j] at heval
    omega
  have hker : RingHom.ker q = Ideal.span {quasiRegularQuotientTail f i j} := by
    change RingHom.ker (Ideal.Quotient.lift _ _ _) = _
    rw [Ideal.ker_quotient_lift, Ideal.mk_ker, prefix_succ f i hi, Ideal.map_sup,
      Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
    rfl
  have hmap : (Ideal.span (Set.range (quasiRegularQuotientTail f i))).map q =
      Ideal.span (Set.range (quasiRegularQuotientTail f (i + 1))) := by
    rw [← tail_map f i, ← tail_map f (i + 1), Ideal.map_map]
    congr 1
  exact quotient_one (quasiRegularQuotientTail f i) (quasiRegularQuotientTail f (i + 1))
    q (Ideal.Quotient.factor_surjective _) j ι hι hne hker (fun _ ↦ rfl) hmap h

/-- Quotienting by any prefix preserves the polynomial associated graded structure.
Source: Stacks, Algebra, Tags 061R, 061P and 061N, with `M = A`
(blueprint: lem-pur-quasi-regular-prefix-quotient).

Proof (the eight steps of the node):
1. For the one-generator quotient put t = f_1, B = A/(t), and K equal to the
   remaining-generator ideal. Expanding products gives q(J^n) = K^n, and the
   quotient-kernel calculation gives B/K = A/J
   (`def-weil-pbc-algebra-hom-quotient`).
2. Multiplication by the first variable shifts distinct monomials to distinct
   monomials, hence is injective (`def-weil-pbc-mv-polynomial-ring`). Transport
   through the assumed isomorphism and use the homogeneous product formula of
   `lem-weil-pbc-associated-graded-ring-structure`: if y lies in J^r but not
   J^(r+1), then ty does not lie in J^(r+2).
3. For n ≥ 1 this implies J^n ∩ tA = t J^(n-1). If ty belongs to J^n but y
   does not belong to J^(n-1), take the least failed filtration level m ≤ n-1.
   Step 2 contradicts ty belonging to J^n ⊆ J^(m+1). No separatedness is used.
4. The maps [x]_n ↦ [q(x)]_n are surjective and assemble to a graded algebra
   map rho by the representative formulas of
   `lem-weil-pbc-associated-graded-ring-structure`. Its kernel in degree n
   consists of the classes represented by J^(n+1) + (tA ∩ J^n).
5. By step 3 this kernel is [t]_1 G_(n-1) for n ≥ 1, and zero in degree zero.
   Under the polynomial isomorphism it is precisely the first-variable multiples.
6. Split any homogeneous polynomial as P + T_1 Q, with P involving only the
   remaining variables. This proves surjectivity there. Comparing first exponents
   proves injectivity, over any coefficient ring, including the zero ring.
7. Polynomial uniqueness identifies the restricted composite rho Phi with the
   canonical evaluation map. Finite homogeneous decompositions assemble the
   degreewise bijections; its inverse is an algebra map and preserves degrees.
8. Induct on i. The base i = 0 is the hypothesis. Apply the one-generator result
   over the current prefix quotient. The quotient by the next generator is the
   next prefix quotient, by representatives and kernels. The induced bijections
   on powers and successive quotients preserve the graded algebra operations.
   Both coefficient maps send a to a mod J, giving the specified identification.
   At i = b the remaining ideal is zero; b = 0 is the base case alone.
-/
theorem quasiRegular_prefix_quotient {A : Type u} [CommRing A]
    {b : ℕ} (f : Fin b → A)
    (hpoly : Function.Bijective
      (MvPolynomial.aeval (R := A ⧸ Ideal.span (Set.range f)) (fun j : Fin b ↦
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) 1
          (Submodule.Quotient.mk
            (⟨f j, by simpa using Ideal.subset_span (Set.mem_range_self j)⟩ :
              (Ideal.span (Set.range f) ^ 1 : Ideal A))))))
    (i : ℕ) (hi : i ≤ b) :
    ∃ e : ((A ⧸ quasiRegularPrefixIdeal f i) ⧸
        Ideal.span (Set.range (quasiRegularQuotientTail f i))) ≃+*
          (A ⧸ Ideal.span (Set.range f)),
      (∀ a : A, e (Ideal.Quotient.mk
          (Ideal.span (Set.range (quasiRegularQuotientTail f i)))
          (Ideal.Quotient.mk (quasiRegularPrefixIdeal f i) a)) =
        Ideal.Quotient.mk (Ideal.span (Set.range f)) a) ∧
      Function.Bijective
        (MvPolynomial.aeval
          (R := (A ⧸ quasiRegularPrefixIdeal f i) ⧸
            Ideal.span (Set.range (quasiRegularQuotientTail f i)))
          (fun j : {j : Fin b // i ≤ j.val} ↦
            DirectSum.of
              (associatedGradedPiece (Ideal.span (Set.range (quasiRegularQuotientTail f i))))
              1 (Submodule.Quotient.mk
                (⟨quasiRegularQuotientTail f i j,
                  by simpa using Ideal.subset_span (Set.mem_range_self j)⟩ :
                  (Ideal.span (Set.range (quasiRegularQuotientTail f i)) ^ 1 :
                    Ideal (A ⧸ quasiRegularPrefixIdeal f i)))))) := by
  classical
  have hzero : quasiRegularPrefixIdeal f 0 = ⊥ := by
    simp [quasiRegularPrefixIdeal]
  have hbase : Function.Bijective (prefixPolynomialMap (quasiRegularQuotientTail f 0)) := by
    let q := Ideal.Quotient.mk (quasiRegularPrefixIdeal f 0)
    have hq : Function.Bijective q := by
      constructor
      · rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, hzero]
      · exact Ideal.Quotient.mk_surjective
    exact transport_polynomial f (quasiRegularQuotientTail f 0) q hq
      Subtype.val Subtype.val_injective (fun _ ↦ rfl) (tail_map f 0) hpoly.1
  have htail : ∀ i, i ≤ b →
      Function.Bijective (prefixPolynomialMap (quasiRegularQuotientTail f i)) := by
    intro i
    induction i with
    | zero => intro _; exact hbase
    | succ i ih =>
      intro hi
      exact tail_step f i (by omega) (ih (by omega)).1
  let E := DoubleQuot.quotQuotEquivQuotOfLE (prefix_le f i)
  let e := (Ideal.quotEquivOfEq (tail_map f i).symm).trans E
  refine ⟨e, ?_, htail i hi⟩
  intro a
  change E ((Ideal.quotEquivOfEq (tail_map f i).symm)
    (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a))) = _
  rw [Ideal.quotEquivOfEq_mk]
  exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk a (prefix_le f i)

end Ideal
