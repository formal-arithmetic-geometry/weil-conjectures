/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.RingTheory.RegularSequenceGradedPolynomial
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer

/-!
# Quasi-regular sequences and arbitrary base change with flat quotient

Source: Stacks Project, More on Algebra, Tag 0CEP, part (1), and Algebra, Tag 061P
(blueprint: lem-pur-quasi-regular-flat-quotient-base-change).

The existing `Ideal.regularSequenceGradedPolynomialMap` is defined for every finite
sequence, without a regularity assumption. It sends variables to their degree-one
classes and constants to degree zero. Bijectivity therefore expresses exactly the
canonical graded quotient-algebra isomorphism in the quasi-regularity criterion.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Ideal

set_option backward.isDefEq.respectTransparency false in
private theorem qbc_monomial_class {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (d : Fin c →₀ ℕ) :
    ∃ x : (Ideal.span (Set.range f) ^ d.degree : Ideal R),
      x.val = d.prod (fun j k ↦ f j ^ k) ∧
      regularSequenceGradedPolynomialMap f (MvPolynomial.monomial d 1) =
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) d.degree
          (Submodule.Quotient.mk x) := by
  classical
  let J := Ideal.span (Set.range f)
  let P := fun d : Fin c →₀ ℕ ↦
    ∃ x : (J ^ d.degree : Ideal R),
      x.val = d.prod (fun j k ↦ f j ^ k) ∧
      regularSequenceGradedPolynomialMap f (MvPolynomial.monomial d 1) =
        DirectSum.of (associatedGradedPiece J) d.degree (Submodule.Quotient.mk x)
  have hzero : P 0 := by
    refine ⟨⟨1, by simp⟩, by simp, ?_⟩
    change regularSequenceGradedPolynomialMap f 1 = _
    rw [map_one]
    exact associatedGraded_one J
  have hadd (d e : Fin c →₀ ℕ) (hd : P d) (he : P e) : P (d + e) := by
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
  have hsingle (j : Fin c) : P (Finsupp.single j 1) := by
    dsimp only [P]
    rw [Finsupp.degree_single]
    refine ⟨⟨f j, by simpa using Ideal.subset_span (Set.mem_range_self j)⟩,
      by simp, ?_⟩
    change regularSequenceGradedPolynomialMap f (MvPolynomial.X j) = _
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
private theorem qbc_coeff_monomial_class {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (d : Fin c →₀ ℕ) (r : R) :
    ∃ x : (Ideal.span (Set.range f) ^ d.degree : Ideal R),
      x.val = r * d.prod (fun j k ↦ f j ^ k) ∧
      regularSequenceGradedPolynomialMap f
          (MvPolynomial.monomial d (Ideal.Quotient.mk (Ideal.span (Set.range f)) r)) =
        DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) d.degree
          (Submodule.Quotient.mk x) := by
  obtain ⟨x, hx, hx'⟩ := qbc_monomial_class f d
  refine ⟨⟨r * x.val, Ideal.mul_mem_left _ r x.property⟩, by dsimp only; rw [hx], ?_⟩
  have hm : MvPolynomial.monomial d (Ideal.Quotient.mk (Ideal.span (Set.range f)) r) =
      Ideal.Quotient.mk (Ideal.span (Set.range f)) r • MvPolynomial.monomial d 1 := by
    simpa only [smul_eq_mul, mul_one] using
      ((MvPolynomial.monomial d).map_smul
        (Ideal.Quotient.mk (Ideal.span (Set.range f)) r) 1)
  rw [hm, map_smul, hx']
  exact associatedGraded_smul _ _ _ x

set_option backward.isDefEq.respectTransparency false in
private theorem qbc_homogeneous_class {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (n : ℕ) (p : MvPolynomial (Fin c) R) (hp : p.IsHomogeneous n) :
    ∃ x : (Ideal.span (Set.range f) ^ n : Ideal R),
      x.val = p.eval f ∧
      regularSequenceGradedPolynomialMap f
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
        regularSequenceGradedPolynomialMap f
            (MvPolynomial.monomial d.val (Ideal.Quotient.mk J (p.coeff d.val))) =
          DirectSum.of (associatedGradedPiece J) n (Submodule.Quotient.mk x) := by
    have h := qbc_coeff_monomial_class f d.val (p.coeff d.val)
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
private theorem qbc_homogeneous_lift {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (n : ℕ) (p : MvPolynomial (Fin c) (R ⧸ Ideal.span (Set.range f)))
    (hp : p.IsHomogeneous n) :
    ∃ q : MvPolynomial (Fin c) R, q.IsHomogeneous n ∧
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
private theorem qbc_component_map {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (n : ℕ) (p : MvPolynomial (Fin c) (R ⧸ Ideal.span (Set.range f))) :
    regularSequenceGradedPolynomialMap f (MvPolynomial.homogeneousComponent n p) =
      DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n
        (regularSequenceGradedPolynomialMap f p n) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d b =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨x, hx, hx'⟩ := qbc_coeff_monomial_class f d r
    rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial _ rfl)]
    by_cases h : n = d.degree
    · subst n
      simp only [ite_true, hx', DirectSum.of_eq_same]
    · simp only [if_neg h, map_zero, hx', DirectSum.of_eq_of_ne _ _ _ h]
  | add p q hp hq =>
    simp only [map_add, DirectSum.add_apply, hp, hq]

set_option backward.isDefEq.respectTransparency false in
private theorem qbc_homogeneous_kernel {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (hrel : ∀ (n : ℕ) (p : MvPolynomial (Fin c) R), p.IsHomogeneous n →
      p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) →
        ∀ d, p.coeff d ∈ Ideal.span (Set.range f))
    (n : ℕ) (p : MvPolynomial (Fin c) (R ⧸ Ideal.span (Set.range f)))
    (hp : p.IsHomogeneous n) (hz : regularSequenceGradedPolynomialMap f p = 0) : p = 0 := by
  obtain ⟨q, hq, hqp⟩ := qbc_homogeneous_lift f n p hp
  obtain ⟨x, hx, hx'⟩ := qbc_homogeneous_class f n q hq
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
private theorem qbc_bijective_of_relation {R : Type u} [CommRing R] {c : ℕ} (f : Fin c → R)
    (hrel : ∀ (n : ℕ) (p : MvPolynomial (Fin c) R), p.IsHomogeneous n →
      p.eval f ∈ Ideal.span (Set.range f) ^ (n + 1) →
        ∀ d, p.coeff d ∈ Ideal.span (Set.range f)) :
    Function.Bijective (regularSequenceGradedPolynomialMap f) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro p hp
    have hc (n : ℕ) : MvPolynomial.homogeneousComponent n p = 0 := by
      apply qbc_homogeneous_kernel f hrel n _ (MvPolynomial.homogeneousComponent_isHomogeneous _ _)
      rw [qbc_component_map, hp]
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
        obtain ⟨z, hz, hz'⟩ := qbc_homogeneous_class f n p hp
        have he : z = x := Subtype.ext (hz.trans hpx)
        exact ⟨MvPolynomial.map (Ideal.Quotient.mk _) p, by simpa only [he] using hz'⟩
    | add x y hx hy =>
      obtain ⟨p, rfl⟩ := hx
      obtain ⟨q, rfl⟩ := hy
      exact ⟨p + q, map_add _ _ _⟩


private theorem qbc_smul {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] {b : ℕ} (f : Fin b → A) (r : R)
    (z : associatedGraded (Ideal.span (Set.range f))) :
    algebraMap R (A ⧸ Ideal.span (Set.range f)) r • z = r • z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of n z =>
    induction z using Submodule.Quotient.induction_on with
    | _ x =>
      have h := associatedGraded_smul (Ideal.span (Set.range f)) (algebraMap R A r) n x
      change Ideal.Quotient.mk _ (algebraMap R A r) • _ = _
      rw [h]
      rw [← DirectSum.of_smul]
      apply congrArg (DirectSum.of (associatedGradedPiece (Ideal.span (Set.range f))) n)
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      ext
      exact (Algebra.smul_def r x.val).symm
  | add z t hz ht => simp only [smul_add, hz, ht]

private theorem qbc_flat_piece {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] {b : ℕ} (f : Fin b → A)
    [Module.Flat R (A ⧸ Ideal.span (Set.range f))]
    (hf : Function.Bijective (regularSequenceGradedPolynomialMap f)) (n : ℕ) :
    Module.Flat R (associatedGradedPiece (Ideal.span (Set.range f)) n) := by
  let J := Ideal.span (Set.range f)
  let F : MvPolynomial (Fin b) (A ⧸ J) →ₗ[R] associatedGraded J :=
    { toFun := regularSequenceGradedPolynomialMap f
      map_add' := map_add _
      map_smul' := fun r p ↦ by
        rw [← IsScalarTower.algebraMap_smul (A ⧸ J) r p, map_smul]
        exact qbc_smul f r _ }
  have : Module.Flat R (MvPolynomial (Fin b) (A ⧸ J)) :=
    Module.Flat.trans R (A ⧸ J) _
  have : Module.Flat R (associatedGraded J) :=
    Module.Flat.of_linearEquiv (LinearEquiv.ofBijective F hf).symm
  exact (Module.Flat.directSum_iff.mp this) n

private theorem qbc_flat_power {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] {b : ℕ} (f : Fin b → A)
    [Module.Flat R (A ⧸ Ideal.span (Set.range f))]
    (hf : Function.Bijective (regularSequenceGradedPolynomialMap f)) (m : ℕ) :
    Module.Flat R (A ⧸ Ideal.span (Set.range f) ^ m) := by
  let J := Ideal.span (Set.range f)
  suffices h : ∀ k, Module.Flat R (A ⧸ J ^ (k + 1)) by
    cases m with
    | zero =>
      have : Subsingleton (A ⧸ J ^ 0) := by
        rw [pow_zero, Ideal.one_eq_top]
        infer_instance
      infer_instance
    | succ m => exact h m
  intro k
  induction k with
  | zero =>
    change Module.Flat R (A ⧸ J ^ 1)
    rw [pow_one]
    infer_instance
  | succ k ih =>
    let n := k + 1
    have : Module.Flat R (A ⧸ J ^ n) := ih
    have : Module.Flat R (associatedGradedPiece J n) := qbc_flat_piece f hf n
    let P := Submodule.comap (J ^ n).subtype (J ^ (n + 1))
    let iA : associatedGradedPiece J n →ₗ[A] A ⧸ J ^ (n + 1) :=
      P.liftQ ((J ^ (n + 1)).mkQ.comp (J ^ n).subtype) (by
        intro x hx
        exact (Submodule.Quotient.mk_eq_zero _).mpr hx)
    let i := iA.restrictScalars R
    let q := (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (n.le_succ)) :
      A ⧸ J ^ (n + 1) →ₐ[R] A ⧸ J ^ n).toLinearMap
    have hi : Function.Injective i := by
      apply (injective_iff_map_eq_zero _).mpr
      intro x hx
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        exact (Submodule.Quotient.mk_eq_zero P).mpr
          ((Submodule.Quotient.mk_eq_zero (J ^ (n + 1))).mp hx)
    have hq : Function.Surjective q :=
      Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right n.le_succ)
    have he : Function.Exact i q := by
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        constructor
        · intro hx
          have hx' : x ∈ J ^ n := (Ideal.Quotient.eq_zero_iff_mem).mp hx
          exact ⟨Submodule.Quotient.mk (⟨x, hx'⟩ : (J ^ n : Ideal A)), rfl⟩
        · rintro ⟨y, hy⟩
          rw [← hy]
          induction y using Submodule.Quotient.induction_on with
          | _ y => exact (Ideal.Quotient.eq_zero_iff_mem).mpr y.property
    exact Module.Flat.of_exact_of_flat_of_flat i q hi hq he

private theorem qbc_tensor_injective {R : Type u} {A : Type v} {R' : Type w}
    [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    (I : Ideal A) [Module.Flat R (A ⧸ I)] :
    Function.Injective (((I.restrictScalars R).subtype).rTensor R') := by
  let q := (Ideal.Quotient.mkₐ R I).toLinearMap
  have he : Function.Exact (I.restrictScalars R).subtype q := by
    intro a
    constructor
    · intro h
      exact ⟨⟨a, Ideal.Quotient.eq_zero_iff_mem.mp h⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property
  have hi := LinearMap.lTensor_injective_of_exact_of_flat q
    Ideal.Quotient.mk_surjective (I.restrictScalars R).subtype Subtype.val_injective he R'
  intro x y h
  apply (TensorProduct.comm R _ R').injective
  apply hi
  simpa only [LinearMap.lTensor_comm] using
    congrArg (TensorProduct.comm R A R') h

private theorem qbc_coefficient_maps {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {b : ℕ} (f : Fin b → A)
    (hf : Function.Bijective (regularSequenceGradedPolynomialMap f)) (n : ℕ) :
    ∃ c : (Fin b →₀ ℕ) → (Ideal.span (Set.range f) ^ n : Ideal A) →ₗ[R]
        A ⧸ Ideal.span (Set.range f),
      (∀ d (x : (Ideal.span (Set.range f) ^ n : Ideal A)),
        x.val ∈ Ideal.span (Set.range f) ^ (n + 1) → c d x = 0) ∧
      (∀ d e (_h : e.degree = n) (a : A)
        (x : (Ideal.span (Set.range f) ^ n : Ideal A)),
        x.val = a * e.prod (fun j k ↦ f j ^ k) →
          c d x = if e = d then Ideal.Quotient.mk _ a else 0) := by
  classical
  let J := Ideal.span (Set.range f)
  let F : MvPolynomial (Fin b) (A ⧸ J) →ₗ[R] associatedGraded J :=
    { toFun := regularSequenceGradedPolynomialMap f
      map_add' := map_add _
      map_smul' := fun r p ↦ by
        rw [← IsScalarTower.algebraMap_smul (A ⧸ J) r p, map_smul]
        exact qbc_smul f r _ }
  let E := LinearEquiv.ofBijective F hf
  let q := (Submodule.mkQ (Submodule.comap (J ^ n).subtype (J ^ (n + 1)))).restrictScalars R
  let c := fun d ↦ ((MvPolynomial.lcoeff (A ⧸ J) d).restrictScalars R).comp
    (E.symm.toLinearMap.comp ((DirectSum.lof R ℕ (associatedGradedPiece J) n).comp q))
  refine ⟨c, ?_, ?_⟩
  · intro d x hx
    have hz : q x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
    change MvPolynomial.coeff d (E.symm (DirectSum.of (associatedGradedPiece J) n (q x))) = 0
    rw [hz, map_zero, map_zero, MvPolynomial.coeff_zero]
  · intro d e h a x hx
    obtain ⟨y, hy, hy'⟩ := qbc_coeff_monomial_class f e a
    have hn := h
    subst n
    have he : y = x := Subtype.ext (hy.trans hx.symm)
    have hm : E (MvPolynomial.monomial e (Ideal.Quotient.mk J a)) =
        DirectSum.of (associatedGradedPiece J) e.degree (q x) := by
      exact he ▸ hy'
    change MvPolynomial.coeff d
      (E.symm (DirectSum.of (associatedGradedPiece J) e.degree (q x))) = _
    rw [← hm, E.symm_apply_apply, MvPolynomial.coeff_monomial]

set_option backward.isDefEq.respectTransparency false in
private theorem qbc_relation_proof {R : Type u} {A : Type v} {R' : Type w}
    [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    {b : ℕ} (f : Fin b → A) [Module.Flat R (A ⧸ Ideal.span (Set.range f))]
    (hf : Function.Bijective (regularSequenceGradedPolynomialMap f))
    (n : ℕ) (p : MvPolynomial (Fin b) (A ⊗[R] R')) (hp : p.IsHomogeneous n)
    (hm : p.eval (fun j ↦ f j ⊗ₜ[R] (1 : R')) ∈
      Ideal.span (Set.range (fun j ↦ f j ⊗ₜ[R] (1 : R'))) ^ (n + 1)) :
    ∀ d, p.coeff d ∈ Ideal.span (Set.range (fun j ↦ f j ⊗ₜ[R] (1 : R'))) := by
  classical
  let J := Ideal.span (Set.range f)
  let K := Ideal.span (Set.range (fun j ↦ f j ⊗ₜ[R] (1 : R')))
  let v : A →+* A ⊗[R] R' := Algebra.TensorProduct.includeLeftRingHom
  have hJK : J.map v = K := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  let I := (J ^ n).restrictScalars R
  let I₁ := (J ^ (n + 1)).restrictScalars R
  let u := I.subtype.rTensor R'
  let u₁ := I₁.subtype.rTensor R'
  let inc : I₁ →ₗ[R] I := Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ)
  have hinc : u.comp (inc.rTensor R') = u₁ := by
    ext x s
    rfl
  have : Module.Flat R (A ⧸ J ^ n) := qbc_flat_power f hf n
  have hu : Function.Injective u := qbc_tensor_injective (J ^ n)
  have hmem : p.eval (fun j ↦ f j ⊗ₜ[R] (1 : R')) ∈ LinearMap.range u₁ := by
    rw [← Ideal.map_includeLeft_eq, Ideal.map_pow]
    change p.eval (fun j ↦ f j ⊗ₜ[R] (1 : R')) ∈ J.map v ^ (n + 1)
    rw [hJK]
    exact hm
  obtain ⟨y, hy⟩ := hmem
  have he (e : p.support) : e.val.degree = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hp (MvPolynomial.mem_support_iff.mp e.property)
  have hz (e : p.support) : ∃ z : I, z.val = e.val.prod (fun j k ↦ f j ^ k) := by
    obtain ⟨z, hz, _⟩ := qbc_monomial_class f e.val
    refine ⟨⟨z.val, ?_⟩, hz⟩
    exact Eq.mp (congrArg (fun k ↦ (z.val : A) ∈ J ^ k) (he e)) z.property
  choose z hz using hz
  let t : p.support → A →ₗ[R] I := fun e ↦
    { toFun := fun a ↦ a • z e
      map_add' := fun a b ↦ add_smul a b _
      map_smul' := fun r a ↦ by
        change (r • a) • z e = r • (a • z e)
        exact smul_assoc r a (z e) }
  have ht (e : p.support) (a : A ⊗[R] R') :
      u ((t e).rTensor R' a) = a * v (e.val.prod (fun j k ↦ f j ^ k)) := by
    induction a using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_mul]
    | tmul a s =>
      change (a * (z e).val) ⊗ₜ[R] s = (a ⊗ₜ[R] s) * (_ ⊗ₜ[R] 1)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hz]
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_mul]
  let x := ∑ e : p.support, (t e).rTensor R' (p.coeff e.val)
  have hx : u x = p.eval (fun j ↦ f j ⊗ₜ[R] (1 : R')) := by
    rw [map_sum]
    simp only [ht]
    conv_rhs => rw [p.as_sum, map_sum]
    rw [← Finset.sum_coe_sort p.support]
    apply Finset.sum_congr rfl
    intro e _
    rw [MvPolynomial.eval_monomial]
    congr 1
    simp only [v, map_finsuppProd, map_pow, Algebra.TensorProduct.includeLeftRingHom_apply]
  have hxy : x = inc.rTensor R' y := hu (by rw [hx, ← hy]; exact congr($hinc y).symm)
  obtain ⟨c₀, hc₀, hc⟩ := qbc_coefficient_maps (R := R) f hf n
  let c : (Fin b →₀ ℕ) → I →ₗ[R] A ⧸ J := fun d ↦
    { toFun := c₀ d
      map_add' := (c₀ d).map_add
      map_smul' := (c₀ d).map_smul }
  intro d
  let q := (Ideal.Quotient.mkₐ R J).toLinearMap
  have hct (e : p.support) : (c d).comp (t e) =
      if e.val = d then q else 0 := by
    ext a
    change c d (t e a) = _
    change c₀ d (t e a) = _
    rw [hc d e.val (he e) a (t e a) (by change a * (z e).val = _; rw [hz])]
    split_ifs <;> rfl
  have hci : (c d).comp inc = 0 := by
    ext a
    exact hc₀ d (inc a) a.property
  have hcx : (c d).rTensor R' x = q.rTensor R' (p.coeff d) := by
    change (c d).rTensor R' (∑ e : p.support, _) = _
    rw [map_sum]
    have hh (e : p.support) :
        (c d).rTensor R' ((t e).rTensor R' (p.coeff e.val)) =
          if e.val = d then q.rTensor R' (p.coeff e.val) else 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hct]
      split_ifs <;> simp only [LinearMap.rTensor_zero, LinearMap.zero_apply]
    simp_rw [hh]
    by_cases hd : d ∈ p.support
    · rw [Finset.sum_eq_single (⟨d, hd⟩ : p.support)]
      · rw [if_pos rfl]
      · intro e _ hne
        exact if_neg (by intro h; exact hne (Subtype.ext h))
      · simp
    · rw [MvPolynomial.notMem_support_iff.mp hd, map_zero]
      apply Finset.sum_eq_zero
      intro e _
      exact if_neg (by intro h; exact hd (h ▸ e.property))
  have hzero : q.rTensor R' (p.coeff d) = 0 := by
    rw [← hcx, hxy, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hci,
      LinearMap.rTensor_zero, LinearMap.zero_apply]
  have heq (a : A ⊗[R] R') :
      Algebra.TensorProduct.quotientTensorEquiv R R' A J (q.rTensor R' a) =
        Ideal.Quotient.mk (J.map v) a := by
    induction a using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a s =>
      change Algebra.TensorProduct.quotientTensorEquiv R R' A J
        (Ideal.Quotient.mk J a ⊗ₜ[R] s) = _
      exact Algebra.TensorProduct.quotientTensorEquiv_apply_tmul R R' A J a s
    | add a b ha hb => simp only [map_add, ha, hb]
  have hquot : Ideal.Quotient.mk (J.map v) (p.coeff d) = 0 := by
    rw [← heq, hzero, map_zero]
  change p.coeff d ∈ K
  rw [← hJK]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hquot

/-- Quasi-regularity survives arbitrary scalar extension when the quotient is flat.
Source: Stacks Project, More on Algebra, Tag 0CEP, part (1); Algebra, Tag 061P
(blueprint: lem-pur-quasi-regular-flat-quotient-base-change).

Proof:
1. The polynomial ring over C = A/J is R-flat by transitivity of flatness.
   The assumed bijection is R-linear, so the associated graded ring is R-flat.
   Each graded piece is a direct summand and is therefore R-flat.
2. The exact sequence J^n/J^(n+1) -> A/J^(n+1) -> A/J^n shows inductively that
   every A/J^n is R-flat. The n = 0 quotient is zero. The injection and exactness
   are checked on representatives; extensions of flat modules are flat.
3. Write B = A tensor R' and K = (f tensor 1). Flatness of A/J^n makes
   u_n : J^n tensor R' -> B injective. Its image is K^n, since extension of
   ideals commutes with powers and the image of the tensor inclusion is the
   extended ideal.
4. Compose the inverse of the assumed graded isomorphism with coefficient
   projection to obtain R-linear maps c_d : J^n -> C. They kill J^(n+1) and
   send a*f^e, for |e| = n, to [a] if e = d and to zero otherwise.
5. Let p be homogeneous of degree n over B, with p(f tensor 1) in K^(n+1).
   Lift its monomial expansion to x in J^n tensor R' and its evaluation to
   y in J^(n+1) tensor R'. Injectivity of u_n gives x = inclusion(y).
   Applying c_d tensor R' shows that [coefficient_d(p)] is zero in C tensor R'.
   The quotient tensor equivalence identifies this with its class in B/K,
   so every coefficient of p belongs to K.
6. This homogeneous relation criterion proves injectivity of the canonical
   map by lifting coefficients and taking homogeneous components. Surjectivity
   follows by writing a representative in K^n as a homogeneous polynomial in
   the generators and summing the finitely many graded components. -/
theorem quasiRegular_flatQuotient_baseChange
    {R : Type u} {A : Type v} {R' : Type w}
    [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    {b : ℕ} (f : Fin b → A) [Module.Flat R (A ⧸ Ideal.span (Set.range f))]
    (hf : Function.Bijective (regularSequenceGradedPolynomialMap f)) :
    Function.Bijective
      (regularSequenceGradedPolynomialMap (fun j ↦ f j ⊗ₜ[R] (1 : R'))) := by
  apply qbc_bijective_of_relation
  exact qbc_relation_proof f hf

end Ideal
