/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.MvPolynomial.Ideal
import Sheaf.RingTheory.PolynomialCombinedIdealCoefficients
import Sheaf.RingTheory.FormallyEtaleAssociatedGraded

/-! # Associated graded ring of the combined polynomial ideal

Source: Stacks Project, Tags 054L and 0AGX, coefficient calculation in
lem-trf-smooth-rational-point-completion, Step 9.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPolynomial

private abbrev gr {A : Type*} [CommRing A] (J : Ideal A) (n : ℕ)
    (a : A) (ha : a ∈ J ^ n) : Ideal.associatedGraded J :=
  DirectSum.of (Ideal.associatedGradedPiece J) n
    (Submodule.Quotient.mk (⟨a, ha⟩ : (J ^ n : Ideal A)))

private theorem gr_zero {A : Type*} [CommRing A] (J : Ideal A) (n : ℕ)
    (h : (0 : A) ∈ J ^ n) : gr J n 0 h = 0 := by
  change DirectSum.of (Ideal.associatedGradedPiece J) n
    (Submodule.Quotient.mk (0 : (J ^ n : Ideal A))) = 0
  rw [Submodule.Quotient.mk_zero, map_zero]

private theorem gr_cast {A : Type*} [CommRing A] (J : Ideal A)
    {n m : ℕ} (h : n = m) (a : A) (ha : a ∈ J ^ n) (hb : a ∈ J ^ m) :
    gr J n a ha = gr J m a hb := by subst m; rfl

private theorem gr_congr {A : Type*} [CommRing A] (J : Ideal A)
    {n m : ℕ} (hn : n = m) (a b : A) (hab : a = b)
    (ha : a ∈ J ^ n) (hb : b ∈ J ^ m) : gr J n a ha = gr J m b hb := by
  subst m
  subst b
  rfl

private theorem gr_mul {A : Type*} [CommRing A] (J : Ideal A)
    (n m : ℕ) (a b : A) (ha : a ∈ J ^ n) (hb : b ∈ J ^ m) :
    gr J n a ha * gr J m b hb =
      gr J (n + m) (a * b) (by simpa [pow_add] using Ideal.mul_mem_mul ha hb) :=
  Ideal.associatedGraded_mul J n m ⟨a, ha⟩ ⟨b, hb⟩

private noncomputable def gradedMap {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (J : Ideal B) (h : I ≤ J.comap f) :
    Ideal.associatedGraded I →+* Ideal.associatedGraded J where
  __ := Ideal.associatedGradedMap f I J h
  map_one' := by
    rw [Ideal.associatedGraded_one]
    change DirectSum.map _ (DirectSum.of _ 0 _) = _
    rw [DirectSum.map_of, Ideal.associatedGraded_one]
    change gr J 0 (f 1) _ = gr J 0 1 _
    congr 2
    exact map_one f
  map_mul' x y := by
    change Ideal.associatedGradedMap f I J h (x * y) =
      Ideal.associatedGradedMap f I J h x * Ideal.associatedGradedMap f I J h y
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_mul, map_add, hx, hy]
    | of n x =>
      induction y using DirectSum.induction_on with
      | zero => simp
      | add x y hx hy => simp only [mul_add, map_add, hx, hy]
      | of m y =>
        induction x using Submodule.Quotient.induction_on with
        | H a =>
          induction y using Submodule.Quotient.induction_on with
          | H b =>
            simp only [Ideal.associatedGraded_mul]
            change DirectSum.map _ (DirectSum.of _ (n + m) _) =
              DirectSum.map _ (DirectSum.of _ n _) * DirectSum.map _ (DirectSum.of _ m _)
            simp only [DirectSum.map_of]
            change gr J (n + m) (f (a.val * b.val)) _ =
              gr J n (f a.val) _ * gr J m (f b.val) _
            rw [gr_mul]
            congr 2
            exact map_mul f a.val b.val

private theorem gradedMap_gr {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (J : Ideal B) (h : I ≤ J.comap f)
    (n : ℕ) (a : A) (ha : a ∈ I ^ n) (hb : f a ∈ J ^ n) :
    gradedMap f I J h (gr I n a ha) = gr J n (f a) hb := by
  change DirectSum.map _ (DirectSum.of _ n _) = _
  rw [DirectSum.map_of]
  rfl

private noncomputable abbrev combined {R : Type u} [CommRing R] (I : Ideal R) (d : ℕ) :=
  I.map (C (σ := Fin d)) ⊔ idealOfVars (Fin d) R

private theorem constant_mem {R : Type u} [CommRing R] (I : Ideal R) (d n : ℕ)
    (a : R) (ha : a ∈ I ^ n) : C (σ := Fin d) a ∈ combined I d ^ n := by
  apply Ideal.pow_right_mono le_sup_left n
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

private theorem variable_mem {R : Type u} [CommRing R] (I : Ideal R) (d : ℕ)
    (i : Fin d) : X i ∈ combined I d ^ 1 := by
  rw [pow_one]
  exact (show idealOfVars (Fin d) R ≤ combined I d from le_sup_right)
    (Ideal.subset_span (Set.mem_range_self i))

private noncomputable def polynomialGradedMap {R : Type u} [CommRing R]
    (I : Ideal R) (d : ℕ) :
    MvPolynomial (Fin d) (Ideal.associatedGraded I) →+*
      Ideal.associatedGraded (combined I d) :=
  eval₂Hom (gradedMap C I (combined I d) (by
    intro a ha
    simpa using constant_mem I d 1 a (by simpa using ha)))
    (fun i ↦ gr (combined I d) 1 (X i) (variable_mem I d i))

private theorem polynomialGradedMap_C {R : Type u} [CommRing R]
    (I : Ideal R) (d n : ℕ) (a : R) (ha : a ∈ I ^ n)
    (hb : C a ∈ combined I d ^ n) :
    polynomialGradedMap I d (C (gr I n a ha)) = gr (combined I d) n (C a) hb := by
  rw [polynomialGradedMap, eval₂Hom_C]
  exact gradedMap_gr C I (combined I d) _ n a ha hb

private theorem mono_mem {R : Type u} [CommRing R] (I : Ideal R) (d k : ℕ)
    (E : Fin d →₀ ℕ) (a : R) (ha : a ∈ I ^ k) :
    monomial E a ∈ combined I d ^ (k + E.degree) := by
  classical
  apply (mem_combined_ideal_pow_iff R I d _ _).mpr
  intro F
  by_cases h : E = F
  · subst F
    simpa using ha
  · simp [coeff_monomial, h]

private theorem gr_pow {A : Type*} [CommRing A] (J : Ideal A)
    (a : A) (ha : a ∈ J ^ 1) (e : ℕ) :
    gr J 1 a ha ^ e = gr J e (a ^ e) (by
      simpa only [one_mul] using Ideal.pow_mem_pow (by simpa using ha) e) := by
  induction e with
  | zero => simpa using (Ideal.associatedGraded_one J)
  | succ e ih =>
    rw [pow_succ, ih, gr_mul]
    exact gr_congr J rfl _ _ (pow_succ a e).symm _ _

private theorem gr_prod {A : Type*} [CommRing A] (J : Ideal A)
    {ι : Type*} (s : Finset ι) (k : ι → ℕ) (a : ι → A) (ha : ∀ i, a i ∈ J ^ k i) :
    ∃ hp : (∏ i ∈ s, a i) ∈ J ^ (∑ i ∈ s, k i),
      (∏ i ∈ s, gr J (k i) (a i) (ha i)) =
        gr J (∑ i ∈ s, k i) (∏ i ∈ s, a i) hp := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, by simpa using (Ideal.associatedGraded_one J)⟩
  | @insert i s hi ih =>
    obtain ⟨hp, heq⟩ := ih
    have hm := Ideal.mul_mem_mul (ha i) hp
    rw [← pow_add] at hm
    refine ⟨by simpa [hi] using hm, ?_⟩
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [heq, gr_mul]

private theorem polynomialGradedMap_monomial {R : Type u} [CommRing R]
    (I : Ideal R) (d k : ℕ) (E : Fin d →₀ ℕ) (a : R) (ha : a ∈ I ^ k) :
    polynomialGradedMap I d (monomial E (gr I k a ha)) =
      gr (combined I d) (k + E.degree) (monomial E a) (mono_mem I d k E a ha) := by
  classical
  have hX (i : Fin d) : polynomialGradedMap I d (X i) =
      gr (combined I d) 1 (X i) (variable_mem I d i) := by
    simp [polynomialGradedMap]
  rw [monomial_eq, map_mul, polynomialGradedMap_C I d k a ha
    (constant_mem I d k a ha)]
  simp only [Finsupp.prod, map_prod, map_pow, hX, gr_pow]
  obtain ⟨hp, heq⟩ := gr_prod (combined I d) E.support (fun i ↦ E i)
    (fun i ↦ (X i : MvPolynomial (Fin d) R) ^ E i)
    (fun i ↦ by simpa using Ideal.pow_mem_pow (by
      simpa using variable_mem I d i) (E i))
  rw [heq, gr_mul]
  exact gr_congr (combined I d)
    (congrArg (k + ·) (Finsupp.degree_apply E).symm) _ _ (monomial_eq (s := E) (a := a)).symm _ _

private noncomputable def pieceCoefficient {R : Type u} [CommRing R]
    (I : Ideal R) (d n : ℕ) (E : Fin d →₀ ℕ) :
    Ideal.associatedGradedPiece (combined I d) n →+ Ideal.associatedGraded I := by
  classical
  by_cases hE : E.degree ≤ n
  · let F : (combined I d ^ n : Ideal (MvPolynomial (Fin d) R)) →+
        Ideal.associatedGraded I :=
      { toFun := fun p ↦ gr I (n - E.degree) (p.val.coeff E)
          ((mem_combined_ideal_pow_iff R I d n p.val).mp p.property E)
        map_zero' := by exact gr_zero I _ _
        map_add' := fun p q ↦ by
          change gr I _ ((p.val + q.val).coeff E) _ = _
          simp only [coeff_add]
          unfold gr
          rw [show (⟨p.val.coeff E + q.val.coeff E, _⟩ :
            (I ^ (n - E.degree) : Ideal R)) =
            ⟨p.val.coeff E, _⟩ + ⟨q.val.coeff E, _⟩ from rfl,
            Submodule.Quotient.mk_add, map_add] }
    exact QuotientAddGroup.lift _ F (by
      intro p hp
      change F p = 0
      apply (show ∀ z : Ideal.associatedGradedPiece I (n - E.degree),
        z = 0 → DirectSum.of _ (n - E.degree) z = 0 from
          fun z hz ↦ by rw [hz, map_zero])
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change p.val.coeff E ∈ I ^ (n - E.degree + 1)
      have hc := (mem_combined_ideal_pow_iff R I d (n + 1) p.val).mp hp E
      simpa [Nat.sub_add_comm hE] using hc)
  · exact 0

private theorem pieceCoefficient_gr {R : Type u} [CommRing R]
    (I : Ideal R) (d n : ℕ) (E : Fin d →₀ ℕ)
    (p : MvPolynomial (Fin d) R) (hp : p ∈ combined I d ^ n) :
    pieceCoefficient I d n E (Submodule.Quotient.mk ⟨p, hp⟩) =
      if _hE : E.degree ≤ n then
        gr I (n - E.degree) (p.coeff E)
          ((mem_combined_ideal_pow_iff R I d n p).mp hp E)
      else 0 := by
  classical
  unfold pieceCoefficient
  split_ifs <;> rfl

private noncomputable def gradedCoefficient {R : Type u} [CommRing R]
    (I : Ideal R) (d : ℕ) (E : Fin d →₀ ℕ) :
    Ideal.associatedGraded (combined I d) →+ Ideal.associatedGraded I :=
  DirectSum.toAddMonoid (fun n ↦ pieceCoefficient I d n E)

private theorem gradedCoefficient_monomial {R : Type u} [CommRing R]
    (I : Ideal R) (d k : ℕ) (E F : Fin d →₀ ℕ) (a : R) (ha : a ∈ I ^ k) :
    gradedCoefficient I d F (polynomialGradedMap I d (monomial E (gr I k a ha))) =
      if E = F then gr I k a ha else 0 := by
  classical
  rw [polynomialGradedMap_monomial]
  unfold gradedCoefficient gr
  rw [DirectSum.toAddMonoid_of, pieceCoefficient_gr]
  by_cases h : E = F
  · subst F
    simp only [le_add_iff_nonneg_left, Nat.zero_le, ↓reduceDIte,
      coeff_monomial, ↓reduceIte, Nat.add_sub_cancel_right]
  · simp only [coeff_monomial, h, ↓reduceIte]
    split_ifs <;> simp only [gr_zero]

private theorem gradedCoefficient_map {R : Type u} [CommRing R]
    (I : Ideal R) (d : ℕ) (F : Fin d →₀ ℕ)
    (p : MvPolynomial (Fin d) (Ideal.associatedGraded I)) :
    gradedCoefficient I d F (polynomialGradedMap I d p) = p.coeff F := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial E x =>
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, coeff_add, hx, hy]
    | of n x =>
      induction x using Submodule.Quotient.induction_on with
      | H a =>
        simpa only [coeff_monomial] using
          gradedCoefficient_monomial I d n E F a.val a.property

private theorem gr_sum {A : Type*} [CommRing A] (J : Ideal A) (n : ℕ)
    {ι : Type*} (s : Finset ι) (a : ι → A) (ha : ∀ i, a i ∈ J ^ n) :
    gr J n (∑ i ∈ s, a i) ((J ^ n).sum_mem fun i _ ↦ ha i) =
      ∑ i ∈ s, gr J n (a i) (ha i) := by
  let f : (J ^ n : Ideal A) →+ Ideal.associatedGraded J :=
    (DirectSum.of _ n).comp (Submodule.mkQ _).toAddMonoidHom
  have heq : (⟨∑ i ∈ s, a i, (J ^ n).sum_mem fun i _ ↦ ha i⟩ : (J ^ n : Ideal A)) =
      ∑ i ∈ s, (⟨a i, ha i⟩ : (J ^ n : Ideal A)) := by
    ext
    simp
  change f ⟨∑ i ∈ s, a i, _⟩ = ∑ i ∈ s, f ⟨a i, ha i⟩
  rw [heq, map_sum]

private theorem polynomialGradedMap_surjective {R : Type u} [CommRing R]
    (I : Ideal R) (d : ℕ) : Function.Surjective (polynomialGradedMap I d) := by
  classical
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, map_add _ _ _⟩
  | of n x =>
    induction x using Submodule.Quotient.induction_on with
    | H p =>
      have hc := (mem_combined_ideal_pow_iff R I d n p.val).mp p.property
      have hm (E : Fin d →₀ ℕ) : monomial E (p.val.coeff E) ∈ combined I d ^ n := by
        apply (mem_combined_ideal_pow_iff R I d n _).mpr
        intro F
        by_cases h : E = F
        · subst F; simpa using hc E
        · simp [coeff_monomial, h]
      have hterm (E : Fin d →₀ ℕ) :
          ∃ q, polynomialGradedMap I d q = gr (combined I d) n
            (monomial E (p.val.coeff E)) (hm E) := by
        by_cases hE : E.degree ≤ n
        · refine ⟨monomial E (gr I (n - E.degree) (p.val.coeff E) (hc E)), ?_⟩
          rw [polynomialGradedMap_monomial]
          exact gr_cast (combined I d) (Nat.sub_add_cancel hE) _ _ _
        · refine ⟨0, ?_⟩
          rw [map_zero]
          symm
          unfold gr
          apply (show ∀ z : Ideal.associatedGradedPiece (combined I d) n,
            z = 0 → DirectSum.of _ n z = 0 from fun z hz ↦ by rw [hz, map_zero])
          apply (Submodule.Quotient.mk_eq_zero _).mpr
          change monomial E (p.val.coeff E) ∈ combined I d ^ (n + 1)
          apply (mem_combined_ideal_pow_iff R I d (n + 1) _).mpr
          intro F
          by_cases h : E = F
          · subst F
            simp [coeff_monomial, Nat.sub_eq_zero_of_le (by omega : n + 1 ≤ E.degree)]
          · simp [coeff_monomial, h]
      choose q hq using hterm
      refine ⟨∑ E ∈ p.val.support, q E, ?_⟩
      rw [map_sum]
      simp_rw [hq]
      rw [← gr_sum]
      exact gr_congr (combined I d) rfl _ _ p.val.as_sum.symm _ _

/-- The tangent cone of the combined polynomial ideal is polynomial over the
base tangent cone, with each variable in degree one.

Source: the monomial calculation in Step 9 of
lem-trf-smooth-rational-point-completion.
(blueprint: lem-trf-polynomial-combined-associated-graded)

Proof: In degree n, the coefficient criterion for Q^n and Q^(n+1) identifies
Q^n/Q^(n+1) with the direct sum over E of degree at most n of
I^(n-degree E)/I^(n-degree E+1). Send the corresponding summand to the
monomial X^E with that homogeneous base coefficient. These coefficient maps and
finite monomial sums are mutually inverse additive maps. Multiplication sends
[a]X^E times [b]X^F to [ab]X^(E+F), so the direct sum of the maps is a ring
isomorphism. The zero-exponent summands give the stated base compatibility;
the single-variable monomials give the degree-one assertion. No regularity,
Noetherianity, or nontriviality of the base is required. -/
theorem combinedIdeal_associatedGraded
    (R : Type u) [CommRing R] (I : Ideal R) (d : ℕ) :
    let Q := I.map (C (σ := Fin d)) ⊔ idealOfVars (Fin d) R
    ∃ G : MvPolynomial (Fin d) (Ideal.associatedGraded I) ≃+*
        Ideal.associatedGraded Q,
      (∀ (n : ℕ) (a : R) (ha : a ∈ I ^ n) (hb : C a ∈ Q ^ n),
        G (C (DirectSum.of (Ideal.associatedGradedPiece I) n
          (Submodule.Quotient.mk (⟨a, ha⟩ : (I ^ n : Ideal R))))) =
            DirectSum.of (Ideal.associatedGradedPiece Q) n
              (Submodule.Quotient.mk (⟨C a, hb⟩ : (Q ^ n : Ideal (MvPolynomial (Fin d) R))))) ∧
      ∀ i : Fin d, ∃ z : Ideal.associatedGradedPiece Q 1,
        G (X i) = DirectSum.of (Ideal.associatedGradedPiece Q) 1 z := by
  classical
  intro Q
  have hbij : Function.Bijective (polynomialGradedMap I d) := by
    refine ⟨?_, polynomialGradedMap_surjective I d⟩
    intro p q hpq
    apply MvPolynomial.ext
    intro E
    simpa only [gradedCoefficient_map] using congrArg (gradedCoefficient I d E) hpq
  refine ⟨RingEquiv.ofBijective (polynomialGradedMap I d) hbij, ?_, ?_⟩
  · exact fun n a ha hb ↦ polynomialGradedMap_C I d n a ha hb
  · intro i
    refine ⟨Submodule.Quotient.mk ⟨X i, variable_mem I d i⟩, ?_⟩
    change polynomialGradedMap I d (X i) = _
    simp only [polynomialGradedMap, eval₂Hom_X']
    rfl

end MvPolynomial
