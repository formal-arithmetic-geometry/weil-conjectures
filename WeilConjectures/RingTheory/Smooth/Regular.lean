/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import WeilConjectures.Mathlib.RingTheory.Derivation.Basic
public import WeilConjectures.Mathlib.RingTheory.Ideal.Cotangent
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Standard smooth algebras over a regular ring are regular

Let `R` be a regular ring and let `S` be a standard smooth `R`-algebra, so that
`S = R[x₁, …, x_n] ⧸ (f₁, …, f_c)` for relations whose Jacobian matrix is invertible in `S`.
Then `S` is a regular ring.

The proof is the Jacobian criterion.  Fix a prime `𝔮` of `S` and let `Q` be its contraction to
`P := R[x₁, …, x_n]`.  Since `P` is a regular ring, `P_Q` is a regular local ring, and
`S_𝔮 = P_Q ⧸ (f₁, …, f_c)`.  The partial derivatives `∂/∂xⱼ` are `R`-derivations of `P` and hence
kill `Q ^ 2`; since the Jacobian is a unit its determinant is nonzero in the domain `P ⧸ Q`, so the
classes of `f₁, …, f_c` in the cotangent space of `P_Q` are linearly independent.  Cutting a
regular local ring down by such a family leaves a regular local ring.

## Main results

* `MvPolynomial.mem_of_mul_sum_mem_sq`: the Jacobian criterion at the level of the polynomial
  ring, in the form of a statement about relations modulo `Q ^ 2`.
* `Algebra.IsStandardSmooth.isRegularRing`: a standard smooth algebra over a regular ring is a
  regular ring.  In particular a standard smooth algebra over a field is a regular ring.
-/

@[expose] public section

open IsLocalRing MvPolynomial

attribute [local instance] Fintype.ofFinite

section Jacobian

variable {R : Type*} [CommRing R] {ι σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The key step of the Jacobian criterion.  Let `Q` be a prime of `R[xᵢ]` containing the
relations `rel`, and suppose the Jacobian determinant of `rel` with respect to the variables
`mp` is not in `Q`.  If `t ∉ Q` and `t * ∑ bᵢ relᵢ ∈ Q ^ 2`, then every `bᵢ` lies in `Q`. -/
theorem MvPolynomial.mem_of_mul_sum_mem_sq (Q : Ideal (MvPolynomial ι R)) [Q.IsPrime]
    (mp : σ → ι) (rel : σ → MvPolynomial ι R) (hrel : ∀ i, rel i ∈ Q)
    (hdet : (Matrix.of fun j i ↦ pderiv (mp j) (rel i)).det ∉ Q)
    (b : σ → MvPolynomial ι R) {t : MvPolynomial ι R} (ht : t ∉ Q)
    (hz : t * ∑ i, b i * rel i ∈ Q ^ 2) (i : σ) : b i ∈ Q := by
  have h2 : t * ∑ i, b i * rel i = ∑ i, (t * b i) * rel i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ (mul_assoc _ _ _).symm
  have key : ∀ j : σ, ∑ i, (t * b i) * pderiv (mp j) (rel i) ∈ Q := by
    intro j
    have h1 : (pderiv (mp j)) (∑ i, (t * b i) * rel i) ∈ Q :=
      Ideal.derivation_mem_of_mem_sq _ Q (h2 ▸ hz)
    have h3 : ∑ i, rel i * (pderiv (mp j)) (t * b i) ∈ Q :=
      Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_right _ _ (hrel i)
    have h4 : ∑ i, (t * b i) * (pderiv (mp j)) (rel i)
        = (pderiv (mp j)) (∑ i, (t * b i) * rel i) - ∑ i, rel i * (pderiv (mp j)) (t * b i) := by
      rw [map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      ring
    rw [h4]
    exact Ideal.sub_mem _ h1 h3
  set M : Matrix σ σ (MvPolynomial ι R ⧸ Q) :=
    (Matrix.of fun j i ↦ pderiv (mp j) (rel i)).map (Ideal.Quotient.mk Q) with hM
  have hdetM : M.det ≠ 0 := by
    have hmap : M.det = Ideal.Quotient.mk Q (Matrix.of fun j i ↦ pderiv (mp j) (rel i)).det :=
      (RingHom.map_det (Ideal.Quotient.mk Q) _).symm
    rw [hmap]
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hdet
  have hw : M.mulVec (fun i ↦ Ideal.Quotient.mk Q (t * b i)) = 0 := by
    funext j
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.map_apply, Matrix.of_apply,
      Pi.zero_apply, ← map_mul, ← map_sum, Ideal.Quotient.eq_zero_iff_mem]
    simpa only [mul_comm] using key j
  have hw0 := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdetM hw) i
  simp only [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at hw0
  exact (Ideal.IsPrime.mem_or_mem ‹Q.IsPrime› hw0).resolve_left ht

variable [Finite ι] [IsRegularRing R]

/-- The Jacobian criterion: if the Jacobian determinant of `rel` with respect to the variables
`mp` avoids the prime `Q`, then the localisation of `R[xᵢ] ⧸ (rel)` at `Q` is regular. -/
theorem MvPolynomial.isRegularLocalRing_quotient_map_localization_atPrime
    (Q : Ideal (MvPolynomial ι R)) [Q.IsPrime] (mp : σ → ι) (rel : σ → MvPolynomial ι R)
    (hrel : ∀ i, rel i ∈ Q)
    (hdet : (Matrix.of fun j i ↦ pderiv (mp j) (rel i)).det ∉ Q) :
    IsRegularLocalRing (Localization.AtPrime Q ⧸ (Ideal.span (Set.range rel)).map
      (algebraMap (MvPolynomial ι R) (Localization.AtPrime Q))) := by
  set A := Localization.AtPrime Q
  have : IsRegularLocalRing A := IsRegularRing.isRegularLocalRing_localization Q
  have hmax : maximalIdeal A = Q.map (algebraMap (MvPolynomial ι R) A) :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal Q A).symm
  set f : σ → A := fun i ↦ algebraMap (MvPolynomial ι R) A (rel i)
  have hmem : ∀ i, f i ∈ maximalIdeal A := fun i ↦ by
    rw [hmax]; exact Ideal.mem_map_of_mem _ (hrel i)
  -- the classes of the relations are linearly independent in the cotangent space of `A`
  have hli : LinearIndependent (ResidueField A)
      (fun i ↦ (maximalIdeal A).toCotangent ⟨f i, hmem i⟩) := by
    refine IsLocalRing.linearIndependent_toCotangent f hmem fun a hsq i ↦ ?_
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite Q.primeCompl a
    choose b hb using hs
    have key : algebraMap (MvPolynomial ι R) A (∑ i, b i * rel i)
        ∈ (Q ^ 2).map (algebraMap (MvPolynomial ι R) A) := by
      rw [Ideal.map_pow, ← hmax, map_sum]
      have hterm : ∀ i, algebraMap (MvPolynomial ι R) A (b i * rel i)
          = (s : MvPolynomial ι R) • (a i * f i) := fun i ↦ by
        rw [map_mul, hb i, smul_mul_assoc]
      rw [Finset.sum_congr rfl (fun i _ ↦ hterm i), ← Finset.smul_sum, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hsq
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl] at key
    obtain ⟨t, ht, htmem⟩ := key
    have hbQ : b i ∈ Q :=
      MvPolynomial.mem_of_mul_sum_mem_sq Q mp rel hrel hdet b ht htmem i
    have : (s : MvPolynomial ι R) • a i ∈ maximalIdeal A := by
      rw [← hb i, hmax]; exact Ideal.mem_map_of_mem _ hbQ
    rw [Algebra.smul_def] at this
    exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units A s)).mp this
  have hquot := IsRegularLocalRing.quotient_span_range f hmem hli
  have hspan : Ideal.span (Set.range f)
      = (Ideal.span (Set.range rel)).map (algebraMap (MvPolynomial ι R) A) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rwa [hspan] at hquot

end Jacobian

namespace Algebra

/-- **A standard smooth algebra over a regular ring is regular.**  In particular, a standard
smooth algebra over a field is a regular ring, so all its localisations at primes are regular
local rings. -/
theorem IsStandardSmooth.isRegularRing {R : Type*} [CommRing R] [IsRegularRing R]
    {S : Type*} [CommRing S] [Algebra R S] [IsStandardSmooth R S] : IsRegularRing S := by
  classical
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  have hsurj : Function.Surjective (algebraMap P.Ring S) := P.algebraMap_surjective
  have hquot : IsRegularRing (P.Ring ⧸ RingHom.ker (algebraMap P.Ring S)) := by
    refine IsRegularRing.quotient_of_forall_isRegularLocalRing _ fun Q hQ hle ↦ ?_
    have hle' : P.ker ≤ Q := hle
    have hrel : ∀ i, P.relation i ∈ Q := fun i ↦ hle' (P.relation_mem_ker i)
    have hmat : (Matrix.of fun j i ↦ pderiv (P.map j) (P.relation i)) = P.jacobiMatrix := by
      ext j i; rw [P.jacobiMatrix_apply]; rfl
    have hjac : (Matrix.of fun j i ↦ pderiv (P.map j) (P.relation i)).det ∉ Q := by
      intro hmem
      have h1 : P.jacobian ∈ Q.map (algebraMap P.Ring S) := by
        rw [P.jacobian_eq_jacobiMatrix_det, ← hmat]
        exact Ideal.mem_map_of_mem _ hmem
      have h2 : Q.map (algebraMap P.Ring S) ≠ ⊤ := by
        intro h
        have hc := Ideal.comap_map_of_surjective _ hsurj Q
        rw [h, Ideal.comap_top] at hc
        exact hQ.ne_top (hc.trans (sup_eq_left.mpr hle')).symm
      exact h2 (Ideal.eq_top_of_isUnit_mem _ h1 P.jacobian_isUnit)
    have := MvPolynomial.isRegularLocalRing_quotient_map_localization_atPrime
      (R := R) (ι := ι) (σ := σ) Q P.map P.relation hrel hjac
    rwa [P.span_range_relation_eq_ker] at this
  exact IsRegularRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)

end Algebra
