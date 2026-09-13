/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import WeilConjectures.Mathlib.RingTheory.Derivation.Basic
public import WeilConjectures.Mathlib.RingTheory.Ideal.Cotangent
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The Jacobian criterion over a regular ring

Let `R` be a regular ring, let `P = R[xᵢ]` be a polynomial ring in finitely many variables and let
`rel : σ → P` be a finite family of relations contained in a prime `Q` of `P`.  If the determinant
of the Jacobian matrix `∂ relᵢ / ∂ x_{mp j}` avoids `Q`, then `P_Q ⧸ (rel)` is a regular local
ring.

Indeed `P` is a regular ring, so `P_Q` is a regular local ring; the partial derivatives are
`R`-derivations of `P` and hence kill `Q ^ 2`, so the nonvanishing of the Jacobian determinant
modulo `Q` makes the classes of the `relᵢ` linearly independent in the cotangent space of `P_Q`;
and cutting a regular local ring down by such a family leaves a regular local ring.

## Main results

* `MvPolynomial.isRegularLocalRing_quotient_map_localization_atPrime`: the Jacobian criterion in
  the above form.
-/

@[expose] public section

open IsLocalRing MvPolynomial

variable {R : Type*} [CommRing R] {ι σ : Type*} [Fintype σ] [DecidableEq σ] [Finite ι]
  [IsRegularRing R]

/-- **The Jacobian criterion.**  If the Jacobian determinant of `rel` with respect to the variables
`mp` avoids the prime `Q`, then the localisation of `R[xᵢ] ⧸ (rel)` at `Q` is regular local. -/
theorem MvPolynomial.isRegularLocalRing_quotient_map_localization_atPrime
    (Q : Ideal (MvPolynomial ι R)) [hQ : Q.IsPrime] (mp : σ → ι) (rel : σ → MvPolynomial ι R)
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
    rw [hmax]
    exact Ideal.mem_map_of_mem _ (hrel i)
  -- the classes of the relations are linearly independent in the cotangent space of `A`
  have hli : LinearIndependent (ResidueField A)
      (fun i ↦ (maximalIdeal A).toCotangent ⟨f i, hmem i⟩) := by
    refine (IsLocalRing.linearIndependent_toCotangent_iff f hmem).mpr fun a hsq i ↦ ?_
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
    -- strip the auxiliary denominator `t` off the relation and apply the derivation step
    have hmul : ∑ j, t * b j * rel j = t * ∑ j, b j * rel j := by
      simp [Finset.mul_sum, mul_assoc]
    have htb : t * b i ∈ Q :=
      Ideal.mem_of_sum_mul_mem_sq_of_det_notMem Q (fun j ↦ pderiv (mp j)) rel hrel hdet _
        (hmul ▸ htmem) i
    have hbQ : b i ∈ Q := (hQ.mem_or_mem htb).resolve_left ht
    have hsmul : (s : MvPolynomial ι R) • a i ∈ maximalIdeal A := by
      rw [← hb i, hmax]
      exact Ideal.mem_map_of_mem _ hbQ
    rw [Algebra.smul_def] at hsmul
    exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units A s)).mp hsmul
  have hquot := IsRegularLocalRing.quotient_span_range f hmem hli
  have hspan : Ideal.span (Set.range f)
      = (Ideal.span (Set.range rel)).map (algebraMap (MvPolynomial ι R) A) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rwa [hspan] at hquot
