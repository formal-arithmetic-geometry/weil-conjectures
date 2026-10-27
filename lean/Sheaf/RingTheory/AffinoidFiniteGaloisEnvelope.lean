/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Finite Galois envelopes of reduced affinoid algebras

Source: Kedlaya, More on affinoid algebras, proof of Theorem 4, PDF p. 2;
Conrad, Several approaches to non-archimedean geometry, Theorem 1.2.6(2),(3), p. 6
(blueprint: lem-trf-affinoid-finite-galois-envelope).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace RestrictedSeries

/-- A nonzero reduced affinoid algebra has a finite, jointly injective family of
finite normal affinoid envelopes, Galois over suitable Tate normalization algebras.
The fraction-field algebra map is required to extend the specified Tate inclusion.
Source: Kedlaya, More on affinoid algebras, Theorem 4 proof, PDF p. 2, steps (a),(b);
Conrad, Theorem 1.2.6(2),(3), printed p. 6
(blueprint: lem-trf-affinoid-finite-galois-envelope).

Proof:
1. By lem-trf-affinoid-polynomial-closed-point-comparison at J = 0 and
lem-weil-pbc-finite-algebra-noetherian, C is Noetherian. Its finitely many minimal
primes (lem-sc-finite-minimal-primes-over-ideal) intersect in zero by reducedness
and lem-per-nilradical-minimal-prime-intersection. There is at least one since C
is nonzero. Thus C injects into the product of its nonzero domain quotients A_i.
2. Apply lem-trf-tate-normalization-lift to each domain quotient. This gives a finite
injective S_i -> A_i with S_i a Tate algebra. By lem-trf-finite-domain-fraction-degree,
Frac(A_i)/Frac(S_i) is finite, and lem-weil-pbc-finite-algebra-is-integral gives
monic equations for all elements of A_i.
3. Apply lem-trf-tate-variable-roots-separable-compositum: after replacing S_i by
the finite free Tate algebra T_i with sufficiently high p-power-root variables,
Frac(A_i) Frac(T_i)/Frac(T_i) is separable. In characteristic zero use exponent one.
4. Use lem-weil-pbc-finite-galois-receiving-separable-extensions to embed this field
in a finite Galois extension N_i of Frac(T_i). Take B_i to be the integral closure
of T_i in N_i (def-weil-pbc-integral-closure). The monic equations from step 2 give
an injection A_i -> B_i, hence the required map j_i from C.
5. By lem-trf-tate-integrally-closed, T_i is normal; it is also Noetherian.
Apply lem-weil-pbc-noetherian-normal-separable-integral-closure-finite to get
T_i-finiteness. By lem-weil-pbc-integral-closure-finite-extension-normal, B_i is a
nonzero normal domain with fraction field N_i, via the actual inclusion.
6. Products of finite S_i-generators of T_i and finite T_i-generators of B_i generate
B_i over S_i, hence over A_i and C. Joint injectivity follows from the zero
intersection of the minimal primes, without individual injectivity of j_i.
7. By lem-trf-finite-algebra-affinoid-presentation, B_i has a Tate quotient Banach
norm. Apply lem-trf-affinoid-homomorphism-bounded to j_i and the Tate inclusion
to obtain the positive bounds D_i and E_i. Zero-variable normalizations are included.
-/
theorem affinoid_finite_galois_envelope
    (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
    (hK : ∃ a : K, a ≠ 0 ∧ ‖a‖ ≠ 1)
    (C : Type v) [NormedCommRing C] [Nontrivial C] [IsReduced C]
    (scalar : K →+* C) (hC : IsAffinoidQuotient K C scalar) :
    ∃ (s : ℕ), 1 ≤ s ∧
      ∃ (B : Fin s → Type (max u v)) (_ : ∀ i : Fin s, NormedCommRing (B i))
        (j : ∀ i : Fin s, C →+* B i) (d : Fin s → ℕ)
        (t : ∀ i : Fin s,
          (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin (d i) ↦ (1 : ℝ)))
            →+* B i),
        Function.Injective (fun c : C ↦ fun i ↦ j i c) ∧
        ∀ i : Fin s,
          (j i).Finite ∧ (t i).Finite ∧ Function.Injective (t i) ∧
          (t i).comp (constants K (d i)) = (j i).comp scalar ∧
          IsAffinoidQuotient K (B i) ((j i).comp scalar) ∧
          ∃ (_ : IsDomain (B i)), IsIntegrallyClosed (B i) ∧
            ∃ (_ : IsDomain
              ↥(MvPowerSeries.IsRestricted.subring (R := K)
                (fun _ : Fin (d i) ↦ (1 : ℝ)))),
              IsIntegrallyClosed
                ↥(MvPowerSeries.IsRestricted.subring (R := K)
                  (fun _ : Fin (d i) ↦ (1 : ℝ))) ∧
              (∃ (_ : Algebra
                (FractionRing ↥(MvPowerSeries.IsRestricted.subring (R := K)
                  (fun _ : Fin (d i) ↦ (1 : ℝ)))) (FractionRing (B i))),
                (algebraMap
                  (FractionRing ↥(MvPowerSeries.IsRestricted.subring (R := K)
                    (fun _ : Fin (d i) ↦ (1 : ℝ)))) (FractionRing (B i))).comp
                  (algebraMap
                    ↥(MvPowerSeries.IsRestricted.subring (R := K)
                      (fun _ : Fin (d i) ↦ (1 : ℝ)))
                    (FractionRing ↥(MvPowerSeries.IsRestricted.subring (R := K)
                      (fun _ : Fin (d i) ↦ (1 : ℝ)))))
                  = (algebraMap (B i) (FractionRing (B i))).comp (t i) ∧
                FiniteDimensional
                  (FractionRing ↥(MvPowerSeries.IsRestricted.subring (R := K)
                    (fun _ : Fin (d i) ↦ (1 : ℝ)))) (FractionRing (B i)) ∧
                IsGalois
                  (FractionRing ↥(MvPowerSeries.IsRestricted.subring (R := K)
                    (fun _ : Fin (d i) ↦ (1 : ℝ)))) (FractionRing (B i))) ∧
              ∃ D E : ℝ, 0 < D ∧ 0 < E ∧
                (∀ c : C, ‖j i c‖ ≤ D * ‖c‖) ∧
                ∀ a, ‖t i a‖ ≤ E * MvPowerSeries.gaussNorm
                  (norm : K → ℝ) (fun _ : Fin (d i) ↦ 1) a.val := by
  sorry

end RestrictedSeries
