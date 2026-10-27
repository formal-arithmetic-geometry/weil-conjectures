/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Operations

/-!
# Spectrum of localization at closed-fibre regular scalars

Source: Stacks Project, More on Flatness, Tag 05DE (`lemma-homothety-spectrum`),
statement and proof in `flat.tex`.
(blueprint: lem-sfb-fibre-regular-localization-spectrum).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace RingTheory

/-- The localization at scalars injective on the finite closed-fibre module is semilocal.
The submonoid `nonZeroSMulDivisors` supplies multiplicative closure, and the first clause
identifies its carrier with exactly the injective scalar maps. The spectrum and maximal-ideal
correspondences are contraction bijections; `Maximal` means maximal under ideal inclusion.
The quotient module has its canonical quotient-ring action from Mathlib's torsion API.

Source: Stacks Project, More on Flatness, Tag 05DE (`lemma-homothety-spectrum`),
statement and proof in `flat.tex`.
(blueprint: lem-sfb-fibre-regular-localization-spectrum).

Proof, following the seven steps of the node:
1. The identity and composites of injective scalar maps are injective. Write I = m_A B,
   M = N/IN and pi : B -> C = B/I. For each z, Ann_B(z) = pi^{-1}(Ann_C(z));
   the surjective quotient map preserves and reflects primality, giving the bijection
   Ass_C(M) -> Ass_B(M) of exact element-annihilator primes (definition 00LA, Tag 05BY).
2. Apply lem-weil-pbc-noetherian-associated-primes-finite over C, which alone is Noetherian.
   The finite C-module hypothesis gives finitely many associated primes over C and hence B.
3. Apply lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes over C.
   A scalar fails injectivity exactly when it kills a nonzero element. Taking inverse
   images under pi gives B minus Sigma as the union of the finitely many associated primes.
4. By lem-weil-pbc-localization-spectrum-embedding, contraction is injective with image the
   primes disjoint from Sigma. Apply lem-weil-pbc-prime-avoidance to the finite union in
   step 3 to identify these with primes contained in an associated prime. If the family is
   empty, neither condition holds: every ideal contains zero, whereas the empty union does not.
5. In T = Sigma^{-1}B, a/s belongs to an ideal J iff a/1 does, since s/1 is a unit.
   Thus contraction determines ideals and reflects inclusions, including between primes.
6. The contraction of any proper ideal of T misses Sigma. Prime avoidance puts it inside
   an associated prime q; step 5 then puts the ideal inside the prime of T over q.
   It follows in both directions that maximal ideals of T correspond exactly to the
   maximal members of Ass_B(M). Step 2 gives finiteness, and step 1 gives the asserted
   inverse-image description over C.
7. If M is zero, every scalar is injective and no proper element annihilator is prime.
   Thus Sigma is all of B and contains zero. The fraction relation makes 1/1 = 0/1,
   so T is the zero ring and has neither primes nor maximal ideals.
-/
theorem fibre_regular_localization_spectrum
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] (N : Type w) [AddCommGroup N] [Module B N]
    [IsNoetherianRing (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B))]
    [Module.Finite (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) (N ⧸
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B N)))] :
    (∀ b : B, b ∈ (nonZeroSMulDivisors B (N ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B) •
      (⊤ : Submodule B N)))) ↔ Function.Injective (fun z : (N ⧸ ((IsLocalRing.maximalIdeal A).map
      (algebraMap A B) • (⊤ : Submodule B N))) ↦ b • z)) ∧
    Set.BijOn (PrimeSpectrum.comap (algebraMap B (Localization (nonZeroSMulDivisors B (N ⧸
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B N))))))) Set.univ
      {p : PrimeSpectrum B | ∃ q ∈ annihilatorAssociatedPrimes B (N ⧸ ((IsLocalRing.maximalIdeal
        A).map (algebraMap A B) • (⊤ : Submodule B N))), p.asIdeal ≤ q} ∧
    {J : Ideal (Localization (nonZeroSMulDivisors B (N ⧸ ((IsLocalRing.maximalIdeal A).map
      (algebraMap A B) • (⊤ : Submodule B N))))) | J.IsMaximal}.Finite ∧
    Set.BijOn (Ideal.comap (algebraMap B (Localization (nonZeroSMulDivisors B (N ⧸
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B N)))))))
      {J : Ideal (Localization (nonZeroSMulDivisors B (N ⧸ ((IsLocalRing.maximalIdeal A).map
        (algebraMap A B) • (⊤ : Submodule B N))))) | J.IsMaximal}
      {q : Ideal B | Maximal (fun q ↦ q ∈ annihilatorAssociatedPrimes B (N ⧸
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B N)))) q} ∧
    (∀ J : Ideal (Localization (nonZeroSMulDivisors B (N ⧸ ((IsLocalRing.maximalIdeal A).map
      (algebraMap A B) • (⊤ : Submodule B N))))), J.IsMaximal →
      ∃ Q ∈ annihilatorAssociatedPrimes (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) (N
        ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B N))),
        Ideal.comap (algebraMap B (Localization (nonZeroSMulDivisors B (N ⧸
          ((IsLocalRing.maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B N)))))) J =
          Ideal.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map (algebraMap A B))) Q) ∧
    (Subsingleton (N ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B N))) →
      (nonZeroSMulDivisors B (N ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B) • (⊤ :
        Submodule B N)))) = ⊤ ∧ Subsingleton (Localization (nonZeroSMulDivisors B (N ⧸
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B N))))) ∧ IsEmpty
        (PrimeSpectrum (Localization (nonZeroSMulDivisors B (N ⧸ ((IsLocalRing.maximalIdeal A).map
        (algebraMap A B) • (⊤ : Submodule B N)))))) ∧
        ∀ J : Ideal (Localization (nonZeroSMulDivisors B (N ⧸ ((IsLocalRing.maximalIdeal A).map
          (algebraMap A B) • (⊤ : Submodule B N))))), ¬ J.IsMaximal) := by
  sorry

end RingTheory
