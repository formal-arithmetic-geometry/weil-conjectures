/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF lead L
-/
module

public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Jacobson radical descends through an integral overring

Source: Stacks Project, Varieties Lemma 09N2 proof, paragraph beginning
“Moreover, `Spec(B') -> Spec(A)` is surjective” (blueprint:
lem-sc-integral-overring-jacobson-power).
-/

@[expose] public section

universe u v w

/--
(blueprint: lem-sc-integral-overring-jacobson-power)
Let `B` be a semilocal commutative ring, let `B'` be a semilocal commutative
ring integral over `B`, and let `A` be an intermediate commutative ring.
If `Spec(B') → Spec(A)` is surjective, then `A` is semilocal and
`J(A) = √(m_B A)`.  Every element of `A` lying in `J(B')` therefore has a
positive power in `m_B A`.  This is the Jacobson-radical argument in
Stacks, Varieties Lemma 09N2, proof of `lemma-semi-local-dimension-one-conductor`.

Proof (following the DAG node):
1. Injectivity and the scalar tower identify `B ⊆ A ⊆ B'`. Integrality of `B'`
   over `B` implies integrality of `A` over `B` and of `B'` over `A`
   (def-weil-pbc-integral-closure).
2. Spec-surjectivity lifts each maximal ideal of `A` to a prime of `B'`.
   Integrality makes that prime maximal
   (lem-weil-pbc-integral-prime-over-maximal-maximal), and contraction of a maximal
   ideal is maximal (lem-weil-pbc-integral-algebra-ideal-in-radical). Thus the
   maximal ideals of `A` are contractions of the finitely many maximal ideals of `B'`.
3. Integrality gives `m_B A ≤ J(A)`
   (lem-weil-pbc-integral-algebra-ideal-in-radical), hence `√(m_B A) ≤ J(A)`.
   A prime of `A` containing `m_B A` contracts to a prime containing the finite
   intersection of the maximal ideals of `B`. Their product lies in this
   intersection, so primality forces the contraction to contain one maximal ideal,
   hence to equal it. The original prime is then maximal
   (lem-weil-pbc-integral-prime-over-maximal-maximal). The intersection of these
   primes therefore contains `J(A)`, proving the reverse inclusion. If `B` has no
   maximal ideals, `m_B` and its extension are the unit ideals, and equality holds.
4. An element of `A` mapping into `J(B')` lies in every maximal ideal of `A`
   by step 2. Step 3 puts it in `√(m_B A)`, so a positive power lies in `m_B A`.
-/
theorem integral_overring_jacobson_power
    (B : Type u) (A : Type v) (B' : Type w)
    [CommRing B] [CommRing A] [CommRing B']
    [Algebra B A] [Algebra A B'] [Algebra B B']
    [IsScalarTower B A B']
    [Finite (MaximalSpectrum B)] [Finite (MaximalSpectrum B')]
    [Algebra.IsIntegral B B']
    [FaithfulSMul B A] [FaithfulSMul A B']
    (hspec : Function.Surjective (PrimeSpectrum.comap (algebraMap A B')))
    : Finite (MaximalSpectrum A) ∧
      Ideal.jacobson (⊥ : Ideal A) =
        (Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))).radical ∧
      ∀ (x : A),
        algebraMap A B' x ∈ Ideal.jacobson (⊥ : Ideal B') →
          ∃ m : ℕ, 0 < m ∧
            x ^ m ∈ Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B)) := by
  sorry
