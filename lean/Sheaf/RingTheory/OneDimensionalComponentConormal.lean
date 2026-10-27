module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Conormal torsion of a one-dimensional completed component

Source: Stacks Project, More on Algebra, Tag 0AW3, `lemma-not-formally-catenary`,
the paragraph treating dimension one
(blueprint: lem-per-one-dimensional-component-conormal).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AdicCompletion

/-- A positive power of a minimal prime defining a one-dimensional component of the
maximal-ideal completion vanishes upon localization at that prime, and its conormal
module is annihilated by a positive power of the extended maximal ideal.

Source: Stacks Project, More on Algebra, Tag 0AW3, `lemma-not-formally-catenary`,
dimension-one paragraph (blueprint: lem-per-one-dimensional-component-conormal).

Proof:
1. The completion B is Noetherian by lem-weil-pbc-adic-completion-noetherian and local
   with maximal ideal mB by lem-weil-pbc-local-completion-local-ring. Every ideal is
   finitely generated, by def-weil-pbc-noetherian-ring.
2. The ring B_q is Noetherian by lem-weil-pbc-localization-noetherian. Minimality of q
   and lem-weil-pbc-minimal-prime-localization-radical identify the radical of zero
   with qB_q. Apply lem-weil-pbc-fg-ideal-radical-power to obtain a positive n with
   (qB_q)^n = 0. Extension commutes with products, so J = q^n has JB_q = 0.
3. The conormal M = J/J^2 is finite and killed by J. At a prime p not containing q,
   an element of q outside p has its nth power in J and becomes an invertible
   annihilator of M_p, so M_p = 0. At q, JB_q = 0 implies M_q = 0 by the fraction
   description in def-weil-pbc-localization-at-prime. A prime strictly between q and
   mB would induce a chain of length two in B/q, contradicting its dimension one
   in def-weil-pbc-krull-dimension-ring. Hence M is supported only at mB.
4. By lem-weil-pbc-finite-module-support-annihilator, V(Ann M) is contained in {mB}.
   The intersection-of-primes clause of lem-weil-pbc-zero-locus-eq-iff-radical-eq
   gives mB contained in the radical of Ann M, including when M = 0. Since mB is
   finitely generated, lem-weil-pbc-fg-ideal-radical-power gives a positive c with
   (mB)^c contained in Ann M. This is precisely the second conclusion. -/
theorem exists_pow_minimalPrime_localization_eq_bot_and_cotangent_annihilated
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (q : Ideal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) [q.IsPrime]
    (hq : q ∈ minimalPrimes (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (hdim : ringKrullDim ((AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ q) = 1) :
    ∃ n c : ℕ, 1 ≤ n ∧ 1 ≤ c ∧
      (q ^ n).map
        (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (Localization.AtPrime q)) = ⊥ ∧
      ((IsLocalRing.maximalIdeal A).map
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))) ^ c ≤
        Module.annihilator (AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (q ^ n).Cotangent := by
  sorry

end AdicCompletion
