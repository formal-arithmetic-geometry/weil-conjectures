/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Finite quotient detection by prime localizations

Source: Stacks Project, Algebra, Tag 07N9, quotient decomposition and cofinal ideal powers.
(blueprint: lem-weil-pbc-local-tensor-quotient-detection)
-/

@[expose] public section

universe u v w
open scoped TensorProduct
namespace AdicCompletion

/-- Sufficiently deep local maximal-ideal reductions detect any fixed tensor quotient.
Source: Stacks Project, Algebra, Tag 07N9, using Tags 00JA, 00CT and 0394.
(blueprint: lem-weil-pbc-local-tensor-quotient-detection)

Proof: Put A = R_p and B = A tensor_R S, a finite Noetherian A-algebra. For fixed n > 0,
B/m^n B is Artinian, and its canonical product decomposition into its localizations
at maximal ideals is an isomorphism (Tags 00JA and 00CT). These maximal ideals correspond
to primes q of S over p, and the factors are S_q/m^n S_q. There are finitely many q.
In each S_q the ideal m S_q has radical its maximal ideal N_q, since the special fibre
is a finite-dimensional local algebra over the residue field of A. Noetherianity gives
a positive c_q with N_q^{c_q} contained in m S_q. Choose k at least n and at least
n c_q for every q. Then N_q^k is contained in m^n S_q for all q. The assumed vanishings
therefore kill the image of the finite sum in every factor of B/m^n B; injectivity of
the product decomposition kills the sum itself. Identify B/m^n B with
(A/m^n) tensor_R S to obtain the conclusion. For n = 0 the conclusion lies in the zero
quotient, so take k = 0. If there are no q, the product and the Artinian quotient are
zero. Empty sums also satisfy the conclusion. -/
theorem local_tensor_quotient_detection
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] (n : ℕ) :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let Q := p.primesOver S
    ∃ k : ℕ, n ≤ k ∧ ∀ (ι : Type w) (t : Finset ι) (r : ι → A) (s : ι → S),
      (∀ q : Q,
        ∑ i ∈ t, Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ k)
          (Localization.localRingHom p q.1 (algebraMap R S)
            (Ideal.LiesOver.over (P := q.1) (p := p)) (r i) *
            algebraMap S (Localization.AtPrime q.1) (s i)) = 0) →
      (∑ i ∈ t, (Ideal.Quotient.mk (m ^ n) (r i)) ⊗ₜ[R] s i) = 0 := by sorry

end AdicCompletion
