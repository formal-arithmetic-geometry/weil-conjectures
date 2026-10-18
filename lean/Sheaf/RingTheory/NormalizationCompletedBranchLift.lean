/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs

import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# A closed normalization point lifts to a completed branch

Source: Swanson–Huneke, *Integral Closure of Ideals, Rings, and Modules*, Lemma 4.8.3,
printed p. 84 (PDF p. 98), together with Corollary 2.1.13
(blueprint: lem-trf-normalization-completed-branch-lift).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

@[expose] public section

namespace RingTheory

/-- A closed point of the normalization of a Noetherian local domain lifts to one
normalization branch of its completed local ring.

Source: Swanson–Huneke, *Integral Closure of Ideals, Rings, and Modules*, Lemma 4.8.3,
printed p. 84 (PDF p. 98), together with Corollary 2.1.13
(blueprint: lem-trf-normalization-completed-branch-lift).

Proof:
1. Completion is faithfully flat, Noetherian and local with maximal ideal n = mH
   (`lem-weil-pbc-local-completion-faithfully-flat`,
   `lem-weil-pbc-adic-completion-noetherian`, `lem-weil-pbc-local-completion-local-ring`).
   Its minimal primes p_i form a finite nonempty list
   (`lem-weil-pbc-noetherian-finitely-many-minimal-primes`,
   `lem-weil-pbc-prime-contains-minimal-prime`).
2. Put C = H tensor_A B. The identifications C tensor_B N = H tensor_A N identify
   exactness of scalar extension with exactness over A, so B to C is faithfully flat
   (`def-weil-pbc-faithfully-flat-ring-map`).
3. Lift q to a prime Q of C (`lem-weil-pbc-faithfully-flat-surjective-spectrum`).
   Tensor balancing shows that its H-contraction contains mH, hence equals n.
4. Flatness preserves injectivity of multiplication by each nonzero element of A
   (`lem-trf-flat-tensor-preserves-injection`). Such elements avoid all p_i
   (`lem-pc-minimal-prime-avoids-nonzerodivisor`), giving compatible maps
   Frac(A) to Frac(H/p_i).
5. Tensoring B into Frac(A) gives an injection C into S^{-1}H, S = A minus zero
   (`lem-trf-flat-tensor-preserves-injection`). The identification sends
   h tensor (a/s) to iota(a)h/s; its inverse sends h/s to h tensor (1/s)
   (`def-weil-pbc-module-localization`).
6. Monic equations show that B maps into every branch normalization T_i
   (`def-weil-pbc-integral-closure`). The tensor universal property gives
   psi_i : C to T_i, h tensor b mapping to h_bar times b_i
   (`lem-weil-pbc-algebra-tensor-base-change-universal-property`). Put U = product T_i
   and D = image(psi) in U.
7. If psi(c) = 0 and c maps to h/s, then h is in every minimal prime, hence in every
   prime (`lem-weil-pbc-prime-contains-minimal-prime`). It is nilpotent
   (`lem-weil-pbc-zero-locus-eq-iff-radical-eq`), so c is nilpotent by the injection.
   Thus ker(psi) is contained in Q, and Q descends to a proper prime P of D.
8. The inclusion D into U is integral: lift the coefficients of one monic equation
   over H/p_i per coordinate, and multiply these finitely many monic polynomials.
   Their product vanishes in each coordinate and its H-coefficients lie in D
   (`def-weil-pbc-integral-closure`).
9. Lift P to a prime of U (`lem-weil-pbc-integral-injective-lying-over`), and select
   its factor prime M in some T_i (`lem-weil-pbc-product-prime-factor`).
10. Set p = p_i and j(b) = psi_i(1 tensor b). Contracting M to B gives q and
    contracting it to H gives n, hence to H/p gives n/p. Tensor balancing gives
    j(a) = psi_i(iota(a) tensor 1), the required compatibility on A.
-/
theorem normalizationCompletedBranchLift
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (q : Ideal (integralClosure A (FractionRing A))) [q.IsPrime]
    (hqA : q.comap (algebraMap A (integralClosure A (FractionRing A))) =
      IsLocalRing.maximalIdeal A) :
    ∃ (p : Ideal (AdicCompletion (IsLocalRing.maximalIdeal A) A)),
      p ∈ minimalPrimes (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
      ∃ (j : integralClosure A (FractionRing A) →+* integralClosure
          (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p)
          (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p)))
        (M : Ideal (integralClosure
          (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p)
          (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p)))),
        M.IsPrime ∧
        Ideal.comap j M = q ∧
        Ideal.comap (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p)
          (integralClosure
            (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p)
            (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p)))) M =
          Ideal.map (Ideal.Quotient.mk p)
            (RingHom.ker (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A)).toRingHom) ∧
        ∀ a : A,
          j (algebraMap A (integralClosure A (FractionRing A)) a) =
            algebraMap (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p)
              (integralClosure
                (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p)
                (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ p)))
              (Ideal.Quotient.mk p
                (AdicCompletion.of (IsLocalRing.maximalIdeal A) A a)) := by
  sorry

end RingTheory
