/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs

import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
import Sheaf.RingTheory.PolynomialNagata
import WeilConjectures.RingTheory.FiniteOverNagata
import WeilConjectures.RingTheory.NagataLocalization
import Sheaf.RingTheory.ReducedNoetherianTotalRingFractions
import Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import WeilConjectures.RingTheory.CompletionOfDVR
import WeilConjectures.RingTheory.CompletionFiniteExtension
import WeilConjectures.RingTheory.CompletionDimension
import Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Normalization and completion of a reduced local algebraic curve

Source: Stacks Project, `varieties.tex`, Tags 0C3S and 0C3V
(blueprint: lem-trf-curve-normalization-completion).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open scoped TensorProduct

namespace RingTheory

/-- Normalization of a reduced one-dimensional local algebra commutes with completion.

Source: Stacks Project, `varieties.tex`, Tags 0C3S and 0C3V
(blueprint: lem-trf-curve-normalization-completion).

Proof:
1. Fields are Nagata. Polynomial stability, quotients and localization show that an
   essentially finite type algebra over a field is Nagata, hence Noetherian.
2. Decompose its total fraction ring as the product of the fields at its minimal primes
   (`lem-weil-pbc-reduced-noetherian-total-ring-fractions`). Each component quotient is a
   one-dimensional local Nagata domain.
3. Each component normalization is finite by the Japanese property and Dedekind by
   `lem-sc-integral-closure-dedekind-surjective-fibres`. Their product is the normalization B
   and is finite over A: coordinate generators suffice, and integrality is componentwise.
4. Localize B at a prime over the maximal ideal. The product description selects a Dedekind
   factor and a nonzero maximal prime, hence a DVR by `lem-sc-dedekind-localization-dvr`.
   Its completion is a DVR (`lem-weil-pbc-completion-of-dvr-is-dvr`), hence normal.
5. The finite-extension completion decomposition
   (`lem-weil-pbc-completion-finite-extension`) identifies the completed tensor product C
   with the finite product of these completed DVRs, compatibly with both algebra maps.
6. Completion is flat. Tensoring A into B injects the completed ring R into the reduced
   ring C, so R is reduced. `lem-weil-pbc-completion-dimension` gives dimension one.
   The base-changed finite generators make C finite and integral over R.
7. C is Noetherian and a finite product of normal domains, hence integrally closed in its
   total fractions by `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`.
8. Clear the denominators of finite generators of B with a single regular element s of A.
   Then sB lies in A. Flatness preserves regularity of s on both R and C.
9. Tensor the map B to A given by multiplication by s, obtaining d : C to R.
   The identities i(d(c)) = sc and d(i(r)) = sr show that c maps to d(c)/s in R[1/s].
   Regularity verifies multiplicativity and injectivity, giving R inside C inside Q(R).
10. A regular r of R is regular on C since sC lies in R. For regular t in C, st lies
    in R and is regular there; c/t = (sc)/(st). Thus Q(C) and Q(R) agree.
11. C is integral over R and integrally closed in their common total fractions, so it is
    exactly the integral closure of R. Flatness preserves every regular denominator of A.
    The resulting fraction map sends a/t to the same fraction of completed elements;
    the equation t(b tensor 1) = a tensor 1 identifies the tensor comparison with that map.

The tensor order is R tensor B, the canonical commuted form of B tensor R used by the node.
The final formula determines the normalization isomorphism on all pure tensors by R-linearity.
-/
theorem curve_normalization_completion
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsReduced A] [Algebra.EssFiniteType k A]
    (hdim : ringKrullDim A = (1 : WithBot ℕ∞)) :
    Module.Finite A (integralClosure A (FractionRing A)) ∧
    IsReduced (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) = (1 : WithBot ℕ∞) ∧
    ∃ hreg : ∀ s : A, s ∈ nonZeroDivisors A →
        algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) s ∈
          nonZeroDivisors (AdicCompletion (IsLocalRing.maximalIdeal A) A),
      ∃ (e : ((AdicCompletion (IsLocalRing.maximalIdeal A) A) ⊗[A]
            (integralClosure A (FractionRing A))) ≃ₐ[
              AdicCompletion (IsLocalRing.maximalIdeal A) A]
            integralClosure (AdicCompletion (IsLocalRing.maximalIdeal A) A)
              (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
        (φ : FractionRing A →+* FractionRing
          (AdicCompletion (IsLocalRing.maximalIdeal A) A)),
        (∀ (a : A) (s : nonZeroDivisors A),
          φ (IsLocalization.mk' (FractionRing A) a s) =
            IsLocalization.mk' (FractionRing
              (AdicCompletion (IsLocalRing.maximalIdeal A) A))
              (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a)
              ⟨algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) s,
                hreg s s.property⟩) ∧
        (∀ b : integralClosure A (FractionRing A),
          (e ((1 : AdicCompletion (IsLocalRing.maximalIdeal A) A) ⊗ₜ[A] b) :
            FractionRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)) = φ b.1) := by
  sorry

end RingTheory
