/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.CompletionFiniteExtension
import WeilConjectures.RingTheory.CompletionOfDVR
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompletionDimension
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Completion of a finite algebra with DVR branches

Source: Stacks Project, Varieties, Tag 0C3V, final paragraph; Algebra, Tag 07N9;
More on Algebra, Tag 0AP1 (blueprint: lem-trf-finite-dvr-branch-completion).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace AdicCompletion

/-- An injective finite algebra with DVR closed branches has a reduced completed base and
an integrally closed completed algebra, canonically a finite product of completed DVRs.
Source: Stacks Project, Varieties, Tag 0C3V, final paragraph
(blueprint: lem-trf-finite-dvr-branch-completion).

The maps `g q` are the completed local maps: their values modulo every power of the
branch maximal ideal agree with the localized image of a representative from `A`.
The `B`-algebra equivalence and the equation on `1 ⊗ₜ r` express both compatibilities.
`RingHom.Finite` and `RingHom.IsIntegral` refer to the right tensor inclusion, so the
finite module and integral algebra structures are those over the completed base.
`IsIntegrallyClosed` uses the total fraction ring, including for a ring with zero divisors.

Proof:
1. Apply lem-weil-pbc-completion-finite-extension at the maximal ideal of `A`.
   Localization of a local ring at its maximal ideal is itself, since the denominators
   are units. Compose the resulting product isomorphism with tensor symmetry. Its
   quotient-level characterization gives `g`, and its algebra compatibilities give `e`.
2. Apply lem-weil-pbc-completion-of-dvr-is-dvr to each branch, using the DVR hypothesis.
   A DVR is a PID, so lem-weil-pbc-pid-noetherian-normal makes every factor a normal domain.
3. By lem-weil-pbc-noetherian-completion-flat, completion is flat. Tensoring the given
   injection with the completion stays injective by def-weil-pbc-flat-ring-map. Under
   the canonical identification of the base tensor its completion with the completion,
   this injection is exactly `r ↦ 1 ⊗ₜ r`.
4. A nilpotent in the completed algebra has zero image in each domain factor, hence is
   zero. Injectivity of the right inclusion then descends reducedness to the base completion.
5. The completed base is Noetherian and local by lem-weil-pbc-adic-completion-noetherian
   and lem-weil-pbc-local-completion-local-ring, and has dimension one by
   lem-weil-pbc-completion-dimension. If `b_j` generate `B`, then `b_j ⊗ₜ 1` generate its
   completed tensor algebra over the completed base. The finite-algebra-is-integral and
   finite-algebra-noetherian nodes give integrality and Noetherianity.
6. In the product of domain factors, a non-zero-divisor has nonzero coordinate at every
   branch: otherwise it annihilates the nonzero tuple supported at that branch. For an
   integral fraction `c/s`, its coordinate fractions satisfy the projected monic equation,
   hence belong to the respective normal domains. Their tuple `d` satisfies `c = s*d`,
   so `c/s = d/1` by def-weil-pbc-module-localization. This is integral closedness in the
   total ring of fractions, as in def-weil-pbc-integral-closure. -/
theorem finite_dvr_branch_completion
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsLocalRing A] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B)) (hdim : ringKrullDim A = 1)
    (hbranch : ∀ q : (IsLocalRing.maximalIdeal A).primesOver B,
      ∃ _ : IsDomain (Localization.AtPrime q.1),
        IsDiscreteValuationRing (Localization.AtPrime q.1)) :
    Finite ((IsLocalRing.maximalIdeal A).primesOver B) ∧
    (∃ (e : (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) ≃ₐ[B]
          (∀ q : (IsLocalRing.maximalIdeal A).primesOver B,
            AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
              (Localization.AtPrime q.1)))
        (g : ∀ q : (IsLocalRing.maximalIdeal A).primesOver B,
          AdicCompletion (IsLocalRing.maximalIdeal A) A →+*
            AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
              (Localization.AtPrime q.1)),
      (∀ (q : (IsLocalRing.maximalIdeal A).primesOver B) (n : ℕ)
          (a : AdicCompletion (IsLocalRing.maximalIdeal A) A) (r : A),
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n a =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) r →
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n
              (g q a) =
            Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n)
              (algebraMap A (Localization.AtPrime q.1) r)) ∧
      (∀ (a : AdicCompletion (IsLocalRing.maximalIdeal A) A)
          (q : (IsLocalRing.maximalIdeal A).primesOver B),
        e ((1 : B) ⊗ₜ[A] a) q = g q a)) ∧
    (∀ q : (IsLocalRing.maximalIdeal A).primesOver B,
      ∃ _ : IsDomain
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
            (Localization.AtPrime q.1)),
        IsDiscreteValuationRing
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
            (Localization.AtPrime q.1)) ∧
        IsIntegrallyClosed
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
            (Localization.AtPrime q.1))) ∧
    RingHom.Flat (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
    Function.Injective
      (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (B := AdicCompletion (IsLocalRing.maximalIdeal A) A)) ∧
    IsReduced (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
    IsReduced (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
    IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) = 1 ∧
    RingHom.Finite
      (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (B := AdicCompletion (IsLocalRing.maximalIdeal A) A)).toRingHom ∧
    RingHom.IsIntegral
      (Algebra.TensorProduct.includeRight (R := A) (A := B)
        (B := AdicCompletion (IsLocalRing.maximalIdeal A) A)).toRingHom ∧
    IsNoetherianRing (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
    IsIntegrallyClosed (B ⊗[A] AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  sorry

end AdicCompletion
