/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import WeilConjectures.RingTheory.AnalyticallyUnramified
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import WeilConjectures.RingTheory.AnalyticallyUnramifiedPrincipalCriterion
import WeilConjectures.RingTheory.CompletionFiniteExtensionDecomposition
import WeilConjectures.RingTheory.FiniteOverNagata
import WeilConjectures.RingTheory.IntegralExtensionDimension
import WeilConjectures.RingTheory.NagataDomainN2
import WeilConjectures.RingTheory.NagataLocalization
import WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight
import WeilConjectures.RingTheory.RegularLocalDimOneIffNormal

/-!
# Reduced completion of a local Nagata domain

A Noetherian local Nagata domain is analytically unramified: its completion is reduced.

## Implementation details

The proof is by induction on the dimension. The integral closure `S` of `A` in its fraction
field is finite over `A`, so the completion of `A` embeds into that of `S`, which is the product
of the completions of the localizations of `S` at its finitely many maximal ideals. These are
normal local Nagata domains; in positive dimension, for `0 ≠ x` in the maximal ideal, the
associated primes `p` of `R/xR` have height one, `R_p` is regular, and `R/p` has smaller
dimension, so the principal criterion for analytic unramifiedness applies.

## References

* [Stacks, Tag 0331]
* [Stacks, Tag 0330]
* [Stacks, Tag 07N9]
-/

@[expose] public section

universe u

/-- A field has zero maximal ideal, and its completion is the field itself. -/
private theorem analyticallyUnramified_of_field (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A]
    (hf : IsField A) : IsAnalyticallyUnramified A := by
  let := hf.toField
  unfold IsAnalyticallyUnramified
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact isReduced_of_injective (AdicCompletion.ofAlgEquiv (⊥ : Ideal A)).symm.toRingHom
    (AdicCompletion.ofAlgEquiv (⊥ : Ideal A)).symm.injective

/-- The normal inductive step: if all Noetherian local Nagata domains of dimension at most `n`
are analytically unramified, then so is every normal one of dimension at most `n + 1`. -/
private theorem analyticallyUnramified_normal_step (n : ℕ)
    (ih : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsDomain B],
      IsNagataRing B → ringKrullDim B ≤ (n : WithBot ℕ∞) → IsAnalyticallyUnramified B)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsIntegrallyClosed A] (hA : IsNagataRing A)
    (hdim : ringKrullDim A ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    IsAnalyticallyUnramified A := by
  classical
  by_cases hf : IsField A
  · exact analyticallyUnramified_of_field A hf
  have hm : IsLocalRing.maximalIdeal A ≠ ⊥ :=
    fun h ↦ hf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
  obtain ⟨x, hxm, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hle (p : Ideal A) (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {x})) :
      Ideal.span {x} ≤ p := by
    simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using hp.annihilator_le
  have hheight (p : Ideal A) (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {x})) :
      p.height = 1 := Ideal.height_eq_one_of_mem_associatedPrimes_quotient_span hx hp
  apply isAnalyticallyUnramified_of_principal_quotient A x hx hxm
  · intro p hp
    let : p.IsPrime := hp.isPrime
    refine ⟨⟨inferInstance, hle p hp⟩, ?_⟩
    intro q hq hqp
    let : q.IsPrime := hq.1
    by_contra hpq
    have hlt : q < p := lt_of_le_not_ge hqp hpq
    have hqbot : q ≠ ⊥ := by
      intro heq
      have : x ∈ q := hq.2 (Ideal.subset_span (Set.mem_singleton x))
      exact hx (by simpa [heq] using this)
    have hqheight : 1 ≤ q.height := Order.one_le_iff_ne_zero.mpr
      (Ideal.height_eq_zero_iff_eq_bot.not.mpr hqbot)
    have hbad := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hheight p hp] at hbad
    have htwo : (2 : ℕ∞) ≤ q.height + 1 := by
      calc
        (2 : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ q.height + 1 := add_le_add hqheight le_rfl
    have : (2 : ℕ∞) ≤ 1 := htwo.trans hbad
    norm_num at this
  · intro p
    let : IsIntegrallyClosed (Localization.AtPrime p.1) :=
      isIntegrallyClosed_of_isLocalization _ p.1.primeCompl p.1.primeCompl_le_nonZeroDivisors
    apply (IsRegularLocalRing.iff_isDomain_and_isIntegrallyClosed_of_dim_one _ ?_).mpr
    · exact ⟨inferInstance, inferInstance⟩
    · rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.1, hheight p.1 p.2]
      rfl
  · intro p hp
    let : p.IsPrime := hp.isPrime
    have hxp : x ∈ p := hle p hp (Ideal.subset_span (Set.mem_singleton x))
    have hsucc := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
      ((Ideal.Quotient.eq_zero_iff_mem).mpr hxp)
    let : IsLocalRing (A ⧸ p) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have hdimq : ringKrullDim (A ⧸ p) ≤ (n : WithBot ℕ∞) := by
      have h := hsucc.trans hdim
      rw [Nat.cast_add, Nat.cast_one] at h
      exact ENat.WithBot.add_le_add_one_right_iff.mp h
    have hquot := ih (A ⧸ p) ((finite_over_nagata_is_nagata A A hA).2 p) hdimq
    refine ⟨inferInstance, ?_⟩
    rw [IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    exact hquot

/-- Reduced local completions of a finite extension force the base completion to be reduced. -/
private theorem analyticallyUnramified_finite_descent (A S : Type u) [CommRing A] [CommRing S]
    [IsNoetherianRing A] [IsLocalRing A] [Algebra A S] [Module.Finite A S]
    (hinj : Function.Injective (algebraMap A S))
    (hred : ∀ p : (IsLocalRing.maximalIdeal A).primesOver S,
      IsReduced (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.1))
        (Localization.AtPrime p.1))) : IsAnalyticallyUnramified A := by
  let m := IsLocalRing.maximalIdeal A
  let L := Localization.AtPrime m
  let C := AdicCompletion (IsLocalRing.maximalIdeal L) L
  let : Module.Flat L C := AdicCompletion.flat_of_isNoetherian _
  let : Module.Flat A C := Module.Flat.trans A L C
  let D := fun p : m.primesOver S ↦
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.1))
      (Localization.AtPrime p.1)
  let : ∀ p, IsReduced (D p) := hred
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := C) (B := S)
  obtain ⟨_, e, _, _, _⟩ := AdicCompletion.completion_finite_extension_decomposition A S m
  let : IsReduced (TensorProduct A C S) := isReduced_of_injective e.toRingHom e.injective
  let : IsReduced C := isReduced_of_injective
    (Algebra.TensorProduct.includeLeft : C →ₐ[A] TensorProduct A C S)
    (Algebra.TensorProduct.includeLeft_injective hinj)
  let eL : A ≃ₐ[A] L := IsLocalization.atUnits A m.primeCompl (by
    intro a ha
    exact not_not.mp ha)
  obtain ⟨eC, _⟩ := AdicCompletion.exists_ringEquiv m (IsLocalRing.maximalIdeal L)
    eL.toRingEquiv (IsLocalRing.map_ringEquiv_maximalIdeal eL.toRingEquiv).symm
  exact isReduced_of_injective eC.toRingHom eC.injective

/-- If all normal Noetherian local Nagata domains of dimension at most `n` are analytically
unramified, then so is every Noetherian local Nagata domain of dimension at most `n`. -/
private theorem analyticallyUnramified_normalization_descent (n : ℕ)
    (hnormal : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
      [IsDomain B] [IsIntegrallyClosed B], IsNagataRing B →
      ringKrullDim B ≤ (n : WithBot ℕ∞) → IsAnalyticallyUnramified B)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (hA : IsNagataRing A) (hdim : ringKrullDim A ≤ (n : WithBot ℕ∞)) :
    IsAnalyticallyUnramified A := by
  let S := integralClosure A (FractionRing A)
  let : Module.Finite A S := isN1_of_isN2 A (FractionRing A)
    (isN2_of_isNagataRing_domain A hA)
  let : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  let : IsIntegrallyClosed S :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing A)
  have hS : IsNagataRing S := (finite_over_nagata_is_nagata A S hA).1
  have hdimS : ringKrullDim S ≤ ringKrullDim A :=
    (RingHom.IsIntegral.ringKrullDim_le_and_isMaximal_comap (algebraMap A S)
      (Algebra.IsIntegral.isIntegral (R := A) (A := S))).1
  apply analyticallyUnramified_finite_descent A S (FaithfulSMul.algebraMap_injective A S)
  intro p
  let B := Localization.AtPrime p.1
  let : IsIntegrallyClosed B := isIntegrallyClosed_of_isLocalization B p.1.primeCompl
    p.1.primeCompl_le_nonZeroDivisors
  have hB := (isNagataRing_localization S p.1.primeCompl hS).2.1 p.1
  have hdimB : ringKrullDim B ≤ (n : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.1 B]
    exact (Ideal.height_le_ringKrullDim_of_isPrime (I := p.1)).trans (hdimS.trans hdim)
  exact hnormal B hB hdimB

/-- A Noetherian local Nagata integral domain has reduced maximal-ideal-adic completion. -/
theorem isAnalyticallyUnramified_of_isNagataRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] (hA : IsNagataRing A) :
    IsAnalyticallyUnramified A := by
  have hbound : ∀ n : ℕ, ∀ (B : Type u) [CommRing B] [IsNoetherianRing B]
      [IsLocalRing B] [IsDomain B], IsNagataRing B →
      ringKrullDim B ≤ (n : WithBot ℕ∞) → IsAnalyticallyUnramified B := by
    intro n
    induction n with
    | zero =>
      intro B _ _ _ _ _ hdim
      let : Ring.KrullDimLE 0 B := Ring.krullDimLE_iff.mpr hdim
      exact analyticallyUnramified_of_field B Ring.KrullDimLE.isField_of_isDomain
    | succ n ih =>
      intro B _ _ _ _ hB hdim
      apply analyticallyUnramified_normalization_descent (n + 1) ?_ B hB hdim
      intro R _ _ _ _ _ hR hdimR
      exact analyticallyUnramified_normal_step n ih R hR hdimR
  exact hbound (IsLocalRing.maximalIdeal A).spanFinrank A hA
    (ringKrullDim_le_spanFinrank_maximalIdeal A)
