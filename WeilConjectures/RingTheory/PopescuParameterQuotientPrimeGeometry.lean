/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The prime of the parameter quotient

The parameter quotient has a zero-dimensional localization at its quotient prime, and that
prime is minimal over every extended singular ideal it contains.

## References

* [Stacks, Tag 07FE] (final paragraph of the proof)
-/

@[expose] public section

universe u v w

namespace Algebra

/-- The parameter quotient has a zero-dimensional localization at its quotient prime,
and that prime is minimal over every extended singular ideal it contains. -/
theorem parameter_quotient_prime_geometry
    {k : Type u} {C : Type v} {Λ : Type w}
    [Field k] [CommRing C] [CommRing Λ] [Algebra k Λ]
    (d c : ℕ) (φ : MvPolynomial (Fin d) k →ₐ[k] Λ)
    [Algebra (MvPolynomial (Fin d) k) C]
    [FinitePresentation (MvPolynomial (Fin d) k) C]
    (q : PrimeSpectrum Λ)
    (hgen : Ideal.span (Set.range (fun i : Fin d ↦
      algebraMap Λ (Localization.AtPrime q.asIdeal) (φ (MvPolynomial.X i)))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)) :
    letI := φ.toRingHom.toAlgebra
    let J : Ideal (MvPolynomial (Fin d) k) :=
      Ideal.span (Set.range (fun i : Fin d ↦ (MvPolynomial.X i ^ c) ^ 8))
    let J_C := Ideal.map (algebraMap (MvPolynomial (Fin d) k) C) J
    let J_Λ := Ideal.map (algebraMap (MvPolynomial (Fin d) k) Λ) J
    ∀ (_ : FinitePresentation (MvPolynomial (Fin d) k ⧸ J) (C ⧸ J_C))
      (γ₀ : (C ⧸ J_C) →ₐ[MvPolynomial (Fin d) k ⧸ J] (Λ ⧸ J_Λ))
      (q₀ : PrimeSpectrum (Λ ⧸ J_Λ)),
      PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q →
      ringKrullDim (Localization.AtPrime q₀.asIdeal) = 0 ∧
      (popescuIdeal γ₀ ≤ q₀.asIdeal → q₀.asIdeal ∈ (popescuIdeal γ₀).minimalPrimes) := by
  let := φ.toRingHom.toAlgebra
  dsimp
  intro hfp γ₀ q₀ hcomap
  let := hfp
  let J : Ideal (MvPolynomial (Fin d) k) :=
    Ideal.span (Set.range (fun i : Fin d ↦ (MvPolynomial.X i ^ c) ^ 8))
  let J_Λ := Ideal.map (algebraMap (MvPolynomial (Fin d) k) Λ) J
  change PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q at hcomap
  have hsmall : ∀ (P : Ideal (Λ ⧸ J_Λ)), P.IsPrime → P ≤ q₀.asIdeal → q₀.asIdeal ≤ P := by
    intro P hP hle
    let := hP
    let p := Ideal.comap (Ideal.Quotient.mk J_Λ) P
    have : p.IsPrime := Ideal.comap_isPrime _ P
    have hpq : p ≤ q.asIdeal := by
      have h := Ideal.comap_mono (f := Ideal.Quotient.mk J_Λ) hle
      change p ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀).asIdeal at h
      simpa only [hcomap] using h
    have hparam : ∀ i : Fin d, φ (MvPolynomial.X i) ∈ p := by
      intro i
      apply (inferInstance : p.IsPrime).mem_of_pow_mem (n := c)
      apply (inferInstance : p.IsPrime).mem_of_pow_mem (n := 8)
      have hx : φ ((MvPolynomial.X i ^ c) ^ 8) ∈ J_Λ :=
        Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
      change (Ideal.Quotient.mk J_Λ) ((φ (MvPolynomial.X i) ^ c) ^ 8) ∈ P
      rw [map_pow, map_pow] at hx
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact P.zero_mem
    let L := Localization.AtPrime q.asIdeal
    have hprime : (p.map (algebraMap Λ L)).IsPrime :=
      Ideal.isPrime_map_of_isLocalizationAtPrime q.asIdeal hpq
    have hm : IsLocalRing.maximalIdeal L ≤ p.map (algebraMap Λ L) := by
      rw [← hgen]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_map_of_mem _ (hparam i)
    have hpeq : p.map (algebraMap Λ L) = IsLocalRing.maximalIdeal L :=
      le_antisymm (IsLocalRing.le_maximalIdeal hprime.ne_top) hm
    have heq : p = q.asIdeal := by
      rw [← Ideal.under_map_of_isLocalizationAtPrime (S := L) q.asIdeal hpq, hpeq]
      exact IsLocalization.AtPrime.under_maximalIdeal L q.asIdeal
    have hQP : q₀.asIdeal = P := by
      apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk J_Λ)
        Ideal.Quotient.mk_surjective
      change (PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀).asIdeal = p
      rw [hcomap, heq]
    exact hQP.le
  have hmin : q₀.asIdeal ∈ minimalPrimes (Λ ⧸ J_Λ) :=
    ⟨⟨q₀.isPrime, bot_le⟩, fun P hP hle ↦ hsmall P hP.1 hle⟩
  have : Ring.KrullDimLE 0 (Localization.AtPrime q₀.asIdeal) :=
    Ring.KrullDimLE.of_isLocalization q₀.asIdeal hmin _
  constructor
  · exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  · intro hle
    exact ⟨⟨q₀.isPrime, hle⟩, fun P hP hPQ ↦ hsmall P hP.1 hPQ⟩

end Algebra
