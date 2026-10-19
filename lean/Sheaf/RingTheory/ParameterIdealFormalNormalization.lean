/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import Sheaf.RingTheory.IntegralExtensionDimension
import Sheaf.RingTheory.ReducedNoetherianTotalRingFractions

/-!
# Formal normalization for supplied parameter ideals

Source: Stacks Project, Algebra, Tag 032D, proof Cases I and II; ILO, Travaux de Gabber,
Exposé IV, 2.1.5, 2.1.12 and 4.2.5
(blueprint: lem-per-parameter-ideal-formal-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct
open IsLocalRing

namespace MvPowerSeries

/-- Finite formal normalization for the supplied parameters, in the coefficient-field
case (first conjunct) and the complete-DVR case (second conjunct).
The existential algebra structure records the evaluation homomorphism: its values on
constants and variables determine it uniquely by the complete power-series universal
property. Continuity is stated for the maximal-ideal adic filtrations.
In the first case the maps `f q` are the fraction-field embeddings characterized by
compatibility on the power-series ring. The pure-tensor formula characterizes the
canonical generic-product isomorphism, not just an abstract isomorphism of rings.

Source: Stacks Project, Algebra, Tag 032D, proof Cases I and II, and ILO, Travaux de
Gabber, IV 2.1.5, 2.1.12 and 4.2.5.
(blueprint: lem-per-parameter-ideal-formal-normalization)

Proof (the eight steps of the DAG):
1. Power-series Noetherianity, the domain and local-ring statements, and the
   quotient-variables statement identify the maximal ideal as the coefficient maximal
   ideal plus the variables. The complete-base statement gives completeness, including
   for arbitrary complete DVRs (lem-weil-pbc-power-series-complete-over-complete-base).
2. Successive variable quotients are power-series domains. The nonzerodivisor dimension
   formula gives dimension e plus the coefficient dimension, which is zero for a field
   and one for a DVR (lem-weil-pbc-dimension-quotient-nonzerodivisor and the local
   maximal-ideal generator bound). This includes e=0.
3. Apply lem-weil-pbc-power-series-universal-property-complete to the supplied elements
   of the target maximal ideal. The evaluation carries each power of the source maximal
   ideal into the corresponding target power. Its residue map is the assumed coefficient
   residue isomorphism. This also proves locality.
4. If z_i generate the target maximal ideal and z_i^(a_i) belong to the supplied ideal J,
   every monomial of degree 1+sum(a_i-1) belongs to J. Thus J contains a maximal-ideal
   power. The quotient is Artinian local and finite over the common residue field.
   Source completeness and target separatedness give finiteness by
   lem-weil-pbc-finite-over-complete-ring, using the actual supplied ideal.
5. For B in the domain case, or each minimal component B/q in the reduced case, finiteness
   and equal dimension force injectivity: a nonzero kernel element would lower the
   source dimension by one, contradicting integral-extension dimension comparison
   (lem-weil-pbc-integral-extension-dimension and the nonzerodivisor dimension formula).
6. Injectivity and the domain property give torsion-freeness in the DVR case. In the
   reduced case every nonzero source element avoids every minimal prime by step 5;
   lem-weil-pbc-reduced-zerodivisors-union-minimal-primes gives torsion-freeness.
7. In the reduced case identify B tensor K with localization at nonzero source elements.
   It is finite-dimensional over K. Every nonzerodivisor of B acts injectively and hence
   surjectively, so becomes invertible; this identifies it with the total fraction ring.
8. Apply lem-weil-pbc-reduced-noetherian-total-ring-fractions. Its component fields are
   Frac(B/q). The finite-domain-fraction-degree statement makes each extension finite.
   All component maps send b tensor a/s to the image of b times the image of a/s,
   giving exactly the displayed canonical isomorphism. -/
theorem parameter_ideal_formal_normalization
    (B : Type v) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal B) B] (e : ℕ) :
    (∀ (Λ : Type u) [Field Λ] [IsReduced B]
      (α : Λ →+* B) (_hα : Function.Injective α)
      (_hres : Function.Bijective ((residue B).comp α))
      (_hdim : ∀ q : PrimeSpectrum B, q.asIdeal ∈ minimalPrimes B →
        ringKrullDim (B ⧸ q.asIdeal) = (e : WithBot ℕ∞))
      (b : Fin e → B) (_hb : ∀ i : Fin e, b i ∈ maximalIdeal B)
      (_hparam : (Ideal.span (Set.range b)).radical = maximalIdeal B),
      ∃ (_ : Algebra (MvPowerSeries (Fin e) Λ) B)
        (_ : IsLocalHom (algebraMap (MvPowerSeries (Fin e) Λ) B)),
        (∀ c : Λ, algebraMap (MvPowerSeries (Fin e) Λ) B (C c) = α c) ∧
        (∀ i : Fin e, algebraMap (MvPowerSeries (Fin e) Λ) B (X i) = b i) ∧
        (∀ N : ℕ, ∃ M : ℕ, ∀ F ∈ maximalIdeal (MvPowerSeries (Fin e) Λ) ^ M,
          algebraMap (MvPowerSeries (Fin e) Λ) B F ∈ maximalIdeal B ^ N) ∧
        Function.Injective (algebraMap (MvPowerSeries (Fin e) Λ) B) ∧
        Function.Bijective (ResidueField.map (algebraMap (MvPowerSeries (Fin e) Λ) B)) ∧
        Module.Finite (MvPowerSeries (Fin e) Λ) B ∧
        Module.IsTorsionFree (MvPowerSeries (Fin e) Λ) B ∧
        ∃ f : ∀ q : {q : PrimeSpectrum B // q.asIdeal ∈ minimalPrimes B},
            FractionRing (MvPowerSeries (Fin e) Λ) →+* FractionRing (B ⧸ q.val.asIdeal),
          (∀ q : {q : PrimeSpectrum B // q.asIdeal ∈ minimalPrimes B},
            ∀ r : MvPowerSeries (Fin e) Λ,
              f q (algebraMap (MvPowerSeries (Fin e) Λ)
                (FractionRing (MvPowerSeries (Fin e) Λ)) r) =
              algebraMap (B ⧸ q.val.asIdeal) (FractionRing (B ⧸ q.val.asIdeal))
                (Ideal.Quotient.mk q.val.asIdeal (algebraMap (MvPowerSeries (Fin e) Λ) B r))) ∧
          (∀ q : {q : PrimeSpectrum B // q.asIdeal ∈ minimalPrimes B}, (f q).Finite) ∧
          ∃ E : B ⊗[MvPowerSeries (Fin e) Λ] FractionRing (MvPowerSeries (Fin e) Λ) ≃+*
              (∀ q : {q : PrimeSpectrum B // q.asIdeal ∈ minimalPrimes B},
                FractionRing (B ⧸ q.val.asIdeal)),
            ∀ (x : B) (k : FractionRing (MvPowerSeries (Fin e) Λ))
              (q : {q : PrimeSpectrum B // q.asIdeal ∈ minimalPrimes B}),
              E (x ⊗ₜ[MvPowerSeries (Fin e) Λ] k) q =
                algebraMap (B ⧸ q.val.asIdeal) (FractionRing (B ⧸ q.val.asIdeal))
                  (Ideal.Quotient.mk q.val.asIdeal x) * f q k) ∧
    (∀ (Λ : Type u) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsDomain B]
      [IsAdicComplete (maximalIdeal Λ) Λ]
      (π : Λ) (_hπ : maximalIdeal Λ = Ideal.span {π})
      (α : Λ →+* B) [IsLocalHom α] (_hα : Function.Injective α)
      (_hres : Function.Bijective (ResidueField.map α))
      (_hdim : ringKrullDim B = ((e + 1 : ℕ) : WithBot ℕ∞))
      (b : Fin e → B) (_hb : ∀ i : Fin e, b i ∈ maximalIdeal B)
      (_hparam : (Ideal.span (insert (α π) (Set.range b))).radical = maximalIdeal B),
      ∃ (_ : Algebra (MvPowerSeries (Fin e) Λ) B)
        (_ : IsLocalHom (algebraMap (MvPowerSeries (Fin e) Λ) B)),
        (∀ c : Λ, algebraMap (MvPowerSeries (Fin e) Λ) B (C c) = α c) ∧
        (∀ i : Fin e, algebraMap (MvPowerSeries (Fin e) Λ) B (X i) = b i) ∧
        (∀ N : ℕ, ∃ M : ℕ, ∀ F ∈ maximalIdeal (MvPowerSeries (Fin e) Λ) ^ M,
          algebraMap (MvPowerSeries (Fin e) Λ) B F ∈ maximalIdeal B ^ N) ∧
        Function.Injective (algebraMap (MvPowerSeries (Fin e) Λ) B) ∧
        Function.Bijective (ResidueField.map (algebraMap (MvPowerSeries (Fin e) Λ) B)) ∧
        Module.Finite (MvPowerSeries (Fin e) Λ) B ∧
        Module.IsTorsionFree (MvPowerSeries (Fin e) Λ) B) := by
  sorry

end MvPowerSeries
