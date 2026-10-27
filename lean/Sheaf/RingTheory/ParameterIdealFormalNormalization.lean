/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import WeilConjectures.RingTheory.IntegralExtensionDimension
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions

/-!
# Finite formal normalization for supplied parameter ideals

Source: Stacks Project, Algebra, Tag 032D, Cases I and II; Tag 031D;
ILO IV 2.1.5, 2.1.12 and 4.2.5 for the reduced equidimensional and complete DVR forms.
(blueprint: lem-per-parameter-ideal-formal-normalization)

## Main statements

- `MvPowerSeries.parameter_ideal_formal_normalization`: the coefficient-field case,
  including the canonical generic product.
- `MvPowerSeries.parameter_ideal_formal_normalization_dvr`: the complete DVR case.
-/

@[expose] public section

universe u v

set_option autoImplicit false

open scoped TensorProduct
open IsLocalRing

namespace MvPowerSeries

/-- Finite formal normalization for the supplied parameters over a coefficient field.
Source: Stacks Project, Tag 032D, Case I, applied componentwise; ILO IV 2.1.5 and 2.1.12.
(blueprint: lem-per-parameter-ideal-formal-normalization)

The existential algebra has its constant and variable values prescribed, so its structure
map is precisely evaluation, uniquely determined by maximal-ideal completeness. Continuity
is expressed by inverse images of maximal-ideal powers. The field maps in the last clause
extend the component maps from the source, and the pure-tensor formula fixes the canonical
product isomorphism.

Proof (the eight steps of the node):
1. The power-series Noetherian, domain, local-ring, quotient-variables and complete-base
   statements make the source a complete Noetherian local domain, with maximal ideal the
   variables ideal and the prescribed residue field.
2. Successive variable quotients are power-series domains. The nonzerodivisor dimension
   formula, iterated through these quotients, gives source dimension e; e = 0 is included.
3. The complete power-series universal property constructs evaluation with the given
   constant and variable values. Maximal-ideal powers prove continuity, and the coefficient
   residue isomorphism proves locality and the residue-field assertion.
4. From the radical equality choose positive powers of generators of the target maximal
   ideal lying in the parameter ideal. The pigeonhole bound puts a power of that maximal
   ideal in the parameter ideal. The quotient is Artinian local and finite over the common
   residue field by the Artinian finite-over-residue statement. Target separatedness and
   source completeness then give finiteness by the finite-over-complete-ring statement.
5. For each minimal component, a nonzero kernel element would lower the source dimension
   by one, while integrality of the finite component algebra bounds its dimension above by
   that quotient dimension. This contradicts the supplied component dimension. Hence each
   component map, and therefore evaluation, is injective.
6. A nonzero source element lies in no target minimal prime by step 5. The reduced-ring
   zero-divisor criterion makes its multiplication injective, proving torsion-freeness.
7. Identify the tensor product with the localization at nonzero source elements by
   b tensor (a/s) mapping to ab/s. Finiteness makes this a finite-dimensional vector space.
   Every target nonzerodivisor acts injectively, hence surjectively, and is thus a unit.
   This identifies the localization with the total ring of fractions of the target.
8. The reduced Noetherian total-fraction theorem identifies that ring with the product
   of the minimal-prime localizations. Each is the fraction field of the corresponding
   quotient domain. The finite-domain-fraction-degree statement makes every component
   field finite over the source fraction field. All these maps have the displayed
   pure-tensor values, proving canonicity. -/
theorem parameter_ideal_formal_normalization
    (Λ : Type u) [Field Λ] (B : Type v) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsReduced B] [IsAdicComplete (maximalIdeal B) B]
    (e : ℕ) (α : Λ →+* B) (_hα : Function.Injective α)
    (_hres : Function.Bijective ((residue B).comp α))
    (_hdim : ∀ q : PrimeSpectrum B, q.asIdeal ∈ minimalPrimes B →
      ringKrullDim (B ⧸ q.asIdeal) = (e : WithBot ℕ∞))
    (b : Fin e → B) (_hb : ∀ i : Fin e, b i ∈ maximalIdeal B)
    (_hparams : (Ideal.span (Set.range b)).radical = maximalIdeal B) :
    ∃ (_ : Algebra (MvPowerSeries (Fin e) Λ) B),
      (∀ a : Λ, algebraMap (MvPowerSeries (Fin e) Λ) B (C a) = α a) ∧
      (∀ i : Fin e, algebraMap (MvPowerSeries (Fin e) Λ) B (X i) = b i) ∧
      (∀ n : ℕ, ∃ m : ℕ,
        Ideal.map (algebraMap (MvPowerSeries (Fin e) Λ) B)
          (maximalIdeal (MvPowerSeries (Fin e) Λ) ^ m) ≤ maximalIdeal B ^ n) ∧
      Function.Injective (algebraMap (MvPowerSeries (Fin e) Λ) B) ∧
      ∃ (_ : IsLocalHom (algebraMap (MvPowerSeries (Fin e) Λ) B)),
        Function.Bijective
          (ResidueField.map (algebraMap (MvPowerSeries (Fin e) Λ) B)) ∧
        Module.Finite (MvPowerSeries (Fin e) Λ) B ∧
        Module.IsTorsionFree (MvPowerSeries (Fin e) Λ) B ∧
        ∃ f : ∀ q : {p : PrimeSpectrum B // p.asIdeal ∈ minimalPrimes B},
            FractionRing (MvPowerSeries (Fin e) Λ) →+* FractionRing (B ⧸ q.val.asIdeal),
          (∀ (q : {p : PrimeSpectrum B // p.asIdeal ∈ minimalPrimes B})
              (r : MvPowerSeries (Fin e) Λ),
            f q (algebraMap _ (FractionRing (MvPowerSeries (Fin e) Λ)) r) =
              algebraMap (B ⧸ q.val.asIdeal) (FractionRing (B ⧸ q.val.asIdeal))
                (Ideal.Quotient.mk q.val.asIdeal (algebraMap _ B r))) ∧
          (∀ q : {p : PrimeSpectrum B // p.asIdeal ∈ minimalPrimes B}, (f q).Finite) ∧
          ∃ E : (B ⊗[MvPowerSeries (Fin e) Λ] FractionRing (MvPowerSeries (Fin e) Λ)) ≃+*
              (∀ q : {p : PrimeSpectrum B // p.asIdeal ∈ minimalPrimes B},
                FractionRing (B ⧸ q.val.asIdeal)),
            ∀ (x : B) (k : FractionRing (MvPowerSeries (Fin e) Λ))
                (q : {p : PrimeSpectrum B // p.asIdeal ∈ minimalPrimes B}),
              E (x ⊗ₜ[MvPowerSeries (Fin e) Λ] k) q =
                algebraMap (B ⧸ q.val.asIdeal) (FractionRing (B ⧸ q.val.asIdeal))
                  (Ideal.Quotient.mk q.val.asIdeal x) * f q k := by
  sorry

/-- Finite formal normalization for the supplied parameters over an arbitrary complete DVR.
Source: Stacks Project, Tag 032D, Case II, with the complete DVR adaptation of ILO IV 4.2.5.
(blueprint: lem-per-parameter-ideal-formal-normalization)

Proof (the node's steps 1--6, since steps 7--8 concern only the coefficient-field case):
1. A DVR is Noetherian and local. The power-series Noetherian, domain, local-ring,
   quotient-variables and complete-base statements make the source a complete Noetherian
   local domain with maximal ideal generated by pi and the variables and the same residue.
2. Quotient the variables successively and use the nonzerodivisor dimension formula.
   The DVR has dimension one by its one-generator maximal ideal and the strict chain
   from zero to that ideal. The source therefore has dimension e + 1, also when e = 0.
3. The complete power-series universal property constructs evaluation. The coefficient
   map is local, and evaluation sends the source maximal ideal into the target maximal
   ideal. Maximal-ideal powers prove continuity; the given residue isomorphism gives
   locality and the asserted residue isomorphism of evaluation.
4. The supplied radical equality bounds a power of the target maximal ideal by the ideal
   generated by alpha(pi) and b. Its Artinian quotient is finite over the common residue
   field, since pi vanishes there. The finite-over-complete-ring statement, with target
   separatedness and source completeness, makes the target finite over the source.
5. A nonzero kernel element lowers the source dimension by one. Finite implies integral,
   and the integral dimension bound would then contradict dimension e + 1 of the target.
   Thus evaluation is injective.
6. The target is a domain, so injectivity makes multiplication by a nonzero source element
   injective. This proves torsion-freeness. No unramified or Cohen-ring assumption is used. -/
theorem parameter_ideal_formal_normalization_dvr
    (Λ : Type u) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ]
    (B : Type v) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B]
    [IsAdicComplete (maximalIdeal B) B]
    (e : ℕ) (_hdim : ringKrullDim B = ((e + 1 : ℕ) : WithBot ℕ∞))
    (π : Λ) (_hπ : maximalIdeal Λ = Ideal.span {π})
    (α : Λ →+* B) (_hα : Function.Injective α) [IsLocalHom α]
    (_hres : Function.Bijective (ResidueField.map α))
    (b : Fin e → B) (_hb : ∀ i : Fin e, b i ∈ maximalIdeal B)
    (_hparams : (Ideal.span ({α π} ∪ Set.range b)).radical = maximalIdeal B) :
    ∃ (_ : Algebra (MvPowerSeries (Fin e) Λ) B),
      (∀ a : Λ, algebraMap (MvPowerSeries (Fin e) Λ) B (C a) = α a) ∧
      (∀ i : Fin e, algebraMap (MvPowerSeries (Fin e) Λ) B (X i) = b i) ∧
      (∀ n : ℕ, ∃ m : ℕ,
        Ideal.map (algebraMap (MvPowerSeries (Fin e) Λ) B)
          (maximalIdeal (MvPowerSeries (Fin e) Λ) ^ m) ≤ maximalIdeal B ^ n) ∧
      Function.Injective (algebraMap (MvPowerSeries (Fin e) Λ) B) ∧
      ∃ (_ : IsLocalHom (algebraMap (MvPowerSeries (Fin e) Λ) B)),
        Function.Bijective
          (ResidueField.map (algebraMap (MvPowerSeries (Fin e) Λ) B)) ∧
        Module.Finite (MvPowerSeries (Fin e) Λ) B ∧
        Module.IsTorsionFree (MvPowerSeries (Fin e) Λ) B := by
  sorry

end MvPowerSeries
