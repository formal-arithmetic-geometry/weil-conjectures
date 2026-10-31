/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.TorCoefficientModule
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Exactness
import WeilConjectures.RingTheory.TorFlatBaseChange

/-! # Localization of Tor in the coefficient ring

Source: Stacks Project, Algebra, Tag 00M8, the free-resolution argument for
flat coefficient localization, and Tag 00HN, the local criterion for zero modules.
(blueprint: lem-trf-tor-localization-on-spec).

## Main declarations

* `ModuleCat.torCoefficientLocalizationMap`: the canonical fraction map.
* `ModuleCat.tor_coefficient_localization`: this map is bijective, and vanishing
  of Tor can be checked at every prime of the coefficient ring.
-/

@[expose] public section

universe u

namespace ModuleCat

/-- Denominators outside the prime act invertibly on localized-coefficient Tor.
Source: Stacks Project, Algebra, Tags 00M7 and 00M8.
Proof: each denominator has an inverse in `A_p`. Multiplication by that inverse
is an `R`-linear coefficient endomorphism. Applying `Tor'` makes it an inverse
of multiplication by the denominator. These maps are coefficient-linear by
commutativity. Thus the scalar endomorphism is a unit, in every degree.
(blueprint: lem-trf-tor-localization-on-spec). -/
theorem torCoefficientLocalization_units (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (M : ModuleCat.{u} R) (n : ℕ) (p : PrimeSpectrum A)
    (s : p.asIdeal.primeCompl) :
    IsUnit (algebraMap A
      (Module.End A (torCoefficientModule R A M (Localization.AtPrime p.asIdeal) n)) s) := by
  sorry

/-- The canonical coefficient-localization map on Tor.
It is the unique extension of the functorial coefficient map from `A` to `A_p`;
`LocalizedModule.lift_mk` gives the formula `t/s ↦ s⁻¹ Tor(M, A → A_p)(t)`.
Source: Stacks Project, Algebra, Tag 00M8, free-resolution argument, and Tag 00DK.
(blueprint: lem-trf-tor-localization-on-spec). -/
noncomputable def torCoefficientLocalizationMap (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (M : ModuleCat.{u} R) (n : ℕ) (p : PrimeSpectrum A) :
    LocalizedModule p.asIdeal.primeCompl (torCoefficientModule R A M A n) →ₗ[A]
      torCoefficientModule R A M (Localization.AtPrime p.asIdeal) n :=
  LocalizedModule.lift p.asIdeal.primeCompl
    (torCoefficientLinearMap R A M A (Localization.AtPrime p.asIdeal) n
      (Algebra.ofId A (Localization.AtPrime p.asIdeal)))
    (torCoefficientLocalization_units R A M n p)

/-- Localization in the coefficient ring commutes with Tor in every degree,
and vanishing is local on its prime spectrum.
Source: Stacks Project, Algebra, Tag 00M8 (free-resolution argument for flat
coefficient change), Tag 00DK (tensor localization), Tag 00HT (flatness),
and Tag 00HN (local vanishing).
Proof: put `T = Tor^R_n(M,A)`, with coefficient action induced by multiplication.
Identify `T_p` with `T tensor_A A_p` by `t/s ↦ t tensor (1/s)`; the inverse
sends `t tensor (a/s)` to `at/s`. Flat coefficient base change identifies the
latter tensor product with `Tor^R_n(M,A_p)`. On a projective resolution of `M`
the composite sends a cycle represented by `z/s` to the class of `s⁻¹ z`.
This is exactly the extension defining `torCoefficientLocalizationMap`, so it
is bijective, also when `n=0`. If `T=0` all its localizations vanish. Conversely,
vanishing of localized-coefficient Tor implies all prime localizations of `T`
vanish. Apply the maximal-localization bijectivity criterion to `T → 0`:
maximal ideals are prime, so each localized map is bijective, hence `T=0`.
The criterion includes the zero coefficient ring and its empty prime spectrum.
(blueprint: lem-trf-tor-localization-on-spec). -/
theorem tor_coefficient_localization (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (M : ModuleCat.{u} R) (n : ℕ) :
    (∀ p : PrimeSpectrum A,
      Function.Bijective (torCoefficientLocalizationMap R A M n p)) ∧
    (Subsingleton (torCoefficientModule R A M A n) ↔
      ∀ p : PrimeSpectrum A,
        Subsingleton (torCoefficientModule R A M (Localization.AtPrime p.asIdeal) n)) := by
  sorry

end ModuleCat
