/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Local dimension inequality for quasi-finite ring maps

A finite-type ring map quasi-finite at `q` satisfies `dim S_q ≤ dim R_{q ∩ R}`.

## Implementation details

With `T` the integral closure of `R` in `S` and `q'` the contraction of `q`, Zariski's Main
Theorem and `Localization.localRingHom_bijective_of_saturated_inf_eq_top` identify `T_q'` with
`S_q`. Integral incomparability makes contraction to `R` strictly monotone, which bounds the
height of `q'` by that of `q ∩ R`. Infinite dimensions are covered.

## References

* [Stacks, Tag 00QF]
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite-type ring map that is quasi-finite at `q` does not increase the dimension of
local rings. -/
theorem ringKrullDim_le_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) (hq : IsQuasiFiniteAtPrime R S q) :
    ringKrullDim (Localization.AtPrime q.asIdeal) ≤
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S)).asIdeal) := by
  let T := integralClosure R S
  let q' := q.asIdeal.under T
  have : QuasiFiniteAt R q.asIdeal := by
    let e := PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S))
    apply QuasiFiniteAt.of_isOpen_singleton_fiber q
    rwa [← e.isOpen_image, Set.image_singleton]
  have hmain : ZariskisMainProperty R q.asIdeal :=
    ZariskisMainProperty.of_finiteType q.asIdeal
  obtain ⟨r, hrq, hrT, hr⟩ := zariskisMainProperty_iff.mp hmain
  have hsat : T.saturation (q.asIdeal.primeCompl ⊓ T.toSubmonoid) (by simp) = ⊤ := by
    apply top_le_iff.mp
    intro x _hx
    obtain ⟨n, hn⟩ := hr x
    exact ⟨r ^ n, ⟨pow_mem hrq n, pow_mem hrT n⟩, hn⟩
  have hbij := Localization.localRingHom_bijective_of_saturated_inf_eq_top _ hsat q'
  let e := RingEquiv.ofBijective
    (Localization.localRingHom q' q.asIdeal (algebraMap T S) (q.asIdeal.over_def q')) hbij
  rw [← ringKrullDim_eq_of_ringEquiv e]
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q',
    IsLocalization.AtPrime.ringKrullDim_eq_height (q.comap (algebraMap R S)).asIdeal]
  apply WithBot.coe_le_coe.mpr
  let f : PrimeSpectrum T → PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R T)
  have hf : StrictMono f := by
    intro a b hab
    exact Ideal.IsIntegral.under_lt_under hab
  have hh := Order.height_le_height_apply_of_strictMono f hf
    (⟨q', inferInstance⟩ : PrimeSpectrum T)
  simpa [← PrimeSpectrum.height_eq_orderHeight, f, q', T, Ideal.under,
    Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R (integralClosure R S) S] using hh

end Algebra
