/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.RegularPermanence
import WeilConjectures.RingTheory.GRingMaximalIdealComparison
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Checking the G-ring condition at maximal ideals

A Noetherian ring is a G-ring iff the completion maps of its localizations at maximal ideals are
regular.

## Implementation details

For a prime `p` contained in a maximal ideal `m`, set `A = R_m`, choose a prime of `Â` over
`p A`, and let `B` be the localization of `Â` there; `Â` is a G-ring, being complete local. The
map `R_p → B̂` is regular, and the induced map of completions `R̂_p → B̂` is faithfully flat, so
regularity descends to `R_p → R̂_p`.

## References

* [Stacks, Tag 07PT]
-/

@[expose] public section

universe w

/-- A Noetherian ring is a G-ring iff all maximal local completion maps are regular. -/
theorem isGRing_iff_maximalIdeal
    (R : Type w) [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ (m : Ideal R) [m.IsMaximal],
        RingHom.IsRegular
          (algebraMap (Localization.AtPrime m)
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime m))
              (Localization.AtPrime m))) := by
  constructor
  · intro hR m
    exact hR.2 m
  · intro h
    refine ⟨inferInstance, ?_⟩
    intro p hp
    obtain ⟨B, hB, hBlocal, hBnoeth, φ, hflat, hlocal, hregular⟩ :=
      exists_flat_local_regular_completion_comparison R h p
    let A := Localization.AtPrime p
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let Bhat := AdicCompletion (IsLocalRing.maximalIdeal B) B
    obtain ⟨φhat, _, hcomm, hflatHat⟩ :=
      flat_adicCompletion_of_flat_local A B φ hflat hlocal
    have hlocalHat : IsLocalHom φhat := by
      apply ((IsLocalRing.local_hom_TFAE φhat).out 1 3).mpr
      rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hcomm]
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      exact map_nonunit (algebraMap B Bhat) (φ x) (hlocal x hx)
    let : Algebra Ahat Bhat := φhat.toAlgebra
    let : Algebra A Bhat := (φhat.comp (algebraMap A Ahat)).toAlgebra
    let : IsScalarTower A Ahat Bhat := IsScalarTower.of_algebraMap_eq' rfl
    have : IsLocalHom (algebraMap Ahat Bhat) := hlocalHat
    have : Module.Flat Ahat Bhat := hflatHat
    have : Module.FaithfullyFlat Ahat Bhat :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    apply RingHom.isRegular_of_isRegular_comp (C := Bhat)
    · change (φhat.comp (algebraMap A Ahat)).IsRegular
      rw [hcomm]
      exact hregular
    · exact hflatHat
    · exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
