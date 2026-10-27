/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# DVR localizations of a normalization in a finite field extension

Source: Stacks Project, Algebra, Tags 00PH (`lemma-exists-dvr`), final paragraph,
and 09IG (`lemma-integral-closure-Dedekind`).
(blueprint: lem-sfb-finite-normalization-local-dvr)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace integralClosure

/-- The normalization of a one-dimensional Noetherian local domain in an arbitrary
finite field extension has DVR localizations above its closed point, embedded in
the extension by the fraction formula. The image subring has that same fraction
field and the indicated maximal ideal and contractions.

Source: Stacks Project, Algebra, Tags 00PH (`lemma-exists-dvr`), final paragraph,
and 09IG (`lemma-integral-closure-Dedekind`).
(blueprint: lem-sfb-finite-normalization-local-dvr)

Proof:
1. Apply `lem-sc-integral-closure-dedekind-surjective-fibres` to `D`, `K`, `L`.
   The integral closure `C` is Noetherian, normal, a domain, and of dimension one.
   The given inclusion makes `L` its fraction field by
   `lem-weil-pbc-integral-closure-finite-extension-normal`. Neither result needs
   `D` normal or `L/K` separable.
2. The inclusion `D -> C` is integral and injective. Apply `pqf-lem-lying-over`
   to the maximal ideal of `D`. Any prime `q` over it contains the image of a
   nonzero element of that ideal, so is nonzero. If it were not maximal, a
   maximal ideal properly above it would give a chain `(0) < q < n`, contrary
   to dimension one.
3. For every such `q`, apply `lem-sc-dedekind-localization-dvr`. Apply
   `lem-weil-pbc-localization-normal-domain` with `S = C \ q` to obtain the
   injective fraction map from `C_q` to `L`. Equivalently, this is Mathlib's
   `Localization.mapToFractionRing`; every fraction maps to `c/s`. Every element
   of the localization has such a representation, so its image is precisely
   the stated set. Transport the DVR structure and fraction-field property
   through the isomorphism from the localization to its image. Each `d` in `D`
   belongs to the image as `d/1`.
4. The prime-localization definition `def-weil-pbc-localization-at-prime` gives
   `m_A = qA`. Apply `lem-trf-localization-maximal-contraction` to get its
   contraction `q` in `C`, then contract once more to `D`. Transporting these
   equalities to the image subring gives the same three ideal identities there.
-/
theorem finite_normalization_local_dvr
    (D : Type u) (K : Type v) (L : Type w)
    [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
    [Field K] [Field L] [Algebra D K] [IsFractionRing D K]
    [Algebra K L] [Algebra D L] [IsScalarTower D K L] [FiniteDimensional K L]
    (hdim : ringKrullDim D = 1) (hm : IsLocalRing.maximalIdeal D ≠ ⊥)
    (C : Subalgebra D L) (hC : C = integralClosure D L) :
    IsNoetherianRing C ∧ IsDomain C ∧ IsIntegrallyClosed C ∧ ringKrullDim C = 1 ∧
      IsFractionRing C L ∧
      (∃ q : PrimeSpectrum C,
        q.asIdeal.comap (algebraMap D C) = IsLocalRing.maximalIdeal D) ∧
      ∀ q : PrimeSpectrum C,
        q.asIdeal.comap (algebraMap D C) = IsLocalRing.maximalIdeal D →
        q.asIdeal ≠ ⊥ ∧ q.asIdeal.IsMaximal ∧
        ∃ e : Localization.AtPrime q.asIdeal →ₐ[C] L,
          Function.Injective e ∧
          (∀ (c : C) (s : q.asIdeal.primeCompl),
            e (IsLocalization.mk' (Localization.AtPrime q.asIdeal) c s) =
              (c : L) / ((s : C) : L)) ∧
          (∀ x : L, x ∈ e.range ↔
            ∃ c s : C, s ∉ q.asIdeal ∧ x = (c : L) / (s : L)) ∧
          (∀ d : D, algebraMap D L d ∈ e.range) ∧
          IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) ∧
          @IsFractionRing (Localization.AtPrime q.asIdeal) _ L _ e.toRingHom.toAlgebra ∧
          IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) =
            q.asIdeal.map (algebraMap C (Localization.AtPrime q.asIdeal)) ∧
          (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).comap
            (algebraMap C (Localization.AtPrime q.asIdeal)) = q.asIdeal ∧
          (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).comap
            ((algebraMap C (Localization.AtPrime q.asIdeal)).comp (algebraMap D C)) =
              IsLocalRing.maximalIdeal D ∧
          ∃ h : IsDiscreteValuationRing e.range,
            IsFractionRing e.range L ∧
            @IsLocalRing.maximalIdeal e.range _ h.toIsLocalRing =
              q.asIdeal.map (algebraMap C e.range) ∧
            (@IsLocalRing.maximalIdeal e.range _ h.toIsLocalRing).comap
              (algebraMap C e.range) = q.asIdeal ∧
            (@IsLocalRing.maximalIdeal e.range _ h.toIsLocalRing).comap
              ((algebraMap C e.range).comp (algebraMap D C)) = IsLocalRing.maximalIdeal D := by
  sorry

end integralClosure
