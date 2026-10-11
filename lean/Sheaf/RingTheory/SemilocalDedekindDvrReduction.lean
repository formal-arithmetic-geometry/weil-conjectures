/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Reduction of a semilocal Dedekind domain to discrete valuation rings

Source: Stacks Project, Algebra, Tags 034W and 034X, and Varieties, Lemma 33.37.8
(Tag 09N5), the reduction to local rings
(blueprint: lem-sc-semilocal-dedekind-dvr-reduction).
-/

@[expose] public section

universe u v

namespace MaximalSpectrum

/-- A semilocal Dedekind domain of dimension one has finitely many
maximal ideals. Its localizations there are DVRs with the original fraction field; an element
of that field comes from the Jacobson radical precisely when it comes from the maximal ideal
of each localization. The local algebra structures are the canonical localization embeddings.
Mathlib's Dedekind predicate permits dimension zero, so dimension one is stated
separately to retain the node's convention.
Source: Stacks Project, Algebra, Tags 034W and 034X; Varieties, Tag 09N5, local-ring reduction
(blueprint: lem-sc-semilocal-dedekind-dvr-reduction).

Proof:
1. Semilocality says that the maximal spectrum is finite. Dimension one and the domain
   hypothesis imply that each maximal ideal is a nonzero prime.
2. Apply `lem-sc-dedekind-localization-dvr` to each such prime. The canonical embedding
   identifies the fraction field of its localization with the original field: every fraction
   of elements of the base ring is also a fraction of elements of the localization.
3. An element from the Jacobson radical belongs to every maximal ideal, hence to every
   localized maximal ideal. Conversely, membership in all the localized maximal ideals
   first implies membership in all localizations. The intersection assertion of
   `lem-sc-dedekind-intersection-localizations` puts it in the base ring, and the contraction
   assertion puts it in each maximal ideal of the base ring, hence in its Jacobson radical. -/
theorem semilocal_dedekind_dvr_reduction
    (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    (K : Type v) [Field K] [Algebra B K] [IsFractionRing B K] :
    let a := fun m : MaximalSpectrum B =>
      IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime m.asIdeal) K
        m.asIdeal.primeCompl (nonZeroDivisors B) m.asIdeal.primeCompl_le_nonZeroDivisors
    Finite (MaximalSpectrum B) ∧
      (∀ m : MaximalSpectrum B,
        letI := a m
        IsDiscreteValuationRing (Localization.AtPrime m.asIdeal) ∧
          IsFractionRing (Localization.AtPrime m.asIdeal) K) ∧
      (∀ x : K,
        (∃ b : B, b ∈ Ideal.jacobson (⊥ : Ideal B) ∧ algebraMap B K b = x) ↔
          ∀ m : MaximalSpectrum B,
            letI := a m
            ∃ y : Localization.AtPrime m.asIdeal,
              y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) ∧
                algebraMap (Localization.AtPrime m.asIdeal) K y = x) := by
  sorry

end MaximalSpectrum
