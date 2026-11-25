/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.StrictWCover.ThmPeIndetaleRefinementPart3Supplement
public import Mathlib.SetTheory.Cardinal.Arithmetic
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.PrincipalWLocalizationSize
import WeilConjectures.RingTheory.EtaleContraction.EtaleContractionSize
import WeilConjectures.ProperBaseChange.PrincipalWLocalization.Retained.RetainedLocalizationSize

/-!
# Cardinality of the strict w-local cover

If `κ` is an infinite cardinal bounding the cardinality of a commutative ring `A`, then the
strict w-local cover of `A` also has cardinality at most `κ`.

## Main results

- `PrincipalWLocalization.StrictWCover.cardinalMk_le`: the cardinality bound.

## Implementation details

The cover is built in three stages, each bounded separately: the principal w-localization `W`
of `A`, its étale contraction `E`, and the retained localization of the w-localization of `E`
along the closed subset `V(IE)`. Each stage has cardinality at most `max |A| ℵ₀` by encoding
its elements through finite data (finite lists, tuples of fractions, finite presentations)
and choosing stage representatives in filtered colimits.

## References

- Stacks Project, Tags 0976, 097S, 0984, 097X.
-/

@[expose] public section

universe u v

namespace PrincipalWLocalization.StrictWCover

/-- The strict w-local cover of `A` has cardinality at most any infinite cardinal bounding the
cardinality of `A`. -/
theorem cardinalMk_le (A : Type u) [CommRing A] (κ : Cardinal.{v})
    (hκ : Cardinal.aleph0 ≤ κ)
    (hA : Cardinal.lift.{v} (Cardinal.mk A) ≤ Cardinal.lift.{u} κ) :
    Cardinal.lift.{v} (Cardinal.mk (algebra A)) ≤ Cardinal.lift.{u} κ := by
  let μ : Cardinal.{u} := max (Cardinal.mk A) Cardinal.aleph0
  have hμ : Cardinal.aleph0 ≤ μ := le_max_right _ _
  have hW := PrincipalWLocalization.cardinalMk_le A μ hμ (le_max_left _ _)
  have hE : Cardinal.mk (contraction A) ≤ μ :=
    CommRingCat.EtaleContraction.cardinalMk_le
      (CommRingCat.of (PrincipalWLocalization.algebra A)) μ hμ hW
  have hEw := PrincipalWLocalization.cardinalMk_le (contraction A) μ hμ hE
  have hC : Cardinal.mk (algebra A) ≤ μ :=
    (PrincipalWLocalization.Retained.cardinalMk_le (contraction A)
      (PrimeSpectrum.zeroLocus (extendedIdeal A : Set (contraction A)))
      (PrimeSpectrum.isClosed_zeroLocus _)).trans hEw
  apply (Cardinal.lift_le.mpr hC).trans
  simpa [μ] using max_le hA (Cardinal.lift_le.mpr hκ)

end PrincipalWLocalization.StrictWCover
