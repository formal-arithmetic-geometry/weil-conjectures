/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.Retained.ThmPeIndetaleRefinementPart2Supplement3
public import Mathlib.SetTheory.Cardinal.Basic

/-! # Cardinality of retained localization

The retained localization at a closed subset `T` of `Spec R` is a quotient of the principal
w-localization of `R`, so its cardinality is at most that of the principal w-localization.

## References

- Stacks Project, Tag 0984
-/

@[expose] public section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits

namespace PrincipalWLocalization.Retained

/-- Retained localization is a quotient of the principal w-localization, hence no larger. -/
theorem cardinalMk_le (R : Type u) [CommRing R]
    (T : Set (PrimeSpectrum R)) (hT : IsClosed T) :
    #(algebra T hT) ≤ #(PrincipalWLocalization.algebra R) := by
  apply mk_le_of_surjective (f := algebraMap (PrincipalWLocalization.algebra R) (algebra T hT))
  intro x
  obtain ⟨E, y, hy⟩ := Concrete.colimit_exists_rep (localizationDiagram T) x
  obtain ⟨r, hr⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
    (S := Localization.Away (selector E.val E.property.1)) _
    (selector_idempotent E.val E.property.1) y
  refine ⟨r, ?_⟩
  rw [← hy, ← hr]
  exact ((colimit.ι (localizationDiagram T) E).hom.commutes r).symm

end PrincipalWLocalization.Retained
