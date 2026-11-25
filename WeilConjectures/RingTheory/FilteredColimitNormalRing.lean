/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import WeilConjectures.RingTheory.FilteredColimitNormalRingDomain
import WeilConjectures.RingTheory.FilteredColimitNormalRingIntegrallyClosed

/-!
# A filtered colimit of normal rings is normal

A filtered colimit of normal rings is normal, with no condition on the transition maps.

## Implementation details

Normality is reduced to the localizations at primes: the localization of the colimit at a prime
is the filtered colimit of the localizations at the contracted primes. Finitely many elements
and relations lift to a common stage, so this colimit is a domain, and a monic equation cleared
of denominators lifts to a stage where normality puts the root back.

The reference states the result for directed systems; it is formalized here for filtered
diagrams.

## References

* [Stacks, Tag 037D]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- A filtered colimit of normal rings is normal, with no condition on transition maps:
all localizations of the colimit at primes are integrally closed domains. -/
theorem isNormal_of_filtered_colimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (hF : ∀ i : I, ∀ (p : Ideal (F.obj i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧
        IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal ((colimit F : CommRingCat.{u}) : Type u)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧
        IsIntegrallyClosed (Localization.AtPrime p) := by
  set_option linter.style.haveILetI false in
  intro p hp
  letI := hp
  exact ⟨filtered_colimit_localization_isDomain F (fun i q hq => (hF i q).1) p,
    filtered_colimit_localization_isIntegrallyClosed F hF p⟩

end CommRingCat
