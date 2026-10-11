/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# A filtered colimit of normal rings is normal

Source: Stacks Project, Algebra, Lemma Tag 037D (lemma-colimit-normal-ring)
(blueprint: lem-weil-pbc-filtered-colimit-normal-ring).
-/

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- A filtered colimit of normal rings is normal, with no condition on transition maps.
Source: Stacks Project, Algebra, Lemma Tag 037D (lemma-colimit-normal-ring),
stated there for a directed system; the filtered formulation is the one used in the
blueprint (blueprint: lem-weil-pbc-filtered-colimit-normal-ring).

Proof: reduce normality to the localizations at prime ideals.  The localization at a
prime of the colimit is the filtered colimit of the corresponding localizations at the
contracted primes.  Finitely many elements and relations lift to one common index, so
the colimit is a domain; clearing denominators in a monic equation and lifting it to one
stage, normality of that stage puts the root back in the colimit.  This proves each
localization is a normal domain.
-/
theorem isNormal_of_filtered_colimit
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (hF : ∀ i : I, ∀ (p : Ideal (F.obj i)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧
        IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (p : Ideal ((colimit F : CommRingCat.{u}) : Type u)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧
        IsIntegrallyClosed (Localization.AtPrime p) := by
  sorry

end CommRingCat
