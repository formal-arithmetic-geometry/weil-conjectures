module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- The localization of a filtered colimit at a prime is integrally closed when
 every stage localization at a contracted prime is integrally closed.
(blueprint: lem-weil-pbc-filtered-colimit-normal-ring-integrally-closed)

This is the integral-closedness part of the proof of Stacks Project, Algebra,
Tag 037D. A monic relation and a fraction are lifted to one common stage;
normality there puts the fraction in that stage, hence in the colimit.
-/
theorem filtered_colimit_localization_isIntegrallyClosed
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (hF : ∀ i : I, ∀ (p : Ideal (F.obj i)) [p.IsPrime],
      IsIntegrallyClosed (Localization.AtPrime p))
    (p : Ideal ((colimit F : CommRingCat.{u}) : Type u)) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  sorry

end CommRingCat
