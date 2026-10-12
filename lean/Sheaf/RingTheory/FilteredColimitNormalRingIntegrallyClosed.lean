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

/-- The integrally closedness conclusion from the common-stage argument, once the
localization cocone has been constructed.  This isolates the algebraic part of
Stacks Project, Algebra, Lemma Tag 037D.
(blueprint: lem-weil-pbc-filtered-colimit-normal-ring-integrally-closed-common-stage)
-/
theorem integrallyClosed_of_localization_cocone
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {R : Type u} [CommRing R]
    (D : I ⥤ CommRingCat.{u})
    (c : Cocone D) (hc : c.pt = CommRingCat.of R)
    (hD : ∀ i : I, IsIntegrallyClosed (D.obj i)) :
    IsIntegrallyClosed R := by
  sorry

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
  let ι : ∀ i : I, (F.obj i) ⟶ colimit F := fun i => colimit.ι F i
  let pᵢ : ∀ i : I, Ideal ((F.obj i : CommRingCat) : Type u) :=
    fun i => Ideal.comap (ι i).hom p
  obtain ⟨hpᵢ, hcomp, D, hD, hmaps, c, hc, hι, hcol⟩ :=
    AlgebraicGeometry.filteredColimitLocalizationAtPrime F p
  have hDi : ∀ i : I, IsIntegrallyClosed (D.obj i) := by
    intro i
    rw [hD i]
    exact hF i (pᵢ i)
  exact integrallyClosed_of_localization_cocone D c hc hDi

end CommRingCat
