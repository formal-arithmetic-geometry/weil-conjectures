/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
/-!
# Derived comparison in fixed constant coefficients

## Implementation details

* `siteComparisonDerivedPullbackPlus` uses the fixed-ring sheaf presentation, which agrees
  directly with both open extension and the canonical direct-image mate.

## References

* [Stacks Project, Tag 099R](https://stacks.math.columbia.edu/tag/099R)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The bounded below exact comparison in the fixed-ring sheaf presentation.
Its realization as modules over the continuous-function coefficient sheaf is
`finiteCoefficientDerivedComparisonPlus`. -/
noncomputable abbrev siteComparisonDerivedPullbackPlus (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus

end AlgebraicGeometry.ProEtale
