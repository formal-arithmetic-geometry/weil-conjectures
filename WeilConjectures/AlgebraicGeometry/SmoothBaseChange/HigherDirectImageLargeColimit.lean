/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit

/-!
# Higher direct images and filtered diagrams at coefficient size

## References

* [Stacks Project](https://stacks.math.columbia.edu), Tags 0739, 03Q8, 09Z1
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Higher direct image along a qcqs morphism preserves colimits of filtered diagrams
indexed in the coefficient universe. -/
theorem preservesColimitsOfShape_higherDirectImage_large
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (q : ℤ)
    (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J
      (DerivedCategory.Plus.singleFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
        R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙ DerivedCategory.Plus.homologyFunctor _ q) :=
  (Etale.preservesFilteredColimitsOfSize_higherDirectImage Λ h q).preserves_filtered_colimits J

end AlgebraicGeometry.Etale
