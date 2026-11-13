/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology

/-! # Formula for the canonical restricted cohomology map

## References

* [Stacks Project, Tag 0EZM](https://stacks.math.columbia.edu/tag/0EZM)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

attribute [local irreducible] cohomology upperStar rawAffineComplexPullback
  rightDerivedGlobalSections DerivedCategory.Q

/-- An explicit formula for the canonical cohomology map of any triangle over S. -/
theorem rawAffineRestrictedCohomologyMap_formula {S Y Y' : Scheme.{v}} (a : Y' ⟶ Y)
    (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F') (U : S.Etale) :
    HEq (rawAffineRestrictedCohomologyMap a h h' w p F F' φ U)
      (rawAffineComplexPullback (p : ℤ) (rawAffineRestrictedMap a h h' w U)
          ((CochainComplex.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom h)).obj F)) ≫
        (cohomology AddCommGrpCat.{v + 1} (pullback U.hom h') (p : ℤ)).map
          (DerivedCategory.Q.map
            (((upperStar AddCommGrpCat.{v + 1}
                (rawAffineRestrictedMap a h h' w U)).mapCochainComplexSingleFunctor 0).hom.app
                ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom h)).obj F) ≫
              (CochainComplex.singleFunctor _ 0).map
                (rawAffineRestrictedCoefficient a h h' w F F' φ U)))) := by
  rfl

end AlgebraicGeometry.Etale
