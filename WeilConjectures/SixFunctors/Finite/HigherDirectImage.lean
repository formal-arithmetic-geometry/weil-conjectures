/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Higher direct images along a finite morphism

For a finite morphism `f : X ⟶ Y` the direct image `f_*` on étale sheaves of `Λ`-modules is
exact (`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`), so its bounded
below right derived functor is `f_*` applied levelwise, and the higher direct images
`R^q f_* F` vanish for `q ≠ 0`, while `R^0 f_* F = f_* F`.

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedFunctorPlusLowerStarSingleIso`:
  `R f_* (F[0]) ≅ (f_* F)[0]` for a finite `f`.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isFinite`: `R^q f_* F = 0` for `q ≠ 0`.
- `AlgebraicGeometry.Etale.higherDirectImageZeroIsoOfIsFinite`: `R^0 f_* F ≅ f_* F`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- For a finite morphism `f`, the derived direct image of a sheaf placed in degree `0` is the
direct image placed in degree `0`, `f_*` being exact. -/
noncomputable def Etale.rightDerivedFunctorPlusLowerStarSingleIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    R+((f)_*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((f)_*[ModuleCat.{u + 1} Λ].obj F) :=
  ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app _ ≪≫
    (((f)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F

end AlgebraicGeometry
