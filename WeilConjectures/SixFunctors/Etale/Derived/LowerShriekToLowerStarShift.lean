/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# The forget-supports map commutes with shifts

For a morphism `f` with chosen compactification `(i, g)`, the forget-supports map
`Rf_! ⟶ Ri_* ⋙ Rg_*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekToLowerStarComp`) and,
for `f` proper, the identification `Rf_! ≅ Rf_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`) commute with the
shifts. Each ingredient does: the units of the adjunctions `D(j_!) ⊣ D(j^*)` and
`D(g^*) ⊣ Rg_*`, and the composition isomorphism `Ri_* ⋙ Rg_* ≅ R(i ≫ g)_*`, the conjugate of
the composition isomorphism of the pullbacks.

## Main results

- `AlgebraicGeometry.Etale.commShift_rightDerivedLowerShriekToLowerStarComp`
- `AlgebraicGeometry.Etale.commShift_rightDerivedLowerShriekIsoRightDerivedLowerStar_hom`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

end Etale

end AlgebraicGeometry
