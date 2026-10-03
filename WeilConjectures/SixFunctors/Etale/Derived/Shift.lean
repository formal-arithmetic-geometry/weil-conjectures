/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# Compatibility of the derived six functors with shifts

The derived pullback, pushforward, lower shriek and exceptional inverse image on the
unbounded derived categories of étale sheaves commute with the shift functors. This file
equips each of them with its `CategoryTheory.Functor.CommShift` structure:

* `D(g^*)` is the functor induced by an exact functor, so it commutes with shifts by
  Mathlib's `Functor.mapDerivedCategory` instance;
* `Rg_*` is right adjoint to `D(g^*)` (`Etale.mapDerivedUpperStarLowerStarAdjunction`), so it
  inherits the structure by `Adjunction.rightAdjointCommShift`;
* `Lg^*` is isomorphic to `D(g^*)` (`Etale.leftDerivedUpperStarIsoMapDerivedCategory`);
* `Rf_! = D(i_!) ⋙ R(g_*)` for the chosen compactification `(i, g)` is a composite of two
  functors commuting with shifts;
* `Rf^!` is right adjoint to `Rf_!` (`Etale.rightDerivedUpperShriekAdjunction`).

These are what make the boundary of the supported localization triangle and the cup
product with supports compatible with the degree shifts in which cohomology classes live.

## Main definitions

- `AlgebraicGeometry.Etale.commShiftRightDerivedLowerStar`
- `AlgebraicGeometry.Etale.commShiftLeftDerivedUpperStar`
- `AlgebraicGeometry.Etale.commShiftRightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.commShiftRightDerivedUpperShriek`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The total right derived pushforward `Rg_*` commutes with shifts: it is right adjoint to the
functor `D(g^*)` induced by the exact pullback, which does. -/
noncomputable instance commShiftRightDerivedLowerStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (R((g)_*[A])).CommShift ℤ :=
  (mapDerivedUpperStarLowerStarAdjunction A g).rightAdjointCommShift ℤ

/-- The derived lower shriek `Rf_!` commutes with shifts: for the chosen compactification
`(i, g)` of `f` it is the composite of the functor `D(i_!)` induced by the exact extension by
zero and of the right derived pushforward `Rg_*`. -/
noncomputable instance commShiftRightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (R(f)_![A]).CommShift ℤ :=
  inferInstanceAs ((D(((HasCompactification.compactification f).i)_!open[A]) ⋙
    R(((HasCompactification.compactification f).g)_*[A])).CommShift ℤ)

/-- The exceptional inverse image `Rf^!` commutes with shifts, being right adjoint to `Rf_!`. -/
noncomputable instance commShiftRightDerivedUpperShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (R(f)^![A]).CommShift ℤ :=
  (rightDerivedUpperShriekAdjunction A f).rightAdjointCommShift ℤ

section Monoidal

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived pullback `Lg^*` commutes with shifts, being isomorphic to the functor `D(g^*)`
induced by the exact pullback (`Etale.leftDerivedUpperStarIsoMapDerivedCategory`). -/
noncomputable instance commShiftLeftDerivedUpperStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).CommShift ℤ :=
  Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ

end Monoidal

end Etale

end AlgebraicGeometry
