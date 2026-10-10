/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.LowerShriek.Defs

/-!

# Derived lower shriek on module objects over `C(-, T)`

This is the module-object counterpart of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`, for the
coefficient ring objects `A_X(T) = C(-, T)` of a commutative topological ring `T`.

As there, the derived functors entering `Rf_!` are not given definitions of their own: they
are the generic derived-functor constructions of the folder
`WeilConjectures.CategoryTheory.DerivedCategory`, written `D(-)`, `D+(-)`, `R(-)` and `R+(-)`,
applied to the underived functors `(c.i)_!open⟦T⟧` and `(c.g)_*⟦T⟧` on module objects. The
extension by zero `i_!` is exact on module objects, so it is derived levelwise, while the
pushforward `g_*` is derived via K-injective resolutions.

## Main definitions

- `ProEtale.ContinuousMapRing.rightDerivedLowerShriekOfCompactification` : `Rf_!` with
  respect to a compactification `c`, with scoped notation `Rf_!(c)⟦T⟧`, and its bounded below
  version `ProEtale.ContinuousMapRing.rightDerivedLowerShriekOfCompactificationPlus`, with
  scoped notation `Rf_!(c)⟦T⟧+`.

- `ProEtale.ContinuousMapRing.rightDerivedLowerShriek` : `Rf_!` for the chosen compactification
  `HasCompactification.compactification f`, with scoped notation `R(f)_!⟦T⟧`, and its bounded
  below version `ProEtale.ContinuousMapRing.rightDerivedLowerShriekPlus`, with scoped notation
  `R(f)_!⟦T⟧+`.

## Main results

- `ProEtale.ContinuousMapRing.rightDerivedLowerShriekOfCompactificationPlusCompatibility` and
  `ProEtale.ContinuousMapRing.rightDerivedLowerShriekPlusCompatibility` : the bounded below
  `Rf_!` is the restriction of the unbounded `Rf_!` along the inclusions
  `DerivedCategory.Plus.ι` of the bounded below derived categories.

-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.ContinuousMapRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] {X Y : Scheme.{u}}

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f)

/-- The derived lower shriek `Rf_! : D(Mod_{A_X(T)}) ⥤ D(Mod_{A_Y(T)})` attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of module
objects: the functor `Di_!` induced on derived categories by the *exact* extension by zero
`i_!`, followed by the total right derived pushforward `Rg_*`.

Warning: as in the finite-coefficient case, it is deliberately *not* the total right derived
functor of the composite `i_! ⋙ g_* = f_!`. -/
noncomputable abbrev rightDerivedLowerShriekOfCompactification :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (continuousMapRingObj T Y)) :=
  D((c.i)_!open⟦T⟧) ⋙ R((c.g)_*⟦T⟧)

/-- The derived lower shriek `Rf_! : D⁺(Mod_{A_X(T)}) ⥤ D⁺(Mod_{A_Y(T)})` attached to a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the *bounded below* derived categories of
module objects: the bounded below counterpart of
`rightDerivedLowerShriekOfCompactification`. -/
noncomputable abbrev rightDerivedLowerShriekOfCompactificationPlus :
    DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X)) ⥤
      DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (continuousMapRingObj T Y)) :=
  D+((c.i)_!open⟦T⟧) ⋙ R+((c.g)_*⟦T⟧)

@[inherit_doc rightDerivedLowerShriekOfCompactification]
scoped notation "Rf_!(" c ")⟦" T "⟧" =>
  rightDerivedLowerShriekOfCompactification T c

@[inherit_doc rightDerivedLowerShriekOfCompactificationPlus]
scoped notation "Rf_!(" c ")⟦" T "⟧+" =>
  rightDerivedLowerShriekOfCompactificationPlus T c

/-- The bounded below derived lower shriek attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` is the restriction of the unbounded one along the inclusions of the
bounded below derived categories: on the `Di_!` factor this is
`Functor.mapDerivedCategoryPlusCompatibility` (`i_!` is exact), on the `Rg_*` factor it is
`Functor.rightDerivedFunctorPlusCompatibility`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusCompatibility :
    Rf_!(c)⟦T⟧+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ Rf_!(c)⟦T⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D+((c.i)_!open⟦T⟧)
      ((c.g)_*⟦T⟧).rightDerivedFunctorPlusCompatibility ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((c.i)_!open⟦T⟧).mapDerivedCategoryPlusCompatibility
      R((c.g)_*⟦T⟧) ≪≫
    Functor.associator _ _ _

end OfCompactification

section Chosen

variable (f : X ⟶ Y) [HasCompactification f]

/-- The derived lower shriek `Rf_! : D(Mod_{A_X(T)}) ⥤ D(Mod_{A_Y(T)})` along a morphism
`f : X ⟶ Y` admitting a compactification, on the unbounded derived categories of module
objects: the functor `rightDerivedLowerShriekOfCompactification` attached to the chosen
compactification `HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriek :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (continuousMapRingObj T Y)) :=
  Rf_!(HasCompactification.compactification f)⟦T⟧

@[inherit_doc rightDerivedLowerShriek]
scoped notation "R(" f ")_!⟦" T "⟧" => rightDerivedLowerShriek T f

/-- The derived lower shriek `Rf_! : D⁺(Mod_{A_X(T)}) ⥤ D⁺(Mod_{A_Y(T)})` on the *bounded
below* derived categories of module objects, for the chosen compactification. -/
noncomputable def rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X)) ⥤
      DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (continuousMapRingObj T Y)) :=
  Rf_!(HasCompactification.compactification f)⟦T⟧+

@[inherit_doc rightDerivedLowerShriekPlus]
scoped notation "R(" f ")_!⟦" T "⟧+" => rightDerivedLowerShriekPlus T f

lemma rightDerivedLowerShriek_eq :
    R(f)_!⟦T⟧ = Rf_!(HasCompactification.compactification f)⟦T⟧ := rfl

lemma rightDerivedLowerShriekPlus_eq :
    R(f)_!⟦T⟧+ = Rf_!(HasCompactification.compactification f)⟦T⟧+ := rfl

/-- The bounded below derived lower shriek on module objects is the restriction of the
unbounded one along the inclusions of the bounded below derived categories. -/
noncomputable def rightDerivedLowerShriekPlusCompatibility :
    R(f)_!⟦T⟧+ ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ R(f)_!⟦T⟧ :=
  rightDerivedLowerShriekOfCompactificationPlusCompatibility T
    (HasCompactification.compactification f)

end Chosen

end AlgebraicGeometry.ProEtale.ContinuousMapRing
