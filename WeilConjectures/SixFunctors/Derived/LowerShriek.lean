/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Derived.HasDerivedCategory
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Derived Lower Shriek

# Main Results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` : `Rf_!` with respect
  to a compcatification `c`, with scoped notation `Rf_!(c)[A]`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlus` : `Rf_!`
  on bounded below derived category with respect to a compcatification `c`, with scoped
  notation `Rf_!(c)[A]+`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriek` : `Rf_!`
  specifying to the chosen compcatification `HasCompactification.compactification`, with
  scoped notation `R(f)_![A]`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus` : `Rf_!` on bounded below derived
  category specifying to the chosen compcatification `HasCompactification.compactification`,
  with scoped notation `R(f)_![A]+`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section DerivedLowerShriek

variable {X Y : Scheme.{u}}

section OfCompactification

namespace Etale

variable {f : X ⟶ Y} (c : Compactification f)

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded derived categories of étale sheaves: the
functor `Di_!` induced on derived categories by the *exact* extension by zero `i_!`, followed
by the total right derived pushforward `Rg_*`.

Warning: It is deliberately *not* the total right derived functor of the composite
`i_! ⋙ g_* = Etale.lowerShriek`. In general, `i_!` does not sends injective sheaves to
`g_*`-acyclic ones, and `Rf_!` is not the derived functor of `f_!`, through its zeroth
homology is `f_!`. Deligne made explicit calculations on $A^1$, see SGA. -/
noncomputable def rightDerivedLowerShriekOfCompactification :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (c.i)_!open[A].mapDerivedCategory ⋙ (c.g)_*[A].rightDerivedFunctor

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the *bounded below* derived categories of étale sheaves:
the bounded below counterpart of `rightDerivedLowerShriekOfCompactification`, with `Di_!` the
functor `Functor.mapDerivedCategoryPlus` induced by the exact `i_!` and `R⁺g_*` the bounded
below right derived pushforward. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (c.i)_!open[A].mapDerivedCategoryPlus ⋙ (c.g)_*[A].rightDerivedFunctorPlus

@[inherit_doc rightDerivedLowerShriekOfCompactification]
scoped notation "Rf_!("c")[" A "]" =>
  rightDerivedLowerShriekOfCompactification A c

@[inherit_doc rightDerivedLowerShriekOfCompactificationPlus]
scoped notation "Rf_!("c")[" A "]+" =>
  rightDerivedLowerShriekOfCompactificationPlus A c

end Etale

end OfCompactification

variable (f : X ⟶ Y) [HasCompactification f]

namespace Etale

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves: the
functor `rightDerivedLowerShriekOfCompactification` attached to the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  Rf_!(HasCompactification.compactification f)[A]

@[inherit_doc rightDerivedLowerShriek]
scoped notation "R(" f ")_![" A "]" =>
  rightDerivedLowerShriek A f

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` on the *bounded below* derived
categories of étale sheaves: the functor `rightDerivedLowerShriekOfCompactificationPlus`
attached to the chosen compactification `HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  Rf_!(HasCompactification.compactification f)[A]+

@[inherit_doc rightDerivedLowerShriekPlus]
scoped notation "R(" f ")_![" A "]+" =>
  rightDerivedLowerShriekPlus A f

lemma rightDerivedLowerShriek_eq : R(f)_![A] =
    Rf_!(HasCompactification.compactification f)[A] := rfl

lemma rightDerivedLowerShriekPlus_eq : R(f)_![A]+ =
    Rf_!(HasCompactification.compactification f)[A]+ := rfl

end Etale

end DerivedLowerShriek

end AlgebraicGeometry
