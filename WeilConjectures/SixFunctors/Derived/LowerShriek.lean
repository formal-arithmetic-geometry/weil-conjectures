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

- `AlgebraicGeometry.rightDerivedLowerShriekOfCompactification` : `Rf_!` with respect to a
  compcatification.

- `AlgebraicGeometry.rightDerivedLowerShriekOfCompactificationPlus` : `Rf_!`
  on bounded below derived category with respect to a compcatification.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriek` : `Rf_!`
  specifying to the chosen compcatification `HasCompactification.compactification`.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriek` : `Rf_!` on bounded below derived category
  specifying to the chosen compcatification `HasCompactification.compactification`.

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

This is how `Rf_!` is defined in the six functor formalism: `i_!` is exact
(`Etale.preservesFiniteLimits_openImmersionLowerShriek` and the fact that it is a left
adjoint), so it needs no derivation and induces `Di_! = Functor.mapDerivedCategory` termwise;
only the pushforward is derived.

It is deliberately *not* the total right derived functor of the composite
`i_! ⋙ g_* = Etale.lowerShriek`. The two agree exactly when `i_!` sends injective sheaves to
`g_*`-acyclic ones, which is a theorem, not a definitional matter, and is not proved here. -/
noncomputable def rightDerivedLowerShriekOfCompactification :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
    (Etale.lowerStar A c.g).rightDerivedFunctor

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the *bounded below* derived categories of étale sheaves:
the bounded below counterpart of `rightDerivedLowerShriekOfCompactification`, with `Di_!` the
functor `Functor.mapDerivedCategoryPlus` induced by the exact `i_!` and `R⁺g_*` the bounded
below right derived pushforward. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus ⋙
    (Etale.lowerStar A c.g).rightDerivedFunctorPlus

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
  Etale.rightDerivedLowerShriekOfCompactification A (HasCompactification.compactification f)

@[inherit_doc rightDerivedLowerShriek]
scoped notation "R(" f ")_![" A "]" =>
  rightDerivedLowerShriek A f

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` on the *bounded below* derived
categories of étale sheaves: the functor `rightDerivedLowerShriekOfCompactificationPlus`
attached to the chosen compactification `HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  Etale.rightDerivedLowerShriekOfCompactificationPlus A (HasCompactification.compactification f)

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
