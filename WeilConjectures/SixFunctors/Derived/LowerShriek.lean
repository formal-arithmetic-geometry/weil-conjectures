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

- `AlgebraicGeometry.Compactification.rightDerivedLowerShriek` : `Rf_!` with respect to a
  compcatification.

- `AlgebraicGeometry.Compactification.rightDerivedLowerShriekPlus` : `Rf_!`
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
noncomputable def Compactification.rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
    (Etale.lowerStar A c.g).rightDerivedFunctor

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the *bounded below* derived categories of étale sheaves:
the bounded below counterpart of `Compactification.rightDerivedLowerShriek`, with `Di_!` the
functor `Functor.mapDerivedCategoryPlus` induced by the exact `i_!` and `R⁺g_*` the bounded
below right derived pushforward. -/
noncomputable def Compactification.rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus ⋙
    (Etale.lowerStar A c.g).rightDerivedFunctorPlus

end OfCompactification

variable (f : X ⟶ Y) [HasCompactification f]

/-- The derived lower shriek `Rf_! : D(X_ét) ⥤ D(Y_ét)` along a morphism `f : X ⟶ Y`
admitting a compactification, on the unbounded derived categories of étale sheaves: the
functor `Compactification.rightDerivedLowerShriek` attached to the chosen compactification
`HasCompactification.compactification f`. -/
noncomputable def Etale.rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (HasCompactification.compactification f).rightDerivedLowerShriek A

/-- The derived lower shriek `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` on the *bounded below* derived
categories of étale sheaves: the functor `Compactification.rightDerivedLowerShriekPlus`
attached to the chosen compactification `HasCompactification.compactification f`. -/
noncomputable def Etale.rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (HasCompactification.compactification f).rightDerivedLowerShriekPlus A

lemma Etale.rightDerivedLowerShriek_eq : Etale.rightDerivedLowerShriek A f =
    (HasCompactification.compactification f).rightDerivedLowerShriek A := rfl

lemma Etale.rightDerivedLowerShriekPlus_eq : Etale.rightDerivedLowerShriekPlus A f =
    (HasCompactification.compactification f).rightDerivedLowerShriekPlus A := rfl

end DerivedLowerShriek

end AlgebraicGeometry
