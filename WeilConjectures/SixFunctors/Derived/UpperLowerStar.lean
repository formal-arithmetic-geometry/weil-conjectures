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

# Derived Upper Star and Lower Star

# Main Results

- `AlgebraicGeometry.Etale.rightDerivedLowerStar` : total right derived of lower star, with
  scoped notation `R(g)_*[A]`, prefixing the notation `(g)_*[A]` of the underived
  pushforward by `R`.

- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` : total right derived of lower star on
  bounded below derived category, with scoped notation `R(g)_*[A]+`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section DerivedLowerStar

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (g)_*[A].rightDerivedFunctor

@[inherit_doc rightDerivedLowerStar]
scoped notation "R(" g ")_*[" A "]" =>
  rightDerivedLowerStar A g

/-- The right derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_*` on the
*bounded below* derived categories of étale sheaves. -/
noncomputable def rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (g)_*[A].rightDerivedFunctorPlus

@[inherit_doc rightDerivedLowerStarPlus]
scoped notation "R(" g ")_*[" A "]+" =>
  rightDerivedLowerStarPlus A g

end Etale

end DerivedLowerStar

end AlgebraicGeometry
