/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.Defs

/-!

# Derived Upper Star and Lower Star

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`.

# Main Results

- `AlgebraicGeometry.ProEtale.rightDerivedLowerStar` : total right derived of lower star,
  with scoped notation `R(g)_*[A]`, prefixing the notation `(g)_*[A]` of the underived
  pushforward by `R`.

- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarPlus` : total right derived of lower star
  on bounded below derived category, with scoped notation `R(g)_*[A]+`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section DerivedLowerStar

namespace ProEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_proét) ⥤ D(Y_proét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
pro-étale sheaves. -/
noncomputable def rightDerivedLowerStar :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  (g)_*[A].rightDerivedFunctor

@[inherit_doc rightDerivedLowerStar]
scoped notation "R(" g ")_*[" A "]" =>
  rightDerivedLowerStar A g

/-- The right derived functor `Rg_* : D⁺(Z_proét) ⥤ D⁺(Y_proét)` of the pushforward `g_*` on
the *bounded below* derived categories of pro-étale sheaves. -/
noncomputable def rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z) A) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) A) :=
  (g)_*[A].rightDerivedFunctorPlus

@[inherit_doc rightDerivedLowerStarPlus]
scoped notation "R(" g ")_*[" A "]+" =>
  rightDerivedLowerStarPlus A g

end ProEtale

end DerivedLowerStar

end AlgebraicGeometry
