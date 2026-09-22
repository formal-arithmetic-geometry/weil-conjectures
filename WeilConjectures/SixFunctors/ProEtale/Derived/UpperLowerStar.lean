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
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.Defs

/-!

# Derived Upper Star and Lower Star

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`.

As there, the derived pushforward of pro-étale sheaves is *not* given a definition of its
own: it is the generic derived-functor construction of the folder
`WeilConjectures.CategoryTheory.DerivedCategory` applied to the underived pushforward
`(g)_*[A]`, and it is written by nesting the generic notation inside the underived one:

| derived functor | notation | meaning |
| --- | --- | --- |
| `Rg_* : D(Z_proét) ⥤ D(Y_proét)` | `R((g)_*[A])` | `(g)_*[A].rightDerivedFunctor` |
| `Rg_* : D⁺(Z_proét) ⥤ D⁺(Y_proét)` | `R+((g)_*[A])` | `(g)_*[A].rightDerivedFunctorPlus` |

The generic notations `R(-)` and `R+(-)` are scoped in the `CategoryTheory.Functor`
namespace, so a file using them needs `open scoped CategoryTheory.Functor`. Each row above
is recorded below as an `example`, at the place where a definition of the corresponding
functor would have stood, so that the type of the functor is spelled out.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section DerivedLowerStar

namespace ProEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_proét) ⥤ D(Y_proét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
pro-étale sheaves.

It is not a definition of its own: it is the generic `Functor.rightDerivedFunctor`,
written `R(-)`, applied to the underived pushforward `(g)_*[A]`. -/
noncomputable example :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) :=
  R((g)_*[A])

/-- The right derived functor `Rg_* : D⁺(Z_proét) ⥤ D⁺(Y_proét)` of the pushforward `g_*`
on the *bounded below* derived categories of pro-étale sheaves: the generic
`Functor.rightDerivedFunctorPlus`, written `R+(-)`, applied to `(g)_*[A]`. -/
noncomputable example :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z) A) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Y) A) :=
  R+((g)_*[A])

end ProEtale

end DerivedLowerStar

end AlgebraicGeometry
