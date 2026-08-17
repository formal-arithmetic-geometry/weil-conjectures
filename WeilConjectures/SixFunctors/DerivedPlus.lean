/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Derived pushforward and derived lower shriek on bounded below derived categories

This file is the bounded below counterpart of `WeilConjectures.SixFunctors.Derived`. For an
abelian coefficient category `A` admitting sheafification on the small étale sites, it
records the right derived functors `R⁺g_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` and
`R⁺f_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_* = Etale.lowerStar` and the lower
shriek `f_! = Etale.lowerShriek`, implemented via
`CategoryTheory.Functor.rightDerivedFunctorPlus`.

## Why this file exists separately

The unbounded construction in `WeilConjectures.SixFunctors.Derived` goes through
`CategoryTheory.Functor.rightDerivedFunctor`, which needs the source abelian category to
have K-injective resolutions. In this repository the only source of that hypothesis is the
sorried instance
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`, recording the
theorem of Alonso Tarrío–Jeremías López–Souto Salorio and Serpé, which is not formalized
here or in Mathlib.

The bounded below construction needs no such input: `rightDerivedFunctorPlus` asks only for
enough injectives in the source, and a Grothendieck abelian category has enough injectives
by `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`. Since the sheaf categories are
Grothendieck abelian under the hypotheses already assumed here
(`AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`), the functors
below rest only on proved theorems.

This is why the file deliberately does **not** import
`WeilConjectures.DerivedCategory.HomotopyCategory.GrothendieckAbelian`: keeping the sorried
instance out of the import closure is what makes the independence mechanically checkable
rather than a claim in prose. Anything added here should preserve that.

Downstream code that only needs bounded below complexes — which is the case for the Weil
conjectures, where the target is `D^b_c` — should prefer these definitions over the
unbounded ones. The two agree where both apply, by
`CategoryTheory.Functor.rightDerivedFunctorPlusCompatibility`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`: the right derived functor `R⁺g_*`
  of the pushforward on bounded below derived categories of étale sheaves.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus`: the right derived functor `R⁺f_!`
  of the lower shriek on bounded below derived categories of étale sheaves.

-/

@[expose] public section

universe w w' v' u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]

section DerivedLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
variable [HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The right derived functor `R⁺g_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_*` along
an arbitrary morphism `g : Z ⟶ Y` on the bounded below derived categories of étale
sheaves.

Unlike `AlgebraicGeometry.Etale.rightDerivedLowerStar` this needs no K-injective
resolutions, only enough injectives in the source, which the sheaf category has for free
being Grothendieck abelian. -/
noncomputable def Etale.rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctorPlus

end DerivedLowerStar

section DerivedLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The right derived functor `R⁺f_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` of the lower shriek `f_!` along
a morphism `f : X ⟶ Y` admitting a compactification, on the bounded below derived
categories of étale sheaves.

Unlike `AlgebraicGeometry.Etale.rightDerivedLowerShriek` this needs no K-injective
resolutions, only enough injectives in the source, which the sheaf category has for free
being Grothendieck abelian. -/
noncomputable def Etale.rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerShriek A f).rightDerivedFunctorPlus

end DerivedLowerShriek

end AlgebraicGeometry
