/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Derived pushforward and derived lower shriek on bounded below derived categories

For an abelian coefficient category `A` admitting sheafification on the small étale sites,
the categories of `A`-valued étale sheaves are abelian, the pushforward
`g_* = Etale.lowerStar` along an arbitrary morphism `g` and the lower shriek
`f_! = Etale.lowerShriek` along a morphism `f` admitting a compactification are additive,
and this file records their total right derived functors
`Rg_* : D^+(Z_ét) ⥤ D^+(Y_ét)` and `Rf_! : D^+(X_ét) ⥤ D^+(Y_ét)` on the bounded below
derived categories, implemented via `CategoryTheory.Functor.rightDerivedFunctorPlus`.

The chosen localized categories `HasDerivedCategory` are inputs with a general universe.
That the sheaf categories have enough injectives is deduced by mathlib's instances from
the sheaf categories being Grothendieck abelian
(`AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`): this holds
whenever the coefficient category `A` is a concrete Grothendieck abelian category (with
hom types and underlying types in the universe `u` of the base schemes, and the
forgetful functor preserving limits and filtered colimits and reflecting isomorphisms),
since the small étale site is equivalent to the essentially small affine étale site.
This covers the intended applications `A = Ab.{u}` and `A = ModuleCat.{u} Λ`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`: the total right derived functor
  `Rg_*` of the pushforward on bounded below derived categories of étale sheaves.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus`: the total right derived functor
  `Rf_!` of the lower shriek on bounded below derived categories of étale sheaves.

-/

@[expose] public section

universe w w' v' u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology A]

section DerivedLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
variable [HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The total right derived functor `Rg_* : D^+(Z_ét) ⥤ D^+(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the bounded below derived categories of
étale sheaves. -/
noncomputable def Etale.rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctorPlus

end DerivedLowerStar

section DerivedLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The total right derived functor `Rf_! : D^+(X_ét) ⥤ D^+(Y_ét)` of the lower shriek
`f_!` along a morphism `f : X ⟶ Y` admitting a compactification on the bounded below
derived categories of étale sheaves. -/
noncomputable def Etale.rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerShriek A f).rightDerivedFunctorPlus

end DerivedLowerShriek

end AlgebraicGeometry
