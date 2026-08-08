/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctor
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Derived pushforward and derived lower shriek on unbounded derived categories

For an abelian coefficient category `A` admitting sheafification on the small étale sites,
the categories of `A`-valued étale sheaves are abelian, the pushforward
`g_* = Etale.lowerStar` along an arbitrary morphism `g` and the lower shriek
`f_! = Etale.lowerShriek` along a morphism `f` admitting a compactification are additive,
and this file records their total right derived functors
`Rg_* : D(Z_ét) ⥤ D(Y_ét)` and `Rf_! : D(X_ét) ⥤ D(Y_ét)` on the unbounded
derived categories, implemented via `CategoryTheory.Functor.rightDerivedFunctor`.

The chosen localized categories `HasDerivedCategory` are inputs with a general universe.
The construction of the unbounded right derived functor requires the source abelian
category to have K-injective resolutions (`CategoryTheory.Abelian.HasKInjectiveResolutions`).
As in `WeilConjectures.SixFunctors.DerivedFunctors.Plus`, the sheaf categories are
Grothendieck abelian
(`AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`) whenever the
coefficient category `A` is a concrete Grothendieck abelian category (with hom types and
underlying types in the universe `u` of the base schemes, and the forgetful functor
preserving limits and filtered colimits and reflecting isomorphisms); this covers the
intended applications `A = Ab.{u}` and `A = ModuleCat.{u} Λ`. That Grothendieck abelian
categories have K-injective resolutions is a theorem of Alonso Tarrío–Jeremías
López–Souto Salorio and Serpé; it is recorded here as the sorried instance
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStar`: the total right derived functor
  `Rg_*` of the pushforward on unbounded derived categories of étale sheaves.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriek`: the total right derived functor
  `Rf_!` of the lower shriek on unbounded derived categories of étale sheaves.

-/

@[expose] public section

universe w w' v' u' u

open CategoryTheory Abelian Limits

namespace CategoryTheory.Abelian

/-- Every Grothendieck abelian category has K-injective resolutions: any cochain
complex admits a monomorphic quasi-isomorphism into a K-injective complex. This is a
theorem of Alonso Tarrío–Jeremías López–Souto Salorio and Serpé, whose formalization
is not yet available. -/
instance hasKInjectiveResolutions_of_isGrothendieckAbelian
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    HasKInjectiveResolutions C :=
  sorry

end CategoryTheory.Abelian

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

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def Etale.rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctor

end DerivedLowerStar

section DerivedLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The total right derived functor `Rf_! : D(X_ét) ⥤ D(Y_ét)` of the lower shriek
`f_!` along a morphism `f : X ⟶ Y` admitting a compactification on the unbounded
derived categories of étale sheaves. -/
noncomputable def Etale.rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerShriek A f).rightDerivedFunctor

end DerivedLowerShriek

end AlgebraicGeometry
