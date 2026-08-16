/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.DerivedCategory.HomotopyCategory.GrothendieckAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.DerivedCategory.RightDerivedFunctor.Defs
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
The sheaf categories are Grothendieck abelian
(`AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`) whenever the
coefficient category `A` is a concrete Grothendieck abelian category (with hom types and
underlying types in the universe `u` of the base schemes, and the forgetful functor
preserving limits and filtered colimits and reflecting isomorphisms); this covers the
intended applications `A = Ab.{u}` and `A = ModuleCat.{u} Λ`. That Grothendieck abelian
categories have K-injective resolutions is a theorem of Alonso Tarrío–Jeremías
López–Souto Salorio and Serpé; it is recorded here as the sorried instance
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`.

On the *bounded below* derived categories no such input is needed: Mathlib's
`CategoryTheory.Functor.rightDerivedFunctorPlus` requires only `EnoughInjectives` on the
source, and a Grothendieck abelian category has enough injectives
(`CategoryTheory.IsGrothendieckAbelian.enoughInjectives`). So `Etale.rightDerivedLowerStarPlus`
and `Etale.rightDerivedLowerShriekPlus` are unconditional, and the `#print axioms` guards at
the end of this file record that they do not depend on `sorryAx`. Since the `ℓ`-adic
formalism only needs `Dᵇc`, that is the version to build on until the K-injective statement
is proved; `WeilConjectures.DerivedCategory.RightDerivedFunctor.PlusCompatibility` identifies
the restriction of the unbounded functors to `DerivedCategory.Plus` with these.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStar`: the total right derived functor
  `Rg_*` of the pushforward on unbounded derived categories of étale sheaves.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriek`: the total right derived functor
  `Rf_!` of the lower shriek on unbounded derived categories of étale sheaves.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus`: the same two functors on the
  bounded below derived categories, free of the K-injective hypothesis.

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

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def Etale.rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctor

/-- The right derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_*` on the
*bounded below* derived categories of étale sheaves.

Unlike `Etale.rightDerivedLowerStar` this does not depend on
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`, which is still
sorried: `Functor.rightDerivedFunctorPlus` needs only `EnoughInjectives` on the source, which
Mathlib provides for every Grothendieck abelian category. -/
noncomputable def Etale.rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctorPlus

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

/-- The right derived functor `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` of the lower shriek `f_!` on the
*bounded below* derived categories of étale sheaves.

Unlike `Etale.rightDerivedLowerShriek` this does not depend on
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`, which is still
sorried; see `Etale.rightDerivedLowerStarPlus`. -/
noncomputable def Etale.rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerShriek A f).rightDerivedFunctorPlus

end DerivedLowerShriek

/-! ### The bounded below functors are free of the K-injective `sorry`

The whole point of the `Plus` variants is that they do not rest on the sorried instance
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`. These guards
make that machine-checked, so a later refactor cannot quietly reintroduce the dependency.
-/

section AxiomChecks

open Etale

/-- info: 'AlgebraicGeometry.Etale.rightDerivedLowerStarPlus' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rightDerivedLowerStarPlus

/-- info: 'AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rightDerivedLowerShriekPlus

end AxiomChecks

end AlgebraicGeometry
