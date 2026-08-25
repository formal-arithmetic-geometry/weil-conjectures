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
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Derived pushforward and derived lower shriek on unbounded derived categories

The categories of `A`-valued étale sheaves are abelian, the pushforward
`g_* = Etale.lowerStar` along an arbitrary morphism `g` and the lower shriek
`f_! = Etale.lowerShriek` along a morphism `f` admitting a compactification are additive,
and this file records their total right derived functors
`Rg_* : D(Z_ét) ⥤ D(Y_ét)` and `Rf_! : D(X_ét) ⥤ D(Y_ét)` on the unbounded
derived categories, implemented via `CategoryTheory.Functor.rightDerivedFunctor`.

The sheaf categories are Grothendieck abelian (the sorried instance
`CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_smallGrothendieckTopology`
of `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`) whenever the
coefficient category `A` is a Grothendieck abelian category with `Hom`-types in the
universe `u + 1`, one above the universe `u` of the base schemes; this covers the
intended applications `A = Ab.{u + 1}` and `A = ModuleCat.{u + 1} Λ`. The chosen localized
categories are accordingly fixed once and for all by the instance
`AlgebraicGeometry.Scheme.hasDerivedCategory_sheaf_smallEtaleTopology` below, which
installs `HasDerivedCategory.{u + 1}` on every sheaf category via
`HasDerivedCategory.ofIsGrothendieckAbelian`; no auxiliary universe parameters appear.

The construction of the unbounded right derived functor requires the source abelian
category to have K-injective resolutions (`CategoryTheory.Abelian.HasKInjectiveResolutions`).
That Grothendieck abelian categories have K-injective resolutions is a theorem of Alonso
Tarrío–Jeremías López–Souto Salorio and Serpé; it is recorded as the sorried instance
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`.

On the *bounded below* derived categories the derived functor machinery needs no such
input: Mathlib's `CategoryTheory.Functor.rightDerivedFunctorPlus` requires only
`EnoughInjectives` on the source, and a Grothendieck abelian category has enough injectives
(`CategoryTheory.IsGrothendieckAbelian.enoughInjectives`). So `Etale.rightDerivedLowerStarPlus`
and `Etale.rightDerivedLowerShriekPlus` need no K-injective hypothesis. Note however that
the chosen `HasDerivedCategory.{u}` instance is itself built from the sorried K-injective
statement (through the local `u`-smallness of the derived category), so every derived
functor in this file — including the `Plus` variants — currently depends on `sorryAx`. Since
the `ℓ`-adic formalism only needs `Dᵇc`, the `Plus` variants are the versions to build on;
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility` identifies
the restriction of the unbounded functors to `DerivedCategory.Plus` with these.

The same asymmetry governs the composition isomorphism. The unbounded
`CategoryTheory.Functor.rightDerivedFunctorCompIso`
(`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`) takes
`HasKInjectiveResolutions` on both sheaf categories. Its bounded below counterpart
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp` asks only
that the first functor preserve injective objects, which for an étale `g` holds because
`g_*` is right
adjoint to the left exact `g^*`. That is what makes `Etale.rightDerivedLowerStarPlusComp`
below free of any K-injective hypothesis as well.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStar`: the total right derived functor
  `Rg_*` of the pushforward on unbounded derived categories of étale sheaves.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriek`: the total right derived functor
  `Rf_!` of the lower shriek on unbounded derived categories of étale sheaves.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus`: the same two functors on the
  bounded below derived categories, free of the K-injective hypothesis.
- `AlgebraicGeometry.Compactification.rightDerivedLowerShriek` and
  `AlgebraicGeometry.Compactification.rightDerivedLowerShriekPlus`: the derived lower
  shriek attached to a *given* compactification of `f`, rather than to the chosen one; for
  the chosen compactification they are definitionally the two functors above.
- `AlgebraicGeometry.Etale.preservesInjectiveObjects_lowerStar`: for étale `g`, the
  pushforward `g_*` preserves injective objects, being right adjoint to the left exact `g^*`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlusComp`: the composition isomorphism
  `R⁺(h₁)_* ⋙ R⁺(h₂)_* ≅ R⁺(h₁ ≫ h₂)_*` for `h₁` étale, again free of the K-injective
  hypothesis.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The chosen localized category `D(X_ét)` of `A`-valued étale sheaves, with `Hom`-types in
`Type (u + 1)`, obtained from the Grothendieck abelian structure of the sheaf category via
`HasDerivedCategory.ofIsGrothendieckAbelian`. -/
noncomputable instance Scheme.hasDerivedCategory_sheaf_smallEtaleTopology (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology A) :=
  HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _

section DerivedLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def Etale.rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctor

/-- The right derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_*` on the
*bounded below* derived categories of étale sheaves.

Unlike `Etale.rightDerivedLowerStar` this needs no K-injective hypothesis:
`Functor.rightDerivedFunctorPlus` needs only `EnoughInjectives` on the source, which
Mathlib provides for every Grothendieck abelian category. The only dependence on the
sorried `CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian` is
through the chosen `HasDerivedCategory.{u}` instance. -/
noncomputable def Etale.rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctorPlus

end DerivedLowerStar

section DerivedLowerShriek

variable {X Y : Scheme.{u}}

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f)

/-- The total right derived functor `D(X_ét) ⥤ D(Y_ét)` of the lower shriek `i_! ⋙ g_*`
attached to a *given* compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the unbounded
derived categories of étale sheaves.

The functor being derived is `AlgebraicGeometry.Compactification.lowerShriek` for
`P = Q = @Etale`, spelled out as the composition of the extension by zero along `c.i` with
the pushforward along `c.g`; in that form its additivity is found by instance search. For
`c = HasCompactification.compactification f` this is definitionally
`Etale.rightDerivedLowerShriek A f`. -/
noncomputable def Compactification.rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.openImmersionLowerShriek A c.i ⋙ Etale.lowerStar A c.g).rightDerivedFunctor

/-- The right derived functor `D⁺(X_ét) ⥤ D⁺(Y_ét)` of the lower shriek `i_! ⋙ g_*`
attached to a *given* compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, on the *bounded
below* derived categories of étale sheaves.

Unlike `Compactification.rightDerivedLowerShriek` this needs no K-injective
hypothesis; see `Etale.rightDerivedLowerStarPlus`. For
`c = HasCompactification.compactification f` this is definitionally
`Etale.rightDerivedLowerShriekPlus A f`. -/
noncomputable def Compactification.rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.openImmersionLowerShriek A c.i ⋙ Etale.lowerStar A c.g).rightDerivedFunctorPlus

end OfCompactification

variable (f : X ⟶ Y) [HasCompactification f]

/-- The total right derived functor `Rf_! : D(X_ét) ⥤ D(Y_ét)` of the lower shriek
`f_!` along a morphism `f : X ⟶ Y` admitting a compactification on the unbounded
derived categories of étale sheaves. -/
noncomputable def Etale.rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerShriek A f).rightDerivedFunctor

/-- The right derived functor `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` of the lower shriek `f_!` on the
*bounded below* derived categories of étale sheaves.

Unlike `Etale.rightDerivedLowerShriek` this needs no K-injective hypothesis;
see `Etale.rightDerivedLowerStarPlus`. -/
noncomputable def Etale.rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerShriek A f).rightDerivedFunctorPlus

lemma Etale.rightDerivedLowerShriek_eq : Etale.rightDerivedLowerShriek A f =
    (HasCompactification.compactification f).rightDerivedLowerShriek A := rfl

lemma Etale.rightDerivedLowerShriekPlus_eq : Etale.rightDerivedLowerShriekPlus A f =
    (HasCompactification.compactification f).rightDerivedLowerShriekPlus A := rfl

end DerivedLowerShriek

section Comp

/-- For an étale `g`, the pushforward `g_*` preserves injective objects, being right adjoint
to the pullback `g^*`, which is left exact and in particular preserves monomorphisms. This is
the hypothesis of `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`, and it is what
makes the composition isomorphism below available.

Only `g` étale is covered because that is the generality in which
`AlgebraicGeometry.Etale.preservesFiniteLimits_upperStar` fires by instance search; for a
general `g` the left exactness of `g^*` carries an extra hypothesis on the left Kan
extension along base change. -/
instance Etale.preservesInjectiveObjects_lowerStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) [Etale g] :
    (Etale.lowerStar A g).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction A g)

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) [Etale h₁]

/-- The composition isomorphism `R⁺(h₁)_* ⋙ R⁺(h₂)_* ≅ R⁺(h₁ ≫ h₂)_*` for the bounded below
derived pushforwards, for `h₁` étale. It is the general
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso'` applied to the underived
composition isomorphism `AlgebraicGeometry.Etale.lowerStarComp`.

There is no unbounded counterpart of this in the repository that avoids the K-injective
hypothesis: the unbounded composition theorem
`CategoryTheory.Functor.rightDerivedFunctorCompIso` needs `HasKInjectiveResolutions` on both
sheaf categories. -/
noncomputable def Etale.rightDerivedLowerStarPlusComp :
    Etale.rightDerivedLowerStarPlus A h₁ ⋙ Etale.rightDerivedLowerStarPlus A h₂ ≅
      Etale.rightDerivedLowerStarPlus A (h₁ ≫ h₂) :=
  Functor.rightDerivedFunctorPlusCompIso' (Etale.lowerStar A h₁) (Etale.lowerStar A h₂)
    (Etale.lowerStarComp A h₁ h₂)

end Comp

end AlgebraicGeometry
