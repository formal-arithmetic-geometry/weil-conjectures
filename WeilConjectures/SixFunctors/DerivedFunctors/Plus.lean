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
That the sheaf categories have enough injectives is recorded as a separate instance, which
is currently a `sorry`: it should be deduced from the sheaf categories being Grothendieck
abelian for suitable `A`.

## Main definitions

- `AlgebraicGeometry.Etale.enoughInjectives_sheaf`: the category of `A`-valued étale
  sheaves has enough injectives (currently a `sorry`).
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

variable (A : Type u') [Category.{v'} A] [Abelian A]
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology A]

/-- The category of `A`-valued sheaves on the small étale site has enough injectives.

TODO: this should be deduced from `IsGrothendieckAbelian` of the sheaf category, which
holds for suitable Grothendieck abelian coefficient categories `A`. -/
instance Etale.enoughInjectives_sheaf (X : Scheme.{u}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology A) :=
  sorry

section Additive

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The pushforward `g_*` on étale sheaves with values in an abelian category is additive:
it acts on morphisms by whiskering, which is compatible with the objectwise addition. -/
instance Etale.lowerStar_additive : (Etale.lowerStar A g).Additive where

/-- The restriction `j^*` along an open immersion on étale sheaves with values in an
abelian category is additive: it acts on morphisms by whiskering, which is compatible with
the objectwise addition. -/
instance Etale.openImmersionRestriction_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (Etale.openImmersionRestriction A j).Additive where

/-- The extension by zero `j_!` along an open immersion on étale sheaves with values in an
abelian category is additive, being left adjoint to the additive restriction `j^*`. -/
instance Etale.openImmersionLowerShriek_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (Etale.openImmersionLowerShriek A j).Additive :=
  (Etale.openImmersionLowerShriekAdjunction A j).left_adjoint_additive

/-- The lower shriek `f_!` on étale sheaves with values in an abelian category is additive,
being the composition of the extension by zero along the open immersion of the chosen
compactification with the pushforward along its proper structure morphism. -/
instance Etale.lowerShriek_additive {X : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (Etale.lowerShriek A f).Additive := by
  rw [Etale.lowerShriek_eq]
  infer_instance

end Additive

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
