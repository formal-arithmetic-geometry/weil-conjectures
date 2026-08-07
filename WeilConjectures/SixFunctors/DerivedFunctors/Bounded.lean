/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.DerivedFunctors.Plus

/-!

# Derived pushforward and derived lower shriek on bounded derived categories

For a general abelian category `C` with a chosen derived category, this file defines the
property `DerivedCategory.Plus.bounded` of an object of the bounded below derived category
`DerivedCategory.Plus C` of being bounded, and the bounded derived category
`DerivedCategory.Plus.Bounded C` as the full subcategory it determines. In contrast to
`DerivedCategory.Bounded`, this realizes the bounded derived category as a full
subcategory of `DerivedCategory.Plus C` instead of `DerivedCategory C`.

For étale sheaves with values in an abelian category, the derived pushforward
`Rg_* = Etale.rightDerivedLowerStarPlus` and the derived lower shriek
`Rf_! = Etale.rightDerivedLowerShriekPlus` then restrict to these bounded subcategories.
That they preserve boundedness is recorded as separate lemmas, which are currently
`sorry`: this requires finiteness of the cohomological dimension.

## Main definitions

- `DerivedCategory.Plus.bounded`: the property of an object of the bounded below derived
  category of being bounded.
- `DerivedCategory.Plus.Bounded`: the bounded derived category, as the full subcategory of
  bounded objects of the bounded below derived category.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus_bounded` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus_bounded`: the derived pushforward
  and the derived lower shriek preserve boundedness (currently `sorry`).
- `AlgebraicGeometry.Etale.rightDerivedLowerStarBounded`: the restriction
  `Rg_* : D^b(Z_ét) ⥤ D^b(Y_ét)` of the derived pushforward.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekBounded`: the restriction
  `Rf_! : D^b(X_ét) ⥤ D^b(Y_ét)` of the derived lower shriek.

-/

@[expose] public section

universe w w' v' u' v u

open CategoryTheory Limits Triangulated

namespace DerivedCategory.Plus

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An object of the bounded below derived category is bounded if its underlying object of
the derived category is bounded for the canonical t-structure. -/
noncomputable def bounded : ObjectProperty (DerivedCategory.Plus C) :=
  DerivedCategory.TStructure.t.bounded.inverseImage (Plus.ι (C := C))

/-- The bounded derived category, realized as the full subcategory of bounded objects of
the bounded below derived category. -/
noncomputable abbrev Bounded : Type _ :=
  (bounded C).FullSubcategory

/-- The inclusion of the bounded derived category into the bounded below derived
category. -/
noncomputable abbrev Bounded.ι : Bounded C ⥤ DerivedCategory.Plus C :=
  (bounded C).ι

end DerivedCategory.Plus

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]

section BoundedLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
variable [HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The derived pushforward `Rg_*` sends bounded objects to bounded objects. This requires
finiteness of the cohomological dimension of `g_*`. -/
lemma Etale.rightDerivedLowerStarPlus_bounded
    (M : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A))
    (hM : DerivedCategory.Plus.bounded _ M) :
    DerivedCategory.Plus.bounded _ ((Etale.rightDerivedLowerStarPlus A g).obj M) :=
  sorry

/-- The restriction `Rg_* : D^b(Z_ét) ⥤ D^b(Y_ét)` of the derived pushforward along an
arbitrary morphism `g : Z ⟶ Y` to the bounded derived categories of étale sheaves. -/
noncomputable def Etale.rightDerivedLowerStarBounded :
    DerivedCategory.Plus.Bounded (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus.Bounded (Sheaf Y.smallEtaleTopology A) :=
  ObjectProperty.lift _
    (DerivedCategory.Plus.Bounded.ι _ ⋙ Etale.rightDerivedLowerStarPlus A g)
    (fun M => Etale.rightDerivedLowerStarPlus_bounded A g M.obj M.property)

end BoundedLowerStar

section BoundedLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The derived lower shriek `Rf_!` sends bounded objects to bounded objects. This
requires finiteness of the cohomological dimension of the pushforward along the proper
structure morphism of the chosen compactification. -/
lemma Etale.rightDerivedLowerShriekPlus_bounded
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    (hM : DerivedCategory.Plus.bounded _ M) :
    DerivedCategory.Plus.bounded _ ((Etale.rightDerivedLowerShriekPlus A f).obj M) :=
  sorry

/-- The restriction `Rf_! : D^b(X_ét) ⥤ D^b(Y_ét)` of the derived lower shriek along a
morphism `f : X ⟶ Y` admitting a compactification to the bounded derived categories of
étale sheaves. -/
noncomputable def Etale.rightDerivedLowerShriekBounded :
    DerivedCategory.Plus.Bounded (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus.Bounded (Sheaf Y.smallEtaleTopology A) :=
  ObjectProperty.lift _
    (DerivedCategory.Plus.Bounded.ι _ ⋙ Etale.rightDerivedLowerShriekPlus A f)
    (fun M => Etale.rightDerivedLowerShriekPlus_bounded A f M.obj M.property)

end BoundedLowerShriek

end AlgebraicGeometry
