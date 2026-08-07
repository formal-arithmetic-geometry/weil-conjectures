/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.DerivedFunctors.Bounded
public import WeilConjectures.SixFunctors.DerivedFunctors.Constructible

/-!

# Bounded complexes of étale sheaves with constructible homology

For a scheme `X` and a concrete abelian coefficient category `A`, this file defines the
property `Etale.boundedConstructible` of an object of the bounded below derived category
`DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)` of being bounded with constructible
homology sheaves, as the infimum of `DerivedCategory.Plus.bounded` and
`Etale.constructibleHomology`, and the full subcategory
`Etale.DerivedCategoryBoundedConstructible` of such complexes — the constructible bounded
derived category `D^b_c(X_ét)` of the `ℓ`-adic formalism.

The derived pushforward `Rg_* = Etale.rightDerivedLowerStarPlus` and the derived lower
shriek `Rf_! = Etale.rightDerivedLowerShriekPlus` restrict to these subcategories; the
preservation of the property follows by combining the preservation of boundedness
(`WeilConjectures.SixFunctors.DerivedFunctors.Bounded`) with the preservation of
constructibility (`WeilConjectures.SixFunctors.DerivedFunctors.Constructible`).

## Main definitions

- `AlgebraicGeometry.Etale.boundedConstructible`: the property of an object of the
  bounded below derived category of étale sheaves of being bounded with constructible
  homology sheaves.
- `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible`: the constructible
  bounded derived category `D^b_c(X_ét)`, as the full subcategory of bounded complexes
  with constructible homology.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus_boundedConstructible` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus_boundedConstructible`: the derived
  pushforward and the derived lower shriek preserve this property.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarBoundedConstructible`: the restriction
  `Rg_* : D^b_c(Z_ét) ⥤ D^b_c(Y_ét)` of the derived pushforward.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekBoundedConstructible`: the restriction
  `Rf_! : D^b_c(X_ét) ⥤ D^b_c(Y_ét)` of the derived lower shriek.

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
  [HasColimitsOfSize.{u, u} A]
  [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology A]
  [∀ (T S : Scheme.{u}) (f : T ⟶ S) (P : S.Etaleᵒᵖ ⥤ A),
    (MorphismProperty.Over.pullback @Etale ⊤ f).op.HasLeftKanExtension P]
  [∀ (T : Scheme.{u}) (U : T.Etale), HasWeakSheafify (T.smallEtaleTopology.over U) A]

section BoundedConstructible

variable (X : Scheme.{u}) [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]

/-- An object of the bounded below derived category of étale sheaves is bounded
constructible if it is bounded and all its homology sheaves are constructible. -/
noncomputable def Etale.boundedConstructible :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :=
  DerivedCategory.Plus.bounded _ ⊓ Etale.constructibleHomology A X

/-- The constructible bounded derived category `D^b_c(X_ét)`, realized as the full
subcategory of bounded complexes with constructible homology in the bounded below
derived category of étale sheaves. -/
noncomputable abbrev Etale.DerivedCategoryBoundedConstructible : Type _ :=
  (Etale.boundedConstructible A X).FullSubcategory

/-- The inclusion of the constructible bounded derived category into the bounded below
derived category. -/
noncomputable abbrev Etale.DerivedCategoryBoundedConstructible.ι :
    Etale.DerivedCategoryBoundedConstructible A X ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) :=
  (Etale.boundedConstructible A X).ι

end BoundedConstructible

section BoundedConstructibleLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
variable [HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The derived pushforward `Rg_*` sends bounded complexes with constructible homology to
bounded complexes with constructible homology, by combining
`Etale.rightDerivedLowerStarPlus_bounded` and
`Etale.rightDerivedLowerStarPlus_constructibleHomology`. -/
lemma Etale.rightDerivedLowerStarPlus_boundedConstructible
    (M : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A))
    (hM : Etale.boundedConstructible A Z M) :
    Etale.boundedConstructible A Y ((Etale.rightDerivedLowerStarPlus A g).obj M) :=
  ⟨Etale.rightDerivedLowerStarPlus_bounded A g M hM.1,
    Etale.rightDerivedLowerStarPlus_constructibleHomology A g M hM.2⟩

/-- The restriction `Rg_* : D^b_c(Z_ét) ⥤ D^b_c(Y_ét)` of the derived pushforward along
an arbitrary morphism `g : Z ⟶ Y` to the constructible bounded derived categories of
étale sheaves. -/
noncomputable def Etale.rightDerivedLowerStarBoundedConstructible :
    Etale.DerivedCategoryBoundedConstructible A Z ⥤
      Etale.DerivedCategoryBoundedConstructible A Y :=
  ObjectProperty.lift _
    (Etale.DerivedCategoryBoundedConstructible.ι A Z ⋙ Etale.rightDerivedLowerStarPlus A g)
    (fun M => Etale.rightDerivedLowerStarPlus_boundedConstructible A g M.obj M.property)

end BoundedConstructibleLowerStar

section BoundedConstructibleLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The derived lower shriek `Rf_!` sends bounded complexes with constructible homology
to bounded complexes with constructible homology, by combining
`Etale.rightDerivedLowerShriekPlus_bounded` and
`Etale.rightDerivedLowerShriekPlus_constructibleHomology`. -/
lemma Etale.rightDerivedLowerShriekPlus_boundedConstructible
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    (hM : Etale.boundedConstructible A X M) :
    Etale.boundedConstructible A Y ((Etale.rightDerivedLowerShriekPlus A f).obj M) :=
  ⟨Etale.rightDerivedLowerShriekPlus_bounded A f M hM.1,
    Etale.rightDerivedLowerShriekPlus_constructibleHomology A f M hM.2⟩

/-- The restriction `Rf_! : D^b_c(X_ét) ⥤ D^b_c(Y_ét)` of the derived lower shriek along
a morphism `f : X ⟶ Y` admitting a compactification to the constructible bounded derived
categories of étale sheaves. -/
noncomputable def Etale.rightDerivedLowerShriekBoundedConstructible :
    Etale.DerivedCategoryBoundedConstructible A X ⥤
      Etale.DerivedCategoryBoundedConstructible A Y :=
  ObjectProperty.lift _
    (Etale.DerivedCategoryBoundedConstructible.ι A X ⋙ Etale.rightDerivedLowerShriekPlus A f)
    (fun M => Etale.rightDerivedLowerShriekPlus_boundedConstructible A f M.obj M.property)

end BoundedConstructibleLowerShriek

end AlgebraicGeometry
