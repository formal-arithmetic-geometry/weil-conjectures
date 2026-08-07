/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.DerivedFunctors.Plus

/-!

# Complexes of étale sheaves with constructible homology

For a scheme `X` and a concrete abelian coefficient category `A`, this file defines the
property `Etale.constructibleHomology` of an object of the bounded below derived category
`DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)` that all its homology sheaves are
constructible (`AlgebraicGeometry.Scheme.IsConstructibleSheaf`), and the full subcategory
`Etale.DerivedCategoryConstructiblePlus` of such complexes — the constructible bounded below derived
category `D^+_c(X_ét)`.

The derived pushforward `Rg_* = Etale.rightDerivedLowerStarPlus` and the derived lower
shriek `Rf_! = Etale.rightDerivedLowerShriekPlus` then restrict to these subcategories.
That they preserve constructibility of the homology sheaves is recorded as separate
lemmas, which are currently `sorry`: this belongs to the finiteness theorems of étale
cohomology and requires suitable hypotheses (torsion coefficients and finite type
morphisms).

## Main definitions

- `AlgebraicGeometry.Etale.constructibleHomology`: the property of an object of the
  bounded below derived category of étale sheaves that all its homology sheaves are
  constructible.
- `AlgebraicGeometry.Etale.DerivedCategoryConstructiblePlus`: the constructible bounded
  below derived category `D^+_c(X_ét)`, as the full subcategory of complexes with
  constructible homology.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus_constructibleHomology` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus_constructibleHomology`: the derived
  pushforward and the derived lower shriek preserve constructibility of the homology
  sheaves (currently `sorry`).
- `AlgebraicGeometry.Etale.rightDerivedLowerStarConstructible`: the restriction
  `Rg_* : D^+_c(Z_ét) ⥤ D^+_c(Y_ét)` of the derived pushforward.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekConstructible`: the restriction
  `Rf_! : D^+_c(X_ét) ⥤ D^+_c(Y_ét)` of the derived lower shriek.

-/

@[expose] public section

universe w w' v' u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{v'} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory A FA]
  [HasColimitsOfSize.{u, u} A]
  [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology A]
  [∀ (T S : Scheme.{u}) (f : T ⟶ S) (P : S.Etaleᵒᵖ ⥤ A),
    (MorphismProperty.Over.pullback @Etale ⊤ f).op.HasLeftKanExtension P]
  [∀ (T : Scheme.{u}) (U : T.Etale), HasWeakSheafify (T.smallEtaleTopology.over U) A]

section ConstructibleHomology

variable (X : Scheme.{u}) [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]

/-- An object of the bounded below derived category of étale sheaves has constructible
homology if all its homology sheaves are constructible. -/
noncomputable def Etale.constructibleHomology :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :=
  fun M ↦ ∀ n : ℤ, IsConstructibleSheaf
    ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) n).obj
      (DerivedCategory.Plus.ι.obj M))

/-- The constructible bounded below derived category `D^+_c(X_ét)`, realized as the full
subcategory of complexes with constructible homology in the bounded below derived
category of étale sheaves. -/
noncomputable abbrev Etale.DerivedCategoryConstructiblePlus : Type _ :=
  (Etale.constructibleHomology A X).FullSubcategory

/-- The inclusion of the constructible bounded below derived category into the bounded
below derived category. -/
noncomputable abbrev Etale.DerivedCategoryConstructiblePlus.ι :
    Etale.DerivedCategoryConstructiblePlus A X ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) :=
  (Etale.constructibleHomology A X).ι

end ConstructibleHomology

section ConstructibleLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
variable [HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The derived pushforward `Rg_*` sends complexes with constructible homology to
complexes with constructible homology. This is part of the finiteness theorems of étale
cohomology and requires suitable hypotheses (torsion coefficients and `g` of finite
type). -/
lemma Etale.rightDerivedLowerStarPlus_constructibleHomology
    (M : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A))
    (hM : Etale.constructibleHomology A Z M) :
    Etale.constructibleHomology A Y ((Etale.rightDerivedLowerStarPlus A g).obj M) :=
  sorry

/-- The restriction `Rg_* : D^+_c(Z_ét) ⥤ D^+_c(Y_ét)` of the derived pushforward along
an arbitrary morphism `g : Z ⟶ Y` to the constructible bounded below derived categories
of étale sheaves. -/
noncomputable def Etale.rightDerivedLowerStarConstructible :
    Etale.DerivedCategoryConstructiblePlus A Z ⥤ Etale.DerivedCategoryConstructiblePlus A Y :=
  ObjectProperty.lift _
    (Etale.DerivedCategoryConstructiblePlus.ι A Z ⋙ Etale.rightDerivedLowerStarPlus A g)
    (fun M => Etale.rightDerivedLowerStarPlus_constructibleHomology A g M.obj M.property)

end ConstructibleLowerStar

section ConstructibleLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The derived lower shriek `Rf_!` sends complexes with constructible homology to
complexes with constructible homology. This is part of the finiteness theorems of étale
cohomology and requires suitable hypotheses (torsion coefficients and `f` of finite
type). -/
lemma Etale.rightDerivedLowerShriekPlus_constructibleHomology
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    (hM : Etale.constructibleHomology A X M) :
    Etale.constructibleHomology A Y ((Etale.rightDerivedLowerShriekPlus A f).obj M) :=
  sorry

/-- The restriction `Rf_! : D^+_c(X_ét) ⥤ D^+_c(Y_ét)` of the derived lower shriek along
a morphism `f : X ⟶ Y` admitting a compactification to the constructible bounded below
derived categories of étale sheaves. -/
noncomputable def Etale.rightDerivedLowerShriekConstructible :
    Etale.DerivedCategoryConstructiblePlus A X ⥤ Etale.DerivedCategoryConstructiblePlus A Y :=
  ObjectProperty.lift _
    (Etale.DerivedCategoryConstructiblePlus.ι A X ⋙ Etale.rightDerivedLowerShriekPlus A f)
    (fun M => Etale.rightDerivedLowerShriekPlus_constructibleHomology A f M.obj M.property)

end ConstructibleLowerShriek

end AlgebraicGeometry
