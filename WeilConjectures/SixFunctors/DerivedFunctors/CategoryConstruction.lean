/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.ConstructibleSheaf.Defs

/-!

# Subcategories of the derived category of étale sheaves

For a scheme `X` and a concrete abelian coefficient category `A`, this file introduces the
subcategories of the derived category `DerivedCategory (Sheaf X.smallEtaleTopology A)` of
étale sheaves that the `ℓ`-adic formalism is built on.

All of them are full subcategories of `DerivedCategory C` itself, cut out by an
`ObjectProperty`. The boundedness conditions are the ones attached to the canonical
t-structure `DerivedCategory.TStructure.t`, so the bounded above and the bounded derived
categories are mathlib's `DerivedCategory.Minus` and `DerivedCategory.Bounded`, which are
the full subcategories of `DerivedCategory C` on `t.minus` resp. `t.bounded`; there is
nothing to add for them here. What this file adds is the property
`Etale.constructibleHomology` of an object of the derived category that all its homology
sheaves are constructible (`AlgebraicGeometry.Scheme.IsConstructibleSheaf`), and the
constructible bounded derived category `D^b_c(X_ét)` it cuts out in conjunction with
boundedness.

Note that all of these are subcategories of `DerivedCategory C`, not of the bounded below
derived category `DerivedCategory.Plus C`.

## Main definitions

- `AlgebraicGeometry.Etale.constructibleHomology`: the property of an object of the
  derived category of étale sheaves that all its homology sheaves are constructible.
- `AlgebraicGeometry.Etale.boundedConstructible` and
  `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible`: the property of being
  bounded with constructible homology, and the corresponding subcategory `D^b_c(X_ét)`,
  the constructible bounded derived category of the `ℓ`-adic formalism.

-/

@[expose] public section

universe w u' u

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
  [∀ (T S : Scheme.{u}) (f : T ⟶ S) (P : S.Etaleᵒᵖ ⥤ A),
    (MorphismProperty.Over.pullback @Etale ⊤ f).op.HasLeftKanExtension P]
  [∀ (T : Scheme.{u}) (U : T.Etale), HasWeakSheafify (T.smallEtaleTopology.over U) A]

variable (X : Scheme.{u}) [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]

section ConstructibleHomology

/-- An object of the derived category of étale sheaves has constructible homology if all
its homology sheaves are constructible. -/
noncomputable def Etale.constructibleHomology :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  fun M ↦ ∀ n : ℤ, IsConstructibleSheaf
    ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) n).obj M)

end ConstructibleHomology

section BoundedConstructible

/-- An object of the derived category of étale sheaves is bounded constructible if it is
bounded for the canonical t-structure and all its homology sheaves are constructible. -/
noncomputable def Etale.boundedConstructible :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  DerivedCategory.TStructure.t.bounded ⊓ Etale.constructibleHomology A X

/-- The constructible bounded derived category `D^b_c(X_ét)`, realized as the full
subcategory of bounded complexes with constructible homology in the derived category of
étale sheaves. -/
noncomputable abbrev Etale.DerivedCategoryBoundedConstructible : Type _ :=
  (Etale.boundedConstructible A X).FullSubcategory

/-- The inclusion of `D^b_c(X_ét)` into the derived category of étale sheaves. -/
noncomputable abbrev Etale.DerivedCategoryBoundedConstructible.ι :
    Etale.DerivedCategoryBoundedConstructible A X ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (Etale.boundedConstructible A X).ι

end BoundedConstructible

end AlgebraicGeometry
