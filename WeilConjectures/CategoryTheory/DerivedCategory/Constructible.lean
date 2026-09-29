/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.ConstructibleSheaf.Etale

/-!

# The constructible bounded derived category of étale sheaves

For a scheme `X` and a ring `Λ`, this file defines the subcategory `Dᵇc(X, Λ)` of the
derived category `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat Λ))` of étale
sheaves of `Λ`-modules consisting of the
bounded complexes all of whose homology sheaves are constructible
(`AlgebraicGeometry.Etale.IsConstructibleSheaf`). Boundedness refers to the canonical
t-structure `DerivedCategory.TStructure.t`.

Following the convention of the `SixFunctors` folder, the coefficient category is
`ModuleCat.{u + 1} Λ` for a ring `Λ : Type (u + 1)`, a Grothendieck abelian category with
`Hom`-types in the universe `u + 1`, one above
the universe `u` of the base schemes. Nothing beyond that is assumed:

- the left Kan extensions along base change, needed by the pullback `Etale.upperStar`
  entering `IsConstructibleSheaf`, come from the sorried instance
  `AlgebraicGeometry.Etale.hasLeftKanExtension_op_overPullback` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`;
- the chosen localized category `D(X_ét)` comes from the instance
  `HasDerivedCategory.ofIsGrothendieckAbelian` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`, which installs
  `HasDerivedCategory.{u + 1}` on every sheaf category out of the Grothendieck abelian
  structure supplied by `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`. In
  particular the derived category is no longer taken at an auxiliary universe `w`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.constructibleHomology`: the property of an
  object of the derived category of étale sheaves that all its homology sheaves are
  constructible.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible`: the property of being
  bounded with constructible homology.
- `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible`: the subcategory
  `Dᵇc( X, Λ)` cut out by the property above, the constructible bounded derived
  category of the `ℓ`-adic formalism.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [Ring Λ]

variable (X : Scheme.{u})

section ConstructibleHomology

/-- An object of the derived category of étale sheaves has constructible homology if all
its homology sheaves are constructible. -/
noncomputable def Etale.DerivedCategory.constructibleHomology :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun M ↦ ∀ n : ℤ, Etale.IsConstructibleSheaf Λ
    ((DerivedCategory.homologyFunctor _ n).obj M)

end ConstructibleHomology

section BoundedConstructible

/-- An object of the derived category of étale sheaves is bounded constructible if it is
bounded for the canonical t-structure and all its homology sheaves are constructible. -/
noncomputable def Etale.DerivedCategory.boundedConstructible :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  DerivedCategory.TStructure.t.bounded ⊓ Etale.DerivedCategory.constructibleHomology Λ X

/-- The constructible bounded derived category `Dᵇc( X, Λ)`, realized as the full
subcategory of bounded complexes with constructible homology in the derived category of
étale sheaves. -/
noncomputable def Etale.DerivedCategoryBoundedConstructible : Type _ :=
  (Etale.DerivedCategory.boundedConstructible Λ X).FullSubcategory

noncomputable instance : Category (Etale.DerivedCategoryBoundedConstructible Λ X) :=
  inferInstanceAs <|
    Category (Etale.DerivedCategory.boundedConstructible Λ X).FullSubcategory

/-- The inclusion of `Dᵇc(X, Λ)` into the derived category of étale sheaves. -/
noncomputable def Etale.DerivedCategoryBoundedConstructible.ι :
    Etale.DerivedCategoryBoundedConstructible Λ X ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (Etale.DerivedCategory.boundedConstructible Λ X).ι

@[inherit_doc Etale.DerivedCategoryBoundedConstructible]
scoped notation "Dᵇc(" X ", " Λ ")" =>
  Etale.DerivedCategoryBoundedConstructible Λ X

end BoundedConstructible

end AlgebraicGeometry
