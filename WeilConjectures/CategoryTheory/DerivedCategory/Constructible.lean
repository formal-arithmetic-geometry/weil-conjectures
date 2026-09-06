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
public import WeilConjectures.ConstructibleSheaf.ProEtale

/-!

# The constructible bounded derived category

For a scheme `X` and a concrete abelian coefficient category `A`, this file defines the
subcategory `Dᵇc(X, A)` of the derived category of étale sheaves
`DerivedCategory (Sheaf X.smallEtaleTopology A)` consisting of the bounded complexes all of
whose homology sheaves are constructible
(`AlgebraicGeometry.Etale.IsConstructibleSheaf`), and its pro-étale counterpart inside
`DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)`
(`AlgebraicGeometry.ProEtale.IsConstructibleSheaf`). Boundedness refers in both cases to the
canonical t-structure `DerivedCategory.TStructure.t`.

Following the convention of the `SixFunctors` folder, the coefficient category `A` is a
concrete Grothendieck abelian category with `Hom`-types in the universe `u + 1`, one above
the universe `u` of the base schemes. Nothing beyond that is assumed:

- the left Kan extensions along base change, needed by the pullbacks `Etale.upperStar` and
  `ProEtale.upperStar` entering the constructibility conditions, come from the sorried
  instances `AlgebraicGeometry.Etale.hasLeftKanExtension_op_overPullback` and
  `AlgebraicGeometry.ProEtale.hasLeftKanExtension_op_overPullback` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`;
- the chosen localized categories `D(X_ét)` and `D(X_proét)` come from the instance
  `HasDerivedCategory.ofIsGrothendieckAbelian` of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory`, which installs
  `HasDerivedCategory.{u + 1}` on every sheaf category out of the Grothendieck abelian
  structure supplied by `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`. In
  particular the derived category is no longer taken at an auxiliary universe `w`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.constructibleHomology` and
  `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleHomology`: the property of an
  object of the derived category of étale, resp. pro-étale, sheaves that all its homology
  sheaves are constructible.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible` and
  `AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`: the property of being
  bounded with constructible homology.
- `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible` and
  `AlgebraicGeometry.ProEtale.DerivedCategoryBoundedConstructible`: the subcategories
  `Dᵇc(X, A)` cut out by the properties above, the constructible bounded derived categories
  of the `ℓ`-adic formalism. The notation `Dᵇc(X, A)` is scoped in
  `AlgebraicGeometry.Etale` and in `AlgebraicGeometry.ProEtale` respectively, so opening the
  namespace of the site one works on selects the intended one.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]

variable (X : Scheme.{u})

/-! ### The étale site -/

namespace Etale

section ConstructibleHomology

/-- An object of the derived category of étale sheaves has constructible homology if all
its homology sheaves are constructible. -/
noncomputable def DerivedCategory.constructibleHomology :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  fun M ↦ ∀ n : ℤ, Etale.IsConstructibleSheaf
    ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) n).obj M)

end ConstructibleHomology

section BoundedConstructible

/-- An object of the derived category of étale sheaves is bounded constructible if it is
bounded for the canonical t-structure and all its homology sheaves are constructible. -/
noncomputable def DerivedCategory.boundedConstructible :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  _root_.DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.constructibleHomology A X

/-- The constructible bounded derived category `Dᵇc(X, A)`, realized as the full
subcategory of bounded complexes with constructible homology in the derived category of
étale sheaves. -/
noncomputable def DerivedCategoryBoundedConstructible : Type _ :=
  (DerivedCategory.boundedConstructible A X).FullSubcategory

noncomputable instance : Category (DerivedCategoryBoundedConstructible A X) :=
  inferInstanceAs <|
    Category (DerivedCategory.boundedConstructible A X).FullSubcategory

/-- The inclusion of `Dᵇc(X, A)` into the derived category of étale sheaves. -/
noncomputable def DerivedCategoryBoundedConstructible.ι :
    DerivedCategoryBoundedConstructible A X ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (DerivedCategory.boundedConstructible A X).ι

@[inherit_doc DerivedCategoryBoundedConstructible]
scoped notation "Dᵇc(" X ", " A ")" =>
  DerivedCategoryBoundedConstructible A X

end BoundedConstructible

end Etale

/-! ### The pro-étale site -/

namespace ProEtale

section ConstructibleHomology

/-- An object of the derived category of pro-étale sheaves has constructible homology if
all its homology sheaves are constructible. -/
noncomputable def DerivedCategory.constructibleHomology :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  fun M ↦ ∀ n : ℤ, ProEtale.IsConstructibleSheaf
    ((DerivedCategory.homologyFunctor (Sheaf (Scheme.ProEt.topology X) A) n).obj M)

end ConstructibleHomology

section BoundedConstructible

/-- An object of the derived category of pro-étale sheaves is bounded constructible if it
is bounded for the canonical t-structure and all its homology sheaves are constructible. -/
noncomputable def DerivedCategory.boundedConstructible :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  _root_.DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.constructibleHomology A X

/-- The constructible bounded derived category `Dᵇc(X, A)` on the small pro-étale site,
realized as the full subcategory of bounded complexes with constructible homology in the
derived category of pro-étale sheaves. -/
noncomputable def DerivedCategoryBoundedConstructible : Type _ :=
  (DerivedCategory.boundedConstructible A X).FullSubcategory

noncomputable instance : Category (DerivedCategoryBoundedConstructible A X) :=
  inferInstanceAs <|
    Category (DerivedCategory.boundedConstructible A X).FullSubcategory

/-- The inclusion of `Dᵇc(X, A)` into the derived category of pro-étale sheaves. -/
noncomputable def DerivedCategoryBoundedConstructible.ι :
    DerivedCategoryBoundedConstructible A X ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (DerivedCategory.boundedConstructible A X).ι

@[inherit_doc DerivedCategoryBoundedConstructible]
scoped notation "Dᵇc(" X ", " A ")" =>
  DerivedCategoryBoundedConstructible A X

end BoundedConstructible

end ProEtale

end AlgebraicGeometry
