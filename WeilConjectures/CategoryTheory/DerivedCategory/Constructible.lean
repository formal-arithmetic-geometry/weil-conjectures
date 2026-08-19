/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Derived

/-!

# The constructible bounded derived category of étale sheaves

For a scheme `X` and a concrete abelian coefficient category `A`, this file defines the
subcategory `Dᵇc(X, A)` of the derived category
`DerivedCategory (Sheaf X.smallEtaleTopology A)` of étale sheaves consisting of the
bounded complexes all of whose homology sheaves are constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf`). Boundedness refers to the canonical
t-structure `DerivedCategory.TStructure.t`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.constructibleHomology`: the property of an
  object of the derived category of étale sheaves that all its homology sheaves are
  constructible.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible`: the property of being
  bounded with constructible homology.
- `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible`: the subcategory
  `Dᵇc( X, A)` cut out by the property above, the constructible bounded derived
  category of the `ℓ`-adic formalism.

-/

@[expose] public section

universe u' u

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
  [∀ (T : Scheme.{u}) (U : T.Etale), HasWeakSheafify (T.smallEtaleTopology.over U) A]

variable (X : Scheme.{u})
  [∀ (T : Scheme.{u}) (f : T ⟶ X) (P : X.Etaleᵒᵖ ⥤ A),
    (MorphismProperty.Over.pullback @Etale ⊤ f).op.HasLeftKanExtension P]

section ConstructibleHomology

/-- An object of the derived category of étale sheaves has constructible homology if all
its homology sheaves are constructible. -/
noncomputable def Etale.DerivedCategory.constructibleHomology :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  fun M ↦ ∀ n : ℤ, IsConstructibleSheaf
    ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) n).obj M)

end ConstructibleHomology

section BoundedConstructible

/-- An object of the derived category of étale sheaves is bounded constructible if it is
bounded for the canonical t-structure and all its homology sheaves are constructible. -/
noncomputable def Etale.DerivedCategory.boundedConstructible :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  DerivedCategory.TStructure.t.bounded ⊓ Etale.DerivedCategory.constructibleHomology A X

/-- The constructible bounded derived category `Dᵇc( X, A)`, realized as the full
subcategory of bounded complexes with constructible homology in the derived category of
étale sheaves. -/
noncomputable def Etale.DerivedCategoryBoundedConstructible : Type _ :=
  (Etale.DerivedCategory.boundedConstructible A X).FullSubcategory

noncomputable instance : Category (Etale.DerivedCategoryBoundedConstructible A X) :=
  inferInstanceAs <|
    Category (Etale.DerivedCategory.boundedConstructible A X).FullSubcategory

/-- The inclusion of `Dᵇc(X, A)` into the derived category of étale sheaves. -/
noncomputable def Etale.DerivedCategoryBoundedConstructible.ι :
    Etale.DerivedCategoryBoundedConstructible A X ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (Etale.DerivedCategory.boundedConstructible A X).ι

@[inherit_doc Etale.DerivedCategoryBoundedConstructible]
scoped notation "Dᵇc(" X ", " A ")" =>
  Etale.DerivedCategoryBoundedConstructible A X

end BoundedConstructible

end AlgebraicGeometry
