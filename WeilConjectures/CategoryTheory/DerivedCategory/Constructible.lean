/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!

# The constructible bounded derived category of étale sheaves

For a scheme `X` and a concrete abelian coefficient category `A`, this file defines the
subcategory `Dᵇc(X, A)` of the derived category
`DerivedCategory (Sheaf X.smallEtaleTopology A)` of étale sheaves consisting of the
bounded complexes all of whose homology sheaves are constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf`). Boundedness refers to the canonical
t-structure `DerivedCategory.TStructure.t`.

Assuming that the constructible sheaves form a weak Serre class, i.e. that they are closed
under kernels, cokernels and extensions (the blueprint theorem `thm:constructible-serre`,
whose extension part is not yet formalised and which is taken as the hypothesis
`[(AlgebraicGeometry.Etale.isConstructibleSheaf A X).IsWeakSerreClass]`), the category
`Dᵇc(X, A)` is triangulated: this is the specialisation of
`DerivedCategory.hasHomologyIn_isTriangulated` to the constructible sheaves.

Following the convention of the `SixFunctors` folder, the coefficient category `A` is a
concrete Grothendieck abelian category with `Hom`-types in the universe `u + 1`, one above
the universe `u` of the base schemes. Nothing beyond that is assumed:

- the left Kan extensions along base change, needed by the pullback `Etale.upperStar`
  entering `IsConstructibleSheaf`, come from the sorried instance
  `CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback` of
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
  `Dᵇc( X, A)` cut out by the property above, the constructible bounded derived
  category of the `ℓ`-adic formalism.

## Main results

- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_isTriangulated`: the
  bounded complexes with constructible homology form a triangulated subcategory of
  `D(X_ét)`.
- `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible.isTriangulated`: `Dᵇc(X, A)`
  is itself a triangulated category, with the structure induced from `D(X_ét)`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]

variable (X : Scheme.{u})

section ConstructibleHomology

/-- An object of the derived category of étale sheaves has constructible homology if all
its homology sheaves are constructible. -/
noncomputable def Etale.DerivedCategory.constructibleHomology :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  _root_.DerivedCategory.hasHomologyIn (Etale.isConstructibleSheaf A X)

/-- An object of the derived category of étale sheaves has constructible homology if and
only if all its homology sheaves are constructible. -/
lemma Etale.DerivedCategory.constructibleHomology_iff
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Etale.DerivedCategory.constructibleHomology A X M ↔ ∀ n : ℤ, IsConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) n).obj M) :=
  Iff.rfl

instance Etale.DerivedCategory.constructibleHomology_isClosedUnderIsomorphisms :
    (Etale.DerivedCategory.constructibleHomology A X).IsClosedUnderIsomorphisms :=
  inferInstanceAs (ObjectProperty.IsClosedUnderIsomorphisms
    (_root_.DerivedCategory.hasHomologyIn (Etale.isConstructibleSheaf A X)))

/-- **Complexes with constructible homology form a triangulated subcategory**, provided the
constructible sheaves form a weak Serre class
(blueprint: `prop:constructible-derived-subcategory`, with the weak Serre property of
`thm:constructible-serre` as a hypothesis). -/
instance Etale.DerivedCategory.constructibleHomology_isTriangulated
    [(Etale.isConstructibleSheaf A X).IsWeakSerreClass] :
    (Etale.DerivedCategory.constructibleHomology A X).IsTriangulated :=
  inferInstanceAs (ObjectProperty.IsTriangulated
    (_root_.DerivedCategory.hasHomologyIn (Etale.isConstructibleSheaf A X)))

end ConstructibleHomology

section BoundedConstructible

/-- An object of the derived category of étale sheaves is bounded constructible if it is
bounded for the canonical t-structure and all its homology sheaves are constructible. -/
noncomputable def Etale.DerivedCategory.boundedConstructible :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  DerivedCategory.TStructure.t.bounded ⊓ Etale.DerivedCategory.constructibleHomology A X

/-- **`Dᵇc(X, A)` is a triangulated subcategory of `D(X_ét)`**, provided the constructible
sheaves form a weak Serre class
(blueprint: `prop:constructible-derived-subcategory`, with the weak Serre property of
`thm:constructible-serre` as a hypothesis). -/
instance Etale.DerivedCategory.boundedConstructible_isTriangulated
    [(Etale.isConstructibleSheaf A X).IsWeakSerreClass] :
    (Etale.DerivedCategory.boundedConstructible A X).IsTriangulated :=
  inferInstanceAs (DerivedCategory.TStructure.t.bounded ⊓
    Etale.DerivedCategory.constructibleHomology A X).IsTriangulated

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

namespace Etale.DerivedCategoryBoundedConstructible

noncomputable instance preadditive : Preadditive (Dᵇc(X, A)) :=
  inferInstanceAs <|
    Preadditive (Etale.DerivedCategory.boundedConstructible A X).FullSubcategory

variable [(Etale.isConstructibleSheaf A X).IsWeakSerreClass]

noncomputable instance hasZeroObject : HasZeroObject (Dᵇc(X, A)) :=
  inferInstanceAs <|
    HasZeroObject (Etale.DerivedCategory.boundedConstructible A X).FullSubcategory

noncomputable instance hasShift : HasShift (Dᵇc(X, A)) ℤ :=
  inferInstanceAs <|
    HasShift (Etale.DerivedCategory.boundedConstructible A X).FullSubcategory ℤ

instance shiftFunctor_additive (n : ℤ) : (shiftFunctor (Dᵇc(X, A)) n).Additive :=
  inferInstanceAs <|
    (shiftFunctor (Etale.DerivedCategory.boundedConstructible A X).FullSubcategory n).Additive

noncomputable instance pretriangulated : Pretriangulated (Dᵇc(X, A)) :=
  inferInstanceAs <|
    Pretriangulated (Etale.DerivedCategory.boundedConstructible A X).FullSubcategory

/-- **`Dᵇc(X, A)` is a triangulated category**, provided the constructible sheaves form a
weak Serre class (blueprint: `prop:constructible-derived-subcategory`, with the weak Serre
property of `thm:constructible-serre` as a hypothesis). -/
instance isTriangulated : IsTriangulated (Dᵇc(X, A)) :=
  inferInstanceAs <|
    IsTriangulated (Etale.DerivedCategory.boundedConstructible A X).FullSubcategory

end Etale.DerivedCategoryBoundedConstructible

section ModuleCat

variable {Λ : Type (u + 1)} [Ring Λ]

/-- Constructible sheaves of `Λ`-modules are closed under kernels.
(blueprint: `thm:constructible-serre`) -/
instance Etale.isConstructibleSheaf_isClosedUnderKernels :
    ObjectProperty.IsClosedUnderKernels
      (Etale.isConstructibleSheaf (ModuleCat.{u + 1} Λ) X) where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    have := hf.1
    have := hf.2
    exact (Etale.isConstructibleSheaf (ModuleCat.{u + 1} Λ) X).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
      (IsConstructibleSheaf.kernel f)

/-- Constructible sheaves of `Λ`-modules are closed under cokernels.
(blueprint: `thm:constructible-serre`) -/
instance Etale.isConstructibleSheaf_isClosedUnderCokernels :
    ObjectProperty.IsClosedUnderCokernels
      (Etale.isConstructibleSheaf (ModuleCat.{u + 1} Λ) X) where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    have := hf.1
    have := hf.2
    exact (Etale.isConstructibleSheaf (ModuleCat.{u + 1} Λ) X).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      (IsConstructibleSheaf.cokernel f)

end ModuleCat

end AlgebraicGeometry
