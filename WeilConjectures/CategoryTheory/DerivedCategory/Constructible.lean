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
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!

# The constructible bounded derived category of étale sheaves

For a scheme `X` and a concrete abelian coefficient category `A`, this file defines the
subcategory `Dᵇc(X, A)` of the derived category
`DerivedCategory (Sheaf X.smallEtaleTopology A)` of étale sheaves consisting of the
bounded complexes all of whose homology sheaves are constructible
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf`). Boundedness refers to the canonical
t-structure `DerivedCategory.TStructure.t`.

Following the convention of the `SixFunctors` folder, the coefficient category `A` is a
concrete Grothendieck abelian category with small-site sheafification
(`CategoryTheory.HasSmallSiteSheafify`) and `Hom`-types in the universe `u + 1`, one above
the universe `u` of the base schemes. Nothing beyond that is assumed:

- the left Kan extensions along base change, needed by the pullback `Etale.upperStar`
  entering `IsConstructibleSheaf`, come from the instance
  `CategoryTheory.MorphismProperty.Over.hasPointwiseLeftKanExtension_op_pullback` of
  `WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty`;
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
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_isTriangulated`: `Dᵇc(X, A)`
  is a triangulated subcategory of `D(X_ét)`, provided the constructible sheaves are closed
  under kernels, cokernels and extensions (`Etale.constructibleSheaf`, the property of being
  constructible as an `ObjectProperty`; the closure properties are the content of the blueprint
  theorem `thm:constructible-serre`, not yet formalised, and are taken as hypotheses). This is
  `DerivedCategory.homologyProperty_isTriangulated` of
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]

variable (X : Scheme.{u})

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

section Triangulated

/-- The property of being constructible, as a property of objects of the category of étale
sheaves; the closure of this property under kernels, cokernels and extensions is the blueprint
theorem `thm:constructible-serre`. -/
def Etale.constructibleSheaf : ObjectProperty (Sheaf X.smallEtaleTopology A) :=
  fun F ↦ IsConstructibleSheaf F

lemma Etale.constructibleSheaf_iff (F : Sheaf X.smallEtaleTopology A) :
    Etale.constructibleSheaf A X F ↔ IsConstructibleSheaf F :=
  Iff.rfl

instance : (Etale.constructibleSheaf A X).IsClosedUnderIsomorphisms where
  of_iso e h := by
    have := (Etale.constructibleSheaf_iff A X _).mp h
    exact IsConstructibleSheaf.of_iso e

instance [PreservesFiniteLimits (CategoryTheory.forget A)] :
    (Etale.constructibleSheaf A X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, IsConstructibleSheaf.of_isZero (isZero_zero _)⟩

/-- The constructible-homology property is the homology property of
`Etale.constructibleSheaf`. -/
lemma Etale.DerivedCategory.constructibleHomology_eq :
    Etale.DerivedCategory.constructibleHomology A X =
      _root_.DerivedCategory.homologyProperty (Etale.constructibleSheaf A X) :=
  rfl

variable [(Etale.constructibleSheaf A X).IsClosedUnderKernels]
  [(Etale.constructibleSheaf A X).IsClosedUnderCokernels]
  [(Etale.constructibleSheaf A X).IsClosedUnderExtensions]
  [PreservesFiniteLimits (CategoryTheory.forget A)]

/-- **Complexes with constructible homology form a triangulated subcategory**, provided the
constructible sheaves are closed under kernels, cokernels and extensions
(blueprint: `thm:constructible-serre`). (blueprint: `prop:constructible-derived-subcategory`) -/
instance Etale.DerivedCategory.constructibleHomology_isTriangulated :
    (Etale.DerivedCategory.constructibleHomology A X).IsTriangulated := by
  rw [Etale.DerivedCategory.constructibleHomology_eq]
  infer_instance

/-- **`Dᵇc(X, A)` is a triangulated subcategory of `D(X_ét)`**, provided the constructible
sheaves are closed under kernels, cokernels and extensions (blueprint:
`thm:constructible-serre`). (blueprint: `prop:constructible-derived-subcategory`) -/
instance Etale.DerivedCategory.boundedConstructible_isTriangulated :
    (Etale.DerivedCategory.boundedConstructible A X).IsTriangulated :=
  inferInstanceAs (DerivedCategory.TStructure.t.bounded ⊓
    Etale.DerivedCategory.constructibleHomology A X).IsTriangulated

end Triangulated

section ModuleCat

variable {Λ : Type (u + 1)} [Ring Λ]

/-- Constructible sheaves of `Λ`-modules are closed under kernels. -/
instance : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    have := (Etale.constructibleSheaf_iff _ _ _).mp hf.1
    have := (Etale.constructibleSheaf_iff _ _ _).mp hf.2
    exact (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
      ((Etale.constructibleSheaf_iff _ _ _).mpr (IsConstructibleSheaf.kernel f))

/-- Constructible sheaves of `Λ`-modules are closed under cokernels. -/
instance : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    have := (Etale.constructibleSheaf_iff _ _ _).mp hf.1
    have := (Etale.constructibleSheaf_iff _ _ _).mp hf.2
    exact (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      ((Etale.constructibleSheaf_iff _ _ _).mpr (IsConstructibleSheaf.cokernel f))

end ModuleCat

end AlgebraicGeometry
