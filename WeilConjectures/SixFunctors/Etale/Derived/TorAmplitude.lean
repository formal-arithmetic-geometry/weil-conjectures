/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!

# Finite Tor amplitude and the small categories of the six-functor formalism

Let `A` be a monoidal Grothendieck abelian coefficient category and `X` a scheme, so that the
derived category `D(X_ét)` of `A`-valued étale sheaves on `X` carries the derived tensor product
`- ⊗ᴸ -` of `WeilConjectures.SixFunctors.Etale.Derived.Tensor` and the bounded constructible
subcategory `Dᵇc(X, A)` of `WeilConjectures.CategoryTheory.DerivedCategory.Constructible`.

This file cuts out the remaining *small* categories of the six-functor formalism: the objects of
`Dᵇc(X, A)` whose homology is concentrated in a fixed interval, and those of finite Tor amplitude.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.homologyConcentratedIn`: homology vanishing outside
  an interval `[a, b]`.
- `AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn`: Tor amplitude in `[a, b]`, tested by
  tensoring with an arbitrary étale sheaf.
- `AlgebraicGeometry.Etale.DerivedCategory.finiteTorAmplitude`: finite Tor amplitude.
- `AlgebraicGeometry.Etale.DerivedCategoryConstructibleIn`: the category `D_c^{[a,b]}(X, A)`.
- `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor`: the category `Dctf(X, A)` of bounded
  constructible complexes of finite Tor amplitude.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

namespace Etale.DerivedCategory

/-- An object of `D(X_ét)` has homology concentrated in `[a, b]` if its homology sheaves
vanish outside that interval. -/
def homologyConcentratedIn (a b : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  fun M ↦ ∀ n : ℤ, n < a ∨ b < n →
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf X.smallEtaleTopology A) n).obj M)

/-- An object `M` of `D(X_ét)` has *Tor amplitude in `[a, b]`* if for every étale sheaf `F` the
derived tensor product `M ⊗ᴸ F` has homology concentrated in `[a, b]`. -/
def torAmplitudeIn (a b : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  fun M ↦ ∀ F : Sheaf X.smallEtaleTopology A, homologyConcentratedIn A X a b
    (((-⊗ᴸ-(X)[A]).obj M).obj
      ((_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F))

/-- An object of `D(X_ét)` has *finite Tor amplitude* if it has Tor amplitude in some
interval `[a, b]`. -/
def finiteTorAmplitude :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  fun M ↦ ∃ a b : ℤ, torAmplitudeIn A X a b M

end Etale.DerivedCategory

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

namespace Etale

/-- Blueprint `sk-def-sf-categories`: Ambient categories and small subcategories.

The small category `D_c^{[a,b]}(X, A)` of bounded constructible complexes whose homology is
concentrated in the interval `[a, b]`, as a full subcategory of `D(X_ét)`. -/
noncomputable def DerivedCategoryConstructibleIn (a b : ℤ) : Type _ :=
  (Etale.DerivedCategory.boundedConstructible A X ⊓
    Etale.DerivedCategory.homologyConcentratedIn A X a b).FullSubcategory

noncomputable instance (a b : ℤ) : Category (DerivedCategoryConstructibleIn A X a b) :=
  inferInstanceAs <| Category (ObjectProperty.FullSubcategory _)

@[inherit_doc DerivedCategoryConstructibleIn]
scoped notation "D_c^[" a ", " b "](" X ", " A ")" =>
  Etale.DerivedCategoryConstructibleIn A X a b

/-- Blueprint `sk-def-sf-categories`: Ambient categories and small subcategories.

The small category `Dctf(X, A)` of bounded constructible complexes of finite Tor amplitude, as
a full subcategory of `D(X_ét)`. It is the category on which the six operations of the
`ℓ`-adic formalism are typed. -/
noncomputable def DerivedCategoryFiniteTor : Type _ :=
  (Etale.DerivedCategory.boundedConstructible A X ⊓
    Etale.DerivedCategory.finiteTorAmplitude A X).FullSubcategory

noncomputable instance : Category (DerivedCategoryFiniteTor A X) :=
  inferInstanceAs <| Category (ObjectProperty.FullSubcategory _)

/-- The inclusion of `Dctf(X, A)` into the derived category of étale sheaves. -/
noncomputable def DerivedCategoryFiniteTor.ι :
    DerivedCategoryFiniteTor A X ⥤ _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (Etale.DerivedCategory.boundedConstructible A X ⊓
    Etale.DerivedCategory.finiteTorAmplitude A X).ι

@[inherit_doc DerivedCategoryFiniteTor]
scoped notation "Dctf(" X ", " A ")" => Etale.DerivedCategoryFiniteTor A X

end Etale

end AlgebraicGeometry
