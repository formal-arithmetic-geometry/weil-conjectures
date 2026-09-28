/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!

# Finite Tor amplitude and the small category `Dctf(X, A)`

Let `A` be a monoidal Grothendieck abelian coefficient category and `X` a scheme, so that the
derived category `D(X_ét)` of `A`-valued étale sheaves on `X` carries the derived tensor product
`- ⊗ᴸ -` of `WeilConjectures.SixFunctors.Etale.Derived.Tensor` and the bounded constructible
subcategory `Dᵇc(X, A)` of `WeilConjectures.CategoryTheory.DerivedCategory.Constructible`.

This file cuts out the *small* category on which the six operations of the `ℓ`-adic formalism
are typed: the bounded constructible complexes of finite Tor amplitude.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn`: Tor amplitude in `[a, b]`, tested by
  tensoring with an arbitrary étale sheaf.
- `AlgebraicGeometry.Etale.DerivedCategory.finiteTorAmplitude`: finite Tor amplitude.
- `AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor`: membership in `Dctf(X, A)`,
  as an object property.
- `AlgebraicGeometry.Etale.DerivedCategory.constructibleTorAmplitudeIn`: membership in
  `D_c^[a, b](X, A)` together with Tor amplitude in `[a, b]`.
- `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor`: the category `Dctf(X, A)` of bounded
  constructible complexes of finite Tor amplitude.

## Implementation notes

Homology concentration in an interval is not an étale notion and is not defined here: it is
`DerivedCategory.homologyConcentratedIn` of
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`, phrased through the
canonical t-structure so that the t-structure API applies to it.

The blueprint's second small category `D_c^[a, b](X, A)` is not realised as a category: the
statements that speak about it — those of
`WeilConjectures.SixFunctors.Etale.Derived.Stability` — always pair it with a Tor amplitude
bound, and use the object property
`AlgebraicGeometry.Etale.DerivedCategory.constructibleTorAmplitudeIn`.

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

/-- An object `M` of `D(X_ét)` has *Tor amplitude in `[a, b]`* if for every étale sheaf `F` the
derived tensor product `M ⊗ᴸ F` has homology concentrated in `[a, b]`. -/
def torAmplitudeIn (a b : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  fun M ↦ ∀ F : Sheaf X.smallEtaleTopology A,
    _root_.DerivedCategory.homologyConcentratedIn a b
      (((-⊗ᴸ-(X)[A]).obj M).obj
        ((_root_.DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0).obj F))

variable {A X}

/-- Widening the interval preserves Tor amplitude. -/
lemma torAmplitudeIn.mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hM : torAmplitudeIn A X a b M) : torAmplitudeIn A X a' b' M :=
  fun F ↦ (hM F).mono ha hb

variable (A X)

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

/-- Membership in `Dctf(X, A)` as an object property of `D(X_ét)`: bounded constructible and of
finite Tor amplitude. -/
noncomputable def DerivedCategory.constructibleFiniteTor :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  Etale.DerivedCategory.boundedConstructible A X ⊓ Etale.DerivedCategory.finiteTorAmplitude A X

omit [HasSmallSiteSheafify A] in
lemma DerivedCategory.constructibleFiniteTor_iff
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    DerivedCategory.constructibleFiniteTor A X K ↔
      Etale.DerivedCategory.boundedConstructible A X K ∧
        Etale.DerivedCategory.finiteTorAmplitude A X K :=
  Iff.rfl

/-- Membership in the blueprint's `D_c^[a, b](X, A)` together with Tor amplitude in the same
interval, as an object property of `D(X_ét)`: bounded constructible, homology concentrated in
`[a, b]`, and Tor amplitude in `[a, b]`. -/
noncomputable def DerivedCategory.constructibleTorAmplitudeIn (a b : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  Etale.DerivedCategory.boundedConstructible A X ⊓
    _root_.DerivedCategory.homologyConcentratedIn a b ⊓
    Etale.DerivedCategory.torAmplitudeIn A X a b

omit [HasSmallSiteSheafify A] in
lemma DerivedCategory.constructibleTorAmplitudeIn_iff (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    DerivedCategory.constructibleTorAmplitudeIn A X a b K ↔
      (Etale.DerivedCategory.boundedConstructible A X K ∧
          _root_.DerivedCategory.homologyConcentratedIn a b K) ∧
        Etale.DerivedCategory.torAmplitudeIn A X a b K :=
  Iff.rfl

variable {A X}

omit [HasSmallSiteSheafify A] in
/-- An object of `D(X_ét)` lies in `Dctf(X, A)` exactly when, for some interval `[a, b]`, it
is bounded constructible with homology concentrated in `[a, b]` and Tor amplitude in
`[a, b]`. -/
lemma DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (∃ a b : ℤ, DerivedCategory.constructibleTorAmplitudeIn A X a b K) ↔
      DerivedCategory.constructibleFiniteTor A X K := by
  constructor
  · rintro ⟨a, b, ⟨hbc, -⟩, hta⟩
    exact ⟨hbc, a, b, hta⟩
  · rintro ⟨hbc, a, b, hta⟩
    obtain ⟨c, d, hcd⟩ :=
      (_root_.DerivedCategory.exists_homologyConcentratedIn_iff_bounded K).2 hbc.1
    exact ⟨min a c, max b d, ⟨hbc, hcd.mono (min_le_right _ _) (le_max_right _ _)⟩,
      hta.mono (min_le_left _ _) (le_max_left _ _)⟩

variable (A X)

/-- Blueprint `sk-def-sf-categories`: Ambient categories and small subcategories.

The small category `Dctf(X, A)` of bounded constructible complexes of finite Tor amplitude, as
a full subcategory of `D(X_ét)`. It is the category on which the six operations of the
`ℓ`-adic formalism are typed. -/
noncomputable def DerivedCategoryFiniteTor : Type _ :=
  (DerivedCategory.constructibleFiniteTor A X).FullSubcategory

noncomputable instance : Category (DerivedCategoryFiniteTor A X) :=
  inferInstanceAs <| Category (ObjectProperty.FullSubcategory _)

/-- The inclusion of `Dctf(X, A)` into the derived category of étale sheaves. -/
noncomputable def DerivedCategoryFiniteTor.ι :
    DerivedCategoryFiniteTor A X ⥤ _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (DerivedCategory.constructibleFiniteTor A X).ι

@[inherit_doc DerivedCategoryFiniteTor]
scoped notation "Dctf(" X ", " A ")" => Etale.DerivedCategoryFiniteTor A X

end Etale

end AlgebraicGeometry
