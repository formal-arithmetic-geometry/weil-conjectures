/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Hom

/-!
# The monoidal structure of `D(X_ét)` in terms of the derived tensor product

The derived tensor product `AlgebraicGeometry.Etale.derivedTensor` is the tensor product of
the monoidal structure on `D(X_ét)`. This file restates the associator, the left unitor,
invertibility, perfectness of pairings and the linearity of `K ⊗ᴸ -` and `- ⊗ᴸ K` in terms of
`derivedTensor`, for a general coefficient category `A`.

## Implementation notes

Statements about a concrete coefficient category such as `ModuleCat Λ` should use these
declarations rather than `α_`, `λ_`, `CategoryTheory.IsInvertible` or
`CategoryTheory.MonoidalClosed.IsPerfectPairing` directly. There, the monoidal instance on
`D(X_ét)` found by instance search is a different term from the one inside `derivedTensor`.
The two are equal, but the kernel does not decide this in reasonable time: already
`𝟙 (K ⊗ M)`, or `rfl : (K ⊗ᴸ M) = K ⊗ M`, hits a deterministic timeout. Over a general `A`
the comparison is immediate, and specialising the declarations below to `A = ModuleCat Λ`
involves no comparison at all.

## Main definitions

- `AlgebraicGeometry.Etale.derivedTensorAssociator`: `(K ⊗ᴸ M) ⊗ᴸ N ≅ K ⊗ᴸ (M ⊗ᴸ N)`.
- `AlgebraicGeometry.Etale.derivedTensorLeftUnitor`: `Λ_X ⊗ᴸ K ≅ K`.
- `AlgebraicGeometry.Etale.IsPerfectPairing`: perfectness of a pairing `C ⊗ᴸ D ⟶ Λ_X`.

## Main statements

- `AlgebraicGeometry.Etale.isPerfectPairing_iff`,
  `AlgebraicGeometry.Etale.isInvertible_iff_exists_derivedTensor`: the comparison with
  `CategoryTheory.MonoidalClosed.IsPerfectPairing` and `CategoryTheory.IsInvertible`.
- `AlgebraicGeometry.Etale.linear_derivedTensor_obj`,
  `AlgebraicGeometry.Etale.linear_derivedTensor_flip_obj`: the derived tensor product is
  linear in each variable, by `DerivedCategory.monoidalLinear`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

namespace Etale

/-- The associator `(K ⊗ᴸ M) ⊗ᴸ N ≅ K ⊗ᴸ (M ⊗ᴸ N)` of the derived tensor product. -/
noncomputable def derivedTensorAssociator
    (K M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj (((derivedTensor A X).obj K).obj M)).obj N ≅
      ((derivedTensor A X).obj K).obj (((derivedTensor A X).obj M).obj N) :=
  α_ K M N

/-- The left unitor `Λ_X ⊗ᴸ K ≅ K` of the derived tensor product, `Λ_X = 𝟙_` being the
constant complex. -/
noncomputable def derivedTensorLeftUnitor
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj (𝟙_ _)).obj K ≅ K :=
  λ_ K

variable {A X}

/-- A pairing `b : C ⊗ᴸ D ⟶ Λ_X` in `D(X_ét)` is *perfect* if its tensor–internal-hom adjoint
`D ⟶ RHom(C, Λ_X)` is an isomorphism.

This is `CategoryTheory.MonoidalClosed.IsPerfectPairing` (see
`AlgebraicGeometry.Etale.isPerfectPairing_iff`), stated for a pairing whose source is written
with `AlgebraicGeometry.Etale.derivedTensor`. The only difference is the term used to
elaborate `C ⊗ D`: here it is `derivedTensor`, so that the definition can be applied at
`A = ModuleCat Λ` to pairings built from `derivedTensor`, without the kernel having to
compare the two tensor products there (see the implementation notes). -/
def IsPerfectPairing {C D : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (b : ((derivedTensor A X).obj C).obj D ⟶ 𝟙_ _) : Prop :=
  MonoidalClosed.IsPerfectPairing (C := _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) b

lemma isPerfectPairing_iff {C D : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (b : ((derivedTensor A X).obj C).obj D ⟶ 𝟙_ _) :
    IsPerfectPairing b ↔
      MonoidalClosed.IsPerfectPairing (C := _root_.DerivedCategory
        (Sheaf X.smallEtaleTopology A)) b :=
  Iff.rfl

/-- An object `K` of `D(X_ét)` is invertible if and only if `K ⊗ᴸ M ≅ Λ_X` for some `M`. -/
lemma isInvertible_iff_exists_derivedTensor
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsInvertible K ↔ ∃ M, Nonempty (((derivedTensor A X).obj K).obj M ≅ 𝟙_ _) :=
  Iff.rfl

variable (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))

/-- Tensoring with a fixed complex, `M ↦ K ⊗ᴸ M`, is additive. -/
instance additive_derivedTensor_obj : ((derivedTensor A X).obj K).Additive :=
  inferInstanceAs (tensorLeft K).Additive

/-- Tensoring with a fixed complex, `M ↦ M ⊗ᴸ K`, is additive. -/
instance additive_derivedTensor_flip_obj : ((derivedTensor A X).flip.obj K).Additive :=
  inferInstanceAs (tensorRight K).Additive

variable (R : Type*) [Ring R] [Linear R A] [MonoidalLinear R A]

/-- If the tensor product of `A` is `R`-linear, tensoring with a fixed complex,
`M ↦ K ⊗ᴸ M`, is `R`-linear. -/
instance linear_derivedTensor_obj : ((derivedTensor A X).obj K).Linear R :=
  inferInstanceAs ((tensorLeft K).Linear R)

/-- If the tensor product of `A` is `R`-linear, tensoring with a fixed complex,
`M ↦ M ⊗ᴸ K`, is `R`-linear. -/
instance linear_derivedTensor_flip_obj : ((derivedTensor A X).flip.obj K).Linear R :=
  inferInstanceAs ((tensorRight K).Linear R)

end Etale

end AlgebraicGeometry
