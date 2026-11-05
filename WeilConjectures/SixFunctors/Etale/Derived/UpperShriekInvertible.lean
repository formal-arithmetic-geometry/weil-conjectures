/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Tensor products of invertible objects

The derived tensor product of two `⊗`-invertible objects of `D(X_ét)` is invertible. Together
with the stability of invertible objects under derived pullback
(`AlgebraicGeometry.Etale.DerivedCategory.isInvertible.leftDerivedUpperStar`), this is used in
the composition law for cohomologically smooth morphisms (`lem-pur-co-smooth-composition`).

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_derivedTensor`
- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible.derivedTensor`
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

namespace Etale

section General

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

end General

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

end Etale

end AlgebraicGeometry
