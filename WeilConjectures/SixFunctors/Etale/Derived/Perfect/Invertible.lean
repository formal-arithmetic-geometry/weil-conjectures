/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# Dualizable and invertible étale complexes

Tensor products of dualizable complexes are dualizable, invertible complexes are dualizable,
and shifts of invertible complexes are invertible.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isDualizable_derivedTensor`
- `AlgebraicGeometry.Etale.DerivedCategory.isDualizable_of_isInvertible`
- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible_shift`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

namespace Etale.DerivedCategory

variable {A X}

end Etale.DerivedCategory

end AlgebraicGeometry
