/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Constant

/-!
# The monoidal comparison of constant complexes

The monoidal comparison of the derived constant sheaf functor `c_W` is the tensor comparison of
the induced functor on derived categories
(`AlgebraicGeometry.Etale.derivedConstantSheafTensorComparison_eq`). Kept in its own file because
the kernel needs a lot of memory to check it.
-/


@[expose] public section

universe u u'

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Coefficients

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (W : Scheme.{u})
  [(constantSheaf W.smallEtaleTopology A).PreservesFlat]


/-- The monoidal comparison of constant complexes is the tensor comparison
`CategoryTheory.Functor.mapDerivedCategoryTensorComparison` of the functor induced by the
constant sheaf functor. -/
lemma derivedConstantSheafTensorComparison_eq (M N : DerivedCategory A) :
    derivedConstantSheafTensorComparison A W M N =
      ((Functor.mapDerivedCategoryTensorComparison
        (constantSheaf W.smallEtaleTopology A)).app M).app N := by
  rw [Functor.mapDerivedCategoryTensorComparison_app_app]
  rfl


end Coefficients

end Etale

end AlgebraicGeometry
