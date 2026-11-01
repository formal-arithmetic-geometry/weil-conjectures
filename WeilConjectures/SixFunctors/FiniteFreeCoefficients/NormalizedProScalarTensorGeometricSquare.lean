/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedProScalarTensorGeometricSquareFromFlat
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedProScalarTensorGeometricSquareOnFlat

/-! # The normalized pro-etale scalar and geometric tensor square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

end WeilConjectures.FiniteFreeCoefficients
