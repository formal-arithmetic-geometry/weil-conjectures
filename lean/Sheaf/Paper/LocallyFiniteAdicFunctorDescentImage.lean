/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E6
-/
module

public import Sheaf.Paper.LocallyFiniteAdicNormalizedFunctorData
import Sheaf.Paper.ContinuousRationalDerivedRealization
import Sheaf.Paper.RationalCoefficientCategoryComparison
import Sheaf.Paper.CondensedFlatCoefficientCalculus
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.Paper.CondensedQbarLfpLocalTriviality
import Sheaf.Paper.CondensedQbarFunctionCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! # Essential image descent for a normalized locally finite adic functor

Source: Bhatt--Scholze, Proposition 6.8.14(1),(2), using the existing condensed
filtered two-colimit; native realization proof steps 3 and 7.
(blueprint: lem-sf-locally-finite-adic-functor-descent-image)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

/-- Bounded adic constructibility is exactly the essential image of the normalized functor.

Proof in words: identify bounded native constructible objects with the condensed module
category using the internal-module and section-module equivalences and the finite-field
local-freeness theorems. The object clause of
`constructibleCocone_isFilteredTwoColimit` descends a condensed object to a finite field.
Essential surjectivity of the finite-field realization lifts that model to a source object,
and tensor transitivity identifies its normalized image with the original object. In the
other direction, finite realization and scalar extension preserve bounded constructibility.
The argument includes the zero object and empty strata.
(blueprint: lem-sf-locally-finite-adic-functor-descent-image)
-/
theorem normalizedFunctor_descent_image
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] (D : NormalizedFunctor l X) :
    ∀ K, ProEtale.DerivedCategory.boundedAdicConstructible l X K ↔
      ∃ A, Nonempty (D.J.obj A ≅ K) := by
  sorry

end WeilConjectures.LocallyFiniteAdicRealization
