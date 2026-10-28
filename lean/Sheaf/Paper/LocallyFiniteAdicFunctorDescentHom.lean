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

/-! # Hom descent for a normalized locally finite adic functor

Source: Bhatt--Scholze, Proposition 6.8.14(1),(2), using the existing condensed
filtered two-colimit; native realization proof steps 3 and 6.
(blueprint: lem-sf-locally-finite-adic-functor-descent-hom)
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

/-- The normalized native functor is fully faithful on derived Hom sets.

Proof in words: internal-module and section-module equivalences preserve the underlying
sheaves and exact sequences, so their derived Hom groups agree. On each finite field,
the finite realization is fully faithful. The common-field equation of the normalized
functor identifies all transition maps with the finite-stage maps. The Hom-surjectivity
and eventual-injectivity clauses of `constructibleCocone_isFilteredTwoColimit` therefore
identify the source Hom colimit with the ambient native Hom. Applying the same argument
to shifted targets gives every derived degree. The statement is independent of the
construction of the functor and of its essential image.
(blueprint: lem-sf-locally-finite-adic-functor-descent-hom)
-/
theorem normalizedFunctor_descent_hom
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] (D : NormalizedFunctor l X) :
    ∀ K L, Function.Bijective (D.J.map : (K ⟶ L) → (D.J.obj K ⟶ D.J.obj L)) := by
  sorry

end WeilConjectures.LocallyFiniteAdicRealization
