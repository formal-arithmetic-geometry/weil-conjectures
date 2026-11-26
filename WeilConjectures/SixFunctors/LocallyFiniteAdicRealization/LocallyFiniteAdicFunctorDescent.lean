/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicNormalizedFunctorData
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicFunctorDescentHom
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicFunctorDescentImage

/-! # LocallyFiniteAdicFunctorDescent

Object and derived-Hom descent for a normalized locally finite adic functor.

## Implementation details

The restriction of the functor to every finite stage is the finite-field realization
followed by native scalar extension. Derived Homs are compared through the Hom colimit of
the condensed system, using the Hom-surjectivity and eventual-injectivity clauses of
`constructibleCocone_isFilteredTwoColimit`; objects are descended by the object clause of
the same two-colimit theorem.

## References

* [Bhatt--Scholze, Section 6.8, Proposition 6.8.14(1),(2)]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

/-- Object and derived-Hom descent for an already constructed normalized functor.
This statement constructs no functor, coefficient map, scalar comparison, or small model.
-/
theorem normalizedFunctor_descent
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] (D : NormalizedFunctor l X) :
    (∀ K L, Function.Bijective (D.J.map : (K ⟶ L) → (D.J.obj K ⟶ D.J.obj L))) ∧
      (∀ K, ProEtale.DerivedCategory.boundedAdicConstructible l X K ↔
        ∃ A, Nonempty (D.J.obj A ≅ K)) := by
  exact ⟨normalizedFunctor_descent_hom l X D,
    normalizedFunctor_descent_image l X D⟩

end WeilConjectures.LocallyFiniteAdicRealization
