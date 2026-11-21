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

## References

* Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.8, Proposition 6.8.14(1),(2)
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
