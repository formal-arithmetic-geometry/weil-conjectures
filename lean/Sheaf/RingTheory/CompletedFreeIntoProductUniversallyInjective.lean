/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Filtration
import Sheaf.RingTheory.UniversalInjectiveFiniteTest

/-!
# Universal injectivity of the completed free module's coordinate map

Source: Stacks Project, More on Algebra, Tag 05BC,
`lemma-ui-completion-direct-sum-into-product`
(blueprint: lem-trf-completed-free-into-product-universally-injective).
-/

@[expose] public section

universe u v w

namespace AdicCompletion

/-- The canonical coordinate map from the completion of the finitely supported families
`A →₀ R` into the product `A → R`, when `R` is `I`-adically complete. Its `a`-th coordinate
is obtained by completing evaluation at `a` and applying the inverse of the canonical
linear equivalence `R ≃ₗ[R] AdicCompletion I R`. Thus it is the unique coordinatewise
`I`-adic limit, with no choice of an unrelated map.
Source: Stacks Project, More on Algebra, Tag 05BC,
`lemma-ui-completion-direct-sum-into-product`, displayed map and first proof paragraph
(blueprint: lem-trf-completed-free-into-product-universally-injective). -/
noncomputable def completedFreeToProduct {R : Type u} [CommRing R]
    (I : Ideal R) [IsAdicComplete I R] (A : Type v) :
    AdicCompletion I (A →₀ R) →ₗ[R] (A → R) :=
  LinearMap.pi fun a ↦
    (ofLinearEquiv I R).symm.toLinearMap.comp
      ((map I (Finsupp.lapply a)).restrictScalars R)

/-- The canonical coordinate map from the completion of a free module into the product
is universally injective over a Noetherian adically complete ring.
Source: Stacks Project, More on Algebra, Tag 05BC,
`lemma-ui-completion-direct-sum-into-product`
(blueprint: lem-trf-completed-free-into-product-universally-injective).

Proof:
1. A compatible family in the completion is a sequence of finitely supported residue
   families. Completeness of R gives its unique coordinatewise limits. At every power
   of I only finitely many coordinates are nonzero modulo that power. Conversely, such
   a family gives a compatible element of the completion. This identifies the displayed
   coordinate map with the inclusion of convergent families, so it is injective.
2. For a finite module Q choose a finite presentation R^k -> R^m -> Q -> 0, with relation
   map phi. Represent a tensor by m convergent families y_j. If its image vanishes in
   Q tensor the product, each coordinate vector (y_j(a)) lies in the image of phi.
3. Apply `lem-weil-pbc-artin-rees` (Mathlib's `Ideal.exists_pow_inf_eq_pow_smul`) to the
   image of phi in R^m. For some c, a relation vector in (I^r)^m has a preimage in
   (I^(r-c))^k for r >= c. Choose coordinate preimages with orders tending to infinity:
   for every n, all but finitely many relation vectors lie in (I^(n+c))^m, and their
   preimages can be taken in (I^n)^k. The resulting k families converge and hence give
   elements of the completed free module. Their image is the original m-tuple, which
   proves injectivity after tensoring with Q by right exactness of the presentation.
4. Apply `lem-trf-universal-injective-finite-test`, namely
   `LinearMap.universally_injective_tensor_iff`, to pass from all finite Q to all Q
   over the Noetherian ring R (Stacks Algebra, Tag 058K).
-/
theorem completedFreeToProduct_lTensor_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (A : Type v)
    (Q : Type (max u v w)) [AddCommGroup Q] [Module R Q] :
    Function.Injective ((completedFreeToProduct I A).lTensor Q) := by
  sorry

end AdicCompletion
