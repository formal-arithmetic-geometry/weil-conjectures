/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorComparisons
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction
import all WeilConjectures.AlgebraicGeometry.System.SystemCochainTensorReduction
import all WeilConjectures.AlgebraicGeometry.System.SystemTensorReductionFormula
import WeilConjectures.AlgebraicGeometry.System.SystemEvaluationFlat

/-! # Reduction compatibility for semilinear tensor models
Source: Zheng Construction 4.1 and Stacks 07A4, 08J9.
(blueprint: lem-coef-semilinear-tensor-coherence-reduction)
-/
@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

namespace TensorReductionProof
-- Adapt the ordinary, cochain and derived proofs in SystemOrdinaryTensorReduction,
-- SystemCochainTensorReduction and SystemTensorReductionFormula to the supplied
-- scalar/tensor components. Their generic proof helpers are reused through private imports.
attribute [local irreducible] hasDerived SheafOfModules.monoidalCategory evaluation
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end TensorReductionProof

variable (S : SystemScalarCoherence.{c, v, r} J B τ)
end WeilConjectures.SemilinearSections
