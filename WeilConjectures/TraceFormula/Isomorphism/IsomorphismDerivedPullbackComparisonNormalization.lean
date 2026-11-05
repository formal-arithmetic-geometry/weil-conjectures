/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.TraceFormula.Isomorphism.IsomorphismRoosUnitCancellation
import WeilConjectures.TraceFormula.Supporting.StrictQuotientCompletionUnit

/-!
# The specified inverse-image comparison is the completion unit

Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/
  sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md, clauses (2)--(3)
  (blueprint: lem-weil-isomorphism-derived-pullback-comparison-normalization).

For a scheme isomorphism `g : X ⟶ Y`, the specified comparison
`inverseImagePullbackComparisonDerived` from exact inverse image `G` to completed
integral pullback `P_g` is related to `G` of the actual completion unit
`S.adjunction.unit` of the canonical reduction/strict-system-limit calculus `S`
by a natural isomorphism `θ : P_g ≅ G ∘ completion`.  For a derived-complete object
the comparison is invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Limits.limit

section Model
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] comparisonFromModel roosModel
end Model

end WeilConjectures
