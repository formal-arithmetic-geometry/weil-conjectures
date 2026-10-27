/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H8
-/
module

public import Sheaf.Paper.CompletedComparisonQuotientRealizationDefs

/-! # The prescribed ordinary quotient reduction presentation

Source: Stacks 0941 and 06YY; the normalized coherent reduction model.
-/


@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substituteInputs substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction scalarQuotients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The actual ordinary quotient complex, with its fixed reduction-model and
ordinary evaluation isomorphisms, is a coherent reduction presentation.
Source: Stacks 0941 and 06YY; the adjunction normalizations of
pullbackTensorReductionModel_existsUnique and pullbackTensorReductionEvaluation_existsUnique
(blueprint: lem-pur-completed-quotient-reduction-presentation).

Proof: transpose the fixed reduction-model component under the reduction/limit
adjunction. Its defining equation is the localization of the ordinary quotient
unit followed by the canonical total-limit comparison. Project to level n and
transpose under the finite scalar-extension/restriction adjunction. The ordinary
evaluation comparison is normalized by exactly this projected ordinary unit.
The finite K-flat reduction comparison is likewise normalized by this unit;
uniqueness of adjoints gives the CoefficientComparisonEquation. For m >= n,
transpose the two composites of the ordinary evaluation isomorphisms with the
quotient transition under the ordinary extension/restriction adjunction. Both
are the same ordinary quotient unit followed by the quotient map. Injectivity
of the Hom equivalence gives the CoefficientTransitionEquation; applying the
cochain-complex functors preserves the equality. No replacement complex or
new representative is chosen. The argument applies to zero complexes, n=0
(the exponent-one quotient), and m=n, where the quotient map is the identity. -/
theorem completedQuotientReductionPresentation
    (Y : Scheme.{u})
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    CoefficientReductionPresentation l E Y
      (pullbackTensorCalculus l E Y).toCoefficientDerivedSystemReduction
      P.obj P.property.1 (quotient l E P.obj)
      ((pullbackTensorReductionModel l E Y).app P)
      (fun n ↦ ((pullbackTensorReductionEvaluationComplex l E Y n).app P.obj).symm) := by sorry

end WeilConjectures.CompletedQuotient
