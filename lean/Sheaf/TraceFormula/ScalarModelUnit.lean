/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.CompletedLineTensorCoherence
public import Sheaf.Paper.QuotientSystemMixedCoherence

/-! # Scalar model normalization before inverting completion

Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1;
Stacks Project, Tags 06YY and 0941.
(blueprint: lem-trf-scalar-model-unit)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u})

/-- The normalized scalar identity model sends the ordinary multiplication unitor
to the actual reduction-realization unit, before completion is inverted.
Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1;
Stacks 06YY, 0941, the scalar calculation in step 11 of the parent.
(blueprint: lem-trf-scalar-model-unit)

Proof: on a flat-term K-flat representative P, use the simultaneous strict quotient
presentation of SE.reduction(P). The scalar-model normalization identifies realization
with the quotient Roos map. The identity clause of finiteFreeCompletedScalarComparison
identifies the initial completion comparison with multiplication followed by the
strict quotient augmentation. The system scalar unitor multiplies the same tensor
factors. Under the system adjunction the resulting quotient family sends x to
1 tensor x, which is the unit: SE.unit_projection identifies its finite components,
and integralConeCounitRealization gives equality of the whole adjuncts from the
strict compatible family, before localization. The ordinary derived unitor is the
localization of multiplication, so the displayed square commutes on P. Extend along
the localization of K-flat representatives and naturality to every K. This includes
the zero complex and the empty site and uses no inverse to a chain completion map. -/
theorem scalarModelUnit
    (SE : CoefficientDerivedSystemCalculus l E X)
    (ρE : IntegralComparisonRoosModel l E X)
    (bEE : IntegralComparisonScalarModel l E E (AlgHom.id ℚ_[l] E) X SE ρE)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    (completedScalarComparison l E E (AlgHom.id ℚ_[l] E) X).app K ≫
      bEE.realization.hom.app K ≫
      (coefficientSequenceLimit l E X).map
        ((integralComparisonSystemScalarUnit l E X).hom.app (SE.reduction.obj K)) =
    (CompletedLineTensor.ordinaryUnit l E X).hom.app K ≫ SE.adjunction.unit.app K := by
  sorry

end WeilConjectures
