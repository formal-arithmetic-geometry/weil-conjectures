/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.ScalarExtensionTowerRealizationData
public import Sheaf.Paper.CompletedPullbackTowerRealizations

/-! # Normalization of the completed tensor realization

The realization is constructed from the existing normalized tensor descent,
the adjunction comparison of reductions, and the closed tensor comparison.
Only its equation on coherent strict quotient presentations remains to prove.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Transport the uniquely strict-Roos-normalized tensor to the specified calculus.
The comparison of reductions is fixed by their adjunctions to the same limit;
the comparison of tensors preserves their common tensor-Hom transpose.
Source: Stacks 06YY, 07A4, 0941; realization step 8 of scalar tower coherence.
(blueprint: stage3-pur-scalar-tensor-model-normalization) -/
def tensorModelRealization (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) :
    integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
      S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W := by
  let T := pullbackTensorCalculus l E W
  let a := T.adjunction.leftAdjointUniq S.adjunction
  exact pullbackTensorIntegralTensorModel l E W ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (NatIso.prod a a) T.systemClosed.tensor ≪≫
        Functor.isoWhiskerLeft (S.reduction.prod S.reduction)
          (CoefficientClosedStructure.comparison T.systemClosed S.systemClosed))
      (coefficientSequenceLimit l E W)

/-- The constructed tensor realization has the prescribed strict quotient formula
and Roos equation on every pair of whole-system coherent presentations.
Source: Stacks 03EL, 06YY, 07A4, 0941; steps 4 and 8 of
lem-pur-scalar-extension-tower-coherence.
(blueprint: stage3-pur-scalar-tensor-model-normalization)

Proof: choose the flat-term K-flat representatives P,Q. The two finite quotient
presentations identify C,D with their actual reductions. Tensor their chain
isomorphisms, and use the finite total-tensor evaluation comparison to obtain q
with all horizontal transitions. On a homogeneous generator its value is the
tensor of the two prescribed quotient sections, which is the displayed formula.
The two whole-system coherence conditions identify the adjunction transposes of
eC,eD with the strict tensor-unit maps. Their tensor therefore gives the same
whole-tower morphism as this q. Apply the normalized Roos bridge. Naturality of
the bridge and the universal tensor-model isomorphism give the FiveStepEquation.
The unit equation for the left-adjoint comparison identifies the transported
reduction with the same quotient augmentation; the closed tensor comparison
preserves the tensor-Hom transpose. Finally the defining normalization of
pullbackTensorIntegralTensorModel identifies the reference realization on P,Q
with integralCompletedTensorComparison. This proves the
equation for the constructed realization, without asserting that arbitrary
realizations are normalized or that finite derived evaluations are faithful.
Zero complexes, the first quotient, and empty schemes use the same formulas. -/
theorem tensorModelRealization_normalized (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W) :
    IsTensorModelNormalized l E W S ρ (tensorModelRealization l E W S) := by sorry

end WeilConjectures.ScalarExtensionTower
