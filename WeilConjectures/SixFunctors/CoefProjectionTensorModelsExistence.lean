/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefProjectionEvaluationData

/-! # Signed coefficient tensor and open comparison witnesses

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 07A6, 08J9, 0D6D and 0B56.
(blueprint: lem-sf-coef-projection-tensor-models-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures.CoefProjectionEvaluation
attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The signed localized tensor data at the point and on three sequence sites,
with the canonical open-extension tensor comparison between the first and third.
This asserts no derived direct-image adjunction and no scalar specialization.

Source: Stacks 06YT, 0FPT, 08J9 and 0GL1; projection-evaluation proof steps 2, 3 and 6.
(blueprint: lem-sf-coef-projection-tensor-models-existence).

Proof: on each sequence site apply the closed symmetric monoidal construction to
its actual quotient ring sheaf. Retain its signed symmetry and K-flat total-tensor
comparison. The K-flat localization equivalence extends the inverse comparison to
the universal left-derived counit on all pairs of complexes; on two K-flat factors
its composite with the recorded comparison is the identity. Fill the integral and
finite components of CoefficientDerivedSystemTensors by their existing closed
models. At the point carry out the same localization for the quotient-presheaf
and constant-integral module tensors. Totalize the ordinary signed swap to obtain
PointSymmetry; on degree (p,q) its coefficient is (-1)^(pq), and naturality of the
left-derived counit is the localization equation. For open extension, take the
ordinary sheafified tensor map, characterized by the open unit and the restriction
tensor comparison. Totalize and derive using flat-term K-flat representatives.
The ordinary unit-transpose identity determines gamma and the representative
square. All constructions take place on the entire sequence site, so horizontal
quotient restrictions commute with them. Zero objects, the empty site and the
identity open immersion obey the same universal properties. -/
theorem coefficientProjectionTensorModels_exists
    (X Y Z : Scheme.{u}) (j : X ⟶ Z) [IsOpenImmersion j] :
    ∃ (point : PointTensor l E) (symmetry : PointSymmetry l E point)
      (x : SystemTensor l E X) (y : SystemTensor l E Y) (z : SystemTensor l E Z),
      Nonempty (CoefSupportOpenTensor.SystemOpenModel l E j x.data z.data) := by sorry

end WeilConjectures.CoefProjectionEvaluation
