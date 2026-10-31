/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralStratumChartRestrictionsData
import WeilConjectures.AlgebraicGeometry.IntegralDerivedPullbackLinear
import WeilConjectures.AlgebraicGeometry.AmbientComparisonSystemExistence
import WeilConjectures.AlgebraicGeometry.IntegralComparisonPullbackRealizationShifts

/-! # Auxiliary steps for integral stratum restrictions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace WeilConjectures.IntegralStratumCharts

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option linter.unusedVariables false in
/-- The linear and triangulated part for the specified, normalized comparison.
Source: Bhatt--Scholze, Lemma 6.5.9(4) and Remark 6.5.10; Stacks 099N and 0941
(blueprint: lem-a1-integral-stratum-pullback-functorial).

Proof: The representative pullback is finite inverse image followed by products
and the shifted cone of 1 minus transition. Every operation is additive and commutes
with multiplication by a constant integral scalar. The normalized resolving-class
localization comparison transfers these identities to integralDerivedPullback;
its essential surjectivity and full faithfulness on natural transformations give
additivity and the displayed scalar identity on derived arrows. For a triangle
with integral constructible vertices, completeness follows from their defining
predicate. Apply the normalized gamma maps to identify its pulled-back vertices
with strict completed pullback. Naturality handles its first two arrows; the shift
square in c.shifts handles its last arrow, using exactly c.derivedShift. Thus these
three gamma maps define an isomorphism with the completed image triangle.
The latter is distinguished by completedPullback_preserves_shifts_distinguished,
with the coefficient transport preserving distinguished triangles. Invariance under
triangle isomorphism gives the assertion. The argument concerns only complete
constructible vertices and does not assert global t-exactness. Zero objects, empty
schemes, and zero scalars satisfy the same formulas. -/
theorem integral_stratum_pullback_functorial {X W : Scheme.{u}} (h : W ⟶ X)
    [IsNoetherian X] [IsNoetherian W]
    (_hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hWdim : ∃ n : ℕ, topologicalKrullDim W ≤ n)
    (_hXl : IsUnit (l : Γ(X, ⊤))) (_hWl : IsUnit (l : Γ(W, ⊤)))
    (c : IntegralCompletedComparison.Comparison l E h) :
    (integralDerivedPullback l E h).Additive ∧
    (∀ (a : Padic.coefficientExtensionIntegers l E)
      (K L : (constructible l E X).FullSubcategory) (f : K ⟶ L),
      (integralDerivedPullback l E h).map
          ((integralScalarDerivedAction l E X a).app
            ((ImmersionCompletedPullback.transport l E X).obj K.obj) ≫
              (ImmersionCompletedPullback.transport l E X).map f.hom) =
        (integralScalarDerivedAction l E W a).app
            ((IntegralCompletedComparison.integral l E h).obj K.obj) ≫
          (IntegralCompletedComparison.integral l E h).map f.hom) ∧
    (fun [shift : (integralDerivedPullback l E h).CommShift ℤ] ↦
      ∀ T : Triangle (DerivedCategory (integralTowerModules l E X)),
        T ∈ distTriang _ →
        sfIntegralConstructible l E X T.obj₁ →
        sfIntegralConstructible l E X T.obj₂ →
        sfIntegralConstructible l E X T.obj₃ →
        (integralDerivedPullback l E h).mapTriangle.obj T ∈ distTriang _)
      (shift := c.derivedShift) := by
  obtain ⟨hadd, hlin⟩ := integralDerivedPullback_linear l E h
  refine ⟨hadd, ?_, ?_⟩
  · intro a K L f
    rw [← (integralCoefficientLinear_existsUnique l E X).exists.choose_spec,
      ← (integralCoefficientLinear_existsUnique l E W).exists.choose_spec]
    exact hlin.map_smul _ a
  · let := c.derivedShift
    obtain ⟨C⟩ := ambientComparisonSystem_exists.{u} l
    let := integralComparisonLimitShift l E X
    let := integralComparisonLimitShift l E W
    let := integralComparisonReductionShift l E X ((C.coefficient E).system X)
    let := integralComparisonSequencePullbackShift l E h
    have hlimit (Z : Scheme.{u}) :
        let := integralComparisonLimitShift l E Z
        (coefficientSequenceLimit l E Z).IsTriangulated := by
      unfold integralComparisonLimitShift coefficientSequenceLimit
        coefficientSequenceDerivedRestriction coefficientConstantTowerLimit
      infer_instance
    have := hlimit X
    have := hlimit W
    have : ((C.coefficient E).system X).adjunction.CommShift ℤ :=
      ((C.coefficient E).system X).adjunction.commShift_of_rightAdjoint ℤ
    have : ((C.coefficient E).system X).reduction.IsTriangulated :=
      ((C.coefficient E).system X).adjunction.isTriangulated_leftAdjoint
    have : (integralComparisonDerivedSequencePullback l E h).IsTriangulated := by
      unfold integralComparisonDerivedSequencePullback
      infer_instance
    have : NatTrans.CommShift ((C.coefficient E).pullback h).realization.hom ℤ :=
      integralComparisonPullbackRealization_commShift l E h
        ((C.coefficient E).system X) ((C.coefficient E).roos W)
        ((C.coefficient E).pullback h) c.chainShift c.chainShift_coordinates
        c.derivedShift c.derivedShift_descent
    have : (integralDerivedPullback l E h).IsTriangulated :=
      (Functor.isTriangulated_iff_of_iso ((C.coefficient E).pullback h).realization).2
        inferInstance
    intro T hT _ _ _
    exact (integralDerivedPullback l E h).map_distinguished T hT

end WeilConjectures.IntegralStratumCharts
