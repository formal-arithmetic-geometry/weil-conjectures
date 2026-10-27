module

public import Sheaf.Paper.EtaleSystemTensorEvaluation

/-! # Unbounded compact support and projection on strict étale systems

Source: Stacks Tags 0B56, 0F0G, 0GL1 and 0GL6; the ordinary strict-system
refinement of the integral exceptional-adjoint argument
(blueprint: def-coef-etale-system-derived-tensor-evaluation).

All presentations below are conclusion data. The coefficient index n means n+1.
Tensor comparisons are normalized on ordinary pure tensors and signed total complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures.SemilinearSections
open scoped TensorProduct

namespace AlgebraicGeometry.Etale.SystemCompactSupport
open SystemProjection

/-- The representative square for tensor evaluation, in the whole system category.
Source: Stacks 06YU and 07A4
(blueprint: def-coef-etale-system-derived-tensor-evaluation). -/
def TensorEvaluationModel (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1})
    (A : Calculus W B) (n : ℕ) (e : Evaluation W B n)
    (t : TensorEvaluationData W B A n e) : Prop :=
  ∀ (P Q : CochainComplex (Modules W B) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
      (R := rings W B) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
      (R := rings W B) Q),
    HEq (t.tensor.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      e.E.map (tensorModelIso.{u + 1, u, u + 1}
        (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
        (rings W B) A.closed A.tensorModels P Q hP hQ).inv)
      ((Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} (B.obj (op n))) W)).map
        (Prod.mkHom ((evalFactors e).hom.app P)
          ((evalFactors e).hom.app Q)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((evalComplex e).obj P)
          ((evalComplex e).obj Q) ≫
        DerivedCategory.Q.map (t.chain P Q) ≫
        (evalFactors e).inv.app
          ((totalTensor.{u + 1, u, u + 1}
          (WeilConjectures.coefficientSequenceTopology W.smallEtaleTopology)
            (rings W B)).obj (P, Q)))

/-- Evaluation with its ordinary and derived normalizations retained.
Source: Stacks 03EL, 06YU and 07A4
(blueprint: def-coef-etale-system-derived-tensor-evaluation). -/
structure TensorEvaluation (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1})
    (A : Calculus W B) (n : ℕ) (e : Evaluation W B n)
    extends TensorEvaluationData W B A n e where
  model : TensorEvaluationModel W B A n e toTensorEvaluationData

end AlgebraicGeometry.Etale.SystemCompactSupport
