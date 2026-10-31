/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalEvaluationData

/-! # Integral completed evaluation

Source: blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality, first proof paragraph
(blueprint: lem-sf-integral-completed-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Pretriangulated.Opposite
namespace WeilConjectures.IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t}) (U : Option X.ProEt)

/-- Integral exact functors and the uniquely normalized completed evaluation.
Source: Stacks 08JC, 08JD, 08JE, 099A, 0A0E; blueprint first proof paragraph.
(blueprint: lem-sf-integral-completed-evaluation)

Proof: identify the quotient-tower completion with the local-completeness reflector.
K-flat tensor cones and exact derived inverse limit give exactness of completed tensor.
RHom is exact with the reversed shifts and takes complete targets to complete objects.
The scalar actions on representatives give linearity. Extend ordinary evaluation uniquely
across the completion unit into the complete RHom target. Precomposition with the unit
proves naturality and uniqueness. On homogeneous representatives the Hom shift contributes
(-1)^a and the tensor shift (-1)^b, equal to the evaluation shift (-1)^(a+b).
The reflector bijection descends this equality to completed evaluation and all integer
shifts. At the coefficient object ordinary evaluation is the unit isomorphism;
the completed comparison is invertible because M is complete. This holds on either
actual slice site, and for zero objects without any finiteness assumption. -/
theorem integralCompletedEvaluation
    (_hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (M : D l E X U) (hM : IsComplete l E X U M) :
    (phi l E X U M).Additive ∧ (phi l E X U M).Linear
      (Padic.coefficientExtensionIntegers l E) ∧
    (psi l E X U M).Additive ∧ (psi l E X U M).Linear
      (Padic.coefficientExtensionIntegers l E) ∧
    (∀ L : D l E X U, IsComplete l E X U ((psi l E X U M).obj (op L))) ∧
    ∃ (sPhi : (phi l E X U M).CommShift ℤ) (sPsi : (psi l E X U M).CommShift ℤ),
      (fun [phiShift : (phi l E X U M).CommShift ℤ]
        [psiShift : (psi l E X U M).CommShift ℤ] ↦
        (phi l E X U M).IsTriangulated ∧ (psi l E X U M).IsTriangulated ∧
        ∃ α : phi l E X U M ⟶ psi l E X U M,
          (∀ L : D l E X U,
            (completionUnit l E X U).app ((ordinaryPhi l E X U M).obj (op L)) ≫
              α.app (op L) = ordinaryEvaluation l E X U L M) ∧
          (∀ β : phi l E X U M ⟶ psi l E X U M,
            (∀ L : D l E X U,
              (completionUnit l E X U).app ((ordinaryPhi l E X U M).obj (op L)) ≫
                β.app (op L) = ordinaryEvaluation l E X U L M) → β = α) ∧
          NatTrans.CommShift α ℤ ∧
          IsIso (α.app (op (coefficient l E X U))))
        (phiShift := sPhi) (psiShift := sPsi) := by sorry

end WeilConjectures.IntegralOnSlice
