/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit

/-! Right-unit equation for the common-stage completed tensor lift.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-right-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)
  (symmetry : @SymmetricCategory _ _ closed.monoidal)

/-- The right-unit component of the common-stage constraint system.
The finite coefficient multiplication calculation and its transport through the
native right unitor are the proof obligations isolated here.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints-right-unit). -/
theorem completed_tensor_common_lift_constraints_right_unit
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry) :
    ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
      closed.tensor.map (Prod.mkHom (𝟙 _) data.unit.hom) ≫
          data.tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
          (ordinary l X R).map (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
        (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom := by
  sorry

end WeilConjectures.AdicQbarRealization
