/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonLiftCoherence
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonLiftAgreementComponent

/-! # Finite normalization of a common-stage completed tensor lift

This module isolates the finite-stage agreement field from the common-stage
coherence data.  It is the normalized finite comparison in BS Remark 6.8.15
and HRS Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-lift-agreement).
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

/-- Finite normalized comparisons agree with the supplied common-stage tensorator.
The coherence datum is supplied explicitly so the conclusion is only the finite
agreement field needed by `CompletedTensorCommonLift`.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-lift-agreement). -/
theorem completed_tensor_common_lift_agreement
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (C : CompletedTensorCommonLiftCoherence l X R closed symmetry models N) :
    ∀ E, tensorFiniteAgreement l X R closed C.tensor E
      (N E).completion (N E).ordinary := by
  intro E K L
  exact completed_tensor_common_lift_agreement_component l X R closed models symmetry N
    coherence C E K L

end WeilConjectures.AdicQbarRealization
