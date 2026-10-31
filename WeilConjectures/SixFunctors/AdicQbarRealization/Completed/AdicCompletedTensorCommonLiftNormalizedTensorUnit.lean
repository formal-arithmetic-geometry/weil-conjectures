/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonLiftTensorUnit
public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonComponent
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonComponentNaturality
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorOrdinaryUnit

/-! Normalized tensor and unit data for the common-stage completed tensor lift.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-lift-normalized-tensor-unit).
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

/-- The explicit common-field components form tensorator data, with their
normalization retained as an equation instead of forgotten by Nonempty.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-lift-normalized-tensor-unit).

Proof: obtain the ordinary coefficient-unit comparison. Compose it with the
native unit comparison. For the tensorator use NatIso.ofComponents on the
explicit completedTensorCommonComponent isomorphisms; their proved naturality
supplies its naturality field. Each hom component is definitionally the specified
component, so the normalization equations are reflexive. No arbitrary tensorator
is selected and no coherence law is assumed in this construction. -/
theorem completed_tensor_common_lift_normalized_tensor_unit
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry) :
    ∃ data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry,
      ∀ A B, data.tensor.hom.app (A, B) =
        (completedTensorCommonComponent l X R closed models N A B).hom := by
  obtain ⟨e⟩ := completedTensorOrdinaryUnit l X R
  refine ⟨{ tensor := NatIso.ofComponents
              (fun P ↦ completedTensorCommonComponent l X R closed models N P.1 P.2)
              (fun f ↦ completedTensorCommonComponent_naturality l X R closed models symmetry N
                coherence f)
            unit := coherence.unitIso ≪≫ e }, ?_⟩
  intro A B
  rfl

end WeilConjectures.AdicQbarRealization
