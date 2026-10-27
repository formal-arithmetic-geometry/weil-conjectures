/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit

/-! Constraint equations for the common-stage completed tensor lift.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints).
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

/-- The four monoidal constraint equations for fixed common-stage tensor and unit.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints). -/
structure CompletedTensorCommonLiftConstraints
    (models : CoefficientTensorModels.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R) closed)
    (symmetry : @SymmetricCategory _ _ closed.monoidal)
    (tensor : ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor ≅
      commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R)
    (unit : closed.monoidal.tensorUnit ≅
      (ordinary l X R).obj (pullbackTensorCommonUnit l (PadicAlgCl l) X)) where
  associative : ∀ A B C : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (tensor.hom.app (A, B)) (𝟙 _)) ≫
        tensor.hom.app ((commonStageDerivedTensor l (PadicAlgCl l) X).obj (A, B), C) ≫
        (ordinary l X R).map (pullbackTensorCommonAssociator l (PadicAlgCl l) X A B C).hom =
      (closed.monoidal.associator ((ordinary l X R).obj A) ((ordinary l X R).obj B)
        ((ordinary l X R).obj C)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (tensor.hom.app (B, C))) ≫
        tensor.hom.app (A, (commonStageDerivedTensor l (PadicAlgCl l) X).obj (B, C))
  left_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom unit.hom (𝟙 _)) ≫
        tensor.hom.app (pullbackTensorCommonUnit l (PadicAlgCl l) X, A) ≫
        (ordinary l X R).map (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.leftUnitor ((ordinary l X R).obj A)).hom
  right_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (𝟙 _) unit.hom) ≫
        tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
        (ordinary l X R).map (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom
  symmetric : ∀ A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    tensor.hom.app (A, B) ≫
        (ordinary l X R).map (pullbackTensorCommonBraiding l (PadicAlgCl l) X A B).hom =
      (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
        tensor.hom.app (B, A)

/-- The native derived coherence transports all four constraint diagrams to the
common-stage tensorator.  Each equality is represented at a finite coefficient
field, where the representative equations in `N` apply; independence of the
chosen field follows from the supplied comparison coherence.
(blueprint: new-sf-adic-completed-tensor-common-lift-constraints). -/
theorem completed_tensor_common_lift_constraints
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (data : CompletedTensorCommonLiftTensorUnit l X R closed models symmetry) :
    Nonempty (CompletedTensorCommonLiftConstraints l X R closed models symmetry
      data.tensor data.unit) := by
  sorry

end WeilConjectures.AdicQbarRealization
