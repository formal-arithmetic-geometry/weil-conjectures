/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteModels
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonComponentNaturality
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorOrdinaryUnit

/-! Tensorator and unit data for the common-stage completed tensor lift.
(blueprint: new-sf-adic-completed-tensor-common-lift-tensor-unit).
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

/-- The common-stage tensorator and coefficient unit before constraint equations.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: new-sf-adic-completed-tensor-common-lift-tensor-unit). -/
structure CompletedTensorCommonLiftTensorUnit
    (models : CoefficientTensorModels.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R) closed)
    (symmetry : @SymmetricCategory _ _ closed.monoidal) where
  tensor : ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor ≅
    commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R
  unit : closed.monoidal.tensorUnit ≅
    (ordinary l X R).obj (pullbackTensorCommonUnit l (PadicAlgCl l) X)

end WeilConjectures.AdicQbarRealization
