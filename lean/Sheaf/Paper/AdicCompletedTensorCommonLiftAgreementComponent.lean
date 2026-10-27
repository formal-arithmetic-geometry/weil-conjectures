/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicCompletedTensorCommonLiftCoherence

/-! # Componentwise finite normalization comparison

This module isolates one finite coefficient field and one pair of integral objects
from the common-stage finite agreement.  It is the componentwise comparison used
to assemble `tensorFiniteAgreement`.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-lift-agreement-component).
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
open AlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)
  (symmetry : @SymmetricCategory _ _ closed.monoidal)

/-- The normalized finite comparison for one coefficient field and one pair of
integral objects.  These components are the atomic equalities collected by
`completed_tensor_common_lift_agreement`.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-common-lift-agreement-component). -/
theorem completed_tensor_common_lift_agreement_component
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (C : CompletedTensorCommonLiftCoherence l X R closed symmetry)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K L : sfIntegralConstructibleCategory l
      (Coefficient.{u} l (PadicAlgCl l) E) X) :
    HEq (C.tensor.hom.app ((tensorStage l X E).obj K, (tensorStage l X E).obj L))
      (closed.tensor.map (Prod.mkHom ((R.integral E).hom.app K)
        ((R.integral E).hom.app L)) ≫
      (N E).ordinary.inv.app (K.obj, L.obj) ≫
      (pbcDerivedExtend (coefficientMap l X R E)).map
        (tensorQuotientIso l X E (N E).completion K L).hom ≫
      (R.integral E).inv.app
        ((constructibleIntegralTensor l
          (Coefficient.{u} l (PadicAlgCl l) E) X).obj
          (K, L)) ≫
      (AdicQbarRealization.ordinary l X R).map
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E).map
          (tensorIntegralObjectIso l X E K L).inv) ≫
      (AdicQbarRealization.ordinary l X R).map
        (stageTensor l X (PadicAlgCl l) E
          ((sfRationalConstructibleLocalization
            l (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)
          ((sfRationalConstructibleLocalization
            l (Coefficient.{u} l (PadicAlgCl l) E) X).obj L)).hom) := by
  sorry

end WeilConjectures.AdicQbarRealization
