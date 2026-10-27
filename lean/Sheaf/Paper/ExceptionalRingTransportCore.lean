/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalIntegralScalarMates
import Sheaf.Paper.ExceptionalRingTransportCoreLaws

/-! # Core transport assembly for the exceptional ring family -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- The normalized integral system transport can be assembled from the already
constructed finite and integral operation family. The construction uses the
reduction/limit equivalences at each finite coefficient field, the actual
proper/open system realization, and the evaluation/unit/counit comparison maps.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26; this is the transport-data part of the exceptional ring family proof
(blueprint: lem-sf-exceptional-ring-transport-core).

Proof: for each finite coefficient field, apply the actual strict-system
transport and normalized reconstruction equivalence. Conjugate its system
adjunction through the equivalence, and use the simultaneous proper/open
realization to obtain the prescribed integral left realization. Retain the
whole-system unit and counit, their finite evaluations, and all common bounds.
The finite and integral operations supplied by the ring-stage assembly are the
corresponding reconstructed operations, so these maps satisfy every field of
`ExceptionalIntegralScalar.Transported`. Empty schemes use the zero adjunction
and positive finite levels use exponent `n + 1`.
-/
theorem exists_exceptional_transport_for_operations
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s)) :
    Nonempty (ExceptionalIntegralScalar.Transported l Ω D hl c
      operation left) := by
  obtain ⟨d⟩ := ExceptionalIntegralScalar.exists_exceptional_transport_core_data
    l Ω D hl f c operation left
  obtain ⟨h⟩ := ExceptionalIntegralScalar.exists_exceptional_transport_core_laws
    l Ω D hl f c operation left d
  exact ⟨{
    leftShift := d.leftShift
    reconstruction := d.reconstruction
    operations := d.operations
    realizations := d.realizations
    F := d.F
    G := d.G
    adjunction := d.adjunction
    support := h.support
    realizeF := d.realizeF
    realizeG := d.realizeG
    adjunction_eq := h.adjunction_eq
    reductionF := d.reductionF
    reductionF_eq := h.reductionF_eq
    reductionG := d.reductionG
    reductionG_eq := h.reductionG_eq
    evaluationF := d.evaluationF
    evaluationG := d.evaluationG
    evaluation_unit := h.evaluation_unit
    evaluation_counit := h.evaluation_counit
    evaluation_support := h.evaluation_support
    integralLeft := d.integralLeft
    integralLeft_normalized := h.integralLeft_normalized
    inputGood := h.inputGood
    openGood := h.openGood
    integral_system_normalized := h.integral_system_normalized }⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
