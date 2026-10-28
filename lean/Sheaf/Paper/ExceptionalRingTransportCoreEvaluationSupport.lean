/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module
public import Sheaf.Paper.ExceptionalRingTransportCoreData
/-! The evaluated support comparison for exceptional integral transport.
Source: Zheng, Proposition 5.26.
(blueprint: new-lem-sf-exceptional-ring-transport-core-evaluation-support) -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
/-- The finite evaluation of the transported support map agrees with the
support evaluation supplied by the integral realization.  This is the support
clause in Zheng, Proposition 5.26.
(blueprint: new-lem-sf-exceptional-ring-transport-core-evaluation-support) -/
theorem exceptional_transport_core_evaluation_support
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l,
      Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) :
    ∀ (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E X).FullSubcategory),
      (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).ι.map
          ((d.evaluationF E n).hom.app K) ≫
        (left (.finite E ⟨n + 1, Nat.succ_pos n⟩)).hom.app
          (((d.reconstruction E true).evaluation n).obj K) ≍
      (IntegralSystemRealization.supportEvaluation l E.carrier (d.operations E) c n).hom.app
        K.obj := by
  sorry
end WeilConjectures.ExceptionalIntegralScalar
