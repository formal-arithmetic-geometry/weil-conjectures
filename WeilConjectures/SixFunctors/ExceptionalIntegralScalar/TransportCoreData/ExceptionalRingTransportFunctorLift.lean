/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreData
public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalSequencePropertyIsomorphism

/-! # Lifting a specified system functor in exceptional transport

Source: Zheng, Construction 5.25. Replace a transported functor by a specified
naturally isomorphic functor, preserving the actual adjunction and comparisons.
(blueprint: lem-sf-exceptional-transport-functor-lift)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
  (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
  (d : TransportCoreData l Ω D hl c operation left)

/-- Replace the left system functor and transport all dependent data along the
specified natural isomorphism. Retain the right functor, operations, reconstructions
and integral-left comparison. Recompute the right evaluation as the mate of the
transported left evaluation, so its dependent unit and counit equations hold.
Source: Zheng, Construction 5.25; Mathlib's adjunction transport and whiskering.
(blueprint: lem-sf-exceptional-transport-functor-lift) -/
def TransportCoreData.replaceSystemF
    (F' : ∀ E : FieldStage.{u} l,
      (sequenceProperty l E X).FullSubcategory ⥤ (sequenceProperty l E Y).FullSubcategory)
    (e : ∀ E : FieldStage.{u} l, d.F E ≅ F' E) :
    TransportCoreData l Ω D hl c operation left :=
  { d with
    F := F'
    adjunction := fun E ↦ (d.adjunction E).ofNatIsoLeft (e E)
    realizeF := fun E ↦ d.realizeF E ≪≫
      Functor.isoWhiskerLeft (d.reconstruction E true).equivalence.functor
        (Functor.isoWhiskerRight (e E) (d.reconstruction E false).equivalence.inverse)
    evaluationF := fun E n ↦ Functor.isoWhiskerRight (e E).symm
      ((d.reconstruction E false).evaluation n) ≪≫ d.evaluationF E n
    evaluationG := fun _ _ ↦ Adjunction.compatibleRightComparison _ _ _ }

/-- Lift the prescribed ambient functor itself, using the natural comparison only
to transport its domain property and the existing adjunction data. In particular
no equality of its objects with the old functor's objects is required.
Source: Zheng, Construction 5.25, expanded by full-subcategory lifting.
(blueprint: lem-sf-exceptional-transport-functor-lift) -/
def TransportCoreData.liftSystemF
    (H : ∀ E : FieldStage.{u} l,
      (sequenceProperty l E X).FullSubcategory ⥤ coefficientSequenceDerived l E.carrier Y)
    (comparison : ∀ E : FieldStage.{u} l, d.F E ⋙ (sequenceProperty l E Y).ι ≅ H E) :
    TransportCoreData l Ω D hl c operation left :=
  let F' (E : FieldStage.{u} l) := (sequenceProperty l E Y).lift (H E)
    (fun K ↦ sequenceProperty_transport_of_iso l E Y
      ((comparison E).app K) ((d.F E).obj K).property)
  d.replaceSystemF l Ω D hl c operation left F' (fun E ↦
    ((sequenceProperty l E Y).fullyFaithfulι.whiskeringRight
      (sequenceProperty l E X).FullSubcategory).preimageIso (comparison E))

end WeilConjectures.ExceptionalIntegralScalar
