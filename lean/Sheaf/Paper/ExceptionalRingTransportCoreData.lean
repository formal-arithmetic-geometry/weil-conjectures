/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalRingTransportCorePostData

/-! # Data fields for exceptional integral transport

This interface isolates the object, functor, adjunction, and comparison-isomorphism
fields of the normalized exceptional transport record.  Its compatibility equations
are supplied separately by `ExceptionalRingTransportCoreLaws`.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

structure TransportCoreData
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s)) where
  leftShift (s : RingStage.{u} l) : (left s).hom.CommShift ℤ
  reconstruction (E : FieldStage.{u} l) (side : Bool) :
    Reconstruction l E (endpoint X Y side)
  operations (E : FieldStage.{u} l) : IntegralSystemRealization.Operations l E.carrier
  realizations (E : FieldStage.{u} l) :
    IntegralSystemRealization.Realizations l E.carrier D (operations E)
  F (E : FieldStage.{u} l) : (sequenceProperty l E X).FullSubcategory ⥤
    (sequenceProperty l E Y).FullSubcategory
  G (E : FieldStage.{u} l) : (sequenceProperty l E Y).FullSubcategory ⥤
    (sequenceProperty l E X).FullSubcategory
  adjunction (E : FieldStage.{u} l) : F E ⊣ G E
  realizeF (E : FieldStage.{u} l) : (operation (.integral E)).F ≅
    PurReconstruction.realized (reconstruction E true).equivalence
      (reconstruction E false).equivalence (F E)
  realizeG (E : FieldStage.{u} l) : (operation (.integral E)).G ≅
    PurReconstruction.realized (reconstruction E false).equivalence
      (reconstruction E true).equivalence (G E)
  reductionF (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ (reconstruction E false).equivalence.functor ≅
      (reconstruction E true).equivalence.functor ⋙ F E
  reductionG (E : FieldStage.{u} l) :
    (operation (.integral E)).G ⋙ (reconstruction E true).equivalence.functor ≅
      (reconstruction E false).equivalence.functor ⋙ G E
  evaluationF (E : FieldStage.{u} l) (n : ℕ) :
    F E ⋙ (reconstruction E false).evaluation n ≅
      (reconstruction E true).evaluation n ⋙
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F
  evaluationG (E : FieldStage.{u} l) (n : ℕ) :
    G E ⋙ (reconstruction E true).evaluation n ≅
      (reconstruction E false).evaluation n ⋙
        (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G
  integralLeft (E : FieldStage.{u} l) :
    (operation (.integral E)).F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier

/-- The data fields have the construction described in the transport proof.
(blueprint: lem-sf-exceptional-ring-transport-core-data)
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26.  The strict-system transport, reconstruction equivalences, and integral
proper/open realization are assembled first; all displayed functors and
isomorphisms are the resulting data. (blueprint: lem-sf-exceptional-ring-transport-core)
-/
theorem exists_exceptional_transport_core_data
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
    Nonempty (TransportCoreData l Ω D hl c operation left) := by
  classical
  obtain ⟨pre⟩ :=
    exists_exceptional_transport_reconstructions l Ω D hl f c operation left
  let leftShift := pre.leftShift
  let recon := pre.reconstruction
  let operations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Operations l E.carrier :=
    fun E ↦ (IntegralSystemRealization.integralCompactificationSystemRealization
      l E.carrier D hl).choose
  have hrealizations : ∀ E : FieldStage.{u} l,
      Nonempty (IntegralSystemRealization.Realizations l E.carrier D (operations E)) := by
    intro E
    exact (IntegralSystemRealization.integralCompactificationSystemRealization
      l E.carrier D hl).choose_spec
  let realizations : ∀ E : FieldStage.{u} l,
      IntegralSystemRealization.Realizations l E.carrier D (operations E) :=
    fun E ↦ (hrealizations E).some
  obtain ⟨p⟩ := exists_exceptional_transport_post_data l Ω D hl f c operation left
    recon operations realizations
  refine ⟨{
    leftShift := leftShift,
    reconstruction := recon,
    operations := operations,
    realizations := realizations,
    F := p.F,
    G := p.G,
    adjunction := p.adjunction,
    realizeF := p.realizeF,
    realizeG := p.realizeG,
    reductionF := p.reductionF,
    reductionG := p.reductionG,
    evaluationF := p.evaluationF,
    evaluationG := p.evaluationG,
    integralLeft := p.integralLeft }⟩

end WeilConjectures.ExceptionalIntegralScalar
