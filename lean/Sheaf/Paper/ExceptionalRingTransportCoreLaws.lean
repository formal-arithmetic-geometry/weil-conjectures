/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalRingTransportCoreData
import Sheaf.Paper.ExceptionalRingTransportCoreLawsSystem
import Sheaf.Paper.ExceptionalRingTransportCoreLawsEvaluation
import Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization

/-! # Compatibility laws for exceptional integral transport

This interface supplies the equations and normalization predicates attached to the
object and functor data of `TransportCoreData`.  Together they form the full
`ExceptionalIntegralScalar.Transported` record.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26
(blueprint: lem-sf-exceptional-ring-transport-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

structure TransportCoreLaws
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
      LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) where
  support (E : FieldStage.{u} l) :
    d.F E ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g
  adjunction_eq (E : FieldStage.{u} l) :
    (operation (.integral E)).adjunction =
      ((PurReconstruction.realizedAdjunction (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.adjunction E)).ofNatIsoLeft
        (d.realizeF E).symm).ofNatIsoRight (d.realizeG E).symm
  reductionF_eq (E : FieldStage.{u} l)
      (K : C.{u} l Ω X (.integral E)) :
    (d.reductionF E).hom.app K =
      (d.reconstruction E false).equivalence.functor.map ((d.realizeF E).hom.app K) ≫
        (d.reconstruction E false).equivalence.counit.app
          ((d.F E).obj ((d.reconstruction E true).equivalence.functor.obj K))
  reductionG_eq (E : FieldStage.{u} l)
      (K : C.{u} l Ω Y (.integral E)) :
    (d.reductionG E).hom.app K =
      (d.reconstruction E true).equivalence.functor.map ((d.realizeG E).hom.app K) ≫
        (d.reconstruction E true).equivalence.counit.app
          ((d.G E).obj ((d.reconstruction E false).equivalence.functor.obj K))
  evaluation_unit (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E X).FullSubcategory) :
    ((d.reconstruction E true).evaluation n).map ((d.adjunction E).unit.app K) ≫
      (d.evaluationG E n).hom.app ((d.F E).obj K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).G.map
        ((d.evaluationF E n).hom.app K) =
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.unit.app
        (((d.reconstruction E true).evaluation n).obj K)
  evaluation_counit (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E Y).FullSubcategory) :
    (d.evaluationF E n).hom.app ((d.G E).obj K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).F.map
        ((d.evaluationG E n).hom.app K) ≫
      (operation (.finite E ⟨n + 1, Nat.succ_pos n⟩)).adjunction.counit.app
        (((d.reconstruction E false).evaluation n).obj K) =
      ((d.reconstruction E false).evaluation n).map ((d.adjunction E).counit.app K)
  evaluation_support (E : FieldStage.{u} l) (n : ℕ)
      (K : (sequenceProperty l E X).FullSubcategory) :
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) Y).ι.map
        ((d.evaluationF E n).hom.app K) ≫
      (left (.finite E ⟨n + 1, Nat.succ_pos n⟩)).hom.app
        (((d.reconstruction E true).evaluation n).obj K) ≍
      (IntegralSystemRealization.supportEvaluation l E.carrier (d.operations E) c n).hom.app
        K.obj
  integralLeft_normalized (E : FieldStage.{u} l)
      (K : C.{u} l Ω X (.integral E)) :
    (sfIntegralConstructible l E.carrier Y).ι.map ((d.integralLeft E).hom.app K) =
      (left (.integral E)).hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)
  inputGood (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier X
      ((d.reconstruction E true).equivalence.functor.obj K).obj
  openGood (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier c.Z
      ((IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i).obj
        ((d.reconstruction E true).equivalence.functor.obj K).obj)
  integral_system_normalized (E : FieldStage.{u} l)
      (K : C.{u} l Ω X (.integral E)) :
    (finiteTorConstructibleIntegral l E.carrier Y).ι.map
        ((d.realizeF E).inv.app K) ≫ (left (.integral E)).hom.app K ≍
      (IntegralSystemRealization.RealizationModel.push l E.carrier
          (d.realizations E).realizationModel c.g).hom.app
        ((IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i).obj
          ((d.reconstruction E true).equivalence.functor.obj K).obj) ≫
        (PurCompactSupport.push (PurCompactSupport.completed l E.carrier) c.g).map
          (((d.realizations E).openRealization c.i
              (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance)
              ((d.reconstruction E true).equivalence.functor.obj K).obj
              (inputGood E K) (openGood E K)).hom ≫
            (PurCompactSupport.openExtension (PurCompactSupport.completed l E.carrier)
              c.i).mapDerivedCategory.map
              ((eqToIso (congrArg
                  (fun H ↦ H.obj ((d.reconstruction E true).equivalence.functor.obj K))
                  (d.reconstruction E true).limit)).inv ≫
                (finiteTorConstructibleIntegral l E.carrier X).ι.map
                  ((d.reconstruction E true).equivalence.unitIso.inv.app K)))

/-- The compatibility laws are supplied by the normalized system transport and
proper/open realization calculations.  Each field is a strict part of the final
transport record; no operation or functor is chosen here.
(blueprint: lem-sf-exceptional-ring-transport-core-laws)
(blueprint: lem-sf-exceptional-ring-transport-core)
-/
theorem exists_exceptional_transport_core_laws
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
      LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) :
    Nonempty (TransportCoreLaws l Ω D hl c operation left d) := by
  obtain ⟨hs⟩ := exists_exceptional_transport_core_system_laws
    l Ω D hl f c operation left d
  obtain ⟨he⟩ := exists_exceptional_transport_core_evaluation_laws
    l Ω D hl f c operation left d
  obtain ⟨hn⟩ := exists_exceptional_transport_core_normalization_laws
    l Ω D hl f c operation left d
  exact ⟨{
    support := hs.support
    adjunction_eq := hs.adjunction_eq
    reductionF_eq := hs.reductionF_eq
    reductionG_eq := hs.reductionG_eq
    evaluation_unit := he.evaluation_unit
    evaluation_counit := he.evaluation_counit
    evaluation_support := he.evaluation_support
    integralLeft_normalized := hn.integralLeft_normalized
    inputGood := hn.inputGood
    openGood := hn.openGood
    integral_system_normalized := hn.integral_system_normalized }⟩

end WeilConjectures.ExceptionalIntegralScalar
