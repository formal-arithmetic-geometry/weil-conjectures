/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module
public import Sheaf.Paper.ExceptionalRingTransportCoreData
/-! Proper/open normalization laws for exceptional integral transport.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26. (blueprint: lem-sf-exceptional-ring-transport-core-normalization-laws) -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
structure TransportCoreNormalizationLaws
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
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) where
  integralLeft_normalized (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
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
/-- The proper/open normalization equations are supplied by integral realization.
Proof: transport the prescribed integral realization and retain its Good domains.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26. (blueprint: lem-sf-exceptional-ring-transport-core-normalization-laws) -/
theorem exists_exceptional_transport_core_normalization_laws
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) :
    Nonempty (TransportCoreNormalizationLaws l Ω D hl c operation left d) := by
  sorry
end WeilConjectures.ExceptionalIntegralScalar
