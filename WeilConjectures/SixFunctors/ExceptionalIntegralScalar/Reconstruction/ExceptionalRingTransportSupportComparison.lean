/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreData
public import WeilConjectures.SixFunctors.IntegralSystemRealization.ExceptionalSupportLimitComparison
public import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

/-! # Whole-system support comparison for exceptional transport

Source: Zheng, Construction 5.25 and Proposition 5.26. The comparison is a natural
isomorphism; it does not assert equality of an arbitrarily represented functor.
(blueprint: lem-sf-exceptional-transport-support-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
open IntegralSystemRealization

/-- Identify a reconstruction reduction with the canonical reduction to the same limit.
Source: Zheng, Construction 5.25; uniqueness of left adjoints.
(blueprint: lem-sf-exceptional-transport-support-comparison) -/
def Reconstruction.canonicalReduction
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (W : Scheme.{u})
    (R : Reconstruction l E W) :
    R.equivalence.functor ⋙ (sequenceProperty l E W).ι ≅
      (finiteTorConstructibleIntegral l E.carrier W).ι ⋙
        (IntegralSystemRealization.calculus l E.carrier W).reduction :=
  eqToIso R.reduction ≪≫
    Functor.isoWhiskerLeft (finiteTorConstructibleIntegral l E.carrier W).ι
      (R.calculus.adjunction.leftAdjointUniq
        (IntegralSystemRealization.calculus l E.carrier W).adjunction)

/-- Recover a normalized system by canonical reduction of its reconstructed limit.
Source: Zheng, Construction 5.25; the reconstruction counit and adjoint uniqueness.
(blueprint: lem-sf-exceptional-transport-support-comparison) -/
def Reconstruction.canonicalSequence
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (W : Scheme.{u})
    (R : Reconstruction l E W) :
    (sequenceProperty l E W).ι ≅
      R.equivalence.inverse ⋙ (finiteTorConstructibleIntegral l E.carrier W).ι ⋙
        (IntegralSystemRealization.calculus l E.carrier W).reduction :=
  (Functor.isoWhiskerRight R.equivalence.counitIso (sequenceProperty l E W).ι ≪≫
      Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerLeft R.equivalence.inverse (R.canonicalReduction l E W)

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

/-- The left transport is naturally isomorphic to the prescribed open/proper system.
Proof: rewrite the source sequence functor as canonical reduction of its reconstructed
limit. The support-domain theorem gives normalization after both support steps.
The open mate, inverse reconstruction unit, proper limit comparison and recorded
compact-support realization identify its total limit with the integral operation.
The given realization of F and the endpoint limit equations give the same total
limit for F. Apply canonical reduction to this natural isomorphism and compose
with the two invertible actual reconstruction counits. This compares whole systems
and retains naturality, rather than inferring arrows from finite evaluations.
Every inverse is that of a specified isomorphism; no arbitrary data witness is chosen.
Source: Zheng, Construction 5.25 and Proposition 5.26; Stacks Tags 0941 and 0D6E.
(blueprint: lem-sf-exceptional-transport-support-comparison) -/
def TransportCoreData.supportComparison (E : FieldStage.{u} l) :
    d.F E ⋙ (sequenceProperty l E Y).ι ≅
      (sequenceProperty l E X).ι ⋙
        Operations.shriek l E.carrier (d.operations E) c.i ⋙
          Operations.push l E.carrier (d.operations E) c.g := by
  let RX := d.reconstruction E true
  let RY := d.reconstruction E false
  let I := (finiteTorConstructibleIntegral l E.carrier X).ι
  let J := Operations.shriek l E.carrier (d.operations E) c.i
  let P := Operations.push l E.carrier (d.operations E) c.g
  let R := (IntegralSystemRealization.calculus l E.carrier Y).reduction
  let L := coefficientSequenceLimit l E.carrier Y
  let A := d.F E ⋙ (sequenceProperty l E Y).ι
  let B := RX.equivalence.inverse ⋙ I ⋙
    (IntegralSystemRealization.calculus l E.carrier X).reduction ⋙ J ⋙ P
  let einput := Functor.isoWhiskerRight (RX.canonicalSequence l E X) (J ⋙ P)
  let elimit := Functor.isoWhiskerLeft RX.equivalence.inverse
    (finiteTorSupportLimitComparison l E.carrier D hl (d.operations E)
      (d.realizations E).realizationModel c)
  let eleft := Functor.isoWhiskerLeft RX.equivalence.inverse
    (Functor.isoWhiskerRight (d.integralLeft E) (sfIntegralConstructible l E.carrier Y).ι)
  let ereal := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft RX.equivalence.inverse (d.realizeF E) ≪≫
      Functor.isoWhiskerRight RX.equivalence.counitIso
        (d.F E ⋙ RY.equivalence.inverse) ≪≫ Functor.leftUnitor _)
    (finiteTorConstructibleIntegral l E.carrier Y).ι
  let eA : A ⋙ L ≅ RX.equivalence.inverse ⋙ (operation (.integral E)).F ⋙
      (finiteTorConstructibleIntegral l E.carrier Y).ι :=
    (eqToIso (congrArg (fun H ↦ d.F E ⋙ H) RY.limit)).symm ≪≫ ereal.symm
  let e : B ⋙ L ≅ A ⋙ L := elimit ≪≫ eleft.symm ≪≫ eA.symm
  let εA := Functor.whiskerLeft A
    (IntegralSystemRealization.calculus l E.carrier Y).adjunction.counit
  have : ∀ K, IsIso (εA.app K) := fun K ↦
    ((purNormalizedReconstructionOfScheme l E.carrier Y
      (IntegralSystemRealization.calculus l E.carrier Y)).1 _ ((d.F E).obj K).property.1).2
  let εB := Functor.whiskerLeft B
    (IntegralSystemRealization.calculus l E.carrier Y).adjunction.counit
  have : ∀ K, IsIso (εB.app K) := fun K ↦
    ((purNormalizedReconstructionOfScheme l E.carrier Y
      (IntegralSystemRealization.calculus l E.carrier Y)).1 _
        (basicSupportDomain_of_constructible l E.carrier D hl (d.operations E) c
          (RX.equivalence.inverse.obj K).obj
          (RX.equivalence.inverse.obj K).property.1).1.2.2.1).2
  let a : A ⋙ L ⋙ R ≅ A :=
    NatIso.ofComponents (fun K ↦ asIso (εA.app K)) (fun v ↦ εA.naturality v)
  let b : B ⋙ L ⋙ R ≅ B :=
    NatIso.ofComponents (fun K ↦ asIso (εB.app K)) (fun v ↦ εB.naturality v)
  exact (b.symm ≪≫ Functor.isoWhiskerRight e R ≪≫ a).symm ≪≫ einput.symm

end WeilConjectures.ExceptionalIntegralScalar
