/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreData
public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreLawsNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.ProperSupportStepBounds
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenSupportStepBounds

/-! The actual proper/open support comparison, before choosing strict representatives.
Source: Zheng, Constructions 5.17 and 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-transport-actual-support-comparison). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

private theorem sequenceProperty_of_good
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (T : Scheme.{u})
    (N : coefficientSequenceDerived l E.carrier T)
    (hN : IntegralSystemRealization.Good l E.carrier T N) : sequenceProperty l E T N := by
  refine ⟨hN.1, ?_⟩
  obtain ⟨a, b, c, d, hab, hcd, h⟩ := hN.2.1
  refine ⟨a, b, c, d, hab, hcd, fun n ↦ ?_⟩
  refine ⟨⟨(h n).1, c, d, (h n).2.2⟩, ?_, ?_, (h n).2.2⟩
  · apply (DerivedCategory.isGE_iff _ a).2
    intro i hi
    by_contra hz
    exact (not_le_of_gt hi) ((h n).2.1 hz).1
  · apply (DerivedCategory.isLE_iff _ b).2
    intro i hi
    by_contra hz
    exact (not_le_of_gt hi) ((h n).2.1 hz).2

section
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

/-- The actual system compact-support composite preserves the reconstruction domain.
Proof: convert the input's common cohomological and Tor bounds to Good. The open
support theorem preserves Good, and the proper support theorem preserves it again.
Use the inverse reconstruction only for the independent integral constructibility
input to those theorems. The output's common bounds give the sequence property.
Source: Zheng, Constructions 5.17 and 5.25; proper and open support bounds.
(blueprint: lem-sf-exceptional-transport-actual-support-comparison). -/
theorem TransportCoreData.actualSupport_preserves (E : FieldStage.{u} l)
    (K : (sequenceProperty l E X).FullSubcategory) :
    sequenceProperty l E Y
      (((sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g).obj K) := by
  let U : Over (Spec (.of D.k)) := Over.mk (X ↘ Spec (.of D.k))
  let V : Over (Spec (.of D.k)) := Over.mk (c.g ≫ Y ↘ Spec (.of D.k))
  let W : Over (Spec (.of D.k)) := Over.mk (Y ↘ Spec (.of D.k))
  let j : U ⟶ V := Over.homMk c.i (by
    change c.i ≫ c.g ≫ Y ↘ Spec (.of D.k) = X ↘ Spec (.of D.k)
    rw [← Category.assoc, ← c.comm, comp_over f (Spec (.of D.k))])
  let p : V ⟶ W := Over.homMk c.g
  have : LocallyOfFiniteType U.hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of D.k)))
  have : QuasiCompact U.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of D.k)))
  have : LocallyOfFiniteType V.hom :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y ↘ Spec (.of D.k)))
  have : QuasiCompact V.hom :=
    inferInstanceAs (QuasiCompact (c.g ≫ Y ↘ Spec (.of D.k)))
  have : LocallyOfFiniteType W.hom :=
    inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of D.k)))
  have : QuasiCompact W.hom := inferInstanceAs (QuasiCompact (Y ↘ Spec (.of D.k)))
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion c.i)
  have : QuasiCompact j.left :=
    IntegralSystemRealization.compactOpenQuasiCompact c inferInstance
  have : IsProper p.left := inferInstanceAs (IsProper c.g)
  let A := (d.reconstruction E true).equivalence.inverse.obj K
  have hopen := IntegralSystemRealization.openSupportStep_bounds l E.carrier D hl
    (d.operations E) j K.obj (sequenceProperty_good l E X K.obj K.property)
    A.obj A.property.1
  have hproper := IntegralSystemRealization.properSupportStep_bounds l E.carrier D hl
    (d.operations E) p _ hopen.1 _ hopen.2
  exact sequenceProperty_of_good l E Y _ hproper.1

/-- Compare the actual support lift with the integral compact-support operation.
Proof: the reconstruction limit equation identifies its realized source with the
proper/open system composite followed by limit. Proper realization, natural open
realization and the reconstruction unit identify this with integral compact support.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-transport-actual-support-comparison). -/
def TransportCoreData.actualSupportRealization (E : FieldStage.{u} l) :
    let H := (sequenceProperty l E Y).lift
      ((sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g)
      (d.actualSupport_preserves l Ω D hl c operation left E)
    PurReconstruction.realized (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence H ⋙
        (finiteTorConstructibleIntegral l E.carrier Y).ι ≅
      (finiteTorConstructibleIntegral l E.carrier X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c := by
  dsimp only
  let rX := d.reconstruction E true
  let rY := d.reconstruction E false
  let R := rX.equivalence.functor ⋙ (sequenceProperty l E X).ι
  let J := IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i
  let P := IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g
  let LX := coefficientSequenceLimit l E.carrier X
  let LZ := coefficientSequenceLimit l E.carrier c.Z
  let LY := coefficientSequenceLimit l E.carrier Y
  let j := (PurCompactSupport.openExtension (PurCompactSupport.completed l E.carrier)
    c.i).mapDerivedCategory
  let p := PurCompactSupport.push (PurCompactSupport.completed l E.carrier) c.g
  let eopen : R ⋙ J ⋙ LZ ≅ R ⋙ LX ⋙ j :=
    NatIso.ofComponents (fun K ↦ (d.realizations E).openRealization c.i
      (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance) (R.obj K)
      (d.inputGood l Ω D hl c operation left E K)
      (d.openGood l Ω D hl c operation left E K))
      (fun m ↦ d.openRealization_naturality l Ω D hl c operation left E m)
  let einput : R ⋙ LX ≅ (finiteTorConstructibleIntegral l E.carrier X).ι :=
    Functor.isoWhiskerLeft rX.equivalence.functor (eqToIso rX.limit).symm ≪≫
      Functor.isoWhiskerRight rX.equivalence.unitIso.symm
        (finiteTorConstructibleIntegral l E.carrier X).ι
  let H := (sequenceProperty l E Y).lift
    ((sequenceProperty l E X).ι ⋙ J ⋙ P)
    (d.actualSupport_preserves l Ω D hl c operation left E)
  have hsource :
      PurReconstruction.realized rX.equivalence rY.equivalence H ⋙
          (finiteTorConstructibleIntegral l E.carrier Y).ι = R ⋙ J ⋙ P ⋙ LY :=
    congrArg (fun Q ↦ (rX.equivalence.functor ⋙ H) ⋙ Q) rY.limit
  exact eqToIso hsource ≪≫
    Functor.isoWhiskerLeft (R ⋙ J)
      (IntegralSystemRealization.RealizationModel.push l E.carrier
        (d.realizations E).realizationModel c.g) ≪≫
    Functor.isoWhiskerRight eopen p ≪≫
    Functor.isoWhiskerRight einput (j ⋙ p)

/-- Every transport datum has a natural support comparison, without a support-law
hypothesis. This asserts an isomorphism, so it is independent of object representatives.
Proof: compare both realized functors with integral compact support, lift the comparison
through fully faithful integral inclusion, then cancel the reconstruction equivalences.
Finally include the strict full-subcategory support lift back into the ambient category.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-transport-actual-support-comparison). -/
def TransportCoreData.actualSupportComparison (E : FieldStage.{u} l) :
    d.F E ⋙ (sequenceProperty l E Y).ι ≅
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g := by
  let rX := d.reconstruction E true
  let rY := d.reconstruction E false
  let H := (sequenceProperty l E Y).lift
    ((sequenceProperty l E X).ι ⋙
      IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
        IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g)
    (d.actualSupport_preserves l Ω D hl c operation left E)
  let e : PurReconstruction.realized rX.equivalence rY.equivalence (d.F E) ≅
      PurReconstruction.realized rX.equivalence rY.equivalence H :=
    ((finiteTorConstructibleIntegral l E.carrier Y).fullyFaithfulι.whiskeringRight
      (finiteTorConstructibleIntegralCategory l E.carrier X)).preimageIso
        ((Functor.isoWhiskerRight (d.realizeF E).symm
          (finiteTorConstructibleIntegral l E.carrier Y).ι) ≪≫ left (.integral E) ≪≫
          (d.actualSupportRealization l Ω D hl c operation left E).symm)
  let e' : rX.equivalence.functor ⋙ d.F E ≅ rX.equivalence.functor ⋙ H :=
    Functor.fullyFaithfulCancelRight rY.equivalence.inverse e
  let e'' : d.F E ≅ H :=
    (Functor.isoWhiskerRight rX.equivalence.counitIso.symm (d.F E)) ≪≫
      Functor.isoWhiskerLeft rX.equivalence.inverse e' ≪≫
        Functor.isoWhiskerRight rX.equivalence.counitIso H
  exact Functor.isoWhiskerRight e'' (sequenceProperty l E Y).ι

end
end WeilConjectures.ExceptionalIntegralScalar
