/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreData
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated

/-! Object part of the exceptional transport support identity.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-support-law-objects).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

private theorem normalizedCoefficientSequence_of_iso
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (T : Scheme.{u})
    {M N : coefficientSequenceDerived l E.carrier T} (e : M ≅ N)
    (hM : IsNormalizedCoefficientSequence l E.carrier T M) :
    IsNormalizedCoefficientSequence l E.carrier T N := by
  intro m n h P
  let a := (coefficientSequenceDerivedEvaluation l E.carrier T n).mapIso e
  let b := (coefficientSequenceDerivedEvaluation l E.carrier T m).mapIso e
  have comm (f : (coefficientSequenceDerivedEvaluation l E.carrier T n).obj N ⟶ P) :
      (coefficientSequenceDerivedTransition l E.carrier T h).app M ≫
          (normalizedDVRRes l E.carrier T h).map (a.hom ≫ f) =
        b.hom ≫ (coefficientSequenceDerivedTransition l E.carrier T h).app N ≫
          (normalizedDVRRes l E.carrier T h).map f := by
    rw [Functor.map_comp, ← Category.assoc]
    simpa only [a, b, Functor.comp_map, Functor.mapIso_hom, Category.assoc] using
      congrArg (fun t ↦ t ≫ (normalizedDVRRes l E.carrier T h).map f)
        ((coefficientSequenceDerivedTransition l E.carrier T h).naturality e.hom).symm
  constructor
  · intro f g hfg
    apply (cancel_epi a.hom).1
    apply (hM h P).1
    dsimp only at hfg ⊢
    rw [comm, comm, hfg]
  · intro g
    obtain ⟨f, hf⟩ := (hM h P).2 (b.hom ≫ g)
    refine ⟨a.inv ≫ f, ?_⟩
    apply (cancel_epi b.hom).1
    rw [← comm]
    simpa only [Iso.hom_inv_id_assoc] using hf

/-- The prescribed sequence property is unchanged by replacing a system by an
isomorphic one, with the same cohomological and Tor bounds.
Proof: naturality of the specified transition maps conjugates the normalization
bijections by the evaluation isomorphisms. At every level constructibility and
cohomological bounds are invariant under isomorphism. For Tor amplitude, compose
each representative's comparison with the inverse evaluation isomorphism; the
same K-flat tensors and the same interval then apply.
Source: Zheng, Constructions 5.17 and 5.25; restriction to the normalized bounded domain.
(blueprint: lem-sf-exceptional-support-functor-normalization) -/
theorem sequenceProperty_of_iso
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (T : Scheme.{u})
    {M N : coefficientSequenceDerived l E.carrier T} (e : M ≅ N)
    (hM : sequenceProperty l E T M) : sequenceProperty l E T N := by
  refine ⟨normalizedCoefficientSequence_of_iso l E T e hM.1, ?_⟩
  obtain ⟨a, b, c, d, hab, hcd, h⟩ := hM.2
  refine ⟨a, b, c, d, hab, hcd, fun n ↦ ?_⟩
  let q := (coefficientSequenceDerivedEvaluation l E.carrier T n).mapIso e
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) T) :=
    (finite_ctf_isTriangulated l E.carrier (n + 1) (Nat.succ_pos n) T).1
  have : ((coefficientSequenceDerivedEvaluation l E.carrier T n).obj M).IsGE a := (h n).2.1
  have : ((coefficientSequenceDerivedEvaluation l E.carrier T n).obj M).IsLE b := (h n).2.2.1
  refine ⟨ObjectProperty.prop_of_iso _ q (h n).1,
    DerivedCategory.TStructure.t.isGE_of_iso q a,
    DerivedCategory.TStructure.t.isLE_of_iso q b, (h n).2.2.2.1, ?_⟩
  intro L P hL f hf hP A i hi
  exact (h n).2.2.2.2 L P (hL.map (fun z ↦ z ≪≫ q.symm)) f hf hP A i hi

private theorem fullSubcategory_lift_unique
    {A B : Type*} [Category A] [Category B] (P : ObjectProperty B)
    (F : A ⥤ P.FullSubcategory) (H : A ⥤ B) (hH : ∀ K, P (H.obj K))
    (h : F ⋙ P.ι = H) : F = P.lift H hH := by
  subst H
  rfl

section SupportNormalization

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

/-- Change the representative of the transported left functor by an explicit natural
isomorphism. Transport its adjunction and all comparisons involving that functor;
the reduction comparisons are derived canonically from the updated realizations.
The operations and reconstructions remain the supplied ones. This is a construction
from data, without selecting a witness of an existence theorem.
Source: Zheng, Constructions 5.17 and 5.25; transport along natural isomorphisms.
(blueprint: lem-sf-exceptional-support-functor-normalization) -/
def TransportCoreData.rebaseF
    (H : ∀ E : FieldStage.{u} l, (sequenceProperty l E X).FullSubcategory ⥤
      (sequenceProperty l E Y).FullSubcategory)
    (e : ∀ E : FieldStage.{u} l, d.F E ≅ H E) :
    TransportCoreData l Ω D hl c operation left :=
  { d with
    F := H
    adjunction := fun E ↦ (d.adjunction E).ofNatIsoLeft (e E)
    realizeF := fun E ↦ d.realizeF E ≪≫
      Functor.isoWhiskerLeft (d.reconstruction E true).equivalence.functor
        (Functor.isoWhiskerRight (e E) (d.reconstruction E false).equivalence.inverse)
    evaluationF := fun E n ↦
      Functor.isoWhiskerRight (e E).symm ((d.reconstruction E false).evaluation n) ≪≫
        d.evaluationF E n
    evaluationG := fun _ _ ↦ Adjunction.compatibleRightComparison _ _ _ }

/-- The strict support functor is the actual full-subcategory lift of the proper/open
composite, given its preservation of the prescribed normalized bounded category.
Source: Zheng, Constructions 5.15 and 5.17; restriction of the system support functor.
(blueprint: lem-sf-exceptional-support-functor-normalization) -/
def normalizedSystemSupport (E : FieldStage.{u} l)
    (h : ∀ K : (sequenceProperty l E X).FullSubcategory,
      sequenceProperty l E Y
        (((sequenceProperty l E X).ι ⋙
          IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
            IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g).obj K)) :
    (sequenceProperty l E X).FullSubcategory ⥤ (sequenceProperty l E Y).FullSubcategory :=
  (sequenceProperty l E Y).lift
    ((sequenceProperty l E X).ι ⋙
      IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
        IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g) h

/-- The constructed lift has the exact support equality, on objects and morphisms.
Proof: the lift retains the ambient objects and maps, and inclusion forgets only
membership proofs. Thus the functors are definitionally equal.
Source: Zheng, Construction 5.17; the induced full-subcategory functor.
(blueprint: lem-sf-exceptional-support-functor-normalization) -/
theorem normalizedSystemSupport_comp_ι (E : FieldStage.{u} l)
    (h : ∀ K : (sequenceProperty l E X).FullSubcategory,
      sequenceProperty l E Y
        (((sequenceProperty l E X).ι ⋙
          IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
            IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g).obj K)) :
    normalizedSystemSupport l Ω D hl c operation left d E h ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g := rfl

/-- The strict support equation characterizes the specified full-subcategory lift.
Proof: lifting an inclusion-composite recovers the original functor definitionally.
Substitute the ambient functor equality; the converse is the lift's defining equation.
Source: Zheng, Construction 5.17; uniqueness of the induced full-subcategory functor.
(blueprint: lem-sf-exceptional-support-functor-normalization) -/
theorem systemSupport_eq_iff (E : FieldStage.{u} l)
    (h : ∀ K : (sequenceProperty l E X).FullSubcategory,
      sequenceProperty l E Y
        (((sequenceProperty l E X).ι ⋙
          IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
            IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g).obj K)) :
    (d.F E ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g) ↔
    d.F E = normalizedSystemSupport l Ω D hl c operation left d E h := by
  constructor
  · exact fullSubcategory_lift_unique _ (d.F E) _ h
  · intro he
    rw [he]
    rfl

/-- An ambient support comparison already supplies preservation of the prescribed
sequence property, without turning its isomorphisms into object equalities.
Proof: the output of `d.F` has the property; transport it along the comparison's
component using `sequenceProperty_of_iso`.
Source: Zheng, Construction 5.17; invariance of the normalized bounded domain.
(blueprint: lem-sf-exceptional-support-functor-normalization) -/
theorem systemSupport_preservation_of_iso (E : FieldStage.{u} l)
    (e : d.F E ⋙ (sequenceProperty l E Y).ι ≅
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g)
    (K : (sequenceProperty l E X).FullSubcategory) :
    sequenceProperty l E Y
      (((sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g).obj K) :=
  sequenceProperty_of_iso l E Y (e.app K) ((d.F E).obj K).property

/-- Given an ambient support comparison, replace the left functor by its strict support
lift. Preservation follows from that isomorphism. Full faithfulness lifts it, and `rebaseF`
transports every dependent data field along it. No object is chosen by existence.
Source: Zheng, Constructions 5.17 and 5.25; full-subcategory restriction and transport.
(blueprint: lem-sf-exceptional-support-functor-normalization) -/
def TransportCoreData.normalizeSupport
    (e : ∀ E : FieldStage.{u} l,
      d.F E ⋙ (sequenceProperty l E Y).ι ≅
        (sequenceProperty l E X).ι ⋙
          IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
            IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g) :
    TransportCoreData l Ω D hl c operation left :=
  d.rebaseF l Ω D hl c operation left
    (fun E ↦ normalizedSystemSupport l Ω D hl c operation left d E
      (systemSupport_preservation_of_iso l Ω D hl c operation left d E (e E)))
    (fun E ↦ ((sequenceProperty l E Y).fullyFaithfulι.whiskeringRight
      (sequenceProperty l E X).FullSubcategory).preimageIso (e E))

/-- The explicitly normalized datum satisfies the entire support functor equation.
Proof: its `F` is the full-subcategory lift of the same operations' proper/open
composite. Inclusion forgets only the property proofs, so the equation is reflexive.
Source: Zheng, Construction 5.17; the induced normalized-system functor.
(blueprint: lem-sf-exceptional-support-functor-normalization) -/
theorem TransportCoreData.normalizeSupport_support
    (e : ∀ E : FieldStage.{u} l,
      d.F E ⋙ (sequenceProperty l E Y).ι ≅
        (sequenceProperty l E X).ι ⋙
          IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
            IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g)
    (E : FieldStage.{u} l) :
    let d' := d.normalizeSupport l Ω D hl c operation left e
    d'.F E ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d'.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d'.operations E) c.g := rfl

include d

/-- Isomorphic changes of the left functor obstruct the universal object equation
whenever their underlying objects differ. This uses actual transport data, not an
assumed support law: apply the proposed universal equation to d and its rebasing,
and compare their outputs against the unchanged proper/open support object.
Source: Zheng's induced-functor construction, tested against freedom of representatives.
(blueprint: lem-sf-exceptional-support-object-obstruction) -/
theorem not_forall_system_support_obj_of_iso
    (H : ∀ E : FieldStage.{u} l, (sequenceProperty l E X).FullSubcategory ⥤
      (sequenceProperty l E Y).FullSubcategory)
    (e : ∀ E : FieldStage.{u} l, d.F E ≅ H E)
    (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory)
    (hne : ((d.F E).obj K).obj ≠ ((H E).obj K).obj) :
    ¬ ∀ d' : TransportCoreData l Ω D hl c operation left,
      ∀ (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory),
        (d'.F E ⋙ (sequenceProperty l E Y).ι).obj K =
          ((sequenceProperty l E X).ι ⋙
            IntegralSystemRealization.Operations.shriek l E.carrier (d'.operations E) c.i ⋙
              IntegralSystemRealization.Operations.push
                l E.carrier (d'.operations E) c.g).obj K := by
  intro h
  exact hne ((h d E K).trans
    (h (d.rebaseF l Ω D hl c operation left H e) E K).symm)

/-- It suffices to change a single output object to an unequal isomorphic
representative to obstruct the universal equation. The isomorphism is an input in
the actual sequence full subcategory; no unequal representative is assumed to exist.
Proof: use `Functor.copyObj` with a pointwise update at K, and update the family of
functors at E. The resulting functors are naturally isomorphic to the old ones.
Apply the preceding obstruction to the updated family and the same unequal output.
Source: Zheng's induced-functor construction and Mathlib's explicit `Functor.copyObj`.
(blueprint: lem-sf-exceptional-support-object-obstruction) -/
theorem not_forall_system_support_obj_of_representative
    (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory)
    (N : (sequenceProperty l E Y).FullSubcategory)
    (e : (d.F E).obj K ≅ N) (hne : ((d.F E).obj K).obj ≠ N.obj) :
    ¬ ∀ d' : TransportCoreData l Ω D hl c operation left,
      ∀ (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory),
        (d'.F E ⋙ (sequenceProperty l E Y).ι).obj K =
          ((sequenceProperty l E X).ι ⋙
            IntegralSystemRealization.Operations.shriek l E.carrier (d'.operations E) c.i ⋙
              IntegralSystemRealization.Operations.push
                l E.carrier (d'.operations E) c.g).obj K := by
  classical
  let obj := Function.update (d.F E).obj K N
  have eobj (L : (sequenceProperty l E X).FullSubcategory) :
      (d.F E).obj L ≅ obj L := by
    by_cases h : L = K
    · subst L
      simpa only [obj, Function.update_self] using e
    · simp only [obj, Function.update_of_ne h]
      exact Iso.refl _
  let H₀ := (d.F E).copyObj obj eobj
  let H := Function.update d.F E H₀
  have eH (E' : FieldStage.{u} l) : d.F E' ≅ H E' := by
    by_cases h : E' = E
    · subst E'
      simpa only [H, Function.update_self] using (d.F E).isoCopyObj obj eobj
    · simp only [H, Function.update_of_ne h]
      exact Iso.refl _
  apply not_forall_system_support_obj_of_iso l Ω D hl c operation left d H eH E K
  simpa only [H, Function.update_self, H₀, Functor.copyObj_obj, obj] using hne

end SupportNormalization

/- STATEMENT-DISPUTED: `TransportCoreData.F` is an arbitrary representative, related
by isomorphisms to the integral operations. Isomorphisms do not imply equality of
objects. `TransportCoreData.rebaseF` preserves all the data-field types while
changing that representative. `not_forall_system_support_obj_of_iso` proves the
resulting obstruction whenever the underlying outputs differ. For the constructed
strict lift, `TransportCoreData.normalizeSupport_support` proves the full support
identity from an ambient comparison, deriving preservation from it. The current
hypotheses do not specify that lift or its object representatives. -/

/--
The strict-system support comparison on objects at one fixed field stage.
It is the object component used with the corresponding map component to
assemble the support functor equality.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-support-law-objects).
-/
theorem exceptional_transport_core_system_support_obj
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
    (d : TransportCoreData l Ω D hl c operation left)
    (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory) :
    (d.F E ⋙ (sequenceProperty l E Y).ι).obj K =
      ((sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g).obj K := by
  sorry

end WeilConjectures.ExceptionalIntegralScalar
