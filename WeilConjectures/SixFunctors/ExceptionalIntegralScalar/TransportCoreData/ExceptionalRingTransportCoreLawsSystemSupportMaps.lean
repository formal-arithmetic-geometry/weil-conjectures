/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCoreLawsSystemSupportObjects
public import WeilConjectures.CategoryTheory.SixFunctors.FunctorObjectConjugation

/-! Map part of the exceptional transport support identity.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-support-law-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

section Conjugation

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
  (α : ∀ (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory),
    (d.F E).obj K ≅ (d.F E).obj K)

/-- Conjugating the system functor preserves every field required by `TransportCoreData`.
The adjunction is transported by the explicit natural isomorphism. Whiskering that
isomorphism transports `realizeF` and `evaluationF`; the reduction comparison is
derived from `realizeF`. Recompute the right evaluation mate for these transported
data, so its dependent unit and counit equations are retained. All other fields stay fixed.
Source: Zheng, Construction 5.25, and Mathlib's `Adjunction.ofNatIsoLeft`.
(blueprint: lem-sf-exceptional-system-support-conjugation-obstruction) -/
def TransportCoreData.conjugateSystemF : TransportCoreData l Ω D hl c operation left :=
  { d with
    F := fun E ↦ (d.F E).copyObj (d.F E).obj (α E)
    adjunction := fun E ↦ (d.adjunction E).ofNatIsoLeft
      ((d.F E).isoCopyObj (d.F E).obj (α E))
    realizeF := fun E ↦ d.realizeF E ≪≫
      Functor.isoWhiskerLeft (d.reconstruction E true).equivalence.functor
        (Functor.isoWhiskerRight ((d.F E).isoCopyObj (d.F E).obj (α E))
          (d.reconstruction E false).equivalence.inverse)
    evaluationF := fun E n ↦
      Functor.isoWhiskerRight ((d.F E).isoCopyObj (d.F E).obj (α E)).symm
        ((d.reconstruction E false).evaluation n) ≪≫ d.evaluationF E n
    evaluationG := fun _ _ ↦ Adjunction.compatibleRightComparison _ _ _ }

/-- The update retains the underlying system objects exactly.
Source: the explicit conjugation construction.
(blueprint: lem-sf-exceptional-system-support-conjugation-obstruction) -/
theorem TransportCoreData.conjugateSystemF_obj
    (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory) :
    ((d.conjugateSystemF l Ω D hl c operation left α).F E).obj K = (d.F E).obj K := rfl

/-- The update changes system maps by the prescribed object automorphisms.
Source: the explicit conjugation construction.
(blueprint: lem-sf-exceptional-system-support-conjugation-obstruction) -/
theorem TransportCoreData.conjugateSystemF_map (E : FieldStage.{u} l)
    {K K' : (sequenceProperty l E X).FullSubcategory} (u : K ⟶ K') :
    ((d.conjugateSystemF l Ω D hl c operation left α).F E).map u =
      (α E K).inv ≫ (d.F E).map u ≫ (α E K').hom := rfl

/-- The data alone do not determine maps even up to heterogeneous equality.
Proof: apply the proposed unique-map property to the original datum and to its
explicit conjugate. Their object representatives are identical. Full faithfulness
of the subcategory inclusion then identifies the original and conjugated maps,
contradicting the given nonnaturality witness.
Source: Zheng, Construction 5.25, tested against object conjugation.
(blueprint: lem-sf-exceptional-system-support-conjugation-obstruction) -/
theorem not_unique_system_map_of_conjugation (E : FieldStage.{u} l)
    {K K' : (sequenceProperty l E X).FullSubcategory} (u : K ⟶ K')
    (hne : (α E K).inv ≫ (d.F E).map u ≫ (α E K').hom ≠ (d.F E).map u) :
    ¬ ∀ d' : TransportCoreData l Ω D hl c operation left,
      HEq ((d'.F E ⋙ (sequenceProperty l E Y).ι).map u)
        ((d.F E ⋙ (sequenceProperty l E Y).ι).map u) := by
  intro h
  have he := eq_of_heq (h (d.conjugateSystemF l Ω D hl c operation left α))
  apply hne
  exact (sequenceProperty l E Y).ι.map_injective he

/-- A nonnatural conjugation obstructs a universal strict support map law.
Proof: the conjugate retains the operations and all object representatives, so the
two displayed right-hand sides agree, including the equality transports by proof
irrelevance. The claimed laws would therefore identify the two maps. This
contradicts the previous theorem. No support-map law is used as a proof dependency.
Source: the conjugation test for Zheng, Construction 5.25.
(blueprint: lem-sf-exceptional-system-support-conjugation-obstruction) -/
theorem not_forall_system_support_map_of_conjugation (E : FieldStage.{u} l)
    {K K' : (sequenceProperty l E X).FullSubcategory} (u : K ⟶ K')
    (hne : (α E K).inv ≫ (d.F E).map u ≫ (α E K').hom ≠ (d.F E).map u) :
    ¬ ∀ d' : TransportCoreData l Ω D hl c operation left,
      (d'.F E ⋙ (sequenceProperty l E Y).ι).map u =
        eqToHom (exceptional_transport_core_system_support_obj
          l Ω D hl f c operation left d' E K) ≫
        ((sequenceProperty l E X).ι ⋙
          IntegralSystemRealization.Operations.shriek l E.carrier (d'.operations E) c.i ⋙
            IntegralSystemRealization.Operations.push l E.carrier (d'.operations E) c.g).map u ≫
        eqToHom (exceptional_transport_core_system_support_obj
          l Ω D hl f c operation left d' E K').symm := by
  intro h
  have he := h (d.conjugateSystemF l Ω D hl c operation left α)
  change (sequenceProperty l E Y).ι.map
    ((α E K).inv ≫ (d.F E).map u ≫ (α E K').hom) = _ at he
  have he' : (sequenceProperty l E Y).ι.map
      ((α E K).inv ≫ (d.F E).map u ≫ (α E K').hom) =
      (d.F E ⋙ (sequenceProperty l E Y).ι).map u := he.trans (h d).symm
  exact hne ((sequenceProperty l E Y).ι.map_injective he')

omit α in
/-- The prescribed support composite, before lifting it to the full subcategory.
Source: Zheng, Constructions 4.1 and 5.25.
(blueprint: lem-sf-exceptional-system-support-explicit-normalization) -/
abbrev TransportCoreData.systemSupportFunctor (E : FieldStage.{u} l) :=
  (sequenceProperty l E X).ι ⋙
    IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
      IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g

omit α in
/-- Given the support comparison and object identifications, normalize the functor
and transport its existing adjunction and comparisons. This constructs a new datum;
it does not assert that the original arbitrary datum was normalized already.
Source: Zheng, Construction 5.25, with the explicit fully faithful normalization.
(blueprint: lem-sf-exceptional-system-support-explicit-normalization) -/
def TransportCoreData.normalizeSystemF
    (comparison : ∀ E : FieldStage.{u} l,
      d.F E ⋙ (sequenceProperty l E Y).ι ≅
        d.systemSupportFunctor l Ω D hl c operation left E)
    (objects : ∀ (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory),
      (d.F E ⋙ (sequenceProperty l E Y).ι).obj K =
        (d.systemSupportFunctor l Ω D hl c operation left E).obj K) :
    TransportCoreData l Ω D hl c operation left :=
  d.conjugateSystemF l Ω D hl c operation left (fun E ↦
    (d.F E).comparisonNormalizer (sequenceProperty l E Y).ι
      (sequenceProperty l E Y).fullyFaithfulι
      (d.systemSupportFunctor l Ω D hl c operation left E) (comparison E) (objects E))

omit α in
/-- The constructed datum satisfies the full strict support identity.
Proof: its functor is the conjugate by `comparisonNormalizer`. Apply the generic
normalization theorem to the fully faithful sequence-subcategory inclusion. The
operations in the prescribed support functor are unchanged by the structure update.
Source: Zheng, Construction 5.25, expanded using fully faithful preimages.
(blueprint: lem-sf-exceptional-system-support-explicit-normalization) -/
theorem TransportCoreData.normalizeSystemF_support
    (comparison : ∀ E : FieldStage.{u} l,
      d.F E ⋙ (sequenceProperty l E Y).ι ≅
        d.systemSupportFunctor l Ω D hl c operation left E)
    (objects : ∀ (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory),
      (d.F E ⋙ (sequenceProperty l E Y).ι).obj K =
        (d.systemSupportFunctor l Ω D hl c operation left E).obj K)
    (E : FieldStage.{u} l) :
    let d' := d.normalizeSystemF l Ω D hl c operation left comparison objects
    d'.F E ⋙ (sequenceProperty l E Y).ι =
      d'.systemSupportFunctor l Ω D hl c operation left E := by
  exact (d.F E).copyObj_comparisonNormalizer_comp
    (sequenceProperty l E Y).ι (sequenceProperty l E Y).fullyFaithfulι
    (d.systemSupportFunctor l Ω D hl c operation left E) (comparison E) (objects E)

end Conjugation

/- STATEMENT-DISPUTED: `TransportCoreData.F` is an arbitrary functor supplied with
comparison isomorphisms, not a prescribed strict lift of the support composite.
`TransportCoreData.conjugateSystemF` preserves every required data field while
conjugating its maps by arbitrary object automorphisms. Whenever a family changes
a map, `not_forall_system_support_map_of_conjugation` refutes the universal claim.
The object comparison alone cannot supply this missing normalization. -/

/--
The strict-system support comparison on morphisms at one fixed field stage.
Together with the object component, this is the map premise of `Functor.ext`.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-support-law-maps).
-/
theorem exceptional_transport_core_system_support_map
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
    (E : FieldStage.{u} l)
    {K K' : (sequenceProperty l E X).FullSubcategory} (u : K ⟶ K') :
    (d.F E ⋙ (sequenceProperty l E Y).ι).map u =
      eqToHom (exceptional_transport_core_system_support_obj
        l Ω D hl f c operation left d E K) ≫
      ((sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g).map u ≫
      eqToHom (exceptional_transport_core_system_support_obj
        l Ω D hl f c operation left d E K').symm := by
  sorry

end WeilConjectures.ExceptionalIntegralScalar
