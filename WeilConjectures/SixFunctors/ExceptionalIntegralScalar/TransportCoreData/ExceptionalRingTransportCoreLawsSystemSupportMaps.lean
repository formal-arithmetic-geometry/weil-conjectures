/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCoreLawsSystemSupportObjects
public import WeilConjectures.CategoryTheory.SixFunctors.FunctorObjectConjugation
public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.Reconstruction.ExceptionalRingTransportSupportComparison
public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportFunctorLift

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

omit α in
omit α in
omit α in
end Conjugation

/- STATEMENT-DISPUTED: `TransportCoreData.F` is an arbitrary functor supplied with
comparison isomorphisms, not a prescribed strict lift of the support composite.
`TransportCoreData.conjugateSystemF` preserves every required data field while
conjugating its maps by arbitrary object automorphisms. Whenever a family changes
a map, `not_forall_system_support_map_of_conjugation` refutes the universal claim.
The object comparison alone cannot supply this missing normalization. -/

/-- Construct the prescribed support functor and transport the existing data to it.
Its objects and maps are those of the actual open/proper composite. Membership in
sequenceProperty follows from the proved whole-system support comparison, and the
adjunction and comparisons are transported through the fully faithful inclusion.
No equality between the old and prescribed object representatives is assumed.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-ring-transport-core-system-support-law-maps) -/
def TransportCoreData.normalizeCanonicalSupport : TransportCoreData l Ω D hl c operation left :=
  d.liftSystemF l Ω D hl c operation left
    (fun E ↦ d.systemSupportFunctor l Ω D hl c operation left E)
    (fun E ↦ d.supportComparison l Ω D hl c operation left E)

/-- The explicitly constructed transport has the required strict support functor.
Proof: its full-subcategory lift retains the actual support objects and maps.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-ring-transport-core-system-support-law-maps) -/
theorem TransportCoreData.normalizeCanonicalSupport_support (E : FieldStage.{u} l) :
    let d' := d.normalizeCanonicalSupport l Ω D hl c operation left
    d'.F E ⋙ (sequenceProperty l E Y).ι =
      d'.systemSupportFunctor l Ω D hl c operation left E := rfl

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

/-- A nonnatural conjugation obstructs a universal strict support map law.
Proof: the conjugate retains the operations and all object representatives, so the
two displayed right-hand sides agree, including the equality transports by proof
irrelevance. The claimed laws would therefore identify the two maps. This
contradicts the previous theorem. Object identifications are an explicit hypothesis;
no support law is used.
Source: the conjugation test for Zheng, Construction 5.25.
(blueprint: lem-sf-exceptional-system-support-conjugation-obstruction) -/
theorem not_forall_system_support_map_of_conjugation (E : FieldStage.{u} l)
    {K K' : (sequenceProperty l E X).FullSubcategory} (u : K ⟶ K')
    (hne : (α E K).inv ≫ (d.F E).map u ≫ (α E K').hom ≠ (d.F E).map u)
    (objects : ∀ (d' : TransportCoreData l Ω D hl c operation left)
      (K : (sequenceProperty l E X).FullSubcategory),
      (d'.F E ⋙ (sequenceProperty l E Y).ι).obj K =
        ((sequenceProperty l E X).ι ⋙
          IntegralSystemRealization.Operations.shriek l E.carrier (d'.operations E) c.i ⋙
            IntegralSystemRealization.Operations.push l E.carrier (d'.operations E) c.g).obj K) :
    ¬ ∀ d' : TransportCoreData l Ω D hl c operation left,
      (d'.F E ⋙ (sequenceProperty l E Y).ι).map u =
        eqToHom (objects d' K) ≫
        ((sequenceProperty l E X).ι ⋙
          IntegralSystemRealization.Operations.shriek l E.carrier (d'.operations E) c.i ⋙
            IntegralSystemRealization.Operations.push l E.carrier (d'.operations E) c.g).map u ≫
        eqToHom (objects d' K').symm := by
  intro h
  have he := h (d.conjugateSystemF l Ω D hl c operation left α)
  change (sequenceProperty l E Y).ι.map
    ((α E K).inv ≫ (d.F E).map u ≫ (α E K').hom) = _ at he
  have he' : (sequenceProperty l E Y).ι.map
      ((α E K).inv ≫ (d.F E).map u ≫ (α E K').hom) =
      (d.F E ⋙ (sequenceProperty l E Y).ι).map u := he.trans (h d).symm
  exact hne ((sequenceProperty l E Y).ι.map_injective he')

/-- The prescribed support composite, before lifting it to the full subcategory.
Source: Zheng, Constructions 4.1 and 5.25.
(blueprint: lem-sf-exceptional-system-support-explicit-normalization) -/
abbrev TransportCoreData.systemSupportFunctor (E : FieldStage.{u} l) :=
  (sequenceProperty l E X).ι ⋙
    IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
      IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g

/-- The support-map identity for the explicitly normalized datum. The prior
universal assertion for arbitrary representatives was false: conjugation can change
its maps while preserving every field of TransportCoreData. Here normalizeCanonicalSupport
constructs the actual support lift and transports all dependent comparisons.
Proof: the map of the full-subcategory lift is the prescribed composite map.
Source: Zheng, Constructions 4.1 and 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-ring-transport-core-system-support-law-maps) -/
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
    let d' := d.normalizeCanonicalSupport l Ω D hl c operation left
    (d'.F E ⋙ (sequenceProperty l E Y).ι).map u =
      ((sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d'.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d'.operations E) c.g).map u := rfl

end WeilConjectures.ExceptionalIntegralScalar
