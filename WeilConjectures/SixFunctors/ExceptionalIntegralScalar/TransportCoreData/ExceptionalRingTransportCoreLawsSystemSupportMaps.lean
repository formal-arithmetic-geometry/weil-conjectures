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
