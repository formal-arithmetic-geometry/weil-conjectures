/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreSupportComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated

/-! Constructive strict normalization of exceptional system support.
Source: Zheng, Constructions 5.17 and 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-support-functor-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

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

/-- Normalize support using the actual comparison constructed from the realization
fields. This construction requires no equation for the initial arbitrary datum.
Source: Zheng, Constructions 5.17 and 5.25; explicit lift and adjunction transport.
(blueprint: lem-sf-exceptional-transport-actual-support-normalization). -/
def TransportCoreData.normalizeActualSupport :
    TransportCoreData l Ω D hl c operation left :=
  d.normalizeSupport l Ω D hl c operation left
    (d.actualSupportComparison l Ω D hl c operation left)

/-- The explicitly constructed datum satisfies strict support on objects and maps.
Proof: normalization sets its left functor to the actual full-subcategory lift.
The operations are retained, and inclusion forgets only the membership proofs.
Source: Zheng, Constructions 5.17 and 5.25.
(blueprint: lem-sf-exceptional-transport-actual-support-normalization). -/
theorem TransportCoreData.normalizeActualSupport_support (E : FieldStage.{u} l) :
    let d' := d.normalizeActualSupport l Ω D hl c operation left
    d'.F E ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d'.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d'.operations E) c.g := rfl

end SupportNormalization
end WeilConjectures.ExceptionalIntegralScalar
