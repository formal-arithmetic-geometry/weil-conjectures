/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalRingTransportCoreData

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
