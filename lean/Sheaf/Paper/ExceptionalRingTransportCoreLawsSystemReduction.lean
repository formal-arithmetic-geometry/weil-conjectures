/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalRingTransportCoreData

/-! The reduction comparison part of the exceptional integral transport system laws.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-reduction-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

/--
The two reduction comparison equations are the final system-level components
of strict-system transport.  The first transports the `F` comparison through
the false-side reconstruction counit, and the second does the analogous thing
for `G` through the true-side counit.  They are isolated together because both
are the same reconstruction-counit calculation on opposite endpoints.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-reduction-laws).
-/
theorem exists_exceptional_transport_core_system_reduction_laws
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
    Nonempty ((∀ E : FieldStage.{u} l,
      ∀ K : C.{u} l Ω X (.integral E),
        (d.reductionF E).hom.app K =
          (d.reconstruction E false).equivalence.functor.map ((d.realizeF E).hom.app K) ≫
            (d.reconstruction E false).equivalence.counit.app
              ((d.F E).obj ((d.reconstruction E true).equivalence.functor.obj K))) ∧
      (∀ E : FieldStage.{u} l,
      ∀ K : C.{u} l Ω Y (.integral E),
        (d.reductionG E).hom.app K =
          (d.reconstruction E true).equivalence.functor.map ((d.realizeG E).hom.app K) ≫
            (d.reconstruction E true).equivalence.counit.app
              ((d.G E).obj ((d.reconstruction E false).equivalence.functor.obj K)))) := by
  sorry

end WeilConjectures.ExceptionalIntegralScalar
