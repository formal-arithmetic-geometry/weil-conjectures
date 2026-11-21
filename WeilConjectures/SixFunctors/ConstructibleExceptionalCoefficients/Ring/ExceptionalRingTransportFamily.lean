/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalIntegralScalarMates
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Ring.ExceptionalRingTransportCore
import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalTransportLeftShift

/-! # A coherent ring family before scalar comparisons

## References

* Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24, 5.26
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- Finite and integral adjunctions can be chosen with their actual normalized
reduction/limit transport, before constructing any coefficient scalar comparison. -/
theorem exists_exceptional_ring_transport_family
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∃ operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l),
      ∃ left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s),
        Nonempty (ExceptionalIntegralScalar.Transported l Ω D hl c operation left) := by
  obtain ⟨operation, left, shifts⟩ :=
    ExceptionalIntegralScalar.exists_exceptional_transport_left_shifts l Ω D hl f c
  obtain ⟨transport⟩ := exists_exceptional_transport_for_operations
    l Ω D hl f c operation left shifts
  exact ⟨operation, left, ⟨transport⟩⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
