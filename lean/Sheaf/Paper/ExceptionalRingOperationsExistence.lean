/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalIntegralScalarMates

/-! # Finite and integral operation families for exceptional transport -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- Finite and integral exceptional operation families with their compact-support
left realizations exist for every compactification. This is the operation and
realization subargument of the coherent transport construction.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-operations-existence).

Proof: construct each positive finite level from the finite exceptional
adjunction and its proper/open compact-support realization. Construct the
integral level by restricting the actual proper/open system adjunction to the
complete finite-Tor categories and conjugating through reduction/total-limit
reconstruction. The resulting operation and left realization are indexed by
all finite and integral ring stages; positive finite levels use exponent n+1.
Empty schemes use the zero adjunction. Uniform bounds and shifts are retained
as part of the chosen realizations, but scalar comparisons are not asserted.
-/
theorem exists_exceptional_ring_operations
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    ∃ operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l),
      ∃ left : ∀ s : RingStage.{u} l,
        LeftRealization.{u} l Ω c s (operation s), True := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
