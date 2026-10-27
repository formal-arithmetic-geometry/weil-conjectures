/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.ClassicalLisseWeilFrontierData

/-! # Classical Weil restriction along finite-field frontiers

Source: blueprint `thm-zl-real-mixed-by-curves`, proof paragraphs 6--7;
BS 6.8.4, 6.8.14, 6.8.15
(blueprint: lem-zl-classical-successive-restrictions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ZlFrontier
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
variable (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The finite quotient-normalized restriction comparison respects successive
locally closed restrictions with the specified raw and derived compositors.
Source: BS 6.8.4(1),(4), 6.8.15; blueprint thm-zl-real-mixed-by-curves, paragraph 7
(blueprint: lem-zl-classical-successive-restrictions).

Proof: expand RestrictionComparison.iso as the finite bridge's stage comparison,
finitePull, stagePull, and the inverse target stage comparison. For two restrictions,
the intermediate stage comparison cancels with its inverse by naturality. Apply
the finite bridge's unit_square to the remaining maps. At each finite quotient,
the unit of successive inverse images equals the unit of their composite; the
specified raw compositor is obtained from these units by the pullback adjunction.
The completed-system reconstruction and rationalization carry this same equality
to the raw rational category. PullNormalized identifies these units with those of
the completed derived inverse images, so their corresponding derived compositor
is zlPullComp. Cancelling the endpoint stage comparisons gives exactly the stated
iso equation. This argument is natural in the chosen lattice, uses no Frobenius
stability, and also applies to the empty source and zero rank.
-/
theorem classical_successive_restrictions
    (R : Realization D l Ω) (S : ProEtale.CompletedLisse.System.{u} l)
    (A : LisseRealization.Family D l (Fact.out : l ≠ D.p))
    (C : RestrictionComparison D l Ω R S A)
    (T : PerAdic.Base D.k) (M : sfCommonStageHeart l T.scheme Ω)
    (P : PartitionData D l Ω R T M) :
    SuccessiveRestrictions D l Ω R S A C T M P := by sorry

end WeilConjectures.ZlFrontier
