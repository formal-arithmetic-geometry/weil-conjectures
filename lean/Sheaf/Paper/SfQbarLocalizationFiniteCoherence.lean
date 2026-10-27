/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.SfQbarLocalizationFiniteData
import Sheaf.Paper.SfQbarLocalizationFiniteTail

/-! # Normalized finite localization coefficient compatibility

Source: the finite-stage compatibility steps of the localization argument.
(blueprint: lem-sf-qbar-localization-finite-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section Descent
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Z U : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
  (i : Z ⟶ X) (j : U ⟶ X) [i.IsOver (Spec (.of D.k))] [j.IsOver (Spec (.of D.k))]
  [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ z : Z, Invertible (l : Z.residueField z)]
  [∀ t : U, Invertible (l : U.residueField t)]

/-- The normalized finite localization packages admit coherent coefficient actions.
Source: algebraically closed-stage localization proof, steps 1--2 and the finite
normalizations in step 5 (blueprint: lem-sf-qbar-localization-finite-coherence).

Proof: obtain the finite operation package from
`sfQbarLocalizationFiniteBase_exists`. For that fixed package, obtain the
remaining exact, shift, adjunction, mate, unit and counit fields from
`sfQbarLocalizationFiniteTail_exists`. The two records have disjoint field
sets whose concatenation is exactly `SfQbarLocalizationFiniteData`; assemble
them field by field. The two existence results isolate the finite operation
construction from its coherence verification and make no claim about the
descended category or arbitrary common-stage morphisms.
-/
theorem sfQbarLocalizationFiniteCoherence
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    Nonempty (SfQbarLocalizationFiniteData l Ω D hl i j) := by
  obtain ⟨B⟩ := sfQbarLocalizationFiniteBase_exists l Ω D hl i j hij
  obtain ⟨T⟩ := sfQbarLocalizationFiniteTail_exists l Ω D hl i j hij B
  exact ⟨{
    finiteLocalization := B.finiteLocalization
    openAction := B.openAction
    closedAction := B.closedAction
    closedAction_finite := B.closedAction_finite
    openPull := B.openPull
    closedPull := B.closedPull
    openPull_finite := B.openPull_finite
    closedPull_finite := B.closedPull_finite
    openPull_beta := B.openPull_beta
    closedPull_beta := B.closedPull_beta
    openExact := T.openExact
    closedExact := T.closedExact
    openPullExact := T.openPullExact
    closedPullExact := T.closedPullExact
    finiteOpenAdjunction := T.finiteOpenAdjunction
    finiteClosedAdjunction := T.finiteClosedAdjunction
    finiteOpenAdjunction_normalization := T.finiteOpenAdjunction_normalization
    finiteClosedAdjunction_normalization := T.finiteClosedAdjunction_normalization
    closedAction_beta := T.closedAction_beta
    openShift_finite := T.openShift_finite
    closedShift_finite := T.closedShift_finite
    openPullShift_finite := T.openPullShift_finite
    closedPullShift_finite := T.closedPullShift_finite
    finiteOpenAdjunction_shift := T.finiteOpenAdjunction_shift
    finiteClosedAdjunction_shift := T.finiteClosedAdjunction_shift
    openUnit := T.openUnit
    openCounit := T.openCounit
    closedUnit := T.closedUnit
    closedCounit := T.closedCounit
    openUnit_finite := T.openUnit_finite
    openCounit_finite := T.openCounit_finite
    closedUnit_finite := T.closedUnit_finite
    closedCounit_finite := T.closedCounit_finite
  }⟩

end Descent
end WeilConjectures
