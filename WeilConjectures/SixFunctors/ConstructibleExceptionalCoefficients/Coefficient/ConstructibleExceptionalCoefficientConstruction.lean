/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientConstructionData

import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Coefficient.ConstructibleExceptionalCoefficientStages
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalLeftRefinements

/-! # Normalized coefficient adjunction construction before coherence

The coefficient records retain the literal localization and common representative-arrow
normalizations supplied by coefficient-stage construction; the assembly preserves them.

## References

* [Zheng, Lemma 5.22]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
namespace ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Construct the normalized adjunctions and individual invertible coefficient mates.
No identity or composition law for these comparisons is asserted here. -/
theorem exists_coefficient_construction (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (CoefficientConstruction.{u, v} l Ω D hl (f := f)) := by
  obtain ⟨R, F, M, H⟩ := exists_coefficient_stages.{u, v} l Ω D hl f
  obtain ⟨N⟩ := exists_coefficient_left_refinements.{u, v} l Ω D hl f R F M H
  refine ⟨{
    ring := R
    fields := F
    common := M
    localizationIdentity := H.localizationIdentity
    refinements := ?_ }⟩
  exact {
    refinement := fun r s ↦ refinementComparisonOfLeft.{u, v} l Ω
      (R.operation _ s) (R.operation _ s) (N.left r s) (N.leftShift r s)
    refinement_normalized := N.normalized
    refinementRational := N.rational
    refinementCommon := N.common }

end ConstructibleExceptionalCoefficients
end WeilConjectures
