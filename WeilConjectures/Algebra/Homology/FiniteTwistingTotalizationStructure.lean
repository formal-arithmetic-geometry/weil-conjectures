/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationFiltration

/-! # Structural finite twisting totalization

This helper isolates the construction of the filtered totalization and its
square-zero differential from the separate K-flatness argument.
-/

/- The explicit structure assembles the supplied matrix and tail filtration data. -/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
variable {R} {a b : ℤ}

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Assemble the triangular matrix data and the tail data into the realization
record. The two lower constructions separately handle the Maurer--Cartan
matrix calculation and the filtered quotient construction.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24 (steps 1-2 of lem-trf-filtered-mapping-cylinder-step).
(blueprint: lem-trf-finite-filtered-totalization-structure) -/
theorem exists_finiteTwistingTotalization_structure
    (a b : ℤ) (D : FiniteTwistingFamily R a b) :
    Nonempty (FiniteTwistingTotalization D) := by
  obtain ⟨X⟩ := exists_finiteTwistingMatrixData a b D
  obtain ⟨F⟩ := exists_finiteTwistingFiltrationData a b D X
  let M : FiniteTwistingTotalization D :=
    { P := X.P
      F := F.F
      coordinates := X.coordinates
      gradedIso := F.gradedIso
      differential := X.differential
      finite := F.finite
      bottomWeight := F.bottomWeight
      topWeight := F.topWeight
      tailCoordinates := F.tailCoordinates
      tailInclusion := F.tailInclusion
      degreewiseSplit := F.degreewiseSplit
      gradedProjection := F.gradedProjection
      outside := F.outside }
  exact ⟨M⟩

end CochainComplex
