/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Zero
public import WeilConjectures.AlgebraicGeometry.TorsionAbelianBaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# Blueprint statements

lem-weil-pbc-reduction-projective-space.
-/

@[expose] public section

universe u_reduction

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Blueprint: lem-weil-pbc-reduction-projective-space. -/
theorem hasTorsionAbelianBaseChange_projectiveSpace_of_projectiveLine
    (_h : ∀ S : Scheme.{u_reduction}, HasTorsionAbelianBaseChange (ProjectiveLine S ↘ S))
    (T : Scheme.{u_reduction}) (n : ℕ) :
    IsProper (ProjectiveSpace.projectiveLinePowProj n T) ∧
      HasTorsionAbelianBaseChange (ProjectiveSpace.projectiveLinePowProj n T) ∧
      IsProper (ℙ(ULift.{u_reduction} (Fin (n + 1)); T) ↘ T) ∧
      HasTorsionAbelianBaseChange (ℙ(ULift.{u_reduction} (Fin (n + 1)); T) ↘ T) := by
  sorry

end AlgebraicGeometry.Etale
