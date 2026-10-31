/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SystemCompactSupportRestrictionData
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.longLine false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
/-- Construction of normalized open data by identity on extension-by-zero summands and sheafification. (blueprint: lem-sp-system-open-restriction-data-existence) -/
theorem systemOpenRestrictionData (l : ℕ) [Fact l.Prime] {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (c : RestrictionIdentifications.{u} l) :
    ∃ (g : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l) (a : B.rings ⟶ C.rings), GeometricSquare a j)
      (o : ∀ (B C : Etale.SystemProjection.Coefficients.{u} l) (a : B.rings ⟶ C.rings), OpenComparison (g B C a)), True := by
  sorry
end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
