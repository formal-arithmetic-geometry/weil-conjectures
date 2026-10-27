/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalSystemInterfaces

/-! # Construction of proper/open comparison data -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

variable {O : Type (u + 1)} [CommRing O] {ell : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O ell c}
  (CX : ExceptionalSystemSiteComparison O ell X S.PX)
  (CY : ExceptionalSystemSiteComparison O ell Y S.PY)
  (CZ : ExceptionalSystemSiteComparison O ell c.Z S.PZ)

/-! The proper and open pullback squares are assembled from the ordinary
strict-system maps and then localized.  Their mate equations and finite
evaluation equations give the coherence predicate in the comparison record. -/
theorem exceptionalSystemCompactificationComparison_exists
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY)
    (hZ : ExceptionalSystemSiteEquivalence CZ)
    (P : ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation) :
    Nonempty (ExceptionalSystemCompactificationComparison S CX CY CZ P) := by
  sorry

end AlgebraicGeometry
