/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ExceptionalSystemInterfaces

/-! # Construction of the pro-etale compact-support object -/

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

/-! The construction follows Zheng Construction 5.15: extension by zero on
strict pro-etale coefficient systems, followed by the universal derived image
of the proper factor.  The finite evaluation and localization equations are
constructed before passing to the derived category; the site equivalences are
used to transport the prescribed evaluation packages. -/
theorem exceptionalProCompactSupport_exists
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    (hX : ExceptionalSystemSiteEquivalence CX)
    (hY : ExceptionalSystemSiteEquivalence CY)
    (hZ : ExceptionalSystemSiteEquivalence CZ) :
    Nonempty (ExceptionalProCompactSupport O ell c
      CX.proEvaluation CY.proEvaluation CZ.proEvaluation) := by
  sorry

end AlgebraicGeometry
