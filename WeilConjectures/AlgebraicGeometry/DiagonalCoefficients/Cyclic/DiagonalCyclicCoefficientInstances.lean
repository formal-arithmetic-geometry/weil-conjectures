/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-! # Named Ext existence for diagonal coefficient sheaves

Ext existence follows from Mathlib's Ext existence for Grothendieck abelian categories.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Coefficient sheaves have Ext, by `IsGrothendieckAbelian.hasExt`, with the proof
shared by name. -/
theorem cyclicCoefficientHasExt (l : ℕ) [Fact l.Prime] (W : Scheme.{u}) :
    HasExt.{u + 1} (DiagonalMod l W) := by
  infer_instance

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
