/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface

/-! # Small Ext with the canonical sheaf abelian structures -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- Small Ext for module sheaves, with the diagonal interface's canonical
abelian structure fixed in this theorem's type. -/
theorem kummerModuleHasExt (R : Type (u + 1)) [CommRing R] (W : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} R)) := by
  exact geoCartierModuleExt R W

/-- Small Ext for abelian sheaves, with the diagonal interface's canonical
abelian structure fixed in this theorem's type. -/
theorem kummerAbHasExt (W : Scheme.{u}) : HasExt.{u + 1} (DiagonalAb W) := by
  exact geoCartierIntegralExt W

end AlgebraicGeometry.ProEtale
