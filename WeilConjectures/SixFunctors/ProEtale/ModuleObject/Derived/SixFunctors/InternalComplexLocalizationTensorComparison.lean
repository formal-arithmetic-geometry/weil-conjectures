/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedTensorData

/-! # Complex and homotopy localization tensor maps

The strict monoidal homotopy quotient and its identity-component comparison with
complex localization identify the two tensor maps on complex representatives.
(blueprint: lem-sfb-internal-complex-localization-tensor-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing

end AlgebraicGeometry.ProEtale.CondensedRing
