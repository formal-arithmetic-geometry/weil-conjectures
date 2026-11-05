/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedConstantProjection.CompletedConstantResidueData
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
/-! # Canonical finite projections of completed constant realization

Source: Stacks Project, Modules on Sites, Tags 03EK and 093J--093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
namespace CompletedConstantProjection

attribute [local irreducible] constantMap

attribute [local irreducible] residueComparison

attribute [local irreducible] projection

attribute [local irreducible] extensionResidue

end CompletedConstantProjection

end AlgebraicGeometry.Scheme
