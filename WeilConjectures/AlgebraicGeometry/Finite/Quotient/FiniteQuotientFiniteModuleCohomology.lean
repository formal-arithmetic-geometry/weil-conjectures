/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleLocalWeakSerre
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCohomologyFiltrationTriangle
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement

/-! # Finite etale-local cohomology of the successor coefficient quotient

Source: Stacks Project, Tags 094I, 094H and 09C2
(blueprint: lem-weil-pbc-finite-quotient-finite-module-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

-- Retain the published named chart-map binder in the conclusion.

end AlgebraicGeometry.Scheme
