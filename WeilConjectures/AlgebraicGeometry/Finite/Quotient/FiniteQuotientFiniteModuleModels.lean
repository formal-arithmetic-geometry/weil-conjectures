/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData

import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientFiniteModuleCohomology
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleBoundedModels

/-! # Finite-module models after one coefficient extension

Source: Stacks Tags 09C2, 094I and 094G
(blueprint: lem-weil-pbc-finite-quotient-finite-module-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
