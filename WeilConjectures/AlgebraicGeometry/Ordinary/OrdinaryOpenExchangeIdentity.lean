/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryOpenModuleIdentity
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Identity normalization for ordinary open exchange

Source: Stacks Project, Tags 03DI, 07A7 and 099N; the identity part of
proof step 7 of `thm-cbc-complete-proetale`.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] cbcDatumOrdinaryTransport AdicCoefficientDatum.pullId
  cbcModulePullId cbcOpenShriek cbcUnderivedInverseExchange cbcDerivedInverseExchange

attribute [local irreducible] cbcOrdinaryExchange
  cbcDatumOrdinaryExchange

end AlgebraicGeometry.Scheme
