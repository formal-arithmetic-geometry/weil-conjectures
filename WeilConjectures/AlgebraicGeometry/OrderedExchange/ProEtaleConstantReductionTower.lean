/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels
import WeilConjectures.AlgebraicGeometry.OrderedExchange.ConstantPerfectQuotientProjection
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Perfect projection for strict constant-coefficient reduction towers

Source: Stacks Tags 0944 and 099M; smooth-purity blueprint, fix-lem-exchanges,
Step 4 (blueprint: lem-sp-completion-mate-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (f : U ⟶ V)

attribute [local irreducible] projection

attribute [local irreducible] diagonalPullIso

attribute [local irreducible] directLimitIso

attribute [local irreducible] reconstruction

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

attribute [local irreducible] H

end AlgebraicGeometry.Scheme.OrderedExchange

namespace CategoryTheory.AdicSites.OrderedExchangeInterface

end CategoryTheory.AdicSites.OrderedExchangeInterface
