/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
import WeilConjectures.AlgebraicGeometry.Completed.CompletedFiniteExchangeCoordinates
import all WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-!
# Finite etale origins after completed-coefficient open extension

Source: blueprint thm-cbc-complete-proetale, proof step 2; Stacks 03DI, 09AF and 0GL1.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

-- Localize an exact adjunction directly; no resolution choices are needed.

-- Restriction along a coefficient isomorphism has identity sectionwise round trips.
section RestrictionEquivalence
variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{t + 1}}

end RestrictionEquivalence

attribute [local instance] finiteRes_additive finiteRes_limits finiteRes_colimits

end AlgebraicGeometry.Scheme
