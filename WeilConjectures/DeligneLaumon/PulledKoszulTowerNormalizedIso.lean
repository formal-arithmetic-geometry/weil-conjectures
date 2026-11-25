/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PulledKoszulTowerModel.PulledKoszulTowerNormalization
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerScalarComparison
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerQuotientComparison
import WeilConjectures.DeligneLaumon.BalancedFiniteTower.BalancedFiniteTowerKoszulAugmentation

/-! # Normalized ordinary pullback of the principal Koszul tower

This file is reserved for the normalized ordinary pullback of the principal Koszul tower, given by
the scalar and adjacent-transition calculation in the pulled Koszul tower chain comparison.

## References

* Stacks Project, Tags 03EL and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.PrincipalKoszulStrictReplacement
open WeilConjectures.PulledKoszulTowerModel

namespace WeilConjectures

end WeilConjectures
