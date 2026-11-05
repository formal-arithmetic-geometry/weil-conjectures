/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-!
# Scalar extension of a localized inverse-image constant model

Source: Stacks Project, Tags 03EL, 0GMW and 093V
(blueprint: lem-sf-finite-field-local-tensor-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace FiniteFieldTensor

open SheafOfModules

set_option backward.isDefEq.respectTransparency false
open scoped ChangeOfRings

-- The tensor adjunction argument from ModulePullbackPushforwardAdjunction,
-- with the independent object and morphism universes of the pro-etale site.

end FiniteFieldTensor

end AlgebraicGeometry.Scheme
