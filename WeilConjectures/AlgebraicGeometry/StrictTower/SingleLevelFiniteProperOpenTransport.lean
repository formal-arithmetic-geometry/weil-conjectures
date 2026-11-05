/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars
public import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteCoefficientClopenAlpha
import all WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateSiteTransport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality
import all WeilConjectures.CategoryTheory.RightDerivedPlusCube
import all WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import all WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization

/-! # Finite coefficient transport of the single-level proper/open mate

This is the coefficient-realization step between the finite site comparison and
strict-tower evaluation. It contains no strict-tower object or evaluation functor.

Source: Stacks Project, Tags 03DA, 07A7, 099R and 09AF
(blueprint: lem-cbc-single-level-finite-proper-open-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

end AlgebraicGeometry.ProEtale.StrictTower
