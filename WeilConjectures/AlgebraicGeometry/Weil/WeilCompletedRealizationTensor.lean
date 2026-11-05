/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedConstantModuleTensor
import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedModuleTensorTransport
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Tensor comparison for completed constant realization

Source: Stacks Project, Modules on Sites, Tags 03D8, 03EK and 0GMW.
(blueprint: lem-weil-pbc-completed-realization-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] completedCechModulesEquiv pbcCompletedComparison
  completedKoszulConstant completedKoszulOne completedCechCoefficientUnit

end AlgebraicGeometry.Scheme
