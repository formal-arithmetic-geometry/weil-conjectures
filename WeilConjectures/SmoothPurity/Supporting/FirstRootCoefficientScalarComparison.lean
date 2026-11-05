/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralLocalModels
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement

/-! # Root-normalized scalar extension in exponent one

Source: coefficient Tate twists, scalar extension of the integral first line;
Stacks Project, Modules on Sites, Tags 03EK and 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open CategoryTheory.Limits
open scoped ChangeOfRings

attribute [local irreducible] firstRootIntegralIso

attribute [local irreducible] firstRootExtensionIso

attribute [local irreducible] SheafOfModules.changeOfRingsHomOfUniverses
  SheafOfModules.scalarExtensionSection

attribute [local irreducible] firstRootTowerIso

attribute [local irreducible] firstRootTransportIso

attribute [local irreducible] firstRootTargetIso

attribute [local irreducible] firstRootCoefficientIso

end WeilConjectures
