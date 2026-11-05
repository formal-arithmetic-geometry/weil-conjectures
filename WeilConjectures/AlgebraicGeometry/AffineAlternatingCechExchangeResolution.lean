/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechResolutionCore
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechResolutionExchange

/-! # An alternating acyclic resolution with ordinary exchange

Source: Stacks Project, Tags 02KG and 02KH; blueprint finite affine Čech calculation, Steps 1--2
of `lem-pc-affine-alternating-cech-pinned-mate`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

end AlgebraicGeometry
