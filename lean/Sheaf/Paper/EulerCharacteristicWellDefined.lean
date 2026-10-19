/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.BigOperators.Finprod
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper

/-!
# Retired duplicate (2026-10-17)

The source library proves blueprint node
`lem-pc-euler-characteristic-well-defined`
sorry-free as
`AlgebraicGeometry.Scheme.Modules.finite_setOf_nontrivial_H_of_isProper`
`AlgebraicGeometry.Scheme.Modules.finite_support_finrankH_of_isProper`
in
`WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper`
This module re-exports it. Its sorried declaration
`AlgebraicGeometry.Scheme.eulerCharacteristic_wellDefined`
is gone (no module used it).
-/
