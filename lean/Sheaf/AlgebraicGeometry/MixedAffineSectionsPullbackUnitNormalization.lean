/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsComplexUnit
public import Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso
public import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsPullbackUnitNormalization

/-! # The target affine model and its pullback unit normalization

Compatibility import for the adopted source proof of
`AlgebraicGeometry.exists_mixedAffineSections_pullback_unit_normalization`.
The source declaration has exactly the statement of the former copy at this path.
It constructs the K-flat pullback model, transports the affine sections comparison,
and proves the normalized unit equation by counit naturality and inverse cancellation.
Re-export it here so both module paths refer to the same declaration.

Source: Stacks Project, Tags 06Z0, 08DW(2) and 0D5T.
(blueprint: lem-sc-mixed-affine-pullback-unit-normalization).
-/

@[expose] public section
