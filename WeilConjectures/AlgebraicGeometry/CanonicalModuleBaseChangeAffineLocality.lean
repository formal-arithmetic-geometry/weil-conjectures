/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps

import WeilConjectures.AlgebraicGeometry.CanonicalModuleBaseChangeAffineChartComparison
import WeilConjectures.AlgebraicGeometry.FlatOverAffineOpenRestriction

/-! # Affine locality for relatively flat canonical module base change

Source: blueprint `lem-pc-rf-base-change-flat-module`, Step 1 (local affine reduction),
and Stacks Project, Tag 08IB, first paragraph of the proof.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

end AlgebraicGeometry
