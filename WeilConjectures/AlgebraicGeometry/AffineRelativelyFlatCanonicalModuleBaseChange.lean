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

import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModelFlat
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechBaseChangeFactorization

/-! # Affine computation of relatively flat canonical module base change

Source: blueprint `lem-pc-rf-base-change-flat-module`, Steps 2--5;
Stacks Project, Tag 0A1D, specializing to a module in degree zero.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

end AlgebraicGeometry
