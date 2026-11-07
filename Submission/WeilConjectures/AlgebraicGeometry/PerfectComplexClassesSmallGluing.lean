/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.PerfectComplexClassesSmallOnOpen
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Submission.WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisTriangle
import Mathlib.AlgebraicGeometry.AffineScheme

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Gluing smallness of perfect isomorphism classes

Source: Step 2 of lem-pc-perfect-complexes-compact-set, using Stacks Project,
Tags 08BV and 08DR (blueprint: lem-pc-perfect-classes-small-gluing).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
