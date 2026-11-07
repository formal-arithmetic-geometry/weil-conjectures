/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
import Submission.WeilConjectures.AlgebraicGeometry.PerfectAffineClassesSmall
import Submission.WeilConjectures.AlgebraicGeometry.PerfectComplexClassesSmallGluing
import Submission.WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # A set of representatives for perfect complexes

Source: Stacks Project, Derived Categories of Schemes,
Theorem perfect-theorem-bondal-van-den-Bergh, set-of-representatives input
(blueprint: lem-pc-perfect-complexes-compact-set).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
