/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.PerfectLocalizingClosure

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Perfect complexes generate the quasi-coherent derived category

Source: literature/stacks-project/derived-categories-of-schemes.tex, Theorem
perfect-theorem-bondal-van-den-Bergh (blueprint: lem-pc-derived-qcoh-perfect-generation).
-/
