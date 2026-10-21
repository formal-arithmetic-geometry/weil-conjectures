/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups C1, U6
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare

/-! # Pullback comparisons for nested open subschemes

The adopted source library supplies `perfectOverlapNestedRestrictedMaps` and the
explicit construction `perfectOverlapNestedPullbackSquare`. Reexport those declarations
with the overlap compatibility API, without declaring a second copy.

Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-nested-pullback-square).
-/

@[expose] public section
