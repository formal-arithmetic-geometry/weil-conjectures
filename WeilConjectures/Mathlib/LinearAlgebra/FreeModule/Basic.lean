/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Extensions of free modules are free

In a short exact sequence `0 → M → N → P → 0` of modules with `M` and `P` free, the module `N`
is free (`Module.Free.of_exact`): the sequence splits since `P` is projective.
-/

@[expose] public section

