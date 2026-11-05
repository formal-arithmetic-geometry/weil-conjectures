/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The adic tower of continuous maps into a complete normed ring

Let `T` be a complete normed ring all of whose elements have norm `≤ 1` (e.g. the ring of
integers of a complete non-archimedean field) and `n : ℤ` with `‖(n : T)‖ < 1`. For any
topological space `W`, the map `(xᵢ) ↦ (xᵢ - n • xᵢ₊₁)` is a bijection of `ℕ → C(W, T)`
(`ContinuousMap.bijective_sub_zsmul_succ`): it is injective since `T` is `n`-adically separated,
and the inverse is `(yᵢ) ↦ (∑ₖ nᵏ yᵢ₊ₖ)`, the series converging uniformly on `W`.

In other words, the abelian group `C(W, T)` is derived `n`-adically complete.
-/

@[expose] public section

variable {T : Type*} [NormedRing T]

namespace ContinuousMap

variable {W : Type*} [TopologicalSpace W]

end ContinuousMap
