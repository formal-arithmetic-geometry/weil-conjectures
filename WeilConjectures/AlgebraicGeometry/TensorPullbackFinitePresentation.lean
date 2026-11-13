/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Tensor pullback preserves finite presentation

## References

* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 0095](https://stacks.math.columbia.edu/tag/0095)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling back a finitely presented scheme module preserves finite presentation. -/
theorem isFinitePresentation_tensorPullback
    {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Modules) [M.IsFinitePresentation] :
    ((tensorPullback g).obj M).IsFinitePresentation := by
  obtain ⟨adj⟩ := nonempty_tensorPullbackAdjunction g
  let e := adj.leftAdjointUniq (pullbackPushforwardAdjunction g)
  exact isFinitePresentation_of_iso (e.app M).symm

end AlgebraicGeometry.Scheme.Modules
