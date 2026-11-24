/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # The open where a module map is locally invertible

## References

* [Stacks, Tag 05GD](https://stacks.math.columbia.edu/tag/05GD)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The union of the open subschemes on which the tensor pullback of a map is invertible
(Stacks, Tag 05GD). -/
noncomputable def moduleMapIsoLocus {W : Scheme.{u}} {M N : W.Modules} (φ : M ⟶ N) :
    W.Opens :=
  sSup {U : W.Opens | IsIso ((tensorPullback U.ι).map φ)}

/-- Membership means invertibility on an open neighbourhood.
-/
theorem mem_moduleMapIsoLocus {W : Scheme.{u}} {M N : W.Modules} (φ : M ⟶ N) (x : W) :
    x ∈ moduleMapIsoLocus φ ↔
      ∃ U : W.Opens, IsIso ((tensorPullback U.ι).map φ) ∧ x ∈ U := by
  exact TopologicalSpace.Opens.mem_sSup

end AlgebraicGeometry.Scheme.Modules
