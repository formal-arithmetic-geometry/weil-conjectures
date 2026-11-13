/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.AlgebraicGeometry.FormalModuleSupportSucc
import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Constant support of a coherent formal module

## References

* [Stacks Project, Tag 0CYV](https://stacks.math.columbia.edu/tag/0CYV)
-/

@[expose] public section

universe u

open Opposite

namespace AlgebraicGeometry

/-- Every positive level of a coherent formal module has the same support as level one.
The index `op n` denotes level `n + 1`, and `op 0` denotes level one. Support is the
nonzero-stalk locus. (Stacks, Tag 0CYV.) -/
theorem formalModule_support_eq {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I) (n : ℕ) :
    {x : X | ¬ Subsingleton ((F.obj.obj (op n)).presheaf.stalk x)} =
      {x : X | ¬ Subsingleton ((F.obj.obj (op 0)).presheaf.stalk x)} := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (formalModule_support_succ I F n).trans ih

end AlgebraicGeometry
