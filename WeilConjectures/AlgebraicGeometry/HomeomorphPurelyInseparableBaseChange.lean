/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra

/-!
# Base change along a purely inseparable field extension

## References

* Stacks Project, Tags 0BR5 and 04DF.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Base change of a `k`-scheme along a purely inseparable field extension `K/k` induces
a homeomorphism on the underlying topological spaces. (Stacks, Tags 0BR5 and 04DF) -/
theorem isHomeomorph_baseChange_of_isPurelyInseparable
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] :
    IsHomeomorph
      (pullback.fst (X ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base := by
  exact (pullback.fst (X ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).isHomeomorph

end AlgebraicGeometry
