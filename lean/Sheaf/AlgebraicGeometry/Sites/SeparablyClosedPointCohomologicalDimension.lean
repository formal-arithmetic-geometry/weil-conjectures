/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker NR
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport

/-!
# Cohomological dimension of a separably closed point

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-kun-cd-sep-closed-point.md (blueprint: lem-kun-cd-sep-closed-point).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- The torsion étale cohomological dimension of the spectrum of a separably closed field
is zero. Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc,
lem-kun-cd-sep-closed-point (blueprint: lem-kun-cd-sep-closed-point).

Proof: The spectrum of a field has exactly one point, hence is quasi-compact and
quasi-separated. By `def-kun-cd`, its dimension is the least nonnegative bound for the
cohomology of all torsion abelian étale sheaves. By `lem-kun-03qu-sep-closed`, namely
`Scheme.subsingleton_H_of_isSepClosed`, every abelian étale sheaf on this spectrum has
vanishing cohomology in positive degrees. This applies to torsion abelian sheaves, so
zero is a bound. As zero is the least possible nonnegative bound, the dimension is zero. -/
theorem torsionEtaleCohomologicalDimension_eq_zero_of_isSepClosed
    (K : Type u) [Field K] [IsSepClosed K] :
    (Spec (.of K)).torsionEtaleCohomologicalDimension = 0 := by
  sorry

end AlgebraicGeometry.Scheme
