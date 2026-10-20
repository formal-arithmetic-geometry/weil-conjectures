/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension

/-!
# Torsion cohomological dimension of a finite base field

Source: the finite-field clause of `sk-lem-base-field-cd` (blueprint:
`det-base-field-cd-finite-torsion-bound`).

The proof follows the absolute Galois group computation for a finite field: every
geometric stalk is a torsion discrete module for the profinite completion of the
integers, and continuous cohomology of such a module vanishes above degree one.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite base field has torsion étale cohomological dimension at most one.

Source: Stacks Project, Tags 03QQ and 010T, and the finite-field part of
`sk-lem-base-field-cd` (blueprint: det-base-field-cd-finite-torsion-bound).

The proof identifies the small étale topos of `Spec K` with discrete modules for
its absolute Galois group. For finite `K`, the absolute Galois group is the profinite
completion of the integers. A torsion discrete module is the directed union of finite
stable submodules; each finite stable submodule factors through a finite cyclic quotient.
The periodic cyclic resolution and inflation along successive multiples kill every
cohomology class in degree at least two. The continuous cochain colimit therefore
vanishes in those degrees, and the stalk comparison transfers this vanishing to every
torsion étale sheaf.
-/
theorem hasTorsionEtaleCohomologicalDimensionLE_one_of_finite_baseField
    (K : Type u) [Field K] [Finite K] :
    HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) 1 := by
  sorry

end AlgebraicGeometry.Scheme
