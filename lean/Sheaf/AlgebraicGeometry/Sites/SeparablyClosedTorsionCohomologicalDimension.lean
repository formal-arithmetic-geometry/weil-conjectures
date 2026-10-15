/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker NG
-/
module

public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants

/-!
# Torsion cohomological dimension of a separably closed field

Source: blueprint, sec-smooth-purity/sk-prop-sf-fullcd-etale-origin,
lemma lem-sf-separably-closed-torsion-cd; Stacks Project, Tags 04JQ and 04JM
(blueprint: lem-sf-separably-closed-torsion-cd).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A separably closed field has torsion étale cohomological dimension at most zero.
Source: blueprint, sec-smooth-purity/sk-prop-sf-fullcd-etale-origin,
lemma lem-sf-separably-closed-torsion-cd; Stacks Project, Tags 04JQ and 04JM
(blueprint: lem-sf-separably-closed-torsion-cd).

Proof:
1. Take the separable closure to be `K` and an algebraic closure `Ω` of `K`.
The Galois group is trivial. By `lem-exc-abelian-sheaves-gmodules` (Tag 04JQ),
abelian étale sheaves are additively equivalent to abelian groups. The equivalence
preserves kernels and cokernels, hence is exact.
2. By `lem-exc-field-sections-stalk-invariants` (Tag 04JM), with `L = K`, global
sections are naturally the geometric stalk with invariants under the trivial group.
The restriction map preserves addition and zero, identifying global sections with
the exact additive equivalence in step 1. No uniform annihilator is required.
3. Compute ordinary derived sections using `def-weil-pbc-etale-cohomology`:
for a K-injective resolution of a sheaf in degree zero, exact global sections
preserve kernels, cokernels, and thus images. Consequently cohomology commutes
with global sections and is zero in every positive degree. This applies in
particular to every locally torsion abelian sheaf, giving the bound defined by
`def-sc-etale-torsion-cd`. -/
theorem hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed
    (K : Type u) [Field K] [IsSepClosed K] :
    HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) 0 := by
  sorry

end AlgebraicGeometry.Scheme
