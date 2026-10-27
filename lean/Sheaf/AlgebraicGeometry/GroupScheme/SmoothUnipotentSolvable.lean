module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure

import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry

/-! # Smooth unipotent algebraic groups are solvable

Source: Milne, Algebraic Groups (2017), Proposition 14.21, pp.284--285,
Corollary 14.12, p.283, and Example 6.49, pp.136--137
(blueprint: lem-sfb-smooth-unipotent-solvable).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth unipotent affine group scheme of finite type over any field is solvable.
Smoothness is included in `SolvableGroupStructure.IsUnipotent`; solvability uses closed
normal subgroup schemes and commutators on every commutative algebra, including
nonreduced algebras. No perfectness, connectedness or characteristic assumption is needed.

Source: Milne, Algebraic Groups (2017), Proposition 14.21 and Corollary 14.12
(blueprint: lem-sfb-smooth-unipotent-solvable).

Proof:
1. Apply `lem-sfb-geometric-unipotence-unitriangular-embedding` to the faithful
   representation in the unipotence hypothesis, identifying U with a closed subgroup
   of the upper unitriangular group over k itself (Milne, Theorem 14.5 and Corollary 14.12).
2. For every commutative k-algebra R, let J_r(R) consist of matrices whose entries vanish
   unless the column minus the row is at least r. Matrix multiplication gives
   J_r J_s ⊆ J_{r+s}, with J_n = 0. Each J_r is a two-sided ideal in the upper triangular
   matrices. Thus F_r = 1 + J_r is a closed subgroup: multiplication uses A+B+AB and
   inverses use the finite geometric series. Modulo J_{r+1}, F_r is commutative since
   J_r J_r ⊆ J_{2r} ⊆ J_{r+1} for r ≥ 1. Intersect these closed subgroups with U using
   `def-weil-closed-immersion` and `def-sc-group-scheme-subgroup`. This yields closed
   H_{r+1} normal in H_r, with every commutator in H_{r+1}(R), H_1 = U and H_n = 1.
   These polynomial identities hold on nonreduced test algebras too (Example 6.49).
3. The groups H_r are affine of finite type. Apply
   `lem-sfb-affine-normal-quotient-geometry` to represent H_r/H_{r+1} as its fppf quotient.
   On a common fppf refinement, lift two quotient points to H_r. Their commutator is
   in the kernel by step 2, so they commute; the sheaf condition descends this equality.
   Thus each quotient is commutative as a group scheme (`def-sc-group-scheme`), giving
   the required finite closed subnormal series. For n = 1 the series has length zero.
-/
theorem smooth_unipotent_isSolvable {k : Type u} [Field k]
    (U : Grp (Over (Spec (.of k)))) (hU : SolvableGroupStructure.IsAlgebraic U)
    (hu : SolvableGroupStructure.IsUnipotent U) : SolvableGroupStructure.IsSolvable U := by
  sorry

end AlgebraicGeometry
