module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.LinearAlgebra.Trace

/-! # A common fixed vector for a group of unipotent matrices

Source: Milne, Algebraic Groups (2017), Proposition 14.1, printed pp. 279–280,
including footnote 1 (blueprint: lem-sfb-unipotent-matrix-group-fixed-vector).
-/

@[expose] public section

universe u

namespace Matrix.GeneralLinearGroup

/-- A subgroup of invertible matrices whose elements are all unipotent fixes a nonzero
column vector. The subgroup is arbitrary and the positive nilpotence exponent may depend
on its element. The field has arbitrary characteristic.

Source: Milne, Algebraic Groups (2017), Proposition 14.1, printed pp. 279–280,
including footnote 1 (blueprint: lem-sfb-unipotent-matrix-group-fixed-vector).

Proof plan:
1. Choose an algebraic closure L of K using lem-pc-algebraic-closure-exists-unique.
   Extend every matrix entry to L; inverses and the nilpotence equations are preserved.
2. Among the nonzero H-stable subspaces of L^d choose W of least positive dimension.
   It has no proper nonzero stable subspace. The restrictions r_h are invertible and
   satisfy the same nilpotence equations, since inverses also preserve W.
3. Let A be the L-span of the r_h inside End_L(W). The relations r_g r_h = r_(gh)
   and r_1 = 1 make it a unital subalgebra, and W is faithful and simple over A.
   By lem-sfb-simple-algebra-scalar-endomorphisms, End_A(W) consists of scalars.
   A finite L-basis therefore generates W over End_A(W). Applying
   lem-sfb-finite-simple-double-centralizer shows A = End_L(W).
4. The L-span J of the r_h - 1 is a two-sided ideal of A, using
   r_g (r_h - 1) = (r_(gh) - 1) - (r_g - 1) and its right-hand analogue.
   By lem-pc-finite-dimensional-nilpotent-trace and def-weil-endomorphism-trace,
   all elements of J have trace zero. The matrix unit E_11 has trace 1, so J is proper.
5. A nonzero entry x_ij of x in J would give E_ai x E_jb = x_ij E_ab in J for
   every a,b. Scaling gives every matrix unit, contradicting properness. Thus J = 0,
   every r_h is the identity, and any nonzero w in W is fixed by H.
6. Choose a K-basis c_j of the span of the finitely many coordinates of w and write
   w = sum_j c_j v_j with v_j in K^d. For each h, independence of the c_j in
   (h - 1)w = sum_j c_j (h - 1)v_j = 0 gives (h - 1)v_j = 0 for all j.
   Some v_j is nonzero since w is, and it is fixed by every h. This argument does
   not require H to be finite. -/
theorem exists_ne_zero_fixedVec_of_unipotent
    {K : Type u} [Field K] {d : ℕ} (hd : 1 ≤ d)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin d) K))
    (hH : ∀ h ∈ H, ∃ N : ℕ, 1 ≤ N ∧ ((h : Matrix (Fin d) (Fin d) K) - 1) ^ N = 0) :
    ∃ v : Fin d → K, v ≠ 0 ∧ ∀ h ∈ H, Matrix.mulVec (h : Matrix (Fin d) (Fin d) K) v = v := by
  sorry

end Matrix.GeneralLinearGroup
