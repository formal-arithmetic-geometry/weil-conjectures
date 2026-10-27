/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import Mathlib.GroupTheory.Finiteness
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Homomorphisms from diagonalizable groups to unipotent groups

Source: Milne, Algebraic Groups (2017), Corollary 14.18(b), printed p.284,
and Theorem 14.5, printed p.281
(blueprint: lem-sfb-diagonalizable-to-unipotent-trivial).

A closed subgroup of the upper unitriangular group is expressed by its closed
embedding in GL_n, with the unitriangular equations on every algebra-valued point.
The equations are scheme-theoretic: they are not restricted to geometric points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every group-scheme homomorphism from D_k(M) to a closed unitriangular subgroup
is trivial on all algebra-valued points. No smoothness or connectedness is assumed,
and M may have torsion divisible by the characteristic.

Source: Milne, Algebraic Groups (2017), Corollary 14.18(b), printed p.284;
Section 12(b), printed pp.230--232; Theorem 14.5, formula (92), printed p.281
(blueprint: lem-sfb-diagonalizable-to-unipotent-trivial).

Proof plan, following the node's coordinate argument:
1. Put R = k[M] and evaluate f followed by j at the universal R-point of D_k(M)
   (def-weil-affine-spectrum). Write its matrix as (a_ij). The unitriangular
   equations give a_ii = 1 and a_ij = 0 below the diagonal. Evaluate on the two
   universal points over R tensor_k R, using the algebra inclusions of
   lem-weil-pbc-algebra-tensor-pushout-universal-property. Naturality and the
   group homomorphism law (def-sc-group-scheme) give, for i < j,
   Delta(a_ij) = a_ij tensor 1 + 1 tensor a_ij + sum_(i<l<j) a_il tensor a_lj.
2. For each m, let c_m be the coefficient functional of e_m in k[M]. The
   bilinear maps (x,y) maps to c_s(x)c_t(y) induce tensor functionals by
   def-weil-pbc-module-tensor-product. If a = sum b_m e_m is primitive, applying
   the (m,m) functional for m nonzero gives b_m = 0. The (0,0) functional then
   gives b_0 = 2 b_0, hence b_0 = 0. Thus every primitive element is zero,
   in every characteristic, without dividing by an integer.
3. Induct on j-i. At height one the sum in step 1 is empty; at greater height
   every term in that sum vanishes by induction. Step 2 then gives a_ij = 0.
   Consequently the universal matrix is the identity. For n = 1 there are no
   strictly upper triangular entries and the same conclusion is immediate.
4. Every A-point of D_k(M) comes from the universal point via its algebra map
   k[M] to A (def-weil-affine-spectrum). Naturality therefore makes its image
   under f followed by j the identity matrix. The injectivity on A-points of
   the closed subgroup embedding (def-sc-group-scheme-subgroup) gives f_A(d)=1.
   This includes M = 0 and characteristic-p torsion such as M = Z/pZ. -/
theorem diagonalizable_to_unipotent_trivial
    {k : Type u} [Field k] (M : Type u) [AddCommGroup M] [AddGroup.FG M]
    (n : ℕ) (hn : 0 < n)
    (U : Over (Spec (.of k))) [GrpObj U]
    (j : U ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k)
    (hj : IsClosedSubgroupScheme j)
    (hunitriangular : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (x : (Spec (.of A)).asOver (Spec (.of k)) ⟶ U),
      (∀ i : Fin n,
        (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ j)).val
          (ULift.up i) (ULift.up i) = 1) ∧
      (∀ i l : Fin n, l < i →
        (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin n)) k A (x ≫ j)).val
          (ULift.up i) (ULift.up l) = 0))
    (f : (diagonalizableGroup k M).X ⟶ U) [IsMonHom f] :
    ∀ (A : Type u) [CommRing A] [Algebra k A]
      (d : (Spec (.of A)).asOver (Spec (.of k)) ⟶ (diagonalizableGroup k M).X),
      d ≫ f = 1 := by
  sorry

end AlgebraicGeometry
