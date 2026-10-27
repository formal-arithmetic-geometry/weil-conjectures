/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Unitriangular
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.LinearAlgebra.TensorProduct.Basis

import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Rational fixed vectors for closed unitriangular subgroup schemes

Source: Milne, Algebraic Groups (2017), Theorem 14.5(b) implies (a), printed pp.281--282;
the definition preceding Proposition 14.3, printed p.280.
(blueprint: lem-sfb-unitriangular-subgroup-rational-fixed-vector)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry

/-- Every nonzero rational representation of a closed subgroup scheme of U_n has a
nonzero vector over k fixed over every commutative k-algebra.
Source: Milne, Theorem 14.5(b) implies (c) implies (a), pp.281--282, and the
rational fixed-vector definition preceding Proposition 14.3, p.280
(blueprint: lem-sfb-unitriangular-subgroup-rational-fixed-vector).

Proof, following the five steps of the DAG node:
1. The unitriangular coordinate algebra is P=k[x_ij : i<j]. Matrix multiplication gives
Delta(x_ij)=x_ij tensor 1+1 tensor x_ij+sum_{i<l<j} x_il tensor x_lj, and epsilon(x_ij)=0
(def-weil-pbc-mv-polynomial-ring, def-weil-affine-spectrum,
def-sc-general-linear-group, lem-sfb-affine-group-coordinate-hopf).
2. Give x_ij weight j-i and let F_r be the span of monomials of weight at most r.
Then F_0=k, the filtration is increasing and exhaustive, and the weights in each
term of Delta(x_ij) add to j-i. Expanding monomials gives
Delta(F_r) contained in sum_{a=0}^r F_a tensor F_{r-a}. For n=1, P=k and F_r=k
(def-weil-pbc-mv-polynomial-ring, lem-sfb-affine-group-coordinate-hopf).
3. The closed group immersion induces a surjective coordinate algebra map q:P to B=k[U].
It respects Delta and epsilon, so the image filtration C_r=q(F_r) is increasing,
exhaustive, starts with k times 1_B, and satisfies the same tensor filtration rule.
The counit sends 1_B to 1, so 1_B is nonzero (def-weil-closed-immersion,
def-sc-group-scheme, lem-sfb-affine-group-coordinate-hopf).
4. Apply lem-sfb-rational-representation-comodule-dictionary to rho on V=k^d.
The coaction c satisfies coassociativity and the counit law. Since d>=1, V is nonzero.
Apply lem-sfb-filtered-coalgebra-nonzero-coinvariant to B, C_r and g=1_B to obtain
v nonzero with c(v)=v tensor 1_B.
5. For any algebra A and point x:B to A, the dictionary's evaluation formula sends
this equality to rho_A(x)(1 tensor v)=1 tensor v. The tensor flip identifies the
right-coaction and scalar-extension conventions (def-weil-pbc-module-tensor-product).
Thus the same vector over k works for every A and every algebra-valued point.
No smoothness, reducedness, connectedness, perfectness or characteristic hypothesis is used. -/
theorem exists_rational_fixed_vector_of_unitriangular_closedImmersion
    {k : Type u} [Field k] (U : Over (Spec (.of k))) [GrpObj U]
    [IsAffine U.left] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (n : ℕ) (hn : 1 ≤ n) (i : U ⟶ UnitriangularGroup.scheme k n)
    [IsMonHom i] [IsClosedImmersion i.left]
    (d : ℕ) (hd : 1 ≤ d)
    (ρ : U ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} d) k) [IsMonHom ρ] :
    ∃ v : LinearGroupSchemes.Index.{u} d → k, v ≠ 0 ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A] (x : points U A),
        (Matrix.GeneralLinearGroup.toLin'
          ((Pi.basisFun k (LinearGroupSchemes.Index.{u} d)).baseChange A)
          (GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} d) k A
            (x ≫ ρ))).toLinearEquiv (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] v := by
  sorry

end AlgebraicGeometry
