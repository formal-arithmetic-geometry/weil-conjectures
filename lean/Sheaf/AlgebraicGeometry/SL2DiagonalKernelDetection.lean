/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.SL2DiagonalTorus
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.Module
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality

/-!
# The diagonal torus detects the scheme kernel of an SL2 representation

Source: Milne, Algebraic Groups (2017), Sections 10a--10d and 20g; Theorem 3.34
and Corollary 3.35. This is the agent-formulated supporting kernel lemma, not a
verbatim theorem of Milne. (blueprint: lem-sfb-sl2-diagonal-kernel-detection)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.LinearGroupSchemes

/-- A closed normal subgroup of SL2 meeting its diagonal torus scheme-theoretically
trivially is trivial. The intersection hypothesis is imposed on every algebra, not only
on field-valued points: equal images of an N-point and a torus-point must be the identity.
The conclusion says that N → Spec k is an isomorphism, hence N is the trivial subgroup.
Source: Milne, Algebraic Groups, Sections 10a--10d and 20g; agent-formulated lemma
(blueprint: lem-sfb-sl2-diagonal-kernel-detection).

Proof for stage 3:
1. By def-sc-scheme-tangent-space, identity tangent vectors are I + epsilon X with
   trace X = 0. Normality makes their space W conjugation-stable. Trivial intersection
   on dual numbers gives W ∩ kH = 0, where H = diag(1,-1).
2. The algebraically closed field is infinite. Choose three nonzero t with distinct
   squares q. Torus conjugation scales E12 and E21 by q and q⁻¹. The invertible
   Vandermonde matrix with rows (1,q,q⁻¹) separates the H, E12 and E21 components in W.
3. Conjugating E12 by I+E21 gives E12-H-E21, and conjugating E21 by I+E12 gives
   E21+H-E12. Any nonzero off-diagonal component therefore forces H into W. Thus W=0.
   H remains nonzero in characteristic two, so no division by two is needed.
4. A scalar rational point of N lies in the torus. For a nonscalar point choose a
   determinant-one basis in which its lower-left entry c is nonzero. The commutator
   with I+tE12 has trace 2+c²t², by direct multiplication.
5. Choose t with (2+c²t²)² ≠ 4. The characteristic polynomial then has distinct roots
   lambda and lambda⁻¹. A determinant-one eigenbasis conjugates this commutator to a
   nonidentity torus point in N, contradiction. Hence N(k) consists only of the identity.
6. N=Spec B is of finite type, hence Noetherian by lem-wf-affine-noetherian-components.
   Clause 1 of lem-wf-affine-nullstellensatz-vanishing identifies all maximal ideals
   with rational points. Thus B is local with residue field k and augmentation ideal m.
7. By lem-sc-rational-tangent-cotangent-duality, W=0 is dual to m/m². This quotient is
   finite-dimensional, so it is zero. Nakayama (lem-weil-pbc-nakayama-local-generators)
   with the empty family gives m=0. The augmentation B → k is an isomorphism.
No step assumes that N is reduced. -/
theorem sl2_diagonal_kernel_detection (k : Type u) [Field k] [IsAlgClosed k]
    (N : Over (Spec (.of k))) [GrpObj N] (i : N ⟶ specialLinear k 2)
    [IsClosedSubgroupScheme i] [IsNormalSubgroupScheme i]
    (hinter : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (n : StandardGroupSchemes.affine k R ⟶ N)
      (d : StandardGroupSchemes.affine k R ⟶ StandardGroupSchemes.multiplicative k),
      n ≫ i = d ≫ diagonalTorus k → n ≫ i = 1) :
    IsIso N.hom := by
  sorry

/-- A finite-dimensional representation of SL2 that is a closed immersion on its
canonical diagonal torus is a closed immersion. The existing GL scheme is indexed by
Module.Free.chooseBasis k M; thus its points are automorphisms of R ⊗[k] M in that basis.
The chosen index type is empty when M=0, so the zero-dimensional case is included.
Source: Milne, Algebraic Groups, Corollary 3.35 and Theorem 3.34, p.75, together with
Sections 10a--10d and 20g (blueprint: lem-sfb-sl2-diagonal-kernel-detection).

Proof for stage 3:
8. By lem-sc-kernel-subgroup, the scheme kernel K of v is a closed normal subgroup
   and its R-points are ker(v_R). A closed immersion on the torus is injective on
   every algebra's points (def-weil-closed-immersion), so K intersects the torus
   trivially. Apply sl2_diagonal_kernel_detection to obtain K=1, hence injectivity
   of v on every algebra's points. SL2 and GL(M) are affine of finite type, including
   GL(0)=1. Apply lem-sfb-geometric-unipotence-faithful-closed-immersion to conclude. -/
theorem sl2_closedImmersion_of_diagonal (k : Type u) [Field k] [IsAlgClosed k]
    (M : Type u) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (v : specialLinear k 2 ⟶ GeneralLinearGroup (Module.Free.ChooseBasisIndex k M) k)
    [IsMonHom v] (hD : IsClosedImmersion (diagonalTorus k ≫ v).left) :
    IsClosedImmersion v.left := by
  sorry

end AlgebraicGeometry.LinearGroupSchemes
