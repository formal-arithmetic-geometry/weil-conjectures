/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Mathlib.Algebra.Lie.Ideal
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus

/-!
# The Lie ideal of a normal closed subgroup scheme

Source: Milne, Algebraic Groups (2017), 10.12, 10.14, 10.19--10.23, pp.190--193,
and Lemma 23.68, p.506 (blueprint: lem-sfb-normal-subgroup-lie-ideal).

`GrpObj.Lie` is the existing identity-tangent model: its canonical dual-number point is
`GrpObj.tangentPoint`, and its bracket is the mixed coefficient of the group commutator.
The existing `GrpObj.lieIdentityTangentEquiv` identifies this model with `schemeTangentSpace`
at the identity, with scalars restricted along the canonical residue-field identification.
`GrpObj.differential` is postcomposition on those tangent points and already has type
`Lie N →ₗ⁅k⁆ Lie G`. No new Lie algebra or differential is introduced here.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.GrpObj

/-- The differential of a normal closed subgroup inclusion is injective, its source and target
are finite dimensional, and its image is an ideal. If the subgroup is commutative, both its
Lie bracket and the bracket on this image vanish.

Source: Milne, Algebraic Groups (2017), 10.12, 10.14, 10.19--10.23, pp.190--193,
and Lemma 23.68, p.506 (blueprint: lem-sfb-normal-subgroup-lie-ideal).

Proof plan:
1. Apply lem-sfb-affine-group-lie-tangent-calculus for finite dimensionality and preservation
   of brackets. Apply lem-sfb-affine-group-dual-number-calculus for injectivity and the natural
   identification of the differential with postcomposition on infinitesimal points.
2. Choose a faithful closed embedding into a general linear group using
   lem-sfb-affine-group-faithful-linear-representation. Its differential is injective. For
   x in Lie(G) and y in Lie(N), write X and Y for the matrices of x and di(y). In
   A = k[epsilon,delta]/(epsilon^2,delta^2), the images of their tangent points are
   1 + epsilon X and 1 + delta Y. Their commutator is 1 + epsilon delta (XY - YX),
   the image of the tangent point of [x,di(y)] under k[eta]/eta^2 -> A,
   eta -> epsilon delta. Faithfulness identifies the corresponding group points.
3. Normality puts this commutator in N(A). By
   lem-weil-pbc-closed-immersion-affine-cover-criterion, write G = Spec C and N = Spec(C/J).
   The tangent point corresponds to phi : C -> k[eta]/eta^2 by def-weil-affine-spectrum.
   Its base change kills J. The map eta -> epsilon delta is injective, since
   1, epsilon, delta, epsilon delta are a basis of A, so phi itself kills J. Thus the
   tangent point lifts to N, and its reduction is the identity by injectivity of N(k) -> G(k).
   The dual-number calculus gives w in Lie(N) with di(w) = [x,di(y)]. This is exactly
   the ideal condition, expressed by LieHom.IsIdealMorphism from def-wf-lie-algebra.
4. If N is commutative, its two tangent points over A commute. Comparing their matrix
   commutator with 1 gives XY - YX = 0. Bracket preservation and the two injective
   differentials imply [u,v] = 0 in Lie(N). Applying di gives zero bracket for any two
   elements of its image. This argument works in every characteristic, including 2,
   and uses no smoothness, reducedness, connectedness or perfectness assumption. -/
theorem normal_subgroup_lie_ideal
    {k : Type u} [Field k]
    (G N : Over (Spec (.of k))) [GrpObj G] [GrpObj N]
    [IsAffine G.left] [IsAffine N.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [LocallyOfFiniteType N.hom] [QuasiCompact N.hom]
    (i : N ⟶ G) [IsClosedSubgroupScheme i] [IsNormalSubgroupScheme i] :
    FiniteDimensional k (Lie N) ∧ FiniteDimensional k (Lie G) ∧
      Function.Injective (differential i) ∧ (differential i).IsIdealMorphism ∧
      (IsCommMonObj N →
        (∀ x y : Lie N, ⁅x, y⁆ = 0) ∧
          ∀ x y : Lie G, x ∈ (differential i).range →
            y ∈ (differential i).range → ⁅x, y⁆ = 0) := by
  sorry

end AlgebraicGeometry.GrpObj
