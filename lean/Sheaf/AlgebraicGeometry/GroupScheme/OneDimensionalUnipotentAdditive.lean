/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality

/-! # One-dimensional smooth connected unipotent groups are additive

Source: Milne, Algebraic Groups (2017), paragraph 14.58, printed p.298,
and Proposition 1.37, printed p.18
(blueprint: lem-sfb-one-dimensional-unipotent-additive).

The dimension uses the existing Lie module. The proved linear equivalence
`GrpObj.lieIdentityTangentEquiv` identifies it with `schemeTangentSpace` at the
identity, with scalars restricted along the structural map to its residue field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected affine unipotent group of finite type with one-dimensional
Lie algebra over an algebraically closed field is isomorphic to the additive group.
There is no restriction on the characteristic.

Source: Milne, Algebraic Groups (2017), paragraph 14.58, printed p.298,
and Proposition 1.37, printed p.18
(blueprint: lem-sfb-one-dimensional-unipotent-additive).

Proof:
1. Algebraic closedness makes F perfect: in positive characteristic every X^p-b
   has a root. The group is nontrivial, since the tangent space of Spec F is zero,
   contrary to the dimension-one hypothesis (def-sc-scheme-tangent-space).
2. Apply lem-sfb-unipotent-central-additive-subgroup to U. It supplies a smooth
   connected closed subgroup N, an isomorphism a : Ga ≅ N, and its inclusion i.
3. The coordinates of def-sc-gm-ga identify tangent vectors of Ga with y ↦ cε,
   hence its tangent space with F. Transport through a gives dimension one for N.
   The inclusion is injective on all algebra-valued points by
   def-sc-group-scheme-subgroup, in particular on dual-number points. Its tangent
   map is therefore injective, and its image is the whole one-dimensional Lie(U).
4. Apply lem-sfb-smooth-subgroup-tangent-generation to G = U, the singleton family
   H₁ = N, and K = N. The rational tangent-cotangent duality of
   lem-sc-rational-tangent-cotangent-duality identifies the dual-number tangent
   image with the cotangent-dual differential in that criterion. It gives N = U
   as closed subgroup schemes. Composing a with i gives the required isomorphism.
The recorded lieIdentityTangentEquiv transports the dimension hypothesis to the
scheme tangent space used in these steps. -/
theorem oneDimensionalUnipotent_additive
    (F : Type u) [Field F] [IsAlgClosed F]
    (U : Grp (Over (Spec (.of F))))
    [Smooth U.X.hom] [ConnectedSpace U.X.left] [IsAffine U.X.left]
    [LocallyOfFiniteType U.X.hom] [QuasiCompact U.X.hom]
    (hU : SolvableGroupStructure.IsUnipotent U)
    (hdim : Module.finrank F (GrpObj.Lie U.X) = 1) :
    Nonempty (Grp.mk (StandardGroupSchemes.additive F) ≅ U) := by
  sorry

end AlgebraicGeometry
