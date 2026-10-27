/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# A positive-dimensional affine subgroup of a nonproper group

Source: Milne, Algebraic Groups (2017), Proposition 8.25, pp. 153-154,
and Corollaries 1.35 and 1.39, pp. 17-18
(blueprint: lem-sfb-rosenlicht-nonproper-affine-subgroup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A nonproper smooth connected algebraic group contains a smooth connected affine
closed subgroup of positive dimension.

Source: Milne, Algebraic Groups (2017), Proposition 8.25, pp. 153-154,
and Corollaries 1.35 and 1.39, pp. 17-18
(blueprint: lem-sfb-rosenlicht-nonproper-affine-subgroup).

Proof:
1. Strongly induct on d = dim H. The dimension assertions of
lem-sfb-affine-normal-subgroup-products make d finite and give strict dimension drop
for proper smooth connected closed subgroups. If d = 0, apply
lem-pc-zero-dimensional-closed-subscheme-finite to the identity inclusion; then
lem-weil-pbc-finite-proper contradicts nonproperness. Hence d > 0.
2. By lem-sfb-rational-boundary-positive-stabilizer obtain a boundary point with
positive-dimensional reduced stabilizer S. Apply
lem-sfb-locally-algebraic-group-identity-component to C = (S^0)_red. It is smooth,
connected, integral, separated and finite type. By lem-sfb-group-neutral-component-translates,
the components of S have the same dimension. Chains stay in one clopen component;
reduction preserves the space. Thus dim C = dim S > 0.
3. If C = H, the partial stabilizer is dense. The equalizer of the orbit map at the
boundary point and the constant map is closed on its domain, since the completion is
separated. Its ideal vanishes on the dense set and is zero on the reduced domain
(sbc-lem-smooth-geometrically-reduced). The rational action fixes the boundary point.
The action on the dense open H is faithful, by evaluation at the identity.
Apply lem-sfb-rational-fixed-point-affineness; take U = H.
4. Otherwise dim C < d. If C is nonproper, induction gives U inside C.
Compose its closed immersion with C into H; compositions of quotient maps are surjective.
5. If C is proper, it is an abelian variety (def-sc-abelian-variety). Its inclusion
is central by lem-sfb-abelian-subvariety-central. By
lem-sfb-rosenlicht-connected-almost-complement obtain a smooth connected closed normal
N and a surjective faithfully flat multiplication C times N to H, with
dim H = dim C + dim N. Since dim C > 0, dim N < d.
6. If N were proper, C times N would be proper by lem-weil-pbc-proper-base-change
and lem-weil-pbc-proper-composition. Its scheme-theoretic image in H is proper by
lem-weil-pbc-scheme-theoretic-image-proper. Surjectivity makes that image topologically
all of H, and smoothness makes H reduced (sbc-lem-smooth-geometrically-reduced), so its
image ideal is zero. This contradicts nonproperness of H. Thus N is nonproper;
induction gives U inside N, and composition of closed inclusions gives U inside H. -/
theorem exists_smooth_connected_affine_closed_subgroup_of_not_isProper
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Over (Spec (.of k))) [GrpObj H]
    [Smooth H.hom] [ConnectedSpace H.left] [IsSeparated H.hom]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom] (hH : ¬ IsProper H.hom) :
    ∃ (U : Over (Spec (.of k))) (_ : GrpObj U) (i : U ⟶ H),
      IsClosedSubgroupScheme i ∧ Smooth U.hom ∧ ConnectedSpace U.left ∧
      IsAffine U.left ∧ 0 < topologicalKrullDim U.left := by
  sorry

end AlgebraicGeometry
