/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.GroupScheme.IdentityLocalDimension
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.RegularClosedPointComponents

/-!
# A smooth closed subgroup with full tangent space

Source: Milne, Algebraic Groups (2017), Proposition 10.15, printed pp.190-191
(blueprint: lem-sfb-smooth-subgroup-full-tangent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth closed subgroup of a connected affine finite-type group over any field
is the whole group if its differential at the identity is surjective.
Source: Milne, Algebraic Groups (2017), Proposition 10.15, printed pp.190-191
(blueprint: lem-sfb-smooth-subgroup-full-tangent).

The residue-field bijectivity witness in `hsurj` identifies the two rational identity
residue fields. The target point of `schemeTangentMap` is the image of the identity of `B`,
which is the identity of `A` since `j` is a group homomorphism. `IsIso j` is an isomorphism
of schemes over `k`; its inverse respects the group operations by cancellation with `j`.

Proof for stage 3, following the eight steps of the node:
1. Write A = Spec C and B = Spec (C/I). Finite type over a field makes both coordinate
   rings Noetherian, and their identity local rings have residue field k. Use
   lem-pc-affine-finite-type-algebra, lem-weil-pbc-finite-type-algebra-noetherian,
   lem-weil-pbc-affine-open-stalk-localization and lem-weil-pbc-localization-noetherian.
2. By lem-weil-pbc-regular-local-cotangent-dimension, the local dimension is at most the
   cotangent dimension, with equality exactly for a regular local ring. Identify the
   tangent space with its dual by lem-sc-rational-tangent-cotangent-duality, use
   lem-sfb-linear-dual-dimension-rank, and identify the identity local dimension with the
   group dimension by lem-ag-group-identity-local-dimension.
3. Smoothness of B makes its identity local ring regular, by
   lem-weil-pbc-smooth-ring-map-iff-smooth-affine and
   lem-weil-pbc-smooth-over-field-regular-local. Thus dim B = dim Lie(B).
4. Surjectivity gives dim Lie(A) <= dim Lie(B), and closed immersion gives dim B <= dim A.
   The dimension inequalities force equality throughout and regularity at the identity of A.
5. The rational residue extension k/k is separable, so
   lem-sfb-regular-separable-affine-smooth-neighbourhood gives a smooth identity
   neighbourhood. The group is flat over k by lem-weil-pbc-module-over-field-flat;
   lem-sfb-group-smoothness-identity-criterion makes A smooth everywhere.
6. Smoothness gives reducedness by lem-sc-smooth-algebra-reduced-field and the local
   regularity results. By lem-wf-smooth-components-disjoint and connectedness, A is
   irreducible.
7. A proper closed image would have smaller dimension by lem-wf-affine-dimension-drop;
   compare prime-chain and topological dimensions by
   lem-weil-pbc-spec-topological-krull-dimension-ring. Hence the image is all of A.
8. Apply lem-weil-pbc-reduced-source-factors-through-closed-subscheme to the identity
   of the reduced scheme A. This provides a section of j, hence C -> C/I is injective
   as well as surjective. Thus I = 0 and j is an isomorphism. Its inverse is over k
   and respects multiplication, identity and inverse by cancellation with j.
-/
theorem isIso_of_smooth_closedSubgroup_surjective_tangent
    (k : Type u) [Field k] (A B : Over (Spec (.of k))) [GrpObj A] [GrpObj B]
    [IsAffine A.left] [LocallyOfFiniteType A.hom] [QuasiCompact A.hom]
    [ConnectedSpace A.left] (j : B ⟶ A) [IsClosedSubgroupScheme j] [Smooth B.hom]
    (hsurj : ∃ he : Function.Bijective (j.left.residueFieldMap (GrpObj.onePoint B)).hom,
      Function.Surjective
        (schemeTangentMap k B.left A.left B.hom A.hom j.left j.w
          (GrpObj.onePoint B) he)) :
    IsIso j := by
  sorry

end AlgebraicGeometry
