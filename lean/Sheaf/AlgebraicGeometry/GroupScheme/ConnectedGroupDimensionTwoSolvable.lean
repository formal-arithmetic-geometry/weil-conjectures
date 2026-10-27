/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.Topology.KrullDimension

import Sheaf.AlgebraicGeometry.GroupScheme.Borel
import Sheaf.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
import Sheaf.AlgebraicGeometry.StandardGroupSchemes

/-! # Connected affine groups of dimension at most two are solvable

Source: Milne, Algebraic Groups (2017), Corollary 17.27, printed p.360,
with the standing hypotheses of Section 17(b), printed p.353, Proposition 1.26,
printed p.13, and Proposition 6.30, printed p.132.
(blueprint: lem-sfb-connected-group-dimension-two-solvable)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected affine algebraic group of dimension at most two over an
algebraically closed field is solvable in the scheme-theoretic derived-series sense,
in every characteristic.

Source: Milne, Algebraic Groups (2017), Corollary 17.27, printed p.360;
Section 17(b), printed p.353; Propositions 1.26 and 6.30.
(blueprint: lem-sfb-connected-group-dimension-two-solvable)

Proof:
1. Choose a smooth connected solvable closed subgroup B of greatest dimension.
   The identity subgroup supplies one, and dimensions are nonnegative integers bounded
   by dim G. Strict dimension growth for proper inclusions makes B a Borel subgroup
   (`lem-sfb-solvable-normal-subgroup-products`, `def-sfb-borel-subgroup-scheme`).
   Write d = dim B. If d = 2, a proper inclusion would force dim G > 2; hence B = G.
2. For d at most one, use the derived series to give a normal series with commutative
   quotients: the next derived subgroup contains every commutator, so it is normal,
   and commutators of local sections of the quotient lift locally and vanish.
   The field is perfect since it is algebraically closed. Apply
   `lem-sfb-perfect-solvable-unipotent-torus` to obtain a smooth connected normal
   unipotent U in B with torus quotient D. The quotient is affine of finite type,
   its map is faithfully flat of finite presentation, its kernel is U, and
   B times D B is B times U (`lem-sfb-affine-normal-quotient-geometry`).
   The group is separated (`lem-sc-group-scheme-separated-field`), so
   `lem-sfb-homogeneous-quotient-krull-dimension` gives d = dim U + dim D.
   One of these nonnegative dimensions is zero.
3. A smooth connected zero-dimensional group is trivial: otherwise strict dimension
   growth from its identity subgroup gives a contradiction
   (`lem-sfb-solvable-normal-subgroup-products`). If D is trivial, B = U by the kernel
   equality. If U is trivial, the quotient map is a monomorphism by the torsor identity;
   its locally existing lifts are unique and glue, so it is an isomorphism
   (`lem-sfb-affine-normal-quotient-geometry`). Thus B is unipotent or a torus.
4. In the unipotent case, `lem-sfb-perfect-unipotent-additive-series` supplies a finite
   central series. Kernel and image descriptions of the represented quotients translate
   its centrality into [B(A), B_i(A)] contained in B_{i+1}(A), for every algebra A
   (`lem-sfb-affine-normal-quotient-geometry`). A torus is commutative since it is a
   product of multiplicative groups (`def-sc-gm-ga`), so it too has a nilpotent series.
   In either case `lem-sfb-nilpotent-borel-equals-group` gives G = B. Since B was chosen
   solvable, the scheme-theoretic derived series of G terminates. -/
theorem connected_group_dimension_two_solvable {k : Type u} [Field k] [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom] [ConnectedSpace G.left]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (hdim : topologicalKrullDim G.left ≤ 2) : IsSolvableGroupScheme G := by
  sorry

end AlgebraicGeometry
