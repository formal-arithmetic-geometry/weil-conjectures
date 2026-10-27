/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.GeneralBorelFlagVariety
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Rank-one Borel quotients are curves

Source: Milne, Algebraic Groups (2017), Theorem 20.16, (a) implies (c), printed
pp.412--413, and Corollary 20.12, printed p.411
(blueprint: lem-sfb-rank-one-flag-curve).

The rank condition uses the recorded radical-quotient predicate. The quotient by the
Borel is any representation of the fppf sheafification of the right-coset presheaf,
using exactly the presentation of the homogeneous-quotient theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A Borel quotient of a reductive group of semisimple rank one has Krull dimension one,
in every characteristic. The radical and its quotient are specified by
`RankOneRoots.HasSemisimpleRankOne`; in particular solvability is termination of the
scheme-theoretic derived series. The displayed coequalizer is the presheaf of right
cosets, and its unit into the represented sheaf is the fppf sheafification arrow.

Source: Milne, Algebraic Groups (2017), Theorem 20.16, printed pp.412--413,
(a) implies (b) implies (c), and Corollary 20.12, printed p.411
(blueprint: lem-sfb-rank-one-flag-curve).

Proof, following the four steps of the node:
1. Take the smooth connected projective Borel variety Y supplied by
   lem-sfb-general-borel-flag-variety and the point corresponding to B. Its full
   scheme-theoretic stabilizer is B. By lem-sfb-smooth-group-orbit-geometry and
   lem-sfb-homogeneous-orbit-quotient-geometry its reduced orbit is the displayed
   fppf quotient. Transitivity gives every F-point of Y in the orbit. Closed points
   are F-rational by lem-weil-pbc-closed-point-residue-field-base, and are dense in
   every closed subset by lem-sc-lft-over-field-jacobson-space. Thus the locally
   closed orbit is open and its closed complement is empty. Smoothness makes Y
   reduced by sbc-lem-smooth-geometrically-reduced, so the reduced orbit equals Y
   scheme-theoretically. Hence the quotient is isomorphic to Y, equivariantly.
2. Apply the two-Borel clause of lem-sfb-rank-one-opposite-borel-intersection.
   The Borel-variety correspondence identifies these with exactly two distinct
   scheme-theoretically T-fixed F-points of Y.
3. Apply lem-sfb-proper-homogeneous-torus-fixed-bound to H = B, S = T, and Y.
   The proper homogeneous space has at least dim(Y) + 1 distinct fixed points.
   Consequently dim(Y) is at most one.
4. If dim(Y) is at most zero, lem-weil-pbc-finite-type-dim-zero-artinian makes
   Y finite and discrete. Nonemptiness and connectedness make its space a singleton.
   Its residue field is F by lem-weil-pbc-closed-point-residue-field-base; every
   F-point factors through that residue field and its unique F-algebra map to F.
   This gives only one F-point, contradicting step 2. Therefore dim(Y) = 1.
   Transport the dimension through the quotient isomorphism of step 1.
-/
theorem rankOne_flag_quotient_dimension
    {F : Type u} [Field F] [IsAlgClosed F]
    (G T B : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (hRank : RankOneRoots.HasSemisimpleRankOne G)
    (iB : B ⟶ G) (hB : IsBorelGroupScheme iB.hom.hom)
    (t : T ⟶ B) (ht : t ≫ iB = iT)
    (Q : Over (Spec (.of F))) (q : G.X ⟶ Q)
    (hQ : Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.obj Q))
    (ηq : coequalizer (yoneda.map (fst G.X B.X))
      (yoneda.map (lift (fst G.X B.X) (snd G.X B.X ≫ iB.hom.hom) ≫ μ[G.X])) ⟶
        yoneda.obj Q)
    (hηq : coequalizer.π _ _ ≫ ηq = yoneda.map q)
    (hUniversal : ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
      Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηq ≫ f)) :
    topologicalKrullDim Q.left = 1 := by
  sorry

end AlgebraicGeometry
