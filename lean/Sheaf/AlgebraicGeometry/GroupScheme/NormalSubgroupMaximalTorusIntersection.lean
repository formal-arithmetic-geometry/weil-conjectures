/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.MultiplicativeTypeLargestSubtorus
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Maximal tori in connected normal subgroups

Source: Milne, Algebraic Groups (2017), Corollary 17.85, printed pp.379--380;
Notation 12.29, p.241, and Remark 12.5, p.232
(blueprint: lem-sfb-normal-subgroup-maximal-torus-intersection).

The intersection is specified by its pullback square in schemes over the base field.
Its reduced identity component has the open subscheme structure in the actual
nilradical quotient. The isomorphism and commuting inclusion identify its group law
with the subgroup law, rather than merely identifying its rational points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The reduced identity component of the intersection with a maximal torus is a
closed split torus, and is maximal in the connected normal subgroup.
Source: Milne, Corollary 17.85, pp.379--380, Notation 12.29, p.241,
and Remark 12.5, p.232
(blueprint: lem-sfb-normal-subgroup-maximal-torus-intersection).

Proof:
1. The pullback D of M and T is a closed subgroup of T by
lem-weil-pbc-closed-immersion-base-change and def-sc-group-scheme-subgroup.
Its coordinate algebra is a quotient of that of T, so it is affine of finite type
(def-weil-closed-immersion and def-weil-finite-type-morphism). Apply
lem-sfb-locally-algebraic-group-identity-component. Reduction commutes with restriction
to the open identity component (def-weil-pbc-scheme-reduction), so its reduced
identity component H is smooth, connected and closed in D. As a closed subgroup of
T it is a torus by lem-sfb-multiplicative-type-largest-subtorus, and it splits over F.
2. Every torus in D is smooth, hence reduced by sbc-lem-smooth-geometrically-reduced.
It factors through the nilradical quotient and then through the open identity
component, since its connected image contains the identity. Its factorization is
closed: a surjection of affine coordinate rings remains surjective after factoring
through a quotient (def-weil-closed-immersion).
3. For X equal to M or G, lem-kun-dimension-finite-type bounds dimensions of torus
subgroups. They are integral by the identity-component lemma, smooth reducedness,
and connectedness, and nonempty by the identity. Thus their dimensions are
nonnegative integers bounded by the dimension of X (def-kun-dimension).
4. Among tori containing a given torus choose one of greatest dimension. A strictly
larger torus would have a strictly larger closed underlying space: a quotient of a
domain with the same spectrum has zero defining ideal. Appending the larger
irreducible space to a longest chain increases dimension, a contradiction.
5. The rank-zero identity torus is closed in the affine group M. Steps 3--4 give a
maximal torus S of M and then a maximal torus R of G containing S. Composite closed
immersions are closed, by composition of coordinate-ring surjections.
6. By lem-sfb-borel-maximal-torus-conjugacy conjugate R to the prescribed T by g in
G(F). Normality preserves M under conjugation on every algebra. The conjugate S1
of S is a torus in both M and T, hence in D, and remains maximal in M by conjugating
any larger torus back.
7. Step 2 puts S1 in H. Since H is itself a torus in M, maximality gives S1 = H.
The dimension argument includes rank zero. No reductivity of G or M, or smoothness
or reducedness of D, was used. -/
theorem normalSubgroup_maximalTorus_intersection
    (F : Type u) [Field F] [IsAlgClosed F]
    (G M T : Grp (Over (Spec (.of F))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [Smooth M.X.hom] [ConnectedSpace M.X.left]
    (iM : M ⟶ G) [IsClosedSubgroupScheme iM.hom.hom]
    [IsNormalSubgroupScheme iM.hom.hom]
    (iT : T ⟶ G) (hT : ReductiveTorusCentralizer.IsMaximalTorus iT) :
    ∃ (D H : Grp (Over (Spec (.of F)))) (pM : D ⟶ M) (pT : D ⟶ T),
      IsPullback pM.hom.hom pT.hom.hom iM.hom.hom iT.hom.hom ∧
      ∃ U : D.X.left.nilradical.subscheme.Opens,
        (U : Set D.X.left.nilradical.subscheme) =
          D.X.left.nilradical.subschemeι ⁻¹' connectedComponent (GrpObj.onePoint D.X) ∧
        ∃ (e : H.X ≅ Over.mk (U.ι ≫ D.X.left.nilradical.subschemeι ≫ D.X.hom))
          (j : H ⟶ D),
          j.hom.hom.left = e.hom.left ≫ U.ι ≫ D.X.left.nilradical.subschemeι ∧
          IsClosedSubgroupScheme j.hom.hom ∧
          (∃ n : ℕ, Nonempty (H ≅ MultiplicativeType.splitTorus F n)) ∧
          ReductiveTorusCentralizer.IsMaximalTorus (j ≫ pM) := by
  sorry

end AlgebraicGeometry
