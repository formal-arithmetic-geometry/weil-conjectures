/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover
public import Mathlib.AlgebraicGeometry.Group.Affine
import Sheaf.AlgebraicGeometry.GroupScheme.GeneralBorelFlagVariety
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Sheaf.AlgebraicGeometry.GroupScheme.BorelQuotientProperGeometry
import Sheaf.AlgebraicGeometry.Curve.CompleteCurveConnectedLinearAction
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.ConnectedActionMultiplicativeTypeRigidity
import Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange
import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Sheaf.AlgebraicGeometry.GroupScheme.PGL2ProperConnectedSubgroupSolvable

/-! # The adjoint quotient of a reductive group of semisimple rank one

Source: Milne, Algebraic Groups (2017), Theorem 20.22, printed p.415, and
Theorem 20.16, printed pp.412--413
(blueprint: lem-sfb-rank-one-adjoint-projective-linear).

The target is any presentation of the already recorded projective matrix quotient
in size two. Its presentation is a parameter, so no representative is chosen from
an existence theorem. The centre is identified by its image on all test algebras,
including nonreduced algebras, using the recorded universal centralizer condition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A reductive group of semisimple rank one maps faithfully flatly onto PGL2,
with the full scheme-theoretic centre as kernel. The map presents the fppf quotient;
any other represented quotient by the same centre has a compatible group isomorphism
with PGL2. The PGL2 presentation and the semisimple-rank predicate are the existing
ones, and no restriction on the characteristic or reducedness of test algebras is made.

Source: Milne, Algebraic Groups (2017), Theorem 20.22, printed p.415, and
Theorem 20.16, printed pp.412--413
(blueprint: lem-sfb-rank-one-adjoint-projective-linear).

Proof plan:
1. Choose a maximal torus and a Borel B+ by lem-sfb-general-borel-flag-variety and
   lem-sfb-borel-maximal-torus-conjugacy. The opposite Borel B- is supplied by
   lem-sfb-rank-one-opposite-borel-intersection. The homogeneous quotient C = G/B+
   is represented and has the expected points by lem-sfb-homogeneous-orbit-quotient-geometry.
   The flat, surjective, finitely presented quotient map of
   lem-sfb-algebraic-group-homogeneous-quotient and lem-sfb-borel-quotient-proper-geometry
   give smoothness, properness and integrality. By lem-sfb-rank-one-flag-curve, dim C = 1.
2. Left multiplication on the coset sheaf gives a transitive action on C(F). It is
   nontrivial because its orbit map is the surjective map onto the curve C.
   Lem-sfb-complete-curve-connected-linear-action gives C isomorphic to P1, and
   lem-sfb-projective-frames-pgl identifies its automorphism sheaf with PGL2. This
   defines q. Transport to the specified projective matrix presentation.
3. Factor q through its faithfully flat image I by lem-sfb-affine-homomorphism-flat-image.
   The coordinate injection of lem-weil-pbc-faithfully-flat-universally-injective and
   sbc-lem-smooth-geometrically-reduced make I reduced; the spectrum surjectivity of
   lem-weil-pbc-faithfully-flat-surjective-spectrum makes I connected. If I were proper,
   lem-sfb-pgl2-proper-connected-subgroup-solvable and lem-sfb-solvable-proper-fixed-point
   would give a fixed point on C, contradicting transitivity and the two distinct points
   zero and infinity. Thus I = PGL2, so q is faithfully flat.
4. Its kernel K lies in B+ by the stabilizer description in
   lem-sfb-homogeneous-orbit-quotient-geometry. Normality and
   lem-sfb-torus-normalizer-borel-transitivity put K in B- too. Hence K lies in the torus
   by lem-sfb-rank-one-opposite-borel-intersection. It is diagonalizable by
   lem-sfb-split-torus-subgroups-diagonalizable, so conjugation by G is trivial by
   lem-sfb-connected-action-multiplicative-type-rigidity. Thus K is contained in Z(G)
   after every algebra extension, including nonreduced ones.
5. The centre is a closed normal subgroup by lem-sfb-affine-group-centre-base-change.
   Lem-sfb-reductive-torus-self-centralizer puts it in T and hence in B+. Lift every
   coset fppf locally; centrality gives zgB+ = gzB+ = gB+, so it acts trivially on C.
   Descent gives Z(G) contained in K on all test algebras, proving equality as subgroup
   schemes, not merely on rational points.
6. Lem-sfb-affine-normal-quotient-geometry represents G/Z(G). By
   lem-sfb-faithfully-flat-group-quotient-universal, q and any quotient map p factor
   uniquely through one another. Uniqueness makes the two factors inverse and gives
   the compatible isomorphism. No step requires an invertible characteristic or a
   reduced kernel. -/
theorem rankOne_adjoint_projectiveLinear
    {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F))))
    (hG : ReductiveTorusCentralizer.IsReductive G)
    (hRank : RankOneRoots.HasSemisimpleRankOne G)
    (P : Grp (Over (Spec (.of F))))
    (π : GeneralLinearGroup (LinearGroupSchemes.Index.{u} 2) F ⟶ P.X)
    (j : StandardGroupSchemes.roots F 2 ⟶ LinearGroupSchemes.specialLinear F 2)
    (hP : ProjectiveMatrixCentralCover.Presentation F 2 (Nat.le_refl 2) P π j) :
    ∃ (Z : Grp (Over (Spec (.of F)))) (i : Z ⟶ G) (q : G ⟶ P),
      IsClosedSubgroupScheme i.hom.hom ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A],
        ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A =
          Set.range (fun z : (algSpec (.of F)).obj (.op (CommAlgCat.of F A)) ⟶ Z.X ↦
            z ≫ i.hom.hom)) ∧
      q.hom.hom.left.appTop.hom.FaithfullyFlat ∧
      IsFppfGroupQuotient i q ∧
      ∀ (Q : Grp (Over (Spec (.of F)))) (p : G ⟶ Q),
        IsFppfGroupQuotient i p → ∃ e : Q ≅ P, p ≫ e.hom = q := by
  sorry

end AlgebraicGeometry
