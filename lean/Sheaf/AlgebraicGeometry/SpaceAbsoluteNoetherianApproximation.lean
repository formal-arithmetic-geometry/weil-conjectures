module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleAtlasPresentation
import Sheaf.AlgebraicGeometry.SpaceFiniteTypeComposition
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceFpOverSpaceLimitDescent
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.AlgebraicGeometry.Gluing

/-! # Absolute Noetherian approximation for algebraic spaces

Source: Stacks Project, spaces-limits.tex, Tag 07SU, proposition-approximate;
spaces-morphisms.tex, Tag 04ZK, lemma-locally-finite-type-locally-noetherian
(blueprint: lem-sfb-space-absolute-noetherian-approximation).

The limit is specified by a limiting cone with vertex the given space. No chosen
limit object or additional existence assumption for limits is required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every qcqs algebraic space has an affine inverse system of Noetherian stages
of finite type over Spec Z.
Source: Stacks, Tag 07SU, proposition-approximate, with the Noetherian consequence
of Tag 04ZK (blueprint: lem-sfb-space-absolute-noetherian-approximation).

Proof following the eleven steps of the node:
1. Apply lem-sfb-qcqs-space-splitting-filtration. Its qc opens are qs by
   lem-sfb-space-integral-qcqs-permanence. Descend through the finite filtration.
   The last open is a qc separated scheme, so apply prop-nagata-noetherian-inverse-system
   and lem-weil-pbc-cofiltered-limit-directed-reindex. Its finite-type stages are
   Noetherian by lem-weil-pbc-finite-type-over-noetherian and qs by
   lem-weil-pbc-locally-noetherian-quasi-separated. The empty space uses a constant system.
2. At a step write X = U_p, U = U_(p+1), V = V_p, Z = T_p and W = V ×_X U.
   By lem-sfb-qcqs-space-fibre-product, W is qcqs. Its map to U is etale by
   lem-trf-space-chartwise-etale-permanence and qcqs by lem-sfb-space-qcqs-permanence,
   hence finitely presented. Apply lem-sfb-space-fp-over-space-limit-descent to descend
   it to W_0 over U_0. Use lem-sfb-space-fp-qcqs-source and
   lem-sfb-space-etaleness-eventual-stage to make the stage source qcqs and the map etale.
3. Set W_i = W_0 ×_(U_0) U_i. Use lem-sfb-space-flat-proper-fp-locality and
   lem-trf-space-chartwise-etale-permanence for finite presentation and etaleness.
   By lem-sfb-space-affine-locality and lem-sfb-space-affine-limits-schematic-stages,
   W is their limit and a tail consists of schemes. These stages are finite type over Z
   by lem-sfb-space-qcqs-permanence, lem-sfb-space-finite-type-composition and
   lem-sfb-space-local-properties-chart-test. Apply
   lem-sfb-scheme-approximation-prescribed-open to extend W_i to finite-type schemes V_i
   approximating V, with affine transitions and compatible open inclusions W_i in V_i.
   Cofinal reindexing preserves U as limit. The scheme stages are qs by the two
   Noetherian scheme results used in step 1.
4. Set E_i = W_i ×_(U_i) W_i, a scheme by lem-trf-space-fibre-products-etale-covers.
   Its diagonal is an etale monomorphism by lem-trf-space-chartwise-etale-permanence,
   hence open by lem-sfb-space-etale-monomorphism-open. Glue V_i and E_i along W_i
   using lem-weil-pbc-glue-schemes, obtaining R_i with etale projections to V_i by
   lem-weil-pbc-etale-local-on-source. Identity, inversion and composition are the
   identity relation off W_i and the kernel relation on W_i. They agree on overlaps,
   and the relation map is a monomorphism, checked on these opens.
5. Form X_i = V_i/R_i by lem-trf-etale-relation-quotient. Its atlas V_i makes it qc.
   The overlap E_i is qcqs by lem-sfb-qcqs-space-fibre-product, so R_i is qc.
   Its projections are qc by lem-sfb-space-qcqs-permanence. Apply
   lem-sfb-space-qs-atlas-criterion for qs, and lem-sfb-space-local-properties-chart-test
   for local finite type. Together with qc this gives finite type over Z.
6. Glue the transition maps on V_i and E_i and descend them to X_i using
   lem-trf-etale-relation-quotient. The source squares of R_i over V_i are cartesian:
   pull back the open pieces V_j and E_j; they become V_i and E_i because
   W_i = V_i ×_(V_j) W_j = W_j ×_(U_j) U_i. The two comparisons agree on W_i.
7. Local lifting and the kernel-pair description in lem-trf-etale-relation-quotient
   now identify V_i with X_i ×_(X_j) V_j. Thus X_i to X_j is affine by
   lem-sfb-space-affine-locality. Form X' = lim X_i by
   lem-sfb-space-affine-limits-schematic-stages. Its base-change formula gives a
   surjective etale atlas V to X' by lem-trf-space-chartwise-etale-permanence,
   with kernel pair R = lim R_i.
8. The transitions of R_i are affine by the source-cartesian squares and
   lem-sfb-space-affine-locality. Apply the base-change formula of
   lem-sfb-space-affine-limits-schematic-stages to the two opens of a fixed R_0.
   Their inverse images in R are V and W ×_U W, intersecting in W. These comparisons
   preserve both projections to V.
9. By lem-a1-etale-atlas-presentation, X is the quotient of V by V ×_X V.
   This relation is likewise covered by its open diagonal V and W ×_U W:
   a pair outside U lies over Z, where the atlas is an isomorphism. Its intersection
   with the diagonal is W. Gluing identifies it with R, preserving both projections.
   Apply the same atlas-presentation lemma to X' to identify X with X'.
10. This proves the descending induction, and hence supplies the system for Y = U_1.
11. Each constructed atlas V_i is finite type over Z, hence Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. It is in particular locally Noetherian,
   proving the asserted atlas clause. Step 5 gives qc and qs. The scheme base case
   has the same properties. The finite induction and the small scheme systems keep
   the index small, and no step assumes Y itself Noetherian or finite type. -/
theorem exists_absoluteNoetherianApproximation
    (Y : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (hqc : CompactSpace (Point Y.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated Y) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (π : (Functor.const Iᵒᵖ).obj Y ⟶ D),
      Nonempty (IsLimit (Cone.mk Y π)) ∧
      (∀ (i j : I) (h : i ≤ j), MapIsAffine (D.map (homOfLE h).op)) ∧
      ∀ i : I, IsAbsolutelyQuasiSeparated (D.obj (op i)) ∧
        (∃ p : D.obj (op i) ⟶
            schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of (ULift.{u} ℤ))))),
          MapIsFiniteType p) ∧
        CompactSpace (Point (D.obj (op i)).obj.obj) ∧
        ∃ (U : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
          (a : yoneda.obj U ⟶ (D.obj (op i)).obj.obj),
          IsEtale a ∧ IsSurjective a ∧ IsLocallyNoetherian U.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
