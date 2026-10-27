module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.StackClosedImmersionCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition

/-!
# Closed operations on relatively proper supports of algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tags 0CZC, 0CZE and 0CZH;
Properties of Spaces, Tag 047X
(blueprint: lem-sfb-space-proper-support-closed-operations).

Reduced induced structures are quantified as reduced closed subspaces with the specified
point image. Their existence and uniqueness are supplied by
`exists_unique_reduced_closed_subspace`; no extra choice of a reduced structure is needed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Properness of a closed support is independent of its closed-subspace structure and
is preserved under passage to smaller closed subsets and finite unions, including the
empty union. Properness of a support means properness of its reduced induced structure.
Source: Stacks Project, Tags 0CZC, 0CZE, 0CZH and 047X
(blueprint: lem-sfb-space-proper-support-closed-operations).

Proof:
1. Every closed subspace is locally of finite type over Y: its inclusion is proper by
lem-sfb-space-closed-subspace-proper and local finite type composes by
lem-sfb-stack-finite-type-calculus, specialized to spaces. Reduced structures exist
uniquely by lem-sfb-space-reduced-closed-support, without Noetherian hypotheses.
2. For any closed structure D on T, reduce D on its entire point space. Its composite
closed embedding in X (lem-sfb-stack-closed-immersion-calculus) identifies it with the
reduced structure R on T by uniqueness. Hence R -> D is a thickening. Apply
lem-sfb-space-thickening-topological-properties with target thickening the identity of Y.
Separatedness, quasi-compactness and universal closedness agree for R -> Y and D -> Y;
both are locally of finite type by step 1. Thus their properness is equivalent, giving
both the existential and universal characterizations.
3. If T' is closed and contained in T, its inverse image in the proper reduced structure
on T has a reduced closed structure by lem-sfb-space-reduced-closed-support. Its inclusion
is proper by lem-sfb-space-closed-subspace-proper; compose using
lem-sfb-space-proper-composition. Its closed image in X is T', and step 2 gives the claim.
4. For a nonempty finite family, let Z be the reduced structure on its union, and Z_i
those on its members. The spaces W_i = Z_i times_X Z are closed in Z_i and Z by
lem-sfb-space-reduced-closed-support. Their point images cover Z; they need not be reduced.
Each W_i -> Y is proper by closed-immersion properness and proper composition.
5. Form D = coproduct W_i using lem-trf-algebraic-space-coproduct. The scheme-test
partitions of lem-trf-fppf-sheaf-coproduct-partition give disjoint clopen components after
every base change. D -> Y is proper: the chart criterion
lem-sfb-space-local-properties-chart-test gives local finite type; the diagonal is closed
on each clopen block; affine tests give finite disjoint unions of quasi-compact spaces;
and images of closed sets after base change are finite unions of closed images.
6. The induced map D -> Z is universally closed and surjective. Closed immersions stay
closed after base change by lem-sfb-stack-closed-immersion-calculus, so closed images from
its finitely many components remain closed. Surjectivity persists after base change by
lem-a1-space-point-open-calculus.
7. Apply lem-sfb-space-relative-uc-surjection-separated over Y to deduce separatedness
of Z -> Y. On every affine test, its source is a continuous surjective image of the
quasi-compact corresponding test of D. For every base change and closed C in Z, its
inverse image in D is closed and has the same image in the base by surjectivity; that
image is closed since D is proper. Thus Z -> Y is quasi-compact and universally closed;
step 1 supplies local finite type, proving properness.
8. For the empty family, the empty coproduct is the empty scheme by
lem-trf-fppf-sheaf-coproduct-partition. It is reduced and closed in X, hence is its unique
reduced structure on the empty subset. Its map to Y is a closed immersion, thus proper
by lem-sfb-space-closed-subspace-proper. Empty summands and repeated supports are allowed.
-/
theorem proper_support_closed_operations {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : MapIsLocally (@LocallyOfFiniteType) f) :
    (∀ (T : TopologicalSpace.Closeds (Point X.obj.obj)) (R : ClosedSubspace X),
      IsReduced (R.val : AlgebraicSpace S) →
      pointImage R.val.arrow.hom.hom = (T : Set (Point X.obj.obj)) →
      (MapIsProper (R.val.arrow ≫ f) ↔
        ∃ D : ClosedSubspace X,
          pointImage D.val.arrow.hom.hom = (T : Set (Point X.obj.obj)) ∧
          MapIsProper (D.val.arrow ≫ f)) ∧
      (MapIsProper (R.val.arrow ≫ f) ↔
        ∀ D : ClosedSubspace X,
          pointImage D.val.arrow.hom.hom = (T : Set (Point X.obj.obj)) →
          MapIsProper (D.val.arrow ≫ f))) ∧
    (∀ (T T' : TopologicalSpace.Closeds (Point X.obj.obj))
      (R R' : ClosedSubspace X), T' ≤ T →
      IsReduced (R.val : AlgebraicSpace S) →
      pointImage R.val.arrow.hom.hom = (T : Set (Point X.obj.obj)) →
      IsReduced (R'.val : AlgebraicSpace S) →
      pointImage R'.val.arrow.hom.hom = (T' : Set (Point X.obj.obj)) →
      MapIsProper (R.val.arrow ≫ f) → MapIsProper (R'.val.arrow ≫ f)) ∧
    (∀ (n : ℕ) (T : Fin n → TopologicalSpace.Closeds (Point X.obj.obj))
      (R : Fin n → ClosedSubspace X),
      (∀ i : Fin n, IsReduced ((R i).val : AlgebraicSpace S) ∧
        pointImage (R i).val.arrow.hom.hom = (T i : Set (Point X.obj.obj)) ∧
        MapIsProper ((R i).val.arrow ≫ f)) →
      ∀ C : ClosedSubspace X, IsReduced (C.val : AlgebraicSpace S) →
        pointImage C.val.arrow.hom.hom = ⋃ i : Fin n, (T i : Set (Point X.obj.obj)) →
        MapIsProper (C.val.arrow ≫ f)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
