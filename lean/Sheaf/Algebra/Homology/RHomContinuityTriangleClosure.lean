/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-! # Triangle closure of bounded-target internal-Hom continuity

Source: Stacks Project, Cohomology on Sites, Tag 08JC, and the formal bounded-target
closure argument extracted from Bhatt--Scholze, Lemmas 6.3.14 and 6.8.12
(blueprint: lem-sfb-rhom-continuity-triangle-closure).

The predicate below is the P introduced in the statement. Its comparison is the image
under Q of the actual complex-level colimit.post for the existing functor homFixed.
Thus no colimit in the unbounded derived category is used. Every complex representative
of the source is allowed, and the target bound is cohomological, not termwise.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedHomUniverses

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

/-- The property P of the node: continuity for all uniformly cohomologically bounded-below
filtered complex diagrams, and a uniform lower-bound offset for the target variable.
Source: Stacks 08JC and the bounded-target closure extraction in the node
(blueprint: lem-sfb-rhom-continuity-triangle-closure).

The canonical map is Q(colimit.post M (homFixed L)); its coprojection at i is the
localized Hom map of the target coprojection. Exact termwise sheaf colimits compute
its source. Quantification over source representatives avoids a choice of an object
or a noncanonical comparison. The colimit structures quantified here exist for small
module-sheaf diagrams and are only the structures needed to form the displayed map. -/
def BoundedTargetHomContinuous (A : D.{c, v, r, w} J R) : Prop :=
  (∀ (L : Complex.{c, v, r} J R), Nonempty (DerivedCategory.Q.obj L ≅ A) →
    ∀ (I : Type (max c v r)) [SmallCategory I] [IsFiltered I]
      [HasColimitsOfShape I (Modules.{c, v, r} J R)]
      (M : I ⥤ Complex.{c, v, r} J R) (b : ℤ),
      (∀ i : I, (DerivedCategory.Q.obj (M.obj i)).IsGE b) →
        IsIso (DerivedCategory.Q.map (colimit.post M
          (WeilConjectures.SfbHomFilteredColimit.homFixed.{c, v, r} J R L)))) ∧
  ∃ d : ℤ, ∀ (b : ℤ) (N : D.{c, v, r, w} J R),
    N.IsGE b → ((hom.{c, v, r, w} J R A).obj N).IsGE (b + d)

/-- The sources satisfying P contain zero, are invariant under isomorphisms, and form a
triangulated subcategory. The source shift by n takes any lower-bound offset d to d+n.
Finite iterated extensions of isomorphic shifts of any family satisfying P satisfy P.
Source: Stacks 08JC, with exact filtered colimits (03DB), the cohomology long exact
sequence (05RS), and the five lemma (05QB)
(blueprint: lem-sfb-rhom-continuity-triangle-closure).

Proof:
1. Exact filtered colimits of module sheaves commute with cycles, boundaries and
cohomology. Thus termwise colimits preserve quasi-isomorphisms and common cohomological
lower bounds; the specified complex models compute the comparisons in D(O).
2. Hom(0,N) is zero, its comparison is the zero isomorphism, and offset 0 works.
Precomposition with a source isomorphism identifies both comparison maps and bounds.
3. The signed, natural source-shift isomorphism identifies H(A[n],N) with H(A,N)[-n].
Termwise colimits commute with shifts. Since H^q(K[-n])=H^(q-n)(K), the new offset is d+n.
4. A distinguished triangle A -> B -> C -> A[1] gives the contravariant distinguished
Hom triangle for every target. Target cocone maps yield a comparison of the long exact
cohomology rows, including the boundary squares by naturality of the signed shifts.
5. If P(A) and P(C) hold, filtered exactness and the five lemma on the five terms
H^(q-1)(H(A,N)), H^q(H(C,N)), H^q(H(B,N)), H^q(H(A,N)), H^(q+1)(H(C,N))
make the actual comparison for B an isomorphism in every cohomology degree, hence in D(O).
6. Exactness of the three middle cohomology terms gives B the offset min(d_A,d_C),
uniformly in b,N. This proves both clauses of P for the middle vertex.
7. Rotate the triangle. The other two cases follow with offsets min(d_C-1,d_B)
and min(d_B,d_A+1). Thus two-out-of-three holds at every position.
8. Induct on a finite construction. Use zero and source isomorphism invariance at the
base, source-shift closure at each shift, and two-out-of-three at each triangle.
Equivalently, shifts and isomorphisms can be moved through triangles, so finite
constructions are finite iterated extensions of isomorphic shifted initial sources. -/
theorem boundedTargetHomContinuous_triangle_closure :
    ObjectProperty.IsClosedUnderIsomorphisms
      (BoundedTargetHomContinuous.{c, v, r, w} J R) ∧
    ObjectProperty.IsTriangulated (BoundedTargetHomContinuous.{c, v, r, w} J R) ∧
    (∀ (A : D.{c, v, r, w} J R), BoundedTargetHomContinuous.{c, v, r, w} J R A →
      ∀ d : ℤ,
      (∀ (b : ℤ) (N : D.{c, v, r, w} J R), N.IsGE b →
        ((hom.{c, v, r, w} J R A).obj N).IsGE (b + d)) →
      ∀ (n b : ℤ) (N : D.{c, v, r, w} J R), N.IsGE b →
        ((hom.{c, v, r, w} J R (A⟦n⟧)).obj N).IsGE (b + (d + n))) ∧
    (∀ S : ObjectProperty (D.{c, v, r, w} J R),
      S ≤ BoundedTargetHomContinuous.{c, v, r, w} J R → ∀ n : ℕ,
        (S.shiftClosure ℤ).extensionProductIter n ≤
          BoundedTargetHomContinuous.{c, v, r, w} J R) := by
  sorry

end CategoryTheory.RingedHomUniverses
