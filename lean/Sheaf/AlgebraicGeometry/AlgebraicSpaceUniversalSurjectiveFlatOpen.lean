/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import Sheaf.AlgebraicGeometry.SpaceInvariantOpenQuotient
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # The universal surjective-flat locus of a diagram of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 05XC,
`spaces-more-morphisms-lemma-where-surjective-flat`
(blueprint: lem-sfb-space-universal-surjective-flat-open).

The parameter spaces are arbitrary algebraic spaces over the fixed scheme, with no
representability assumption on the morphism whose flatness and surjectivity are tested.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical map `A ×_B T → C ×_B T` of sheaf fibre products, regarded as a
morphism of algebraic spaces using `fibreProduct_isAlgebraicSpace`.
Source: Stacks Project, Tag 05XC, the base change of its commutative diagram
(blueprint: lem-sfb-space-universal-surjective-flat-open). -/
def baseChangeDiagramMap {S : Scheme.{u}} {A C B T : AlgebraicSpace S}
    (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C) (w : f ≫ q = p) (h : T ⟶ B) :
    (⟨Limits.pullback p.hom h.hom, (fibreProduct_isAlgebraicSpace A T B p h).1⟩ :
      AlgebraicSpace S) ⟶
    (⟨Limits.pullback q.hom h.hom, (fibreProduct_isAlgebraicSpace C T B q h).1⟩ :
      AlgebraicSpace S) :=
  ⟨Limits.pullback.map p.hom h.hom q.hom h.hom f.hom (𝟙 T.obj) (𝟙 B.obj)
    (by simpa using (congrArg (fun k : A ⟶ B ↦ k.hom) w).symm) (by simp)⟩

/-- Flatness and point-surjectivity after base change are represented by an open subspace.
Closedness of `p` and `q` says that the image on point classes of every closed set is closed;
surjectivity says that the point image of `f_T` is all of `|C ×_B T|`; images are taken on
field-valued representatives as in `pointImage`.
Source: Stacks Project, More on Morphisms of Spaces, Tag 05XC,
`spaces-more-morphisms-lemma-where-surjective-flat`
(blueprint: lem-sfb-space-universal-surjective-flat-open).

Proof:
1. Apply lem-sfb-space-relative-flat-locus-base-change to `(A,C,B)`. Its flat locus L
   is open in |A|. Its complement E is closed, and p(E) is closed since p is closed.
   Thus F0 = |B| \ p(E) is open. An etale atlas of B and
   lem-a1-space-invariant-open-quotient give the corresponding open subspace F.
2. For arbitrary h:T → B, that lemma identifies the flat locus after base change with
   the inverse image of L. By compatible-point lifting in lem-a1-space-point-open-calculus,
   the base change meets E exactly when h(|T|) meets p(E). Hence f_T is flat exactly
   when h has image in F0, or equivalently factors through F by
   lem-a1-space-open-factor-scheme-tests. In particular f_F is flat.
3. By lem-sfb-space-relative-lfp-permanence, f is locally of finite presentation since
   p is locally of finite presentation and q is locally of finite type. The sheaf
   fibre-product universal property of lem-trf-space-fibre-products-etale-covers
   identifies f_F with its base change. Local finite presentation survives base change
   by lem-sfb-stack-chartwise-smooth-etale-calculus. Thus
   lem-sfb-flat-lfp-space-universally-open makes I = im |f_F| open in |C_F|.
4. The restriction q_F:C_F → F is closed: a closed subset of C_F is D0 intersected
   with q inverse-image F0, for some closed D0 in C, and its image is q(D0) intersected
   with F0. This uses the open embeddings of lem-a1-space-point-open-calculus and
   lem-a1-space-open-factor-scheme-tests. Therefore q_F(D) is closed for D = |C_F| \ I.
5. Set V0 = F0 \ q_F(D), open in F and hence B. The invariant-open quotient lemma
   constructs its open subspace V of B. Its inclusion factors through F by the
   open-factor lemma, since V0 is contained in F0.
6. For g:T → F, write r:C_F ×_F T → C_F and s:C_F ×_F T → T. The fibre-product
   universal property identifies (f_F)_T as the base change of f_F along r. The point
   image formula gives im |(f_F)_T| = r inverse-image I. Compatible-point lifting gives
   s(r inverse-image D) = g inverse-image q_F(D). Thus (f_F)_T is surjective exactly
   when g(|T|) lies in V0, equivalently when the composite T → B factors through V.
7. If h factors through V it factors through F, so steps 2 and 6 give flatness and
   surjectivity. Conversely flatness gives the factor through F, and surjectivity
   then gives the factor through V. The iterated sheaf fibre products over F equal
   the original base changes over B by their universal property: the F-section of
   every matching pair is forced by g. These identifications commute with f. -/
theorem exists_openSubspace_universal_surjective_flat {S : Scheme.{u}}
    (A C B : AlgebraicSpace S) (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C)
    (w : f ≫ q = p)
    (hp_flat : MapIsFlat p) (hp_lfp : MapIsLocallyOfFinitePresentation p)
    (hp_closed : ∀ Z : Set (Point A.obj.obj), IsClosed Z →
      IsClosed {y : Point B.obj.obj | ∃ a : PointRepresentative A.obj.obj,
        (Quot.mk _ a : Point A.obj.obj) ∈ Z ∧ (Quot.mk _ (a.map p.hom.hom) : Point _) = y})
    (hq_lft : MapIsLocally (@LocallyOfFiniteType) q)
    (hq_closed : ∀ Z : Set (Point C.obj.obj), IsClosed Z →
      IsClosed {y : Point B.obj.obj | ∃ c : PointRepresentative C.obj.obj,
        (Quot.mk _ c : Point C.obj.obj) ∈ Z ∧ (Quot.mk _ (c.map q.hom.hom) : Point _) = y}) :
    ∃ V : OpenSubspace B, ∀ (T : AlgebraicSpace S) (h : T ⟶ B),
      (MapIsFlat (baseChangeDiagramMap p q f w h) ∧
        pointImage (baseChangeDiagramMap p q f w h).hom.hom = Set.univ) ↔
      ∃ l : T.obj.obj ⟶ V.val.toFunctor, l ≫ V.val.ι = h.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
