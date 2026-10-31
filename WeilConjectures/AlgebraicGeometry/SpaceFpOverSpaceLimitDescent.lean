/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Finite presentation descends over limits of algebraic-space bases

Source: Stacks Project, Limits of Spaces, Tag 07SK, lemma-descend-finite-presentation
(blueprint: lem-sfb-space-fp-over-space-limit-descent).

The three conjuncts express descent of objects, descent of maps, and eventual equality.
Pullbacks are taken in fppf sheaves; the full subcategory of algebraic spaces has these
same fibre products. Absolute quasi-separatedness uses the equivalent affine-pair test,
so no separatedness of the auxiliary base scheme is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Canonical comparison between direct and iterated base change along a commuting triangle.
It consists solely of transport along the triangle equality and Mathlib's pullback
composition isomorphism, with no choice of a map or isomorphism.
Source: Stacks, Tag 07SK, the base-change identifications in the full-faithfulness clause
(blueprint: lem-sfb-space-fp-over-space-limit-descent). -/
def spaceLimitPullbackIso {S : Scheme.{u}}
    {A B C : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (p : C ⟶ A) (q : C ⟶ B) (t : B ⟶ A) (h : q ≫ t = p) :
    Over.pullback p ≅ Over.pullback t ⋙ Over.pullback q :=
  eqToIso (congrArg (fun r : C ⟶ A ↦ Over.pullback r) h.symm) ≪≫
    Over.pullbackComp q t

/-- Objects, maps and equalities of finitely presented algebraic spaces descend over
nonempty directed inverse systems of qcqs algebraic spaces with affine transitions.
Finite presentation is locally finite presentation, quasi-compactness and a quasi-compact
relative diagonal. The affine-pair test expresses the absolute quasi-separatedness of each
base, rather than quasi-separatedness relative to the auxiliary scheme S.
Source: Stacks Project, Limits of Spaces, Tag 07SK, lemma-descend-finite-presentation
(blueprint: lem-sfb-space-fp-over-space-limit-descent).

Proof:
1. Fix a stage and pass to its cofinal tail. Choose an affine surjective etale atlas
   U_0 of that stage by [lem-sfb-qc-space-affine-etale-atlas]. Its double and triple
   overlaps are schemes by [lem-trf-space-representable-etale-scheme-tests].
2. Base change this atlas and its overlaps to all later stages. The atlas is affine;
   its double and triple overlaps are qcqs, using [lem-weil-pbc-affine-scheme-qcqs],
   [lem-sfb-qcqs-space-fibre-product] and [lem-sfb-space-affine-locality]. By
   [lem-sfb-space-affine-limits-schematic-stages] their limits are the corresponding
   base changes to the limiting space. The atlas stays surjective etale by
   [lem-trf-space-fibre-products-etale-covers].
3. Pull the finitely presented space back to the atlas. Apply the object clause of
   [lem-sfb-fp-space-qcqs-base-limit-descent] to descend it to a stage. All uses of
   this scheme-base result are transported from Spec Z using
   [lem-sfb-space-change-base-to-integers]. Base-change stability is supplied by
   [lem-sfb-space-flat-proper-fp-locality].
4. On the double overlaps descend the canonical overlap isomorphism and its inverse
   with the morphism clause of scheme-base descent, and descend their inverse equations
   with its equality clause. On the triple overlaps descend the cocycle equation;
   on the atlas descend the identity equation. A common upper bound suffices.
5. The atlas is an fppf cover by [lem-sfb-space-fppf-covering-calculus]. Apply
   [lem-sfb-fppf-space-datum-sheaf-realization]. For each scheme test its pulled-back
   atlas is a surjective etale scheme, so [lem-sfb-fppf-space-atlas-bootstrap] proves
   algebraicity of the realized sheaf.
6. Finite presentation follows after every scheme test by the locality assertion of
   [lem-sfb-space-flat-proper-fp-locality]. Quasi-compactness is its affine-test clause;
   the tested relative diagonal is a base change of a quasi-compact diagonal, using
   [lem-sfb-space-quasicompact-fppf-local]. Local finite presentation follows from
   [lem-sfb-space-local-properties-chart-test]. Full faithfulness of sheaf descent
   identifies the pullback with the original space, proving the first conjunct.
7. To descend a map, descend its atlas restriction by the morphism clause of scheme-base
   descent. Descend its compatibility with the overlap data by the equality clause on
   the double overlaps. Full faithfulness of sheaf descent gives the stage map and
   identifies its pullback with the prescribed map. This proves the second conjunct.
8. For two maps with equal limit pullbacks, scheme-base equality descent makes their
   atlas restrictions equal at a later stage. Faithfulness of sheaf descent then gives
   equality over that stage. Maps initially at different stages are first pulled back
   to a common upper bound. This proves the third conjunct. -/
theorem fp_over_space_limit_descent {S : Scheme.{u}}
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    (hqc : ∀ i : I, CompactSpace (Point (D.obj (op i)).obj.obj))
    (hqs : ∀ (i : I) (U V : Over S)
      (a : yoneda.obj U ⟶ (D.obj (op i)).obj.obj)
      (b : yoneda.obj V ⟶ (D.obj (op i)).obj.obj),
      IsAffine U.left → IsAffine V.left → CompactSpace (Point (Limits.pullback a b)))
    (ha : ∀ (i j : I) (h : i ≤ j), MapIsAffine (D.map (homOfLE h).op)) :
    (∀ (Z : AlgebraicSpace S) (f : Z ⟶ c.pt),
      MapIsLocallyOfFinitePresentation f → MapIsQuasiCompact f.hom.hom →
      MapIsQuasiCompact (pullback.diagonal f.hom.hom) →
      ∃ (i : I) (Zi : AlgebraicSpace S) (fi : Zi ⟶ D.obj (op i)),
        MapIsLocallyOfFinitePresentation fi ∧ MapIsQuasiCompact fi.hom.hom ∧
        MapIsQuasiCompact (pullback.diagonal fi.hom.hom) ∧
        Nonempty ((Over.pullback (c.π.app (op i)).hom).obj (Over.mk fi.hom) ≅
          Over.mk f.hom)) ∧
    (∀ (i : I) (Z W : AlgebraicSpace S) (f : Z ⟶ D.obj (op i))
      (g : W ⟶ D.obj (op i)),
      MapIsLocallyOfFinitePresentation f → MapIsQuasiCompact f.hom.hom →
      MapIsQuasiCompact (pullback.diagonal f.hom.hom) →
      MapIsLocallyOfFinitePresentation g → MapIsQuasiCompact g.hom.hom →
      MapIsQuasiCompact (pullback.diagonal g.hom.hom) →
      ∀ α : (Over.pullback (c.π.app (op i)).hom).obj (Over.mk f.hom) ⟶
        (Over.pullback (c.π.app (op i)).hom).obj (Over.mk g.hom),
      ∃ (j : I) (h : i ≤ j)
        (β : (Over.pullback (D.map (homOfLE h).op).hom).obj (Over.mk f.hom) ⟶
          (Over.pullback (D.map (homOfLE h).op).hom).obj (Over.mk g.hom)),
        α = (spaceLimitPullbackIso _ _ _
          (congrArg (fun k ↦ k.hom) (c.w (homOfLE h).op))).hom.app (Over.mk f.hom) ≫
          (Over.pullback (c.π.app (op j)).hom).map β ≫
          (spaceLimitPullbackIso _ _ _
            (congrArg (fun k ↦ k.hom) (c.w (homOfLE h).op))).inv.app (Over.mk g.hom)) ∧
    (∀ (i : I) (Z W : AlgebraicSpace S) (f : Z ⟶ D.obj (op i))
      (g : W ⟶ D.obj (op i)),
      MapIsLocallyOfFinitePresentation f → MapIsQuasiCompact f.hom.hom →
      MapIsQuasiCompact (pullback.diagonal f.hom.hom) →
      MapIsLocallyOfFinitePresentation g → MapIsQuasiCompact g.hom.hom →
      MapIsQuasiCompact (pullback.diagonal g.hom.hom) →
      ∀ α β : Over.mk f.hom ⟶ Over.mk g.hom,
        (Over.pullback (c.π.app (op i)).hom).map α =
          (Over.pullback (c.π.app (op i)).hom).map β →
        ∃ (j : I) (h : i ≤ j),
          (Over.pullback (D.map (homOfLE h).op).hom).map α =
            (Over.pullback (D.map (homOfLE h).op).hom).map β) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
