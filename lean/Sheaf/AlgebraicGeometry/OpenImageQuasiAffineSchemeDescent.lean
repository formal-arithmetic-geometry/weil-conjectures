/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData
import Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Quasi-affine scheme descent over the open image of an affine étale map

Source: Stacks Project, Spaces Morphisms, Tag 03XW, lemma-neighbourhood-scheme,
final proof paragraph (blueprint: lem-a1-open-image-quasi-affine-scheme-descent).

The auxiliary presheaf is the existing restricted Yoneda construction transported
along the iterated-slice functor. Its sections are exactly maps into the given W over B.
The descent comparison is specified by preservation of the W-section and the ordered
base coordinates, rather than by an unspecified isomorphism of local schemes.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The functor of maps into W over B, on schemes over B. This is Mathlib's
`restrictedYonedaObj`, precomposed with the canonical scheme-test functor; its values
are `OverArrows b`, with their actual restriction maps. No sheaf or representation is chosen.
Source: Stacks Project, Tag 03XW, final proof paragraph; Tag 02W5
(blueprint: lem-a1-open-image-quasi-affine-scheme-descent). -/
def openImageSectionPresheaf {S : Scheme.{u}} {W : (Over S)ᵒᵖ ⥤ Type u}
    (B : Over S) (b : W ⟶ yoneda.obj B) : (Over B.left)ᵒᵖ ⥤ Type u :=
  (Over.iteratedSliceBackward B ⋙
    (Over.forget B).toCostructuredArrow yoneda (yoneda.obj B)
      (fun Q ↦ yoneda.map Q.hom)
      (fun {_ _} g ↦ (yoneda.map_comp g.left _).symm.trans
        (congrArg yoneda.map (Over.w g)))).op ⋙ OverPresheafAux.restrictedYonedaObj b

/-- An open algebraic subspace supported on the open image of an affine étale chart
is a scheme if its pullback to that chart is a quasi-affine scheme over the chart.
The presheaf in the conclusion is precisely the functor of maps into W over B.
The transport equivalence fixes the W-section: on points the comparison sends
((w,t0),t1) to (t0,(w,t1)). The `transport_transport` field of the existing descent
structure is the cocycle phi02 = phi12 composed with phi01, in this direction.

Source: Stacks Project, Spaces Morphisms, Tag 03XW, lemma-neighbourhood-scheme,
final proof paragraph (blueprint: lem-a1-open-image-quasi-affine-scheme-descent).

Proof, following the seven steps of the node:
1. The open-subspace property makes W an algebraic space. The image of a is open
   by lem-weil-pbc-etale-morphism-open-map. Apply
   lem-a1-space-open-factor-scheme-tests to obtain b and the surjective etale factor p,
   and to identify the fibre products over T and over B.
2. The map between affine schemes a is affine by pqf-lem-affine-local-target.
   Since B to T is monic, p is its base change, so is affine by
   lem-weil-pbc-affine-morphism-permanence. B need not be affine.
3. Surjectivity and etaleness give the singleton fppf covering. Apply
   lem-trf-fppf-covering-is-fpqc to obtain the fpqc covering as well.
4. Glue W-sections using its fppf sheaf condition. Their maps to B remain the fixed
   structure map by uniqueness for the representable sheaf of B, proving the sheaf
   condition for exactly openImageSectionPresheaf B b.
5. The given Cartesian square represents its pullback by P. By
   lem-trf-fppf-sheaf-representability-descent-data the canonical comparison retains
   the W-section and ordered base coordinates. On triple overlaps both composites
   retain w,t0,t1,t2, proving the cocycle by Yoneda.
6. Apply lem-trf-quasi-affine-fpqc-effective-descent to P over T' and p. It makes
   this very datum effective, over the arbitrary scheme B.
7. The final representability criterion of
   lem-trf-fppf-sheaf-representability-descent-data then represents the specified
   sheaf by a B-scheme. Empty charts and empty W are included throughout. -/
theorem openImageQuasiAffineSchemeDescent
    {S : Scheme.{u}} (T T' : Over S) [IsAffine T.left] [IsAffine T'.left]
    (a : T' ⟶ T) [Etale a.left]
    (X : AlgebraicSpace S) (f : X.obj.obj ⟶ yoneda.obj T) (W : OpenSubspace X)
    (B : Over S) (j : B ⟶ T) [IsOpenImmersion j.left]
    (hB : pointImage (yoneda.map j) = pointImage (yoneda.map a))
    (hW : pointImage (W.val.ι ≫ f) ⊆ pointImage (yoneda.map j))
    (P : Over S) (v : P ⟶ T') (q : yoneda.obj P ⟶ W.val.toFunctor)
    (hP : IsPullback q (yoneda.map v) (W.val.ι ≫ f) (yoneda.map a))
    [IsQuasiAffineHom v.left] :
    ∃ (b : W.val.toFunctor ⟶ yoneda.obj B) (p : T' ⟶ B),
      b ≫ yoneda.map j = W.val.ι ≫ f ∧ p ≫ j = a ∧
      IsAffineHom p.left ∧ Surjective p.left ∧ Etale p.left ∧
      Presieve.singleton p.left ∈ Scheme.fpqcPrecoverage B.left ∧
      Presieve.singleton p.left ∈ Scheme.fppfPrecoverage B.left ∧
      IsPullback q (yoneda.map v) b (yoneda.map p) ∧
      Presheaf.IsSheaf (Scheme.fppfTopology.over B.left)
        (openImageSectionPresheaf B b) ∧
      Nonempty (((Over.map p.left).op ⋙ openImageSectionPresheaf B b).RepresentableBy
        (Over.mk v.left)) ∧
      (∃ D : Over.DescentDatum p.left (Over.mk v.left),
        (∀ (Q : Over S) (m0 m1 : Q ⟶ P)
          (h : (m0 ≫ v) ≫ p = (m1 ≫ v) ≫ p),
          (D.transport (m0.left ≫ v.left) (m1.left ≫ v.left)
            (congrArg (fun k ↦ k.left) h) (Over.homMk m0.left rfl)).left = m1.left ↔
            q.app (op Q) m0 = q.app (op Q) m1) ∧ D.IsEffective) ∧
      (openImageSectionPresheaf B b).IsRepresentable := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
