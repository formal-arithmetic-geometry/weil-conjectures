/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.ProjectiveNodalTower
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.JacobsonSpace
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.TraceFormula.NodalOpenLocus
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.NodalCurveLCICriterion
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete

/-! # Universal nodal relative-dimension-one locus of an algebraic space

Source: Stacks Project, spaces-more-morphisms.tex, Tag 0DSH, with Tag 0DSG and
curves.tex, Tag 0DSC (blueprint: lem-sfb-space-nodal-locus-base-change).

Open subspaces are the existing representable open subfunctors. Base change is their
literal subfunctor preimage along the canonical projection of the presheaf Limits.pullback.

The four predicates below are helpers for this theorem: smooth curve or closed ordinary
node, scheme nodal family, universal étale-chart test, and algebraic-space nodal family.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry


/-- A geometric curve point is smooth on a neighbourhood of relative dimension one,
or is a closed ordinary node. The completion test is the existing
`IsGeometricOrdinaryDoublePoint`; closedness is a separate condition.
Source: Stacks, curves.tex, definition-nodal-family and Tag 0DSC
(blueprint: lem-sfb-space-nodal-locus-base-change). -/
def IsSmoothCurveOrOrdinaryNode {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {C : Scheme.{u}}
    (b : C ⟶ Spec (.of Ω)) (x : C) : Prop :=
  (∃ W : C.Opens, x ∈ W ∧ SmoothOfRelativeDimension 1 (W.ι ≫ b)) ∨
    (x ∈ closedPoints C ∧ IsGeometricOrdinaryDoublePoint Ω C x)

/-- A scheme morphism is flat, locally finitely presented and has only smooth curve
points and ordinary nodes in every geometric fibre. Empty fibres are allowed.
Source: Stacks, curves.tex, definition-nodal-family and lemma-nodal-family
(blueprint: lem-sfb-space-nodal-locus-base-change). -/
def IsSchemeNodalCurve {U V : Scheme.{u}} (h : U ⟶ V) : Prop :=
  Flat h ∧ LocallyOfFinitePresentation h ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ V),
      ∀ x : pullback (C := Scheme.{u}) h g,
        IsSmoothCurveOrOrdinaryNode (pullback.snd h g) x

namespace AlgebraicSpace

/-- Test a scheme-morphism property on every commuting diagram with representable
étale scheme-source vertical arrows. This also applies to actual open subfunctors
and presheaf fibre products, without replacing their canonical inclusion maps.
Source: Stacks, spaces-more-morphisms.tex, Tag 0DSG(6)
(blueprint: lem-sfb-space-nodal-locus-base-change). -/
def OnEtaleCharts {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {E F : (Over S)ᵒᵖ ⥤ Type u} (f : E ⟶ F) : Prop :=
  ∀ (U V : Over S) (a : yoneda.obj U ⟶ E) (b : yoneda.obj V ⟶ F)
    (h : U ⟶ V), IsEtale a → IsEtale b → a ≫ f = yoneda.map h ≫ b → P h.left

/-- At-worst-nodal of relative dimension one, tested on all étale scheme diagrams.
No connectedness, properness or nonemptiness condition is part of this notion.
Source: Stacks, spaces-more-morphisms.tex, definition-nodal-family and Tag 0DSG(6)
(blueprint: lem-sfb-space-nodal-locus-base-change). -/
def HasNodalCurveCharts {S : Scheme.{u}} {E F : (Over S)ᵒᵖ ⥤ Type u}
    (f : E ⟶ F) : Prop :=
  OnEtaleCharts (fun _ _ h ↦ IsSchemeNodalCurve h) f


/-- The largest nodal source open of a flat locally finitely presented algebraic-space
morphism, its largestness after every base change, and its geometric-fibre description.
The last clause tests the geometric fibre on every étale scheme chart; its map to the
field spectrum is specified by the displayed compatibility with the second projection.

Source: Stacks Project, spaces-more-morphisms.tex, Tag 0DSH; Tag 0DSG and curves.tex,
Tag 0DSC (blueprint: lem-sfb-space-nodal-locus-base-change).

Proof, following the node's eight steps:
1. For a flat locally finitely presented scheme chart h, restrict to its syntomic
relative-dimension-one open L using lem-sfb-syntomic-fixed-dimension-locus. Its nonempty
geometric fibres are pure of dimension one. Apply lem-trf-nodal-open-locus to L.
2. Any nodal source open O lies in L: lem-trf-nodal-curve-lci-criterion makes its fibres
local complete intersections of dimension one. Largestness for L and then its nodal
open gives largestness in the whole scheme. Both constructions commute with base change.
3. Smooth curve points lie in L. For a node the completion is Ω[[u,v]]/(uv).
The power-series ring is a regular local domain by
lem-weil-pbc-power-series-field-cohen-regular-complete; uv is a nonzero nonunit and a
regular element. The two branches give dimension one. The completed-ring criterion in
lem-sfb-syntomic-fixed-dimension-locus puts the node in L. The scheme nodal-open theorem
therefore gives exactly the smooth curve points and ordinary nodes, even in mixed fibres.
4. Choose a surjective étale target scheme atlas and a source scheme atlas over it,
using def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers and
lem-weil-pbc-etale-composition-cancellation. The scheme locus has an open image A in X
by lem-a1-space-etale-open-image. It is nodal by lem-sfb-space-nodal-chart-locality.
5. Pull back an arbitrary nodal open to these charts. Scheme largestness and the
surjectivity of the atlas give containment in A. The same argument for A identifies
its entire inverse image with the nodal scheme locus. This also gives independence
of the choice of charts.
6. For any Y' → Y, refine the pulled-back target atlas by a scheme atlas Z. The scheme
U ×_T Z is a surjective étale atlas of X ×_Y Y', by the fibre-product and étale
composition lemmas. Flatness and local finite presentation follow from
lem-weil-pbc-flat-morphism-base-change and lem-weil-pbc-qcqs-morphism-permanence.
7. On this atlas, both the new largest nodal open and the inverse image of A have the
same preimage, by scheme base change and step 5. Surjectivity and the open-subspace
correspondence in lem-a1-space-etale-open-image identify the two opens.
8. Apply this to Spec Ω → Y. Any étale scheme chart of the fibre pulls A back to its
scheme nodal locus by step 5. Step 3 and the pointwise preservation and reflection in
lem-sfb-space-nodal-chart-locality give precisely the last clause. No global purity,
connectedness, nonemptiness or properness hypothesis is used.
-/
theorem exists_nodal_open_baseChange {S : Scheme.{u}} (X Y : AlgebraicSpace S)
    (f : X ⟶ Y)
    (hflat : OnEtaleCharts (fun _ _ h ↦ Flat h) f.hom.hom)
    (hfp : OnEtaleCharts (fun _ _ h ↦ LocallyOfFinitePresentation h) f.hom.hom) :
    ∃ A : OpenSubspace X,
      HasNodalCurveCharts (A.val.ι ≫ f.hom.hom) ∧
      (∀ B : OpenSubspace X,
        HasNodalCurveCharts (B.val.ι ≫ f.hom.hom) → B ≤ A) ∧
      (∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
        IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
          (A.val.preimage (Limits.pullback.fst f.hom.hom g.hom.hom)).ι ∧
        HasNodalCurveCharts
          ((A.val.preimage (Limits.pullback.fst f.hom.hom g.hom.hom)).ι ≫
            Limits.pullback.snd f.hom.hom g.hom.hom) ∧
        (∀ B : Subfunctor (Limits.pullback f.hom.hom g.hom.hom),
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) B.ι →
          HasNodalCurveCharts (B.ι ≫ Limits.pullback.snd f.hom.hom g.hom.hom) →
          B ≤ A.val.preimage (Limits.pullback.fst f.hom.hom g.hom.hom))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
        (g : yoneda.obj (Over.mk s) ⟶ Y.obj.obj) (U : Over S)
        (a : yoneda.obj U ⟶ Limits.pullback f.hom.hom g) (b : U ⟶ Over.mk s),
        IsEtale a → a ≫ Limits.pullback.snd f.hom.hom g = yoneda.map b →
        ∀ x : U.left,
          schemePointMap (a ≫ Limits.pullback.fst f.hom.hom g) x ∈ pointImage A.val.ι ↔
            IsSmoothCurveOrOrdinaryNode b.left x) := by
  sorry

end AlgebraicSpace
end AlgebraicGeometry
