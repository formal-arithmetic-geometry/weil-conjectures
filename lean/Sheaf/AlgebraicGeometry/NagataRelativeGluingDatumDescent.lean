/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1, SHEAF group Z2
-/
module

public import Sheaf.AlgebraicGeometry.RelativeFiniteAffinePresentation
public import Sheaf.AlgebraicGeometry.NagataAffineFpDescent
public import Sheaf.AlgebraicGeometry.NagataMorphismDescent
import Sheaf.AlgebraicGeometry.NagataAffineFpDescends
import Sheaf.AlgebraicGeometry.NagataMorphismDescends
import Sheaf.AlgebraicGeometry.NagataQCOpenDescent
import Sheaf.AlgebraicGeometry.NagataQCOpenDescentSpec
import Sheaf.Order.DirectedFiniteUpperBound
import Sheaf.RingTheory.FilteredColimitFiniteData
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Finite-stage raw relative gluing datum

Source: Weil conjectures blueprint, sec-nagata-compactification,
sk-prop-nagata-sketch-approximation, node order 358
(blueprint: def-nagata-relative-gluing-datum-descent).

The datum is a chain of records, each taking the earlier ones as parameters: the base cover
and coordinate rings, the affine algebra descents, the finite-stage charts, the overlap opens
with their open descents, their common stage, the transported overlap schemes, the canonical
limit comparisons, both morphism descents, and the final raw stage. The finite-stage inverse
and cocycle equations belong to subsequent nodes.

The records are chains of dependent choices, so Lean's automatic injectivity and `sizeOf`
lemmas for them cost far more than the definitions themselves; they are never used and
are switched off for this file.

## Main definitions

* `NagataRawOverlapOpenChoice`: the explicit inputs and output of quasi-compact open descent.
* `nagataRawChartMap`: the chart map induced by the stage algebra and coordinate comparison.
* `nagataRawRelations`, `nagataRawGenerators`: the fixed relative presentation's data.
* `NagataRawBaseData`, `NagataRawAlgebraData`, `NagataRawChartData`: base, algebra and chart
  portions.
* `NagataRawOverlapOpenData`, `NagataRawOverlapStageData`, `NagataRawOverlapSchemeData`: the
  descended overlap opens, their common stage, and their transports as schemes.
* `NagataRawOverlapData`: canonical overlap comparisons.
* `NagataRawTwoWayMorphismChoice`, `NagataRawMorphismData`: paired morphism choices.
* `NagataRawMorphismTransport`: a canonical raw-stage transport entry.
* `NagataRawFiniteStageData`: the final stage and transported diagram for fixed choices.
* `NagataRelativeGluingDatum`: the complete chosen raw relative gluing diagram.
-/

@[expose] public section

universe u

set_option linter.unusedVariables false
set_option genInjectivity false
set_option genSizeOf false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The explicit cover, basic sections and lifts used to descend one overlap open.
The selected open is the output of the recorded `nagataQCOpenDescent` construction, not an
arbitrary finite-stage open. Source: blueprint node order 358
(blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawOverlapOpenChoice
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i : I) {Y : Scheme.{u}} (p : Y ⟶ D.obj (op i))
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (W : (baseChangeCone D c p).pt.Opens)
    (hW : IsCompact (W : Set (baseChangeCone D c p).pt))
    (d : I → I → I) (hd : ∀ a b, a ≤ d a b ∧ b ≤ d a b)
    (r : LinearOrder I) where
  count : ℕ
  cover : Fin count → Y.Opens
  affine : ∀ a, IsAffineOpen (cover a)
  covers : iSup cover = ⊤
  basicCount : Fin count → ℕ
  sectionValue : ∀ a, Fin (basicCount a) → Γ((baseChangeCone D c p).pt,
    pullback.fst p (c.π.app (op i)) ⁻¹ᵁ cover a)
  presentation : ∀ a, W ⊓ (pullback.fst p (c.π.app (op i)) ⁻¹ᵁ cover a) =
    ⨆ k, (baseChangeCone D c p).pt.basicOpen (sectionValue a k)
  liftStage : Fin count → I
  liftGE : ∀ a, i ≤ liftStage a
  lift : ∀ a, Fin (basicCount a) →
    Γ((baseChangeDiagram D p).obj (Over.mk (homOfLE (liftGE a)).op),
      pullback.fst p (D.map (homOfLE (liftGE a)).op) ⁻¹ᵁ cover a)
  lift_eq : ∀ a k,
    ((baseChangeCone D c p).π.app (Over.mk (homOfLE (liftGE a)).op)).appLE
      (pullback.fst p (D.map (homOfLE (liftGE a)).op) ⁻¹ᵁ cover a)
      (pullback.fst p (c.π.app (op i)) ⁻¹ᵁ cover a)
      (nagataQCOpenDescent_limit_chart_le D c p
        (Over.mk (homOfLE (liftGE a)).op) (cover a)) (lift a k) = sectionValue a k
  stage : I
  stageGE : i ≤ stage
  selected : ((baseChangeDiagram D p).obj (Over.mk (homOfLE stageGE).op)).Opens
  selected_eq : (⟨stage, stageGE, selected⟩ : Σ' s : I, Σ' hs : i ≤ s,
    ((baseChangeDiagram D p).obj (Over.mk (homOfLE hs).op)).Opens) =
    nagataQCOpenDescent D c hc i p W hW count cover affine covers basicCount sectionValue
      presentation liftStage liftGE lift lift_eq d hd r

/-- The chart map computed from the descended algebra and the affine coordinate comparison.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
noncomputable def nagataRawChartMap
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    {F : I ⥤ CommRingCat.{u}} {i₀ : I} {n m : ℕ}
    {rels : Fin m → MvPolynomial (Fin n) (↑(colimit F))}
    (E : NagataAffineFpDescent F i₀ n m rels)
    {Y : Scheme.{u}} {U : Y.Opens} (e : F.obj E.stage ≅ Γ(Y, U))
    (hU : IsAffineOpen U) : Spec (.of E.stageAlgebra) ⟶ Y :=
  E.stageMorphism ≫ Spec.map e.inv ≫ hU.fromSpec

/-- Relations of the fixed presentation, with its prescribed scalar structure.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
noncomputable def nagataRawRelations {X S : Scheme.{u}} {f : X ⟶ S}
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] (R : RelativeFiniteAffinePresentation f)
    (j : Σ a, R.chartIndex a) : Fin (R.presentation j.1 j.2).2.1 →
      MvPolynomial (Fin (R.presentation j.1 j.2).1) (Γ(S, R.base j.1)) := by
  letI := (f.appLE (R.base j.1) (R.chart j.1 j.2) (R.chartOver j.1 j.2)).hom.toAlgebra
  exact (R.presentation j.1 j.2).2.2.relation

/-- Generators of the fixed presentation, with its prescribed scalar structure.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
noncomputable def nagataRawGenerators {X S : Scheme.{u}} {f : X ⟶ S}
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f]
    [QuasiCompact f] [QuasiSeparated f] (R : RelativeFiniteAffinePresentation f)
    (j : Σ a, R.chartIndex a) : Fin (R.presentation j.1 j.2).1 → Γ(X, R.chart j.1 j.2) := by
  letI := (f.appLE (R.base j.1) (R.chart j.1 j.2) (R.chartOver j.1 j.2)).hom.toAlgebra
  exact (R.presentation j.1 j.2).2.2.val

open scoped TensorProduct
/-- The fixed relative presentation, the affine cover of the base stage, the selected
upper-bound operation and the coordinate-ring systems of the base charts with their canonical
comparisons. This is the base portion of the raw relative gluing datum.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawBaseData
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] where
  base : RelativeFiniteAffinePresentation f
  baseOpen : base.baseIndex → (D.obj (op i₀)).Opens
  baseOpenAffine : ∀ a, IsAffineOpen (baseOpen a)
  baseOpenCovers : ⨆ a, baseOpen a = ⊤
  base_eq : ∀ a, base.base a = c.π.app (op i₀) ⁻¹ᵁ baseOpen a
  boundPair : I → I → I
  boundPair_le : ∀ a b, a ≤ boundPair a b ∧ b ≤ boundPair a b
  boundOrder : LinearOrder I
  rings : base.baseIndex → I ⥤ CommRingCat.{u}
  ringAtStage : ∀ a s (hs : i₀ ≤ s),
    (rings a).obj s ≅ Γ(D.obj (op s), D.map (homOfLE hs).op ⁻¹ᵁ baseOpen a)
  ringTransition_le : ∀ a s t (hs : i₀ ≤ s) (hst : s ≤ t),
    D.map (homOfLE (hs.trans hst)).op ⁻¹ᵁ baseOpen a ≤
      D.map (homOfLE hst).op ⁻¹ᵁ (D.map (homOfLE hs).op ⁻¹ᵁ baseOpen a)
  ringAtStage_naturality : ∀ a s t (hs : i₀ ≤ s) (hst : s ≤ t),
    (rings a).map (homOfLE hst) ≫ (ringAtStage a t (hs.trans hst)).hom =
      (ringAtStage a s hs).hom ≫ (D.map (homOfLE hst).op).appLE
        (D.map (homOfLE hs).op ⁻¹ᵁ baseOpen a)
        (D.map (homOfLE (hs.trans hst)).op ⁻¹ᵁ baseOpen a)
        (ringTransition_le a s t hs hst)
  ringAtLimit : ∀ a, colimit (rings a) ≅ Γ(c.pt, base.base a)
  ringAtLimit_le : ∀ a s (hs : i₀ ≤ s), base.base a ≤
    c.π.app (op s) ⁻¹ᵁ (D.map (homOfLE hs).op ⁻¹ᵁ baseOpen a)
  ringAtLimit_colimit : ∀ a s (hs : i₀ ≤ s),
    (colimit.ι (rings a) s) ≫ (ringAtLimit a).hom =
      (ringAtStage a s hs).hom ≫ (c.π.app (op s)).appLE
        (D.map (homOfLE hs).op ⁻¹ᵁ baseOpen a) (base.base a) (ringAtLimit_le a s hs)

/-- The chosen affine algebra descents of the chart algebras of the fixed presentation, with
scalars and generators identified with those of the presentation. This is the algebra portion
of the raw relative gluing datum.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawAlgebraData
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (B : NagataRawBaseData D c hc i₀ f) where
  relations : ∀ j : Σ a, B.base.chartIndex a, Fin (B.base.presentation j.1 j.2).2.1 →
    MvPolynomial (Fin (B.base.presentation j.1 j.2).1) (↑(colimit (B.rings j.1)))
  relations_eq : ∀ (j : Σ a, B.base.chartIndex a) z,
    MvPolynomial.map (B.ringAtLimit j.1).hom.hom (relations j z) = nagataRawRelations B.base j z
  algebraDescent : ∀ (j : Σ a, B.base.chartIndex a), NagataAffineFpDescent (B.rings j.1) i₀
    (B.base.presentation j.1 j.2).1 (B.base.presentation j.1 j.2).2.1 (relations j)
  algebraBoundBase_eq : ∀ j, (algebraDescent j).boundBase = i₀
  algebraBoundPair_eq : ∀ j, (algebraDescent j).boundPair = B.boundPair
  algebraBoundOrder_eq : ∀ j, (algebraDescent j).boundOrder = B.boundOrder
  chartAlgebra : ∀ j, (algebraDescent j).algebra ≃+* Γ(X, B.base.chart j.1 j.2)
  chartAlgebra_scalar : ∀ j a, chartAlgebra j
    (algebraMap (↑(colimit (B.rings j.1))) (algebraDescent j).algebra a) =
      (f.appLE (B.base.base j.1) (B.base.chart j.1 j.2) (B.base.chartOver j.1 j.2))
        ((B.ringAtLimit j.1).hom a)
  chartAlgebra_generator : ∀ j z, chartAlgebra j
    ((algebraDescent j).presentation.symm
      (Ideal.Quotient.mk _ (MvPolynomial.X z))) = nagataRawGenerators B.base j z

/-- The finite-stage charts, their maps to the base stages and their canonical comparisons
with the charts of the presentation. This is the chart portion of the raw relative gluing
datum.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawChartData
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (B : NagataRawBaseData D c hc i₀ f) (A : NagataRawAlgebraData D c hc i₀ f B) where
  chart : ∀ j, Scheme.{u}
  chart_eq : ∀ j, chart j = Spec (.of (A.algebraDescent j).stageAlgebra)
  [chartCompact : ∀ j, CompactSpace (chart j)]
  [chartQS : ∀ j, QuasiSeparatedSpace (chart j)]
  chartBaseAffine : ∀ j, IsAffineOpen
    (D.map (homOfLE (A.algebraDescent j).stage_ge).op ⁻¹ᵁ B.baseOpen j.1)
  chartMap : ∀ j, (chart j : Scheme.{u}) ⟶ D.obj (op (A.algebraDescent j).stage)
  chartMap_eq : ∀ j, chartMap j =
    eqToHom (chart_eq j) ≫ nagataRawChartMap (A.algebraDescent j)
      (B.ringAtStage j.1 (A.algebraDescent j).stage (A.algebraDescent j).stage_ge)
      (chartBaseAffine j)
  chartComparison : ∀ j,
    (baseChangeCone D c (chartMap j)).pt ≅ (B.base.chart j.1 j.2).toScheme
  chartComparison_fst : ∀ j, (chartComparison j).inv ≫
    pullback.fst (chartMap j) (c.π.app (op (A.algebraDescent j).stage)) =
      (B.base.chart j.1 j.2).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
        ((A.chartAlgebra j).toRingHom.comp ((A.algebraDescent j).beta.toRingHom.comp
          (Algebra.TensorProduct.includeRight : (A.algebraDescent j).stageAlgebra →ₐ[
            (B.rings j.1).obj (A.algebraDescent j).stage]
            ↑(colimit (B.rings j.1)) ⊗[(B.rings j.1).obj (A.algebraDescent j).stage]
              (A.algebraDescent j).stageAlgebra).toRingHom))) ≫
        eqToHom (chart_eq j).symm
  chartComparison_snd : ∀ j, (chartComparison j).inv ≫
    pullback.snd (chartMap j) (c.π.app (op (A.algebraDescent j).stage)) =
      (B.base.chart j.1 j.2).ι ≫ f


attribute [instance] NagataRawChartData.chartCompact NagataRawChartData.chartQS

/-- Both sides of every basic overlap as quasi-compact opens of the limit charts, with their
chosen open descents. This is the overlap-open portion of the raw relative gluing datum.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawOverlapOpenData
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (B : NagataRawBaseData D c hc i₀ f) (A : NagataRawAlgebraData D c hc i₀ f B)
    (C : NagataRawChartData D c hc i₀ f B A) where
  leftOpen : ∀ j k, B.base.overlapIndex j k → (baseChangeCone D c (C.chartMap j)).pt.Opens
  rightOpen : ∀ j k, B.base.overlapIndex j k → (baseChangeCone D c (C.chartMap k)).pt.Opens
  leftOpen_eq : ∀ j k l, leftOpen j k l = (C.chartComparison j).hom ⁻¹ᵁ
    ((B.base.chart j.1 j.2).ι ⁻¹ᵁ X.basicOpen (B.base.leftSection j k l))
  rightOpen_eq : ∀ j k l, rightOpen j k l = (C.chartComparison k).hom ⁻¹ᵁ
    ((B.base.chart k.1 k.2).ι ⁻¹ᵁ X.basicOpen (B.base.rightSection j k l))
  leftCompact : ∀ j k l, IsCompact (leftOpen j k l).carrier
  rightCompact : ∀ j k l, IsCompact (rightOpen j k l).carrier
  openChoice : ∀ j k l, NagataRawOverlapOpenChoice D c hc
    (A.algebraDescent j).stage (C.chartMap j) (leftOpen j k l) (leftCompact j k l)
    B.boundPair B.boundPair_le B.boundOrder
  rightOpenChoice : ∀ j k l, NagataRawOverlapOpenChoice D c hc
    (A.algebraDescent k).stage (C.chartMap k) (rightOpen j k l) (rightCompact j k l)
    B.boundPair B.boundPair_le B.boundOrder

/-- The common stage of all chart and overlap-open stages and the descended overlap opens
transported to it. This is the overlap-stage portion of the raw relative gluing datum.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawOverlapStageData
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (B : NagataRawBaseData D c hc i₀ f) (A : NagataRawAlgebraData D c hc i₀ f B)
    (C : NagataRawChartData D c hc i₀ f B A) (O : NagataRawOverlapOpenData D c hc i₀ f B A C) where
  /-- All chart and open stages, with the original base stage. -/
  overlapStages : Finset I
  overlapStages_eq : (overlapStages : Set I) = {i₀} ∪
    Set.range (fun j => (A.algebraDescent j).stage) ∪
    Set.range (fun x : Σ j, Σ k, B.base.overlapIndex j k =>
      (O.openChoice x.1 x.2.1 x.2.2).stage) ∪
    Set.range (fun x : Σ j, Σ k, B.base.overlapIndex j k =>
      (O.rightOpenChoice x.1 x.2.1 x.2.2).stage)
  overlapStage : I
  overlapStage_eq : overlapStage =
    directedFiniteUpperBound i₀ B.boundPair B.boundOrder overlapStages
  base_le_overlap : i₀ ≤ overlapStage
  chart_le_overlap : ∀ j, (A.algebraDescent j).stage ≤ overlapStage
  left_le_overlap : ∀ j k l, (O.openChoice j k l).stage ≤ overlapStage
  right_le_overlap : ∀ j k l, (O.rightOpenChoice j k l).stage ≤ overlapStage
  leftAtOverlap : ∀ j k l, ((baseChangeDiagram D (C.chartMap j)).obj
    (Over.mk (homOfLE (chart_le_overlap j)).op)).Opens
  leftAtOverlap_eq : ∀ j k l, leftAtOverlap j k l =
    (baseChangeDiagram D (C.chartMap j)).map
      (Over.homMk (homOfLE (left_le_overlap j k l)).op (Subsingleton.elim _ _)) ⁻¹ᵁ
        (O.openChoice j k l).selected
  rightAtOverlap : ∀ j k l, ((baseChangeDiagram D (C.chartMap k)).obj
    (Over.mk (homOfLE (chart_le_overlap k)).op)).Opens
  rightAtOverlap_eq : ∀ j k l, rightAtOverlap j k l =
    (baseChangeDiagram D (C.chartMap k)).map
      (Over.homMk (homOfLE (right_le_overlap j k l)).op (Subsingleton.elim _ _)) ⁻¹ᵁ
        (O.rightOpenChoice j k l).selected

/-- The transported overlap opens as schemes over the common overlap stage. This is the
overlap-scheme portion of the raw relative gluing datum.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawOverlapSchemeData
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (B : NagataRawBaseData D c hc i₀ f) (A : NagataRawAlgebraData D c hc i₀ f B)
    (C : NagataRawChartData D c hc i₀ f B A) (O : NagataRawOverlapOpenData D c hc i₀ f B A C)
    (S : NagataRawOverlapStageData D c hc i₀ f B A C O) where
  leftScheme : ∀ j k, B.base.overlapIndex j k → Scheme.{u}
  leftScheme_eq : ∀ j k l, leftScheme j k l = (S.leftAtOverlap j k l).toScheme
  rightScheme : ∀ j k, B.base.overlapIndex j k → Scheme.{u}
  rightScheme_eq : ∀ j k l, rightScheme j k l = (S.rightAtOverlap j k l).toScheme
  leftMap : ∀ j k l, leftScheme j k l ⟶ D.obj (op S.overlapStage)
  leftMap_eq : ∀ j k l, leftMap j k l = eqToHom (leftScheme_eq j k l) ≫ (S.leftAtOverlap j k l).ι ≫
    pullback.snd (C.chartMap j) (D.map (homOfLE (S.chart_le_overlap j)).op)
  rightMap : ∀ j k l, rightScheme j k l ⟶ D.obj (op S.overlapStage)
  rightMap_eq : ∀ j k l, rightMap j k l = eqToHom (rightScheme_eq j k l) ≫ (S.rightAtOverlap j k
    l).ι ≫
    pullback.snd (C.chartMap k) (D.map (homOfLE (S.chart_le_overlap k)).op)
  [leftCompactAtOverlap : ∀ j k l, CompactSpace (leftScheme j k l)]
  [leftQSAtOverlap : ∀ j k l, QuasiSeparatedSpace (leftScheme j k l)]
  [rightCompactAtOverlap : ∀ j k l, CompactSpace (rightScheme j k l)]
  [rightQSAtOverlap : ∀ j k l, QuasiSeparatedSpace (rightScheme j k l)]
  [leftLFP : ∀ j k l, LocallyOfFinitePresentation (leftMap j k l)]
  [leftQC : ∀ j k l, QuasiCompact (leftMap j k l)]
  [leftQS : ∀ j k l, QuasiSeparated (leftMap j k l)]
  [rightLFP : ∀ j k l, LocallyOfFinitePresentation (rightMap j k l)]
  [rightQC : ∀ j k l, QuasiCompact (rightMap j k l)]
  [rightQS : ∀ j k l, QuasiSeparated (rightMap j k l)]
  [overlapBaseCompact : CompactSpace (D.obj (op S.overlapStage))]
  [overlapBaseQS : QuasiSeparatedSpace (D.obj (op S.overlapStage))]


/-- The canonical limit identifications of the two transported sides of each overlap and the
canonical overlap isomorphism. This is the comparison portion of the raw relative gluing
datum.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawOverlapData
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (B : NagataRawBaseData D c hc i₀ f) (A : NagataRawAlgebraData D c hc i₀ f B)
    (C : NagataRawChartData D c hc i₀ f B A) (O : NagataRawOverlapOpenData D c hc i₀ f B A C)
    (S : NagataRawOverlapStageData D c hc i₀ f B A C O)
    (T : NagataRawOverlapSchemeData D c hc i₀ f B A C O S) where
  /-- Canonical identifications with the corresponding basic opens of X. -/
  leftLimit : ∀ j k l, (baseChangeCone D c (T.leftMap j k l)).pt ≅
    (X.basicOpen (B.base.leftSection j k l)).toScheme
  leftLimit_eq : ∀ j k l, (leftLimit j k l).hom ≫
    (X.basicOpen (B.base.leftSection j k l)).ι ≫ f =
      pullback.snd (T.leftMap j k l) (c.π.app (op S.overlapStage))
  leftToChartLimit : ∀ j k l, (baseChangeCone D c (T.leftMap j k l)).pt ⟶
    (baseChangeCone D c (C.chartMap j)).pt
  leftToChartLimit_fst : ∀ j k l, leftToChartLimit j k l ≫
    pullback.fst (C.chartMap j) (c.π.app (op (A.algebraDescent j).stage)) =
      pullback.fst (T.leftMap j k l) (c.π.app (op S.overlapStage)) ≫
        eqToHom (T.leftScheme_eq j k l) ≫ (S.leftAtOverlap j k l).ι ≫
          pullback.fst (C.chartMap j) (D.map (homOfLE (S.chart_le_overlap j)).op)
  leftToChartLimit_snd : ∀ j k l, leftToChartLimit j k l ≫
    pullback.snd (C.chartMap j) (c.π.app (op (A.algebraDescent j).stage)) =
      pullback.snd (T.leftMap j k l) (c.π.app (op S.overlapStage))
  leftLimit_chart : ∀ j k l, (leftLimit j k l).hom ≫
    (X.basicOpen (B.base.leftSection j k l)).ι =
      leftToChartLimit j k l ≫ (C.chartComparison j).hom ≫ (B.base.chart j.1 j.2).ι
  rightLimit : ∀ j k l, (baseChangeCone D c (T.rightMap j k l)).pt ≅
    (X.basicOpen (B.base.rightSection j k l)).toScheme
  rightLimit_eq : ∀ j k l, (rightLimit j k l).hom ≫
    (X.basicOpen (B.base.rightSection j k l)).ι ≫ f =
      pullback.snd (T.rightMap j k l) (c.π.app (op S.overlapStage))
  rightToChartLimit : ∀ j k l, (baseChangeCone D c (T.rightMap j k l)).pt ⟶
    (baseChangeCone D c (C.chartMap k)).pt
  rightToChartLimit_fst : ∀ j k l, rightToChartLimit j k l ≫
    pullback.fst (C.chartMap k) (c.π.app (op (A.algebraDescent k).stage)) =
      pullback.fst (T.rightMap j k l) (c.π.app (op S.overlapStage)) ≫
        eqToHom (T.rightScheme_eq j k l) ≫ (S.rightAtOverlap j k l).ι ≫
          pullback.fst (C.chartMap k) (D.map (homOfLE (S.chart_le_overlap k)).op)
  rightToChartLimit_snd : ∀ j k l, rightToChartLimit j k l ≫
    pullback.snd (C.chartMap k) (c.π.app (op (A.algebraDescent k).stage)) =
      pullback.snd (T.rightMap j k l) (c.π.app (op S.overlapStage))
  rightLimit_chart : ∀ j k l, (rightLimit j k l).hom ≫
    (X.basicOpen (B.base.rightSection j k l)).ι =
      rightToChartLimit j k l ≫ (C.chartComparison k).hom ≫ (B.base.chart k.1 k.2).ι
  overlapIso : ∀ j k l, (baseChangeCone D c (T.leftMap j k l)).pt ≅
    (baseChangeCone D c (T.rightMap j k l)).pt
  overlapIso_canonical : ∀ j k l, overlapIso j k l =
    leftLimit j k l ≪≫ eqToIso (congrArg Scheme.Opens.toScheme (B.base.basicAgree j k l)) ≪≫
      (rightLimit j k l).symm

open Classical in
/-- A pair of chosen descents of the hom and inv of one fixed overlap isomorphism,
with a common later stage. This is one entry of the raw datum's finite morphism family.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawTwoWayMorphismChoice
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i : I) {Y Z : Scheme.{u}}
    (p : Y ⟶ D.obj (op i)) (q : Z ⟶ D.obj (op i))
    (e : (baseChangeCone D c p).pt ≅ (baseChangeCone D c q).pt)
    (boundBase : I) (d : I → I → I) (hd : ∀ a b, a ≤ d a b ∧ b ≤ d a b)
    (r : LinearOrder I) where
  [baseCompact : CompactSpace (D.obj (op i))]
  [baseQS : QuasiSeparatedSpace (D.obj (op i))]
  [leftCompact : CompactSpace Y]
  [leftQS : QuasiSeparatedSpace Y]
  [rightCompact : CompactSpace Z]
  [rightQS : QuasiSeparatedSpace Z]
  [leftLFP : LocallyOfFinitePresentation p]
  [leftQC : QuasiCompact p]
  [leftMapQS : QuasiSeparated p]
  [rightLFP : LocallyOfFinitePresentation q]
  [rightQC : QuasiCompact q]
  [rightMapQS : QuasiSeparated q]
  forwardChoice : NagataMorphismDescentData D c hc i p q e.hom d hd r
  backwardChoice : NagataMorphismDescentData D c hc i q p e.inv d hd r
  forward : Σ' s : I, Σ' hs : i ≤ s,
    (Over.mk (pullback.snd p (D.map (homOfLE hs).op)) ⟶
      Over.mk (pullback.snd q (D.map (homOfLE hs).op)))
  forward_eq : forward = nagataMorphismDescent D c hc i p q e.hom d hd r forwardChoice
  backward : Σ' s : I, Σ' hs : i ≤ s,
    (Over.mk (pullback.snd q (D.map (homOfLE hs).op)) ⟶
      Over.mk (pullback.snd p (D.map (homOfLE hs).op)))
  backward_eq : backward = nagataMorphismDescent D c hc i q p e.inv d hd r backwardChoice
  morphismStage : I
  morphismStage_eq : morphismStage =
    directedFiniteUpperBound boundBase d r {i, forward.1, backward.1}
  forward_le_morphism : forward.1 ≤ morphismStage
  backward_le_morphism : backward.1 ≤ morphismStage

open Classical in
/-- Both chosen directions of overlap morphism descent, with their common later stages.
This is the morphism-choice portion of the raw relative gluing datum.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawMorphismData
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (B : NagataRawBaseData D c hc i₀ f) (A : NagataRawAlgebraData D c hc i₀ f B)
    (C : NagataRawChartData D c hc i₀ f B A) (O : NagataRawOverlapOpenData D c hc i₀ f B A C)
    (S : NagataRawOverlapStageData D c hc i₀ f B A C O)
    (T : NagataRawOverlapSchemeData D c hc i₀ f B A C O S)
    (V : NagataRawOverlapData D c hc i₀ f B A C O S T) where
  choice : ∀ j k l, NagataRawTwoWayMorphismChoice D c hc S.overlapStage
    (T.leftMap j k l) (T.rightMap j k l) (V.overlapIso j k l)
    i₀ B.boundPair B.boundPair_le B.boundOrder

/-- The canonical base change of one chosen over-base morphism to a later stage,
characterized by its projection equation and its over-base typing. This is one raw
transport entry; the uniqueness is the fibre-product universal property.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawMorphismTransport
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (i : I)
    {Y Z : Scheme.{u}} (p : Y ⟶ D.obj (op i)) (q : Z ⟶ D.obj (op i))
    (s : I) (hs : i ≤ s)
    (g : Over.mk (pullback.snd p (D.map (homOfLE hs).op)) ⟶
      Over.mk (pullback.snd q (D.map (homOfLE hs).op)))
    (t : I) (ht : i ≤ t) (hst : s ≤ t) where
  map : Over.mk (pullback.snd p (D.map (homOfLE ht).op)) ⟶
    Over.mk (pullback.snd q (D.map (homOfLE ht).op))
  map_eq : map.left ≫ (baseChangeDiagram D q).map
    (Over.homMk (U := Over.mk (homOfLE ht).op) (V := Over.mk (homOfLE hs).op)
      (homOfLE hst).op (Subsingleton.elim _ _)) =
    (baseChangeDiagram D p).map
      (Over.homMk (U := Over.mk (homOfLE ht).op) (V := Over.mk (homOfLE hs).op)
        (homOfLE hst).op (Subsingleton.elim _ _)) ≫ g.left

open Classical in
/-- The final finite set of selected stages, its upper bound, and the transported raw
charts, opens and morphisms, for fixed earlier choices. This is the final portion of
one raw relative gluing datum.
Source: blueprint node order 358 (blueprint: def-nagata-relative-gluing-datum-descent). -/
structure NagataRawFiniteStageData
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (B : NagataRawBaseData D c hc i₀ f) (A : NagataRawAlgebraData D c hc i₀ f B)
    (C : NagataRawChartData D c hc i₀ f B A) (O : NagataRawOverlapOpenData D c hc i₀ f B A C)
    (S : NagataRawOverlapStageData D c hc i₀ f B A C O)
    (T : NagataRawOverlapSchemeData D c hc i₀ f B A C O S)
    (V : NagataRawOverlapData D c hc i₀ f B A C O S T)
    (M : NagataRawMorphismData D c hc i₀ f B A C O S T V) where
  stages : Finset I
  stages_eq : (stages : Set I) = (S.overlapStages : Set I) ∪
    {S.overlapStage} ∪
    Set.range (fun x : Σ j, Σ k, B.base.overlapIndex j k => ((M.choice
      x.1 x.2.1 x.2.2).forward).1) ∪
    Set.range (fun x : Σ j, Σ k, B.base.overlapIndex j k => ((M.choice
      x.1 x.2.1 x.2.2).backward).1) ∪
    Set.range (fun x : Σ j, Σ k, B.base.overlapIndex j k =>
      (M.choice x.1 x.2.1 x.2.2).morphismStage)
  stage : I
  stage_eq : stage = directedFiniteUpperBound i₀ B.boundPair
    B.boundOrder stages
  overlap_le_raw : S.overlapStage ≤ stage
  morphism_le_raw : ∀ j k l, (M.choice j k l).morphismStage ≤ stage
  forwardRaw : ∀ j k l, NagataRawMorphismTransport D S.overlapStage
    (T.leftMap j k l) (T.rightMap j k l)
    (M.choice j k l).forward.1 (M.choice j k l).forward.2.1
    (M.choice j k l).forward.2.2 stage overlap_le_raw
    ((M.choice j k l).forward_le_morphism.trans (morphism_le_raw j k l))
  backwardRaw : ∀ j k l, NagataRawMorphismTransport D S.overlapStage
    (T.rightMap j k l) (T.leftMap j k l)
    (M.choice j k l).backward.1 (M.choice j k l).backward.2.1
    (M.choice j k l).backward.2.2 stage overlap_le_raw
    ((M.choice j k l).backward_le_morphism.trans (morphism_le_raw j k l))
  rawChart : ∀ j, Scheme.{u}
  rawChart_eq : ∀ j, rawChart j = (baseChangeDiagram D (C.chartMap j)).obj
    (Over.mk (homOfLE ((S.chart_le_overlap j).trans overlap_le_raw)).op)
  rawLeftOpen : ∀ j k l, ((baseChangeDiagram D (C.chartMap j)).obj
    (Over.mk (homOfLE ((S.chart_le_overlap j).trans overlap_le_raw)).op)).Opens
  rawLeftOpen_eq : ∀ j k l, rawLeftOpen j k l =
    (baseChangeDiagram D (C.chartMap j)).map
      (Over.homMk (homOfLE overlap_le_raw).op (Subsingleton.elim _ _)) ⁻¹ᵁ
        S.leftAtOverlap j k l
  rawRightOpen : ∀ j k l, ((baseChangeDiagram D (C.chartMap k)).obj
    (Over.mk (homOfLE ((S.chart_le_overlap k).trans overlap_le_raw)).op)).Opens
  rawRightOpen_eq : ∀ j k l, rawRightOpen j k l =
    (baseChangeDiagram D (C.chartMap k)).map
      (Over.homMk (homOfLE overlap_le_raw).op (Subsingleton.elim _ _)) ⁻¹ᵁ
        S.rightAtOverlap j k l

/-- Fixed finite-stage relative gluing datum with canonical chart, overlap, and transport equations.
Source: Weil conjectures blueprint, sec-nagata-compactification, node order 358;
compare Stacks, `limits.tex`, Lemma `lemma-descend-finite-presentation` (Tag 01ZM).
(blueprint: def-nagata-relative-gluing-datum-descent).

First fix the relative presentation and an affine cover of the original base stage.
The coordinate-ring comparisons respect all transitions and the limit projections.
Next choose each affine algebra descent, identifying its scalars and generators with
those of the given presentation. The inverse chart comparison is determined by its
two projections: the spectrum of beta composed with the chart algebra comparison, and f.
Next descend each side of every basic overlap using the recorded open construction,
and transport the selected opens to the upper bound of exactly their stages and the
chart stages. The limit identifications respect both pullback projections and the
inclusions into X. They identify both sides with the same basic open, fixing the
canonical overlap isomorphism using basicAgree. Descend its hom and inv using the
recorded morphism construction and transport both to one common later stage.
Finally the raw stage is the selected upper bound of all these stages. The raw charts
and opens are the canonical base changes and inverse images. The raw morphisms are
over the raw base and commute with the canonical projections to their descent stages;
these two conditions uniquely characterize their base changes. All choices are retained;
no choice independence or finite-stage inverse/cocycle relation is asserted. -/
structure NagataRelativeGluingDatum
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] where
  base : NagataRawBaseData D c hc i₀ f
  algebras : NagataRawAlgebraData D c hc i₀ f base
  charts : NagataRawChartData D c hc i₀ f base algebras
  opens : NagataRawOverlapOpenData D c hc i₀ f base algebras charts
  stages : NagataRawOverlapStageData D c hc i₀ f base algebras charts opens
  schemes : NagataRawOverlapSchemeData D c hc i₀ f base algebras charts opens stages
  overlaps : NagataRawOverlapData D c hc i₀ f base algebras charts opens stages schemes
  morphisms : NagataRawMorphismData D c hc i₀ f base algebras charts opens stages schemes overlaps
  raw : NagataRawFiniteStageData D c hc i₀ f base algebras charts opens stages schemes overlaps
      morphisms

end AlgebraicGeometry
