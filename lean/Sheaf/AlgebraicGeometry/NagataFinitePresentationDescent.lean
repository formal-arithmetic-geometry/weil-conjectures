/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z2
-/
module

public import Sheaf.AlgebraicGeometry.NagataRelativeGluingValidStage
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing the finite-presentation descent model

Source: Weil conjectures blueprint, sec-nagata-compactification, order 362;
Stacks Project, Tag 01ZM, proof (blueprint: def-nagata-finite-presentation-descent).

The chosen scheme gluing datum is identified with the valid transported charts and
unions of overlap opens. Its transitions are prescribed on every overlap piece.
The base map and comparison map retain their chartwise equations. No data is chosen
from a postponed existence proof, and finite presentation and isomorphy are not assumed.
-/

@[expose] public section

universe u

set_option genInjectivity false
set_option genSizeOf false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A scheme gluing realization of the specified transported finite diagram. The overlap
isomorphisms identify the entire overlaps with the unions of the specified left opens;
the inclusion and transition equations fix the maps on every piece.
Source: blueprint order 362, Tag 01ZM proof
(blueprint: def-nagata-finite-presentation-descent). -/
structure NagataFinitePresentationGluingData {S : Scheme.{u}} {J : Type u}
    {K : J → J → Type u} (T : NagataRelativeGluingTransport S J K) where
  data : Scheme.GlueData.{u}
  index : data.J ≃ J
  chartIso : ∀ a, data.U a ≅ (T.chart (index a)).left
  overlapIso : ∀ a b, data.V (a, b) ≅
    (⨆ l, T.leftOpen (index a) (index b) l).toScheme
  inclusion_eq : ∀ a b, data.f a b ≫ (chartIso a).hom =
    (overlapIso a b).hom ≫ (⨆ l, T.leftOpen (index a) (index b) l).ι
  piece : ∀ a b l, (T.left (index a) (index b) l).left ⟶ data.V (a, b)
  piece_eq : ∀ a b l, piece a b l ≫ data.f a b ≫ (chartIso a).hom =
    (T.leftInclusion (index a) (index b) l).left
  transition_eq : ∀ a b l, piece a b l ≫ data.t a b ≫ data.f b a ≫ (chartIso b).hom =
    (T.forward (index a) (index b) l ≫ T.rightInclusion (index a) (index b) l).left

/-- The map from the glued scheme to its stage base, characterized on the chart cover.
Source: blueprint order 362, Tag 01ZM proof
(blueprint: def-nagata-finite-presentation-descent). -/
structure NagataFinitePresentationBaseMap {S : Scheme.{u}} {J : Type u}
    {K : J → J → Type u} {T : NagataRelativeGluingTransport S J K}
    (G : NagataFinitePresentationGluingData T) where
  map : G.data.glued ⟶ S
  chart_eq : ∀ a, G.data.ι a ≫ map = (G.chartIso a).hom ≫ (T.chart (G.index a)).hom

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (R : NagataRelativeGluingDatum D c hc i₀ f)
    (P : NagataRelativeRawInclusions D c hc i₀ f R)
    (A : NagataRelativeGluingValidStageData D c hc i₀ f R P)

/-- The canonical map from a base-changed valid chart to its original descended chart's
base change. Its two projections characterize reassociation of the successive pullbacks.
Source: blueprint order 362, Tag 01ZM proof
(blueprint: def-nagata-finite-presentation-descent). -/
structure NagataFinitePresentationChartComparison (j : Σ a, R.base.base.chartIndex a) where
  map : pullback
    ((nagataRelativeGluingValidDatum D c hc i₀ f R P A).chart j).hom
    (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A))) ⟶
      (baseChangeCone D c (R.charts.chartMap j)).pt
  fst_eq : map ≫ pullback.fst (R.charts.chartMap j)
    (c.π.app (op (R.algebras.algebraDescent j).stage)) =
      pullback.fst ((nagataRelativeGluingValidDatum D c hc i₀ f R P A).chart j).hom
        (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A))) ≫
      pullback.fst (nagataRelativeRawChart D c hc i₀ f R j).hom
        (D.map (homOfLE (nagataRelativeRawStage_le_validStage D c hc i₀ f R P A)).op) ≫
      pullback.fst (R.charts.chartMap j)
        (D.map (homOfLE ((R.stages.chart_le_overlap j).trans R.raw.overlap_le_raw)).op)
  snd_eq : map ≫ pullback.snd (R.charts.chartMap j)
    (c.π.app (op (R.algebras.algebraDescent j).stage)) =
      pullback.snd ((nagataRelativeGluingValidDatum D c hc i₀ f R P A).chart j).hom
        (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))

variable (G : NagataFinitePresentationGluingData
    (nagataRelativeGluingValidDatum D c hc i₀ f R P A))
    (B : NagataFinitePresentationBaseMap G)

/-- The finite-stage model is exactly Mathlib's gluing of the chosen realization of the
valid relative datum. Source: blueprint order 362, Tag 01ZM proof
(blueprint: def-nagata-finite-presentation-descent). -/
noncomputable def nagataFinitePresentationDescent : Scheme.{u} :=
  G.data.glued

/-- The descended structure morphism is the chartwise characterized glued base map.
Source: blueprint order 362, Tag 01ZM proof
(blueprint: def-nagata-finite-presentation-descent). -/
def nagataFinitePresentationDescentMap :
    nagataFinitePresentationDescent D c hc i₀ f R P A G ⟶
      D.obj (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)) :=
  B.map

/-- The chartwise gluing of the original base-change identifications. Each chart-to-pullback
map is determined by both projections. The comparison restriction is the original chart
comparison preceded by the canonical reassociation, and its over-base equation is retained.
Source: blueprint order 362, Tag 01ZM proof
(blueprint: def-nagata-finite-presentation-descent). -/
structure NagataFinitePresentationComparisonData where
  charts : ∀ j, NagataFinitePresentationChartComparison D c hc i₀ f R P A j
  chartToPullback : ∀ a, pullback
    ((nagataRelativeGluingValidDatum D c hc i₀ f R P A).chart (G.index a)).hom
    (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A))) ⟶
      pullback B.map (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))
  chart_fst : ∀ a, chartToPullback a ≫
    pullback.fst B.map (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A))) =
      pullback.fst
        ((nagataRelativeGluingValidDatum D c hc i₀ f R P A).chart (G.index a)).hom
        (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A))) ≫
      (G.chartIso a).inv ≫ G.data.ι a
  chart_snd : ∀ a, chartToPullback a ≫
    pullback.snd B.map (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A))) =
      pullback.snd
        ((nagataRelativeGluingValidDatum D c hc i₀ f R P A).chart (G.index a)).hom
        (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))
  comparison : pullback B.map
    (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A))) ⟶ X
  comparison_chart : ∀ a, chartToPullback a ≫ comparison =
    (charts (G.index a)).map ≫ (R.charts.chartComparison (G.index a)).hom ≫
      (R.base.base.chart (G.index a).1 (G.index a).2).ι
  comparison_base : comparison ≫ f =
    pullback.snd B.map (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A)))

/-- The global comparison epsilon_X, specified by gluing the recorded chart comparisons.
Source: blueprint order 362, Tag 01ZM proof
(blueprint: def-nagata-finite-presentation-descent). -/
def nagataFinitePresentationDescentComparison
    (E : NagataFinitePresentationComparisonData D c hc i₀ f R P A G B) :
    pullback (nagataFinitePresentationDescentMap D c hc i₀ f R P A G B)
      (c.π.app (op (nagataRelativeGluingValidStage D c hc i₀ f R P A))) ⟶ X :=
  E.comparison

end AlgebraicGeometry
