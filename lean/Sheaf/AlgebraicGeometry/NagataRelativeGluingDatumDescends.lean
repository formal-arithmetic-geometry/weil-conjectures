/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescent
import Sheaf.Order.DirectedFiniteUpperBound
import Sheaf.AlgebraicGeometry.NagataAffineFpDescends
import Sheaf.AlgebraicGeometry.NagataQCOpenDescentSpec
import Sheaf.AlgebraicGeometry.NagataMorphismDescends
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Limits

/-!
# Recovery of the raw relative gluing datum

Source: Weil conjectures blueprint, sec-nagata-compactification,
sk-prop-nagata-sketch-approximation, node order 359;
Stacks Project, Tag 01ZM, proof of (1), stages i₂ through i₄
(blueprint: lemma-nagata-relative-gluing-datum-descends).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Every raw chart, overlap open, and overlap map recovers its named counterpart.
Source: blueprint node order 359; Stacks Project, Tag 01ZM, proof of (1), stages i₂--i₄
(blueprint: lemma-nagata-relative-gluing-datum-descends).

The first conjunct uses the fixed chart comparison and the canonical projection to the
raw chart to exhibit the named chart as its base change. The second conjunct recovers
both named overlap opens in the limit charts. Their identification with the presentation's
basic opens is `R.opens.leftOpen_eq` and `R.opens.rightOpen_eq`. The last conjunct gives
both overlap-map comparisons using the canonical projections of `baseChangeCone`;
`R.overlaps.overlapIso_canonical` identifies the limit map with the named overlap map.

Proof:
1. The selected finite upper bound dominates every chosen stage, by
   lemma-nagata-directed-finite-upper-bound. Retain all the fixed lifts of
   def-nagata-relative-gluing-datum-descent.
2. The fibre-product universal property identifies an iterated base change with direct
   base change: the compatible triple (z,t,s) maps to (z,s), with inverse
   (z,s) ↦ (z,p_raw(s),s). These maps are inverse by their projections. They commute
   with every transported morphism, since the two composites have identical projections;
   the cone equations in def-nagata-basechanged-system give compatibility with the bases.
3. Apply lemma-nagata-affine-fp-descends to each chart algebra. Its beta is invertible;
   lem-weil-pbc-fibre-product-affine-spectra identifies its spectrum comparison with the
   chosen chart comparison, including its structure map. Step 2 transports this comparison
   to the raw stage, giving the first conjunct.
4. By lemma-nagata-qc-open-descends each selected open pulls back to the named open.
   The raw open is its inverse image under the intervening chart transition. Composition
   of inverse images and the cone equation give each equality in the second conjunct.
   Restricting the chart comparisons gives the overlap scheme comparisons.
5. The common overlap base is qcqs: its transition to the original qcqs base is affine,
   hence qcqs, by lem-weil-pbc-affine-morphism-permanence and
   lem-weil-pbc-qcqs-morphism-permanence. Each chart is finitely presented over its affine
   base chart. Principal localization B_h = B[t]/(ht-1) is finitely presented, so the
   overlaps are locally of finite presentation. The selected opens are quasi-compact by
   lemma-nagata-qc-open-descends; affine transitions preserve this by
   lem-weil-pbc-quasi-compact-morphism-preimage-qc-open. The affine ambient chart is
   quasi-separated by lem-weil-pbc-affine-scheme-qcqs, so its overlap opens are
   quasi-separated by lem-weil-pbc-quasi-separated-affine-cover-criterion. Their maps to
   the quasi-separated common base are qcqs by lem-weil-pbc-qcqs-morphism-permanence.
   Thus they are finitely presented, using def-sbc-locally-finite-presentation.
   Apply lemma-nagata-morphism-descends to the chosen forward and backward lifts.
   Step 2 transports its projection equations to the raw stage, giving the last
   conjunct. No inverse or cocycle equation at the raw stage is claimed. -/
theorem nagataRelativeGluingDatum_descends
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (i₀ : I) [CompactSpace (D.obj (op i₀))]
    [QuasiSeparatedSpace (D.obj (op i₀))]
    {X : Scheme.{u}} (f : X ⟶ c.pt)
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (R : NagataRelativeGluingDatum D c hc i₀ f) :
    (∀ j : Σ a, R.base.base.chartIndex a,
      IsPullback
        ((R.charts.chartComparison j).inv ≫
          (baseChangeCone D c (R.charts.chartMap j)).π.app
            (Over.mk (homOfLE
              ((R.stages.chart_le_overlap j).trans R.raw.overlap_le_raw)).op) ≫
          eqToHom (R.raw.rawChart_eq j).symm)
        ((R.base.base.chart j.1 j.2).ι ≫ f)
        (eqToHom (R.raw.rawChart_eq j) ≫ pullback.snd (R.charts.chartMap j)
          (D.map (homOfLE
            ((R.stages.chart_le_overlap j).trans R.raw.overlap_le_raw)).op))
        (c.π.app (op R.raw.stage))) ∧
    (∀ (j k : Σ a, R.base.base.chartIndex a) (l : R.base.base.overlapIndex j k),
      ((baseChangeCone D c (R.charts.chartMap j)).π.app
        (Over.mk (homOfLE
          ((R.stages.chart_le_overlap j).trans R.raw.overlap_le_raw)).op) ⁻¹ᵁ
            R.raw.rawLeftOpen j k l = R.opens.leftOpen j k l) ∧
      ((baseChangeCone D c (R.charts.chartMap k)).π.app
        (Over.mk (homOfLE
          ((R.stages.chart_le_overlap k).trans R.raw.overlap_le_raw)).op) ⁻¹ᵁ
            R.raw.rawRightOpen j k l = R.opens.rightOpen j k l)) ∧
    (∀ (j k : Σ a, R.base.base.chartIndex a) (l : R.base.base.overlapIndex j k),
      ((baseChangeCone D c (R.schemes.leftMap j k l)).π.app
        (Over.mk (homOfLE R.raw.overlap_le_raw).op) ≫
          (R.raw.forwardRaw j k l).map.left =
        (R.overlaps.overlapIso j k l).hom ≫
          (baseChangeCone D c (R.schemes.rightMap j k l)).π.app
            (Over.mk (homOfLE R.raw.overlap_le_raw).op)) ∧
      ((baseChangeCone D c (R.schemes.rightMap j k l)).π.app
        (Over.mk (homOfLE R.raw.overlap_le_raw).op) ≫
          (R.raw.backwardRaw j k l).map.left =
        (R.overlaps.overlapIso j k l).inv ≫
          (baseChangeCone D c (R.schemes.leftMap j k l)).π.app
            (Over.mk (homOfLE R.raw.overlap_le_raw).op))) := by
  sorry

end AlgebraicGeometry
