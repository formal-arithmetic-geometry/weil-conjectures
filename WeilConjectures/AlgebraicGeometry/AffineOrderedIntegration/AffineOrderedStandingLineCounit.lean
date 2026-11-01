/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedLineEvaluationCoordinates
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedStandingSourceCounit
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedRankOneSourceCoordinates

/-! # Normalization of geometric line evaluation

Source: projection-purity agreement, final paragraph: normalized last-line evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

attribute [local semireducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] iteratedAffineLine iteratedAffineLineProj
  etaleCategory proCategory sourceEtale affineTraceTower affineTraceProjection

attribute [local semireducible] sourceWitness
attribute [local implicit_reducible] sourceWitness rightDerivedLowerShriek
  Etale.affineTraceOpenLeft affineTraceLineCompactification

set_option maxHeartbeats 1600000 in
-- The comparison contains concrete derived source and compact-support functors.
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

/-- The geometric standing evaluation is the normalized ordinary line counit.
Source: projection-purity agreement, final paragraph, and the coordinate-line
counit tensor formula.
(blueprint: lem-pur-affine-ordered-standing-line-counit).

Proof: precompose with compact support of lineWitness.iso.hom, an isomorphism.
standingEvaluation_source_counit expresses the geometric side through the fixed
origin and chart comparisons, ordinary source coordinates and the original line
counit. rankOne_source_coordinates identifies its prefix with compact support of
the witness followed by lineEvaluationCoordinates. Postcompose that equality with
comparison of orderedCounitStep at zero and eK.hom. Functoriality and associativity
identify it with the reverse of the precomposed goal. Cancel the isomorphism. -/
theorem standingLine_counit_coordinates
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK =
      normalizedLineEvaluation P Y aY K Ke hKe eK := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  apply (cancel_epi ((AffineLineEvaluation.support P aY
    (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
      (AffineLineEvaluation.lineWitness P Y K.obj Ke hKe eK).iso.hom)).mp
  rw [standingEvaluation_source_counit]
  have hs := rankOne_source_coordinates P Y aY K Ke hKe eK
  dsimp only at hs
  simp only [normalizedLineEvaluation, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
