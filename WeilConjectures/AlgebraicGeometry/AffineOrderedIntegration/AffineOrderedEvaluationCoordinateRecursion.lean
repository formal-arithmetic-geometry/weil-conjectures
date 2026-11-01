/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedLineEvaluationCoordinates
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedTensorCoordinateFactor

/-! # Recursion of the ordinary counit coordinates

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
  etaleCategory proCategory sourceEtale

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

/-- Recursive tensor coordinates intertwine the ordinary last-line counit.
No geometric evaluation or preceding ordered counit occurs in this equality.
Source: projection-purity agreement, final paragraph, canonical reassociations.
(blueprint: lem-pur-affine-ordered-evaluation-coordinate-recursion).

Proof: expand normalizedLineEvaluation and the lineEvaluationCoordinates factors.
orderedRight_finiteTor supplies admissibility of the actual ordered right source.
Naturality of the compact-support site comparison moves sourceRealization of the
preceding ordered source through the preceding compact support. Expand
ordinaryTensorCoordinates; ordinaryTensorCoordinatesRaw_factor exposes its specified
ordinary source isomorphism and ordinaryCompactComparison. The recursive source descent
normalization and orderedTateCoefficientComposition identify the rank-(d+2) source
with the last line over the rank-(d+1) source. Tensor associativity and the canonical
pullback/site tensor comparisons identify the realized source comparison with
sourceReassociation, by its HEq characterization. Composition coherence for compact
supports identifies the two site-comparison paths with the actual origin compositor.
Use this coherence at the literal Ring P: reindex the positive finite level by
Nat.sub_add_cancel P.level_pos, as in ringEquiv, or use the generic finite-ring
origin-composition model; the P.Coefficient wrapper alone has different coefficients.
Naturality of the ordinary line counit moves the preceding ordinarySourceIso through
that counit. Cancel the inverse coordinates introduced by lineEvaluationCoordinates.
The remaining ordinary morphism is precisely orderedCounitStep at d+1; the remaining
comparison is orderedCounitCoordinates at d+2. This calculation uses only source,
site-composition and adjunction naturality; it does not use standingEvaluation or any
identity asserting the comparison of its geometric trace with the ordinary counit. -/
theorem orderedEvaluation_coordinate_recursion
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    letI : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
    letI : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
    letI : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 2))).map
        (sourceReassociation P Y aY K.obj (d + 1)).hom ≫
    (AffineLineEvaluation.compositor P aY (iteratedAffineLineProj Y (d + 1))
      ((orderedSource P Y (d + 1)).obj K.obj) (sourceEtale P Y Ke (d + 1))
      (source_applicability P Y aY K Ke hKe eK (d + 1)).2
      (sourceRealization P Y K.obj Ke eK (d + 1))).inv ≫
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map
      (normalizedLineEvaluation P (iteratedAffineLine Y (d + 1))
        (towerBase aY (d + 1))
        ⟨(orderedSource P Y (d + 1)).obj K.obj,
          (source_applicability P Y aY K Ke hKe eK (d + 1)).1⟩
        (sourceEtale P Y Ke (d + 1))
        (source_applicability P Y aY K Ke hKe eK (d + 1)).2
        (sourceRealization P Y K.obj Ke eK (d + 1))) ≫
    (orderedCounitCoordinates P Y aY K Ke hKe eK (d + 1)).hom =
      (orderedCounitCoordinates P Y aY K Ke hKe eK (d + 2)).hom ≫
        (comparison (AffineLinePurity.Ring P) Y).map
          (orderedCounitStep P Y aY Ke (d + 1)) := by
  sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
