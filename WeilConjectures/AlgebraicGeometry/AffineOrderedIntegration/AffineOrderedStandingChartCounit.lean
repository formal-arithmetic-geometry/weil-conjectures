/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedLineEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAugmentationRealization

/-! # Geometric line evaluation in ordinary chart counit coordinates

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

set_option maxHeartbeats 1600000 in
-- Elaborating the fixed chart comparisons requires the concrete derived source types.
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

/-- Standing evaluation expressed through the actual ordinary coordinate-line counit.
Source: the coordinate-line augmentation realization and standing-to-chart comparison
(blueprint: lem-pur-affine-ordered-standing-chart-counit).
Proof: precompose the coordinate-line realization equation with compact support of the
inverse source comparison and the forward fixed site comparison. Their inverses cancel.
This recovers the chart augmentation. Substitute into standingEvaluation, retaining
its prescribed changeSupport and literal line-source endpoint equality. -/
theorem standingEvaluation_chart_counit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    let A := AffineLinePurity.Ring P
    let c := affineTraceLineCompactification Y
    let Q := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let W : DerivedCategory.Plus (Sheaf (AffineSpace PUnit.{u + 1} Y).smallEtaleTopology
        (ModuleCat.{u + 1} A)) :=
      ⟨etaleSource P.coefficients.l P.extension (P.level - 1) Y P.level
          (annihilates P) Ke,
        etaleSource_plus P.coefficients.l P.extension (P.level - 1) Y P.level
          (annihilates P) Ke hKe⟩
    let sc := AffineLinePurity.sourceComparison P.coefficients.l P.extension
      (P.level - 1) Y P.level (annihilates P) K.obj Ke eK
    AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK =
      (AffineLineEvaluation.changeSupport A
        (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y)) c
        (AffineLineEvaluation.linePlus P Y K.obj Ke hKe eK)
        (AffineLineEvaluation.lineWitness P Y K.obj Ke hKe eK)).hom ≫
      Q.map (eqToHom (lineSource_obj_eq P Y K.obj)) ≫ Q.map sc.inv ≫
      (fixedCompactSupportComparisonIso A c).hom.app W ≫
      (comparison A Y).map
        ((Etale.affineTraceLineLeft A Y).map
            (CoordinateLine.sourceCoordinates P Y P.level (annihilates P) Ke).hom ≫
          (CoordinateLine.adjunction A (exponent P) (annihilates P) Y
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
            (exponentUnit P Y aY)).counit.app Ke) ≫ eK.hom := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  dsimp only
  have hc := CoordinateLine.coordinate_line_augmentation_realization
    P Y aY P.level (annihilates P) K Ke hKe eK
  let A := AffineLinePurity.Ring P
  let Q := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (affineTraceLineCompactification Y)
  let sc := AffineLinePurity.sourceComparison P.coefficients.l P.extension
    (P.level - 1) Y P.level (annihilates P) K.obj Ke eK
  let W : DerivedCategory.Plus (Sheaf (AffineSpace PUnit.{u + 1} Y).smallEtaleTopology
      (ModuleCat.{u + 1} A)) :=
    ⟨etaleSource P.coefficients.l P.extension (P.level - 1) Y P.level
        (annihilates P) Ke,
      etaleSource_plus P.coefficients.l P.extension (P.level - 1) Y P.level
        (annihilates P) Ke hKe⟩
  have he :
      AffineLinePurity.augmentation P.coefficients.l P.extension (P.level - 1)
        Y P.level (annihilates P) (primeUnit P Y aY) P.field.k aY K.obj Ke hKe eK =
      Q.map sc.inv ≫
        (fixedCompactSupportComparisonIso A (affineTraceLineCompactification Y)).hom.app W ≫
        (comparison A Y).map
          ((Etale.affineTraceLineLeft A Y).map
              (CoordinateLine.sourceCoordinates P Y P.level (annihilates P) Ke).hom ≫
            (CoordinateLine.adjunction A (exponent P) (annihilates P) Y
              (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
              (exponentUnit P Y aY)).counit.app Ke) ≫ eK.hom := by
    apply (cancel_epi
      ((fixedCompactSupportComparisonIso A (affineTraceLineCompactification Y)).inv.app W ≫
        Q.map sc.hom)).mp
    simp only [Category.assoc]
    rw [hc]
    simp only [Iso.map_hom_inv_id_assoc, Iso.inv_hom_id_app_assoc]
    rfl
  unfold AffineLineEvaluation.standingEvaluation AffineLineEvaluation.evaluation
  rw [he]
  rfl

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
