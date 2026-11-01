/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedStandingLineCounit
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationCoordinateRecursion

/-! # Site comparison for one ordered line evaluation

Source: projection-purity agreement, final paragraph, ordered integration.
(blueprint: lem-pur-affine-ordered-evaluation-step-comparison).
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
-- Instantiating the two comparison identities elaborates large derived source types.
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

/-- Comparison of the last-line evaluation with the actual single-line counit,
before the preceding counit or augmentation is applied.
Source: current blueprint projection-purity agreement, final paragraph.
(blueprint: lem-pur-affine-ordered-evaluation-step-comparison).

Proof: standingLine_counit_coordinates identifies the geometric line evaluation
with its ordinary-counit expression on the actual line projection. At rank one,
normalizedLineEvaluation_zero cancels the source-reassociation isomorphism, the
arrow-congruence isomorphism and eK.hom followed by eK.inv. At every positive
preceding rank, source_applicability supplies the bounded-below ordered source,
its finite-Tor ordinary origin and its realization. Substitute the line-counit
identity at that input under the preceding compact support. The independent
ordinary-coordinate recursion identifies the remaining composite with the next
coordinates followed by the ordinary last-line counit. No preceding counit is
applied, and the statement and all its specified maps are unchanged. -/
theorem orderedEvaluation_step_comparison
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    letI : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
      HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
    ((AffineLineEvaluation.support P aY (iteratedAffineLineProj Y 1)).map
        (sourceReassociation P Y aY K.obj 0).hom ≫
      (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
        (Category.comp_id (lastProjection Y 0)).symm).inv.app
          ((lineSource P Y).obj K.obj) ≫
      AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK ≫ eK.inv =
        (orderedCounitCoordinates P Y aY K Ke hKe eK 1).hom ≫
          (comparison (AffineLinePurity.Ring P) Y).map
            (orderedCounitStep P Y aY Ke 0)) ∧
    (∀ d : ℕ,
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
        (AffineLineEvaluation.standingEvaluation P (iteratedAffineLine Y (d + 1))
          (towerBase aY (d + 1)) ((orderedSource P Y (d + 1)).obj K.obj)
          (sourceEtale P Y Ke (d + 1))
          (source_applicability P Y aY K Ke hKe eK (d + 1)).2
          (sourceRealization P Y K.obj Ke eK (d + 1))) ≫
      (orderedCounitCoordinates P Y aY K Ke hKe eK (d + 1)).hom =
        (orderedCounitCoordinates P Y aY K Ke hKe eK (d + 2)).hom ≫
          (comparison (AffineLinePurity.Ring P) Y).map
            (orderedCounitStep P Y aY Ke (d + 1))) := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
    HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
  constructor
  · rw [standingLine_counit_coordinates P Y aY K Ke hKe eK]
    exact normalizedLineEvaluation_zero P Y aY K Ke hKe eK
  · intro d
    let : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
    let : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
    let : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
    rw [standingLine_counit_coordinates P (iteratedAffineLine Y (d + 1))
      (towerBase aY (d + 1))
      ⟨(orderedSource P Y (d + 1)).obj K.obj,
        (source_applicability P Y aY K Ke hKe eK (d + 1)).1⟩
      (sourceEtale P Y Ke (d + 1))
      (source_applicability P Y aY K Ke hKe eK (d + 1)).2
      (sourceRealization P Y K.obj Ke eK (d + 1))]
    exact orderedEvaluation_coordinate_recursion P Y aY K Ke hKe eK d

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
