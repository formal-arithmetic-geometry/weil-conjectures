/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationNormalization
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationStepComparison

/-! # Contraction of the ordered coefficient evaluations

Source: projection-purity agreement, final paragraph, ordered integration.
(blueprint: lem-route-ordered-evaluation-contraction).
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
-- The source and counit comparisons carry large derived-category instances.
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

/-- The first coefficient evaluation is the normalized line evaluation; each subsequent
one is its compact-support composite with the preceding coefficient evaluation.
This statement involves neither exceptional inverse images nor integration transposes.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, final paragraph
(blueprint: lem-route-ordered-evaluation-contraction).

Proof: identify each supported ordered source with the realization of L_d(R_d Ke)
using orderedCounitCoordinates. orderedEvaluation_normalization identifies its
augmentation with the realized ordinary counit. The one-step comparison identifies
the geometric last-line evaluation with orderedCounitStep before any preceding
counit is applied. For the first line the preceding adjunction is the identity,
so orderedCounit_one and cancellation of eK.inv followed by eK.hom give the first
equation. At a positive stage orderedCounit_step expands the next counit as the
last step followed by the preceding counit. Map this composition through comparison,
substitute the one-step square, and replace the preceding realized counit by its
normalization equation. Associativity gives exactly the displayed composite,
with its prescribed inverse support compositor and source comparisons. -/
theorem orderedEvaluation_contraction
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
        (sourceComparison P Y K.obj 1).hom ≫ augmentation P Y aY K Ke hKe eK 1 =
      (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y 1)).map
        (sourceReassociation P Y aY K.obj 0).hom ≫
      (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
        (Category.comp_id (lastProjection Y 0)).symm).inv.app
          ((lineSource P Y).obj K.obj) ≫
      AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK) ∧
    (∀ d : ℕ,
      letI : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
      letI : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
      letI : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
      (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 2))).map
          (sourceComparison P Y K.obj (d + 2)).hom ≫
        augmentation P Y aY K Ke hKe eK (d + 2) =
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
      (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map
        (sourceComparison P Y K.obj (d + 1)).hom ≫
      augmentation P Y aY K Ke hKe eK (d + 1)) := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
    HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
  have hn := orderedEvaluation_normalization P Y aY K Ke hKe eK
  obtain ⟨hzero, hstep⟩ := orderedEvaluation_step_comparison P Y aY K Ke hKe eK
  constructor
  · rw [hn 1, orderedCounit_one]
    have hz := congrArg (fun f ↦ f ≫ eK.hom) hzero
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hz.symm
  · intro d
    let : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
    let : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
    let : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
    rw [hn (d + 2)]
    have hs := congrArg (fun f ↦ f ≫
      (comparison (AffineLinePurity.Ring P) Y).map
        ((orderedAdjunction P Y aY (d + 1)).counit.app Ke) ≫ eK.hom) (hstep d)
    simp only [Category.assoc] at hs
    rw [orderedCounit_step P Y aY Ke (d + 1), Functor.map_comp,
      Category.assoc]
    rw [← hs]
    apply congrArg (fun f ↦ _ ≫ f)
    apply congrArg (fun f ↦ _ ≫ f)
    apply congrArg (fun f ↦ _ ≫ f)
    exact (hn (d + 1)).symm

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
