/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedLineEvaluationCoordinates
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedTensorCoordinateFactor
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEtaleCounitRecursion
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedSourceReassociationRealization

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

Proof: sourceReassociation_realization identifies the source map before compact
support. Postcompose it with the last-line witness and cancel that witness's inverse.
Apply etaleCounit_recursion to the preceding ordered source and its specified ordinary
realization. Precompose the resulting equality by compact support of the inverse
successor realization. Factor orderedCounitCoordinates into its source realization
and supportedTensorCoordinates. Functoriality and associativity identify the two
sides with the required composites. -/
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
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
  let : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
  let : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
  have hs := sourceReassociation_realization P Y aY K Ke hKe eK d
  have hi := congrArg (fun f ↦ f ≫
    (AffineLineEvaluation.lineWitness P (iteratedAffineLine Y (d + 1))
      ((orderedSource P Y (d + 1)).obj K.obj) (sourceEtale P Y Ke (d + 1))
      (source_applicability P Y aY K Ke hKe eK (d + 1)).2
      (sourceRealization P Y K.obj Ke eK (d + 1))).iso.hom) hs
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hi
  have hc := etaleCounit_recursion P Y aY Ke hKe d
    ⟨(orderedSource P Y (d + 1)).obj K.obj,
      (source_applicability P Y aY K Ke hKe eK (d + 1)).1⟩
    (source_applicability P Y aY K Ke hKe eK (d + 1)).2
    (sourceRealization P Y K.obj Ke eK (d + 1))
    (source_applicability P Y aY K Ke hKe eK (d + 2)).2.1.1.1
  have hh := congrArg (fun f ↦
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 2))).map
      (sourceRealization P Y K.obj Ke eK (d + 2)).inv ≫ f) hc
  rw [orderedCounitCoordinates_factor P Y aY K Ke hKe eK (d + 1),
    orderedCounitCoordinates_factor P Y aY K Ke hKe eK (d + 2)]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [hi]
  simpa only [Functor.map_comp, Category.assoc] using hh

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
