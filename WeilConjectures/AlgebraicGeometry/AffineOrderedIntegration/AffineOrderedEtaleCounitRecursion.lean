/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedSupportedTensorCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedLineEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEtaleSourceReassociation

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

attribute [local semireducible] sourceWitness
attribute [local implicit_reducible] sourceWitness

/-- On ordinary tensor sources, compact-support composition carries the realized
last-line counit to the last counit of the ordered ordinary adjunction.
The pro-etale input H and its realization are arbitrary. There is no pro-etale
source reassociation or successor source realization in this statement.
Source: projection-purity agreement, final paragraph, compact-support composition.
(blueprint: lem-pur-affine-ordered-etale-counit-recursion).

Proof: expand normalizedLineEvaluation and lineEvaluationCoordinates. The rank-one
source-coordinate identity replaces the last-line witness followed by those coordinates
with the fixed chart support comparison followed by the ordinary line source map.
Naturality moves eH through preceding support and cancels it with its inverse. Expand
supportedTensorCoordinates. Factor ordinaryTensorCoordinatesRaw using the explicit
ordinaryOrderedRightCoordinates, and transport along affineTower_projection_eq.
The successor clause of normalized_source_descent, together with ordered Tate pullback
composition, identifies etaleSourceReassociation followed by the line source map with
the successor ordinaryOrderedRightCoordinates followed by the line right functor
applied to the preceding source-coordinate inverse. Naturality of the line counit
then moves the preceding source coordinate past that counit. The remaining support
maps form the generic finite-ring origin-composition model at Ring P. Expand that
model and the successor clause of affineTraceCompactSupportComparison; site-comparison
composition and refinement coherence cancel all intermediate inclusion and standing
compactification comparisons. Thus the remaining ordinary map is precisely
orderedCounitStep. This argument works on all bounded-below inputs displayed here;
it never compares any geometric integration with an ordinary counit. -/
theorem etaleCounit_recursion
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke) (d : ℕ)
    (H : Plus (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1)))
    (hJ : etaleFiniteTor (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1))
      (sourceEtale P Y Ke (d + 1)))
    (eH : (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1))).obj
      (sourceEtale P Y Ke (d + 1)) ≅ H.obj)
    (hJnext : DerivedCategory.TStructure.t.plus (sourceEtale P Y Ke (d + 2))) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    letI : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
    letI : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
    letI : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 2))).map
      ((comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 2))).map
          (etaleSourceReassociation P Y aY Ke d).hom ≫
        (AffineLineEvaluation.lineWitness P (iteratedAffineLine Y (d + 1)) H.obj
          (sourceEtale P Y Ke (d + 1)) hJ eH).iso.hom) ≫
    (AffineLineEvaluation.compositor P aY (iteratedAffineLineProj Y (d + 1))
      H.obj (sourceEtale P Y Ke (d + 1)) hJ eH).inv ≫
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map
      (normalizedLineEvaluation P (iteratedAffineLine Y (d + 1))
        (towerBase aY (d + 1)) H (sourceEtale P Y Ke (d + 1)) hJ eH) ≫
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map eH.inv ≫
    (supportedTensorCoordinates P Y aY Ke hKe (d + 1) hJ.1.1.1).hom =
      (supportedTensorCoordinates P Y aY Ke hKe (d + 2) hJnext).hom ≫
        (comparison (AffineLinePurity.Ring P) Y).map
          (orderedCounitStep P Y aY Ke (d + 1)) := by sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
