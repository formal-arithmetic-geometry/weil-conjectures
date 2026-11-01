/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedLineEvaluationCoordinates

/-! # Cancellation of the line realization

Source: projection-purity agreement, final canonical-reassociation paragraph.
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

/-- The chosen realization cancels after normalized line evaluation is expanded.
Source: projection-purity agreement, final normalized-line counit calculation.
(blueprint: lem-pur-affine-ordered-etale-counit-line-paste).
Proof: expand normalizedLineEvaluation, distribute the support functor over the
three-factor composite, and cancel eH.hom followed by eH.inv. Functoriality and
associativity leave lineEvaluationCoordinates followed by the ordinary line counit. -/
theorem etaleCounit_line_paste
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (_hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke) (d : ℕ)
    (H : Plus (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1)))
    (hJ : etaleFiniteTor (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1))
      (sourceEtale P Y Ke (d + 1)))
    (eH : (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1))).obj
      (sourceEtale P Y Ke (d + 1)) ≅ H.obj) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    letI : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
    letI : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
    letI : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
    letI : IsNoetherian (iteratedAffineLine Y (d + 1)) :=
      tower_noetherian P Y aY (d + 1)
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map
      (normalizedLineEvaluation P (iteratedAffineLine Y (d + 1))
        (towerBase aY (d + 1)) H (sourceEtale P Y Ke (d + 1)) hJ eH) ≫
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map eH.inv =
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))).map
      ((lineEvaluationCoordinates P (iteratedAffineLine Y (d + 1))
        (towerBase aY (d + 1)) H (sourceEtale P Y Ke (d + 1)) hJ eH).hom ≫
      (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1))).map
        (orderedCounitStep P (iteratedAffineLine Y (d + 1))
          (towerBase aY (d + 1)) (sourceEtale P Y Ke (d + 1)) 0)) := by
  simp [normalizedLineEvaluation, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
