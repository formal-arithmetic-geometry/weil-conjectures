/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
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

/-- Realizing the ordinary last-line tensor reassociation gives the specified pro-etale
source reassociation. This is an equality before applying compact support or any counit.
Source: projection-purity agreement, final paragraph, canonical reassociations.
(blueprint: lem-pur-affine-ordered-source-reassociation-realization).

Proof: replace sourceReassociation by its uniquely specified raw tensor map, using its
HEq characterization. Expand sourceRealization into realizedTensorComparison followed
by inverse sourceComparison. Expand the last-line witness into sourceComparison for the
chart coefficient. The comparison of the ordered coefficient action with its tensor
source identifies the initial unit and each shifted-line factor. Naturality of the
pullback/tensor site comparison moves eK past these factors. Its composition law
identifies the total pullback with the two successive pullbacks. The ordered Tate
pullback composition identifies the coefficient pullbacks. Tensor associativity and
its naturality identify the remaining factors with etaleSourceReassociation, including
the inverse chart-coefficient comparison. Cancel the adjacent inverse comparison maps.
All these operations concern sources only; no trace or counit is used. -/
theorem sourceReassociation_realization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    (sourceReassociation P Y aY K.obj (d + 1)).hom ≫
      (AffineLineEvaluation.lineWitness P (iteratedAffineLine Y (d + 1))
        ((orderedSource P Y (d + 1)).obj K.obj) (sourceEtale P Y Ke (d + 1))
        (source_applicability P Y aY K Ke hKe eK (d + 1)).2
        (sourceRealization P Y K.obj Ke eK (d + 1))).iso.inv =
    (sourceRealization P Y K.obj Ke eK (d + 2)).inv ≫
      (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 2))).map
        (etaleSourceReassociation P Y aY Ke d).hom := by sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
