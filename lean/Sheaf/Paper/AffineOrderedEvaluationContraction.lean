/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K6
-/
module

public import Sheaf.Paper.AffineOrderedIntegrationData
public import Sheaf.Paper.AffineLineCompositeTranspose

/-! # Contraction of the ordered coefficient evaluations

Source: projection-purity agreement, final paragraph, ordered integration.
(blueprint: lem-pur-affine-ordered-evaluation-contraction).
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

/-- The first coefficient evaluation is the normalized line evaluation; each subsequent
one is its compact-support composite with the preceding coefficient evaluation.
This statement involves neither exceptional inverse images nor integration transposes.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, final paragraph, expanded ordered-transpose
proof Steps 3--7 (blueprint: lem-pur-affine-ordered-evaluation-contraction).

Proof: on the ordinary etale site expand the ordered adjunction counit at its last
coordinate. The affine-line counit is inverse projection followed by tensor with the
restricted normalized projective trace: commute the open counit through the proper
projection using proper naturality and the open tensor-counit identity. Apply the
two-coefficient projection action law, then projection composition, to combine the two
inverse projections. The coefficient part is ordinaryTraceRaw at the next stage by the
composite-adjunction counit formula. The canonical Tate pullback, the tensor associator,
and coefficientActionComparison give precisely sourceReassociation and sourceComparison.
Transport the calculation by the compact-support site composition square and the finite
projection comparison square. Their inverse maps and the right unitor give the displayed
augmentations and standingEvaluation. At the first coordinate the preceding adjunction
is the identity; only equality transport from q to q followed by id remains. This is the
first conjunct. At each positive stage its left support comparison is compositor, giving
the second conjunct. All sources have the bounded finite-Tor representatives supplied
by source_applicability. All shifts are even, so ordered reassociation has sign +1.
Identity adjunctions, zero coefficients, and empty bases satisfy the same calculation. -/
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
      augmentation P Y aY K Ke hKe eK (d + 1)) := by sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
