/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedLineEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedStandingChartCounit

/-! # Standing evaluation on its specified ordinary source

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
attribute [local implicit_reducible] sourceWitness rightDerivedLowerShriek
  Etale.affineTraceOpenLeft affineTraceLineCompactification
  affineTraceTower affineTraceProjection

set_option maxHeartbeats 6400000 in
-- The concrete source witness requires the displayed derived functor endpoints.
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

/-- The specified ordinary line source transports standing evaluation to its counit.
Source: projection-purity agreement, final paragraph, fixed compact-support coordinates
(blueprint: lem-pur-affine-ordered-standing-source-counit).
Proof: apply the standing chart counit formula. Expand changeSupport, whose first
and last factors are the inverse and forward source-witness isomorphisms. Compact
support of the forward witness cancels its inverse. The remaining chart source map
is sourceComparison followed by the inverse lineSource endpoint equality; its
composite with that endpoint equality and sourceComparison inverse is identity.
Functoriality and the isomorphism inverse laws cancel these factors. Finally expand
CoordinateLine.adjunction as transport of the affine-line adjunction. Its counit is
compact support of rightComparison inverse followed by the original line counit,
which is orderedCounitStep at zero. -/
theorem standingEvaluation_source_counit
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
    let W : DerivedCategory.Plus (Sheaf (AffineSpace PUnit.{u + 1} Y).smallEtaleTopology
        (ModuleCat.{u + 1} A)) :=
      ⟨etaleSource P.coefficients.l P.extension (P.level - 1) Y P.level
          (annihilates P) Ke,
        etaleSource_plus P.coefficients.l P.extension (P.level - 1) Y P.level
          (annihilates P) Ke hKe⟩
    (AffineLineEvaluation.support P aY (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
        (AffineLineEvaluation.lineWitness P Y K.obj Ke hKe eK).iso.hom ≫
      AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK =
      (fixedCompactSupportOriginIso A
        (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y)) c).hom.app W ≫
      (fixedCompactSupportComparisonIso A c).hom.app W ≫
      (comparison A Y).map
        ((Etale.affineTraceLineLeft A Y).map
            ((CoordinateLine.sourceCoordinates P Y P.level (annihilates P) Ke).hom ≫
              (CoordinateLine.rightComparison A (exponent P) (annihilates P) Y).inv.app Ke) ≫
          orderedCounitStep P Y aY Ke 0) ≫ eK.hom := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  dsimp only
  change (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y))).map
        (AffineLineEvaluation.lineWitness P Y K.obj Ke hKe eK).iso.hom ≫
      AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK = _
  rw [standingEvaluation_chart_counit]
  simp only [AffineLineEvaluation.changeSupport, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [Iso.map_hom_inv_id_assoc]
  let Q := rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) (affineTraceLineCompactification Y)
  have hs :
      (AffineLineEvaluation.lineWitness P Y K.obj Ke hKe eK).iso.hom ≫
        eqToHom (lineSource_obj_eq P Y K.obj) ≫
        (AffineLinePurity.sourceComparison P.coefficients.l P.extension (P.level - 1)
          Y P.level (annihilates P) K.obj Ke eK).inv = 𝟙 _ := by
    simp only [AffineLineEvaluation.lineWitness, sourceWitness, Iso.trans_hom,
      Iso.symm_hom, eqToIso.inv, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Iso.hom_inv_id]
  have hm := congrArg (fun f ↦ Q.map f) hs
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id] at hm
  rw [reassoc_of% hm]
  dsimp only [AffineLineEvaluation.lineWitness, sourceWitness]
  simp only [CoordinateLine.adjunction, Adjunction.ofNatIsoRight_counit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
