/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose

/-! # Single-line ordinary counit coordinates

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
-- The concrete derived source and compact-support types need additional elaboration.
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

/-- Rank-one ordinary counit coordinates on the actual affine-line projection.
The equality-of-arrows and source-reassociation isomorphisms have been inverted;
no evaluation map occurs in this construction.
Source: the rank-one instance of the canonical ordinary source coordinates.
(blueprint: lem-pur-affine-ordered-line-evaluation-coordinates). -/
def lineEvaluationCoordinates
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    (AffineLineEvaluation.support P aY (AffineSpace PUnit.{u + 1} Y ↘ Y)).obj
        ((lineSource P Y).obj K.obj) ≅
      (comparison (AffineLinePurity.Ring P) Y).obj
        ((Etale.affineTraceLeft (AffineLinePurity.Ring P) Y 1).obj
          ((Etale.affineTraceRight (AffineLinePurity.Ring P) (exponent P)
            (annihilates P) Y 1).obj Ke)) := by
  letI : IsNoetherian Y := tower_noetherian P Y aY 0
  letI : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
    HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
  exact (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (Category.comp_id (lastProjection Y 0)).symm).app ((lineSource P Y).obj K.obj) ≪≫
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y 1)).mapIso
      (sourceReassociation P Y aY K.obj 0).symm ≪≫
    orderedCounitCoordinates P Y aY K Ke hKe eK 1

/-- The ordinary rank-one counit realized on the actual pro-etale line source.
Source: ordinary affine-line adjunction and the specified site comparison.
(blueprint: lem-pur-affine-ordered-line-evaluation-coordinates). -/
def normalizedLineEvaluation
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    (AffineLineEvaluation.support P aY (AffineSpace PUnit.{u + 1} Y ↘ Y)).obj
        ((lineSource P Y).obj K.obj) ⟶ K.obj :=
  letI : IsNoetherian Y := tower_noetherian P Y aY 0
  (lineEvaluationCoordinates P Y aY K Ke hKe eK).hom ≫
    (comparison (AffineLinePurity.Ring P) Y).map (orderedCounitStep P Y aY Ke 0) ≫ eK.hom

/-- Cancellation of the rank-zero source and equality-of-arrows coordinates.
Source: the two inverse-isomorphism identities and functoriality.
(blueprint: lem-pur-affine-ordered-line-evaluation-coordinates).
Proof: expand the three factors of lineEvaluationCoordinates, cancel the
arrow-congruence isomorphism and the image of sourceReassociation with its inverse,
and cancel eK.hom with eK.inv. -/
theorem normalizedLineEvaluation_zero
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
    (AffineLineEvaluation.support P aY (iteratedAffineLineProj Y 1)).map
        (sourceReassociation P Y aY K.obj 0).hom ≫
      (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
        (Category.comp_id (lastProjection Y 0)).symm).inv.app
          ((lineSource P Y).obj K.obj) ≫
      normalizedLineEvaluation P Y aY K Ke hKe eK ≫ eK.inv =
    (orderedCounitCoordinates P Y aY K Ke hKe eK 1).hom ≫
      (comparison (AffineLinePurity.Ring P) Y).map (orderedCounitStep P Y aY Ke 0) := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
    HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
  simp only [normalizedLineEvaluation, lineEvaluationCoordinates, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
