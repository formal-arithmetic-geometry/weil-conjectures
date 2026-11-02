/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
public import WeilConjectures.AlgebraicGeometry.AffineCoefficientCounit.AffineCoefficientCounitMaps
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineCoefficientTransitionCompatibility

/-! Transport of source comparisons along a specified coefficient square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite

set_option allowUnsafeReducibility true in
attribute [local reducible] projectionSourceObject proSourceObject ordinarySourceObject
    etaleSource tensorCoefficientIso

private theorem tensor_pullback_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) (K : Etale.DerivedCategoryModule A Y)
    {W W' : Etale.DerivedCategoryModule A X} (b : W ⟶ W') :
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj
          ((VectorIntegrationSite.comparison A Y).obj K))).map
      ((VectorIntegrationSite.comparison A X).map b)) ≫
        (tensorPullbackComparison A q K W').inv =
      (tensorPullbackComparison A q K W).inv ≫ (VectorIntegrationSite.comparison A X).map
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.ordinaryFinitePullback A q).obj K)).map b) := by
  have hc := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} A) ((Etale.ordinaryFinitePullback A q).obj K)).inv.naturality b
  have ht := (((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
    ((VectorIntegrationSite.pullback A q).app K)).inv).naturality
      ((VectorIntegrationSite.comparison A X).map b)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.mapIso_inv, Iso.app_inv] at hc ht
  unfold tensorPullbackComparison tensorComparison
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv]
  rw [← Category.assoc, ht, Category.assoc, hc]
  simp only [Category.assoc]

set_option maxHeartbeats 4000000 in
-- Matching the specialized derived-category comparison maps needs extra reduction.
/--
Source comparison transport once the coefficient twist square has been identified.
Source: the source-comparison square in the final paragraph of
`cor-pur-affine-space-zero-section-purity.proof.md`
(blueprint: lem-route-coordinate-line-source-comparison-transport).

Proof: expand `sourceComparison` into its fixed endpoint conversions and the
realized tensor comparison. Naturality of the derived tensor/pullback comparison
and functoriality of the site comparison give the square; the endpoint
conversions cancel by proof irrelevance. The supplied `hcompat` identifies the
coefficient map occurring in that naturality calculation with the displayed
ordinary transition. -/
theorem coordinate_line_source_comparison_transport
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
    (hP : IsUnit (P.coefficients.l : Γ(ProjectiveLine T, ⊤)))
    (hX : IsUnit (P.coefficients.l : Γ(AffineSpace PUnit.{u + 1} T, ⊤)))
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj)
    (q : AffineLinePurity.etaleSource P.coefficients.l P.extension (P.level - 1)
      T r hA Ke ≅ AffineLinePurity.etaleSource P.coefficients.l P.extension
      (P.level - 1) T r' hA' Ke)
    (hq : q = (by
      unfold AffineLinePurity.etaleSource AffineLinePurity.ordinarySourceObject
      exact ((Etale.derivedTensor (ModuleCat.{u + 1} (Ring P))
        (AffineSpace PUnit.{u + 1} T)).obj
        ((Etale.ordinaryFinitePullback (Ring P)
          (AffineSpace PUnit.{u + 1} T ↘ T)).obj Ke)).mapIso
        (coordinate_line_etale_transition P T aT r r' hA hA')))
    (hcompat :
      coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r hA hP hX ≪≫
          (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r' hA'
            hP hX).symm =
        (VectorIntegrationSite.comparison (Ring P)
          (AffineSpace PUnit.{u + 1} T)).mapIso
          (coordinate_line_etale_transition P T aT r r' hA hA')) :
    (tensorCoefficientIso (Ring P) T _ _
      (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r hA hP hX ≪≫
        (coefficientTwistIso P.coefficients.l P.extension (P.level - 1) T r' hA' hP hX).symm)
      K.obj).hom ≫
    (sourceComparison P.coefficients.l P.extension (P.level - 1) T r' hA' K.obj Ke eK).inv =
    (sourceComparison P.coefficients.l P.extension (P.level - 1) T r hA K.obj Ke eK).inv ≫
      (VectorIntegrationSite.comparison (Ring P)
        (AffineSpace PUnit.{u + 1} T)).map q.hom := by
  have _hKe := hKe
  subst q
  rw [hcompat]
  unfold tensorCoefficientIso sourceComparison realizedTensorComparison
  simp only [id_eq, Iso.trans_inv, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.symm_inv, Iso.app_inv,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.assoc]
  rw [(VectorIntegrationSite.comparison (Ring P)
    (AffineSpace PUnit.{u + 1} T)).map_id]
  simp only [Category.comp_id]
  have hn := ((derivedTensor (ModuleCat.{u + 1} (Ring P))
    (AffineSpace PUnit.{u + 1} T)).map
    ((upperStar (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} T ↘ T)).leftDerivedFunctor.map eK.inv)).naturality
        ((VectorIntegrationSite.comparison (Ring P)
          (AffineSpace PUnit.{u + 1} T)).map
            (coordinate_line_etale_transition P T aT r r' hA hA').hom)
  rw [reassoc_of% hn]
  rw [tensor_pullback_natural (Ring P) (AffineSpace PUnit.{u + 1} T ↘ T) Ke
    (coordinate_line_etale_transition P T aT r r' hA hA').hom]
  rw [(VectorIntegrationSite.comparison (Ring P)
    (AffineSpace PUnit.{u + 1} T)).map_id]
  simp only [Category.id_comp]

end AlgebraicGeometry.ProEtale.CoordinateLine
