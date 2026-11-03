/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.AffineIntegrationDirectSumComparisonMaps
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelSigmaOrdinaryComparison
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts

/-! # Site comparison of the coefficient-unit composition mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The standing sigma is the ordinary dualizing tensor mate under the canonical
unit and site comparisons. No diagonal or Tate orientation occurs in this equation.
Source: composition proof Step 1, compact-support site coherence and mate pasting.
(blueprint: new-pur-affine-integration-sigma-site-comparison).

Proof: expand the Hom chain defining the standing exceptional adjunction, at the
coefficient unit and at the ordinary dualizing object of g. The bounded ordinary
origins exist because f and g are smooth of finite type. Use finiteSiteThetaTransport
for the projection/counit tensor transpose. Use finiteSiteDiagramTransposes for the
compact-support compositor, with compactSupportSiteCoherence identifying the actual
proper/open composition diagram. The comparison adjunction triangles cancel the
comparison units. The remaining unit changes are modelOrientationUnit followed by
diagonalDualizingComparison; changing the ordinary tensor unit to the degree-zero
coefficient object gives chartDualizingUnit. Tensor symmetry is preserved by the
monoidal comparison. These substitutions give the equation. No trace normalization
or direct-sum purity identity is used. Identity factors and empty schemes obey the
same adjunction triangle calculations.
-/
theorem affineIntegration_sigma_site_comparison (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ] :
    letI := P.noetherian aZ
    letI := P.noetherian (g ≫ aZ)
    letI := Dnc.compactifiable P f (g ≫ aZ)
    letI := Dnc.compactifiable P g aZ
    letI := Dnc.compactifiable P (f ≫ g) aZ
    ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫
        (P.affineIntegrationUnitComparison (f ≫ g)).hom =
      (P.affineIntegrationTensorComparison f g).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
            (P.affineIntegrationOrdinarySigma f g) := by
  let := P.noetherian aZ
  let := P.noetherian (g ≫ aZ)
  let := Dnc.compactifiable P f (g ≫ aZ)
  let := Dnc.compactifiable P g aZ
  let := Dnc.compactifiable P (f ≫ g) aZ
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
  let A := ModuleCat.{u + 1} P.Coefficient
  let F := (ProEtale.comparisonUpperStar A X).mapDerivedCategory
  let FY := (ProEtale.comparisonUpperStar A Y).mapDerivedCategory
  let H := (ProEtale.upperStar A f).leftDerivedFunctor
  let G := (Etale.upperStar A f).leftDerivedFunctor
  let uf := P.chartDualizingUnit f
  let ug := P.chartDualizingUnit g
  let uh := P.chartDualizingUnit (f ≫ g)
  let Cf := P.affineIntegrationUnitComparison f ≪≫ F.mapIso uf.symm
  let Cg := P.affineIntegrationUnitComparison g ≪≫ FY.mapIso ug.symm
  let Ch := P.affineIntegrationUnitComparison (f ≫ g) ≪≫ F.mapIso uh.symm
  let B := compatibleBifunctorIso (Etale.derivedTensor A X) uf.symm (G.mapIso ug.symm)
  let S := P.compatibleTensorIso Cf
    (H.mapIso Cg ≪≫ Dnc.pullComparison P f (Etale.dualizingComplex P.Coefficient g)) ≪≫
    (compatibleComparisonTensor P.Coefficient X (Etale.dualizingComplex P.Coefficient f)
      (G.obj (Etale.dualizingComplex P.Coefficient g))).symm
  let eta : FY ⋙ H ≅ G ⋙ F :=
    Functor.isoWhiskerLeft FY (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A f) ≪≫
      ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso A f ≪≫
        Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory A f).symm F
  have hn : H.mapIso (FY.mapIso ug.symm) ≪≫
      Dnc.pullComparison P f (Etale.dualizingComplex P.Coefficient g) =
      Dnc.pullComparison P f (P.diagonalOrdinaryDualizing g) ≪≫
        F.mapIso (G.mapIso ug.symm) := by
    apply Iso.ext
    exact eta.hom.naturality ug.inv
  have hfactor :
      (H.mapIso (P.affineIntegrationUnitComparison g) ≪≫
        Dnc.pullComparison P f (P.diagonalOrdinaryDualizing g)) ≪≫
          F.mapIso (G.mapIso ug.symm) =
      H.mapIso Cg ≪≫ Dnc.pullComparison P f (Etale.dualizingComplex P.Coefficient g) := by
    simp only [Cg, Functor.mapIso_trans, Iso.trans_assoc]
    rw [hn]
  have hnat := compatibleTensorComparison_naturality
    (Etale.derivedTensor A X) (ProEtale.derivedTensor A X) F
    (ProEtale.comparisonTensorNatIso P.Coefficient X) uf.symm (G.mapIso ug.symm)
  dsimp only [Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj] at hnat
  have hm₁ := congrArg (fun n ↦ n.app (G.obj (Etale.dualizingComplex P.Coefficient g)))
    (ProEtale.comparison_tensor_app P.Coefficient X (Etale.dualizingComplex P.Coefficient f))
  have hm₂ := congrArg (fun n ↦ n.app (G.obj (P.diagonalOrdinaryDualizing g)))
    (ProEtale.comparison_tensor_app P.Coefficient X (P.diagonalOrdinaryDualizing f))
  rw [hm₁, hm₂] at hnat
  have hi := compatibleIso_inverse_square _ _ (F.mapIso B)
    (compatibleBifunctorIso (ProEtale.derivedTensor A X)
      (F.mapIso uf.symm) (F.mapIso (G.mapIso ug.symm))) hnat
  have hi' :
      (compatibleComparisonTensor P.Coefficient X (P.diagonalOrdinaryDualizing f)
        (G.obj (P.diagonalOrdinaryDualizing g))).symm ≪≫ F.mapIso B =
      compatibleBifunctorIso (ProEtale.derivedTensor A X)
        (F.mapIso uf.symm) (F.mapIso (G.mapIso ug.symm)) ≪≫
      (compatibleComparisonTensor P.Coefficient X (Etale.dualizingComplex P.Coefficient f)
        (G.obj (Etale.dualizingComplex P.Coefficient g))).symm := by
    simpa only [compatibleComparisonTensor, compatibleComparisonTensorGeneric] using hi
  have hsource : P.affineIntegrationTensorComparison f g ≪≫ F.mapIso B = S := by
    dsimp only [affineIntegrationTensorComparison, S, compatibleTensorIso, compatibleTensor]
    rw [Iso.trans_assoc, hi', ← Iso.trans_assoc, compatibleBifunctorIso_trans, hfactor]
  have hsigma : ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫ Ch.hom =
      S.hom ≫ F.map (DiagonalPasting.sigma P.Coefficient P d f g (f ≫ g ≫ aZ)).hom := by
    simpa only [Cf, Cg, Ch, S, affineIntegrationUnitComparison, Iso.trans_assoc,
      F, FY, G, H, A, uf, ug, uh] using model_sigma_ordinary_comparison P d e f g aZ
  have hs := congrArg (fun z ↦ z ≫ F.map uh.hom) hsigma
  have hb := congrArg Iso.hom hsource
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hb
  rw [← hb] at hs
  have hcancel : Ch.hom ≫ F.map uh.hom =
      (P.affineIntegrationUnitComparison (f ≫ g)).hom := by
    dsimp only [Ch, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [Category.assoc, ← F.map_comp, uh.inv_hom_id, F.map_id, Category.comp_id]
  have hord : F.map B.hom ≫
      F.map (DiagonalPasting.sigma P.Coefficient P d f g (f ≫ g ≫ aZ)).hom ≫
        F.map uh.hom = F.map (P.affineIntegrationOrdinarySigma f g) := by
    rw [← F.map_comp, ← F.map_comp]
    apply congrArg F.map
    simp only [affineIntegrationOrdinarySigma, DiagonalPasting.sigma,
      DiagonalPasting.thetaIso, DiagonalPasting.finiteThetaIso,
      DiagonalPasting.compositionUnit, DiagonalPasting.exceptionalUnit,
      dualizingCompositeSigma, dualizingCompositeConjugate, Iso.trans_hom,
      Iso.symm_hom, asIso_hom, B, uf, ug, uh, G, A]
  simpa only [Category.assoc, hcancel, hord] using hs

end WeilConjectures.PurityFiniteSetting
