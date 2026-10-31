/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelSigmaOrdinaryComparison
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalGlobalEquation
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts

/-! # Diagonal pasting in the standing coefficient-unit coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The orientation-free alpha equation in the standing dualizing coordinates.
Source: composition coherence proof Step 1 and diagonal section pasting Steps 1--5.
(blueprint: lem-pur-model-orientation-alpha-pasting).

Proof: apply ordinary diagonal section pasting and comparison inverse image.
The coefficient-unit comparison identifies chart alpha followed by the inverse
model unit with the ordinary alpha followed by the inverse ordinary dualizing
comparison. Naturality of monoidal comparison and of pullback comparison
identifies their two tensor products. The standing sigma comparison identifies
the remaining ordinary sigma with the specified standing sigma. Cancel the
three coefficient-unit comparisons. This is orientation-free and uses neither
Tate powers nor affine coordinates. -/
theorem model_orientation_alpha_pasting (P : PurityFiniteSetting.{u})
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
    letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    (P.compatibleKappa d e f g aZ).hom ≫
        (P.chartDiagonalAlpha (d + e) (f ≫ g) aZ ≪≫
          (P.modelOrientationUnit (f ≫ g)).symm).hom =
      (P.compatibleTensorIso
        (P.chartDiagonalAlpha d f (g ≫ aZ) ≪≫ (P.modelOrientationUnit f).symm)
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
          (P.chartDiagonalAlpha e g aZ ≪≫ (P.modelOrientationUnit g).symm))).hom ≫
        ProEtale.CompositionTensorMate.sigma P.Coefficient f g := by
  let := P.noetherian aZ
  let := P.noetherian (g ≫ aZ)
  let := P.noetherian (f ≫ g ≫ aZ)
  let := Dnc.compactifiable P f (g ≫ aZ)
  let := Dnc.compactifiable P g aZ
  let := Dnc.compactifiable P (f ≫ g) aZ
  let geo := DiagonalPasting.geometryProperties d e f g
  let := geo.1
  let := geo.2.1
  let := geo.2.2.1
  let := geo.2.2.2.1
  let := geo.2.2.2.2
  let := DiagonalPasting.noetherianPullback (f ≫ g) g
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
  let A := ModuleCat.{u + 1} P.Coefficient
  let F := (ProEtale.comparisonUpperStar A X).mapDerivedCategory
  let FY := (ProEtale.comparisonUpperStar A Y).mapDerivedCategory
  let H := (ProEtale.upperStar A f).leftDerivedFunctor
  let G := (Etale.upperStar A f).leftDerivedFunctor
  let Cf := P.modelOrientationUnit f ≪≫ P.diagonalDualizingComparison f ≪≫
    F.mapIso (P.chartDualizingUnit f).symm
  let Cg := P.modelOrientationUnit g ≪≫ P.diagonalDualizingComparison g ≪≫
    FY.mapIso (P.chartDualizingUnit g).symm
  let Cfg := P.modelOrientationUnit (f ≫ g) ≪≫
    P.diagonalDualizingComparison (f ≫ g) ≪≫
      F.mapIso (P.chartDualizingUnit (f ≫ g)).symm
  let af := P.chartDiagonalAlpha d f (g ≫ aZ) ≪≫ (P.modelOrientationUnit f).symm
  let ag := P.chartDiagonalAlpha e g aZ ≪≫ (P.modelOrientationUnit g).symm
  let aTotal := P.chartDiagonalAlpha (d + e) (f ≫ g) aZ ≪≫
    (P.modelOrientationUnit (f ≫ g)).symm
  have hf : af ≪≫ Cf =
      Dnc.sourceComparison P d (pullback.fst f f) (f ≫ g ≫ aZ) (pullback.diagonal f) ≪≫
        F.mapIso (DiagonalPasting.alpha P.Coefficient P d f (f ≫ g ≫ aZ)) := by
    apply Iso.ext
    simp [af, Cf, chartDiagonalAlpha, F, A, Iso.trans_hom,
      diagonalComparedRestriction, DiagonalPasting.alpha, finiteDiagonalRestriction]
  have hg : ag ≪≫ Cg =
      Dnc.sourceComparison P e (pullback.fst g g) (g ≫ aZ) (pullback.diagonal g) ≪≫
        FY.mapIso (DiagonalPasting.alpha P.Coefficient P e g (g ≫ aZ)) := by
    apply Iso.ext
    simp [ag, Cg, chartDiagonalAlpha, FY, A, Iso.trans_hom,
      diagonalComparedRestriction, DiagonalPasting.alpha, finiteDiagonalRestriction]
  have ht : aTotal ≪≫ Cfg =
      Dnc.sourceComparison P (d + e) (pullback.fst (f ≫ g) (f ≫ g))
        ((f ≫ g) ≫ aZ) (pullback.diagonal (f ≫ g)) ≪≫
          F.mapIso (DiagonalPasting.alpha P.Coefficient P (d + e)
            (f ≫ g) ((f ≫ g) ≫ aZ)) := by
    apply Iso.ext
    simp [aTotal, Cfg, chartDiagonalAlpha, F, A, Iso.trans_hom,
      diagonalComparedRestriction, DiagonalPasting.alpha, finiteDiagonalRestriction]
  let afE := DiagonalPasting.alpha P.Coefficient P d f (f ≫ g ≫ aZ)
  let agE := DiagonalPasting.alpha P.Coefficient P e g (g ≫ aZ)
  let Af := Dnc.sourceComparison P d (pullback.fst f f)
    (f ≫ g ≫ aZ) (pullback.diagonal f)
  let Ag := Dnc.sourceComparison P e (pullback.fst g g)
    (g ≫ aZ) (pullback.diagonal g)
  let S := P.compatibleTensorIso Cf
    (H.mapIso Cg ≪≫ Dnc.pullComparison P f (Etale.dualizingComplex P.Coefficient g)) ≪≫
    (compatibleComparisonTensor P.Coefficient X (Etale.dualizingComplex P.Coefficient f)
      (G.obj (Etale.dualizingComplex P.Coefficient g))).symm
  let Ssec := P.compatibleTensorIso Af
    (H.mapIso Ag ≪≫ Dnc.pullComparison P f (DiagonalPasting.diagonalSection
      P.Coefficient P g)) ≪≫
    (compatibleComparisonTensor P.Coefficient X
      (DiagonalPasting.diagonalSection P.Coefficient P f)
      (G.obj (DiagonalPasting.diagonalSection P.Coefficient P g))).symm
  let eta : FY ⋙ H ≅ G ⋙ F :=
    Functor.isoWhiskerLeft FY (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A f) ≪≫
      ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso A f ≪≫
        Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory A f).symm F
  have hn : H.mapIso (FY.mapIso agE) ≪≫
      Dnc.pullComparison P f (Etale.dualizingComplex P.Coefficient g) =
      Dnc.pullComparison P f (DiagonalPasting.diagonalSection P.Coefficient P g) ≪≫
        F.mapIso (G.mapIso agE) := by
    apply Iso.ext
    exact eta.hom.naturality agE.hom
  have hfactor : H.mapIso ag ≪≫
      (H.mapIso Cg ≪≫ Dnc.pullComparison P f (Etale.dualizingComplex P.Coefficient g)) =
      (H.mapIso Ag ≪≫
        Dnc.pullComparison P f (DiagonalPasting.diagonalSection P.Coefficient P g)) ≪≫
          F.mapIso (G.mapIso agE) := by
    rw [← Iso.trans_assoc, ← Functor.mapIso_trans, hg, Functor.mapIso_trans]
    simpa only [Iso.trans_assoc, Ag, agE] using congrArg (fun k ↦ H.mapIso Ag ≪≫ k) hn
  have hnat := compatibleTensorComparison_naturality
    (Etale.derivedTensor A X) (ProEtale.derivedTensor A X) F
    (ProEtale.comparisonTensorNatIso P.Coefficient X) afE (G.mapIso agE)
  dsimp only [Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj] at hnat
  have hm₁ := congrArg (fun n ↦ n.app (G.obj (Etale.dualizingComplex P.Coefficient g)))
    (ProEtale.comparison_tensor_app P.Coefficient X (Etale.dualizingComplex P.Coefficient f))
  have hm₂ := congrArg
    (fun n ↦ n.app (G.obj (DiagonalPasting.diagonalSection P.Coefficient P g)))
      (ProEtale.comparison_tensor_app P.Coefficient X
        (DiagonalPasting.diagonalSection P.Coefficient P f))
  rw [hm₁, hm₂] at hnat
  have hi := compatibleIso_inverse_square _ _
    (F.mapIso (compatibleBifunctorIso (Etale.derivedTensor A X) afE (G.mapIso agE)))
    (compatibleBifunctorIso (ProEtale.derivedTensor A X)
      (F.mapIso afE) (F.mapIso (G.mapIso agE))) hnat
  have hmiddle : P.compatibleTensorIso af (H.mapIso ag) ≪≫ S =
      Ssec ≪≫ F.mapIso
        (compatibleBifunctorIso (Etale.derivedTensor A X) afE (G.mapIso agE)) := by
    dsimp only [S, Ssec, compatibleTensorIso]
    rw [← Iso.trans_assoc, compatibleBifunctorIso_trans, hf, hfactor]
    rw [← compatibleBifunctorIso_trans]
    simpa only [Iso.trans_assoc, compatibleComparisonTensor,
      compatibleComparisonTensorGeneric, compatibleTensor, Af, afE] using
      congrArg (fun k ↦ compatibleBifunctorIso (ProEtale.derivedTensor A X) Af
        (H.mapIso Ag ≪≫ Dnc.pullComparison P f
          (DiagonalPasting.diagonalSection P.Coefficient P g)) ≪≫ k) hi.symm
  have hsigma := model_sigma_ordinary_comparison P d e f g aZ
  change ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫ Cfg.hom =
    S.hom ≫ F.map (DiagonalPasting.sigma P.Coefficient P d f g (f ≫ g ≫ aZ)).hom
    at hsigma
  have hp := DiagonalPasting.diagonalSectionPastingEquation P d e f g aZ
  change F.map _ = F.map _ at hp
  apply (cancel_mono Cfg.hom).mp
  change ((P.compatibleKappa d e f g aZ).hom ≫ aTotal.hom) ≫ Cfg.hom =
    ((P.compatibleTensorIso af (H.mapIso ag)).hom ≫
      ProEtale.CompositionTensorMate.sigma P.Coefficient f g) ≫ Cfg.hom
  have hth := congrArg Iso.hom ht
  simp only [Iso.trans_hom] at hth
  have hmh := congrArg Iso.hom hmiddle
  simp only [Iso.trans_hom] at hmh
  have hk : P.compatibleKappa d e f g aZ =
      Ssec ≪≫ F.mapIso (DiagonalPasting.kappa P.Coefficient P d e f g aZ) ≪≫
        (Dnc.sourceComparison P (d + e) (pullback.fst (f ≫ g) (f ≫ g))
          ((f ≫ g) ≫ aZ) (pullback.diagonal (f ≫ g))).symm := by
    simp only [compatibleKappa, Ssec, Af, Ag, H, G, F, A, Iso.trans_assoc]
  calc
    _ = Ssec.hom ≫ F.map (DiagonalPasting.kappa P.Coefficient P d e f g aZ).hom ≫
        F.map (DiagonalPasting.alpha P.Coefficient P (d + e)
          (f ≫ g) ((f ≫ g) ≫ aZ)).hom := by
      rw [Category.assoc, hth]
      rw [hk]
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Category.assoc, Iso.inv_hom_id_assoc]
    _ = Ssec.hom ≫ F.map
        (compatibleBifunctorIso (Etale.derivedTensor A X) afE (G.mapIso agE)).hom ≫
          F.map (DiagonalPasting.sigma P.Coefficient P d f g (f ≫ g ≫ aZ)).hom := by
      simp only [F.map_comp] at hp
      simpa only [DiagonalPasting.tensorComparison, afE, agE, F, G,
        compatibleBifunctorIso] using congrArg (fun k ↦ Ssec.hom ≫ k) hp
    _ = (P.compatibleTensorIso af (H.mapIso ag)).hom ≫ S.hom ≫
        F.map (DiagonalPasting.sigma P.Coefficient P d f g (f ≫ g ≫ aZ)).hom := by
      simpa only [Category.assoc, Functor.mapIso_hom] using
        congrArg (fun k ↦ k ≫
          F.map (DiagonalPasting.sigma P.Coefficient P d f g (f ≫ g ≫ aZ)).hom) hmh.symm
    _ = _ := by rw [Category.assoc, hsigma]

end WeilConjectures.PurityFiniteSetting
