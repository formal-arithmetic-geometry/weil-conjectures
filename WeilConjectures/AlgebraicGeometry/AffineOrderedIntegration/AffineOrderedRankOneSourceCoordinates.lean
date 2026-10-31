/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedLineEvaluationCoordinates
public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedTensorCoordinateFactor
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineRankOneSourceRealization
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineRankOneSupportNormalization

/-! # Rank-one source comparison in ordinary counit coordinates

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

private theorem pair_reassoc {C : Type*} [Category* C] {A B D E F : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ E} {d : E ⟶ D}
    (h : a ≫ b = c ≫ d) (k : D ⟶ F) : a ≫ b ≫ k = c ≫ d ≫ k := by
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ k) h

private theorem four_two_reassoc {C : Type*} [Category* C] {A B D E F G H : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E} {d : E ⟶ F}
    {e : A ⟶ G} {f : G ⟶ F}
    (h : a ≫ b ≫ c ≫ d = e ≫ f) (k : F ⟶ H) :
    a ≫ b ≫ c ≫ d ≫ k = e ≫ f ≫ k := by
  simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ k) h

private theorem iso_trans_symm_cancel {C : Type*} [Category* C]
    {X Y Z : C} (E : X ≅ Z) (O : Y ≅ Z) :
    (E ≪≫ O.symm).hom ≫ O.hom = E.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem ordinaryCompactComparison_inv_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (Y : Scheme.{u}) [IsNoetherian Y] (d : ℕ)
    (W V : DerivedCategory.Plus
      (Sheaf (affineTraceTower Y d).smallEtaleTopology (ModuleCat.{u + 1} A)))
    (f : W.obj ⟶ V.obj) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection Y d)).map f ≫ (ordinaryCompactComparison A Y d V).inv =
      (ordinaryCompactComparison A Y d W).inv ≫ (Etale.affineTraceLeft A Y d).map f := by
  let e := (Etale.affineTracePlusCompatibility A Y d).symm ≪≫
    Functor.isoWhiskerRight (Etale.affineTraceCompactSupportComparison A Y d)
      DerivedCategory.Plus.ι ≪≫
    Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceProjection Y d)
  exact e.inv.naturality (ObjectProperty.homMk f : W ⟶ V)

private theorem ordinaryTensorCoordinates_one_factor
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke) :
    ordinaryTensorCoordinates P Y aY Ke hKe 1 =
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
        (iteratedAffineLineProj Y 1)).mapIso
          (ordinaryOrderedRightCoordinates P Y aY Ke 1) ≪≫
        (ordinaryCompactComparison (AffineLinePurity.Ring P) Y 1
          ⟨_, ordinarySource_plus P Y aY Ke hKe 1⟩).symm := by
  exact ordinaryTensorCoordinatesRaw_factor P Y aY Ke hKe 1

/-- The rank-one ordered coordinates agree with the specified chart source comparison.
This equality contains neither geometric evaluation nor any counit.
Source: projection-purity agreement, final paragraph, canonical source reassociations
(blueprint: lem-pur-affine-ordered-rank-one-source-coordinates).
Proof: expand the line and ordered counit coordinates and factor the ordinary
rank-one tensor coordinates. Move the line witness through the arrow-congruence
isomorphism by naturality and combine the source maps. The source-realization
identity identifies this composite before compact support. Naturality of the site
comparison, the chosen etale lower-shriek comparison, and the inverse ordinary
compact comparison move the ordinary source map to the end. Cancel the intermediate
ordinaryOrderedRightCoordinates isomorphism. Apply support normalization to the
remaining prefix, on the retained ordinary source W. Expanding the final ordinary
source map gives the displayed sourceCoordinates and rightComparison inverse. -/
theorem rankOne_source_coordinates
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
      (lineEvaluationCoordinates P Y aY K Ke hKe eK).hom =
      (fixedCompactSupportOriginIso A
        (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y)) c).hom.app W ≫
      (fixedCompactSupportComparisonIso A c).hom.app W ≫
      (comparison A Y).map
        ((Etale.affineTraceLineLeft A Y).map
            ((CoordinateLine.sourceCoordinates P Y P.level (annihilates P) Ke).hom ≫
              (CoordinateLine.rightComparison A (exponent P) (annihilates P) Y).inv.app Ke)) := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
    HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
  let A := AffineLinePurity.Ring P
  let W : DerivedCategory.Plus (Sheaf (AffineSpace PUnit.{u + 1} Y).smallEtaleTopology
      (ModuleCat.{u + 1} A)) :=
    ⟨etaleSource P.coefficients.l P.extension (P.level - 1) Y P.level
        (annihilates P) Ke,
      etaleSource_plus P.coefficients.l P.extension (P.level - 1) Y P.level
        (annihilates P) Ke hKe⟩
  let J : DerivedCategory.Plus (Sheaf (AffineSpace PUnit.{u + 1} Y).smallEtaleTopology
      (ModuleCat.{u + 1} A)) :=
    ⟨sourceEtale P Y Ke 1, (source_applicability P Y aY K Ke hKe eK 1).2.1.1.1⟩
  let V : DerivedCategory.Plus (Sheaf (AffineSpace PUnit.{u + 1} Y).smallEtaleTopology
      (ModuleCat.{u + 1} A)) := ⟨_, ordinarySource_plus P Y aY Ke hKe 1⟩
  let E : W.obj ≅ V.obj := CoordinateLine.sourceCoordinates P Y P.level (annihilates P) Ke ≪≫
    (CoordinateLine.rightComparison A (exponent P) (annihilates P) Y).symm.app Ke
  let O : J.obj ≅ V.obj := ordinaryOrderedRightCoordinates P Y aY Ke 1
  let e : W.obj ≅ J.obj := E ≪≫ O.symm
  let C := comparison A (iteratedAffineLine Y 1)
  let F := comparison A Y
  let Q := AffineLineEvaluation.support P aY (iteratedAffineLineProj Y 1)
  let cg := rightDerivedLowerShriekCongr (ModuleCat.{u + 1} A)
    (Category.comp_id (lastProjection Y 0)).symm
  let B := compactSupportSiteComparison A (compactification Y 1)
  let U := Etale.rightDerivedLowerShriekIso A (compactification Y 1)
  have hr : (AffineLineEvaluation.lineWitness P Y K.obj Ke hKe eK).iso.hom ≫
      (sourceReassociation P Y aY K.obj 0).inv ≫
        (sourceRealization P Y K.obj Ke eK 1).inv = C.map e.hom := by
    exact congrArg Iso.hom (rankOne_source_realization P Y aY K Ke hKe eK)
  have hn := cg.hom.naturality
    (AffineLineEvaluation.lineWitness P Y K.obj Ke hKe eK).iso.hom
  have hb : Q.map (C.map e.hom) ≫ B.hom.app J =
      B.hom.app W ≫ F.map
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) (compactification Y 1)).map e.hom) :=
    B.hom.naturality (ObjectProperty.homMk e.hom : W ⟶ J)
  have hu := U.hom.naturality e.hom
  have ht := ordinaryCompactComparison_inv_naturality A Y 1 W V E.hom
  have he : e.hom ≫ O.hom = E.hom := iso_trans_symm_cancel E O
  have ho : (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (compactification Y 1)).map e.hom ≫
      U.hom.app J.obj ≫
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (iteratedAffineLineProj Y 1)).map O.hom ≫
        (ordinaryCompactComparison A Y 1 V).inv =
      U.hom.app W.obj ≫ (ordinaryCompactComparison A Y 1 W).inv ≫
        (Etale.affineTraceLeft A Y 1).map E.hom := by
    erw [reassoc_of% hu, ← Functor.map_comp_assoc, he, ht]
  have hfo := congrArg F.map ho
  simp only [Functor.map_comp] at hfo
  have hs := rankOne_support_normalization P Y aY W
  dsimp only at hs ⊢
  simp only [Functor.map_comp] at hs
  simp only [lineEvaluationCoordinates, orderedCounitCoordinates,
    ordinaryTensorCoordinates_one_factor]
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso, Iso.app]
  change (AffineLineEvaluation.support P aY
      (AffineSpace PUnit.{u + 1} Y ↘ Y)).map
        (AffineLineEvaluation.lineWitness P Y K.obj Ke hKe eK).iso.hom ≫
      cg.hom.app ((lineSource P Y).obj K.obj) ≫
      Q.map (sourceReassociation P Y aY K.obj 0).inv ≫
      Q.map (sourceRealization P Y K.obj Ke eK 1).inv ≫
      B.hom.app J ≫ F.map (U.hom.app J.obj ≫
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
          (iteratedAffineLineProj Y 1)).map O.hom ≫
        (ordinaryCompactComparison A Y 1 V).inv) =
    (fixedCompactSupportOriginIso A
      (HasCompactification.compactification (AffineSpace PUnit.{u + 1} Y ↘ Y))
      (affineTraceLineCompactification Y)).hom.app W ≫
    (fixedCompactSupportComparisonIso A (affineTraceLineCompactification Y)).hom.app W ≫
    F.map ((Etale.affineTraceLeft A Y 1).map E.hom)
  simp only [Functor.map_comp]
  erw [reassoc_of% hn]
  erw [← Q.map_comp_assoc, ← Q.map_comp_assoc, Category.assoc, hr]
  erw [pair_reassoc hb (F.map (U.hom.app J.obj) ≫
    F.map ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (iteratedAffineLineProj Y 1)).map O.hom) ≫
    F.map (ordinaryCompactComparison A Y 1 V).inv), hfo]
  exact four_two_reassoc hs (F.map ((Etale.affineTraceLeft A Y 1).map E.hom))

set_option maxHeartbeats 6400000 in
-- The displayed source witness and rank-one derived coordinates need elaboration.
end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
