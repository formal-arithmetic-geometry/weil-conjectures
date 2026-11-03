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

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
