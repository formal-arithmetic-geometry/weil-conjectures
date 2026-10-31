/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorSiteEquations
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.CoefficientFirstCompactSupportSiteSquareCoefficient

/-! # Specialization of the coefficient-first compact-support comparison to a vector bundle. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] Scheme.Modules
  Etale.vectorBundlePurityLower Etale.vectorBundlePurityCompactification
  Etale.vectorIntegrationSource
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem coefficient_projection_formula
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y) :
    Etale.compactProjectionMapCoeffFirst A f K W =
      ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W) ≫
        ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W).app K ≫
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app W).app
            ((Etale.ordinaryFinitePullback A f).obj K)) := by
  rfl

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem compact_projection_choice
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y) :
    ((Etale.projectionMap (ModuleCat.{u + 1} A) f).app W).app K =
      ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A)
        (HasCompactification.compactification f)).app W).app K := by
  rfl


attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
private theorem chosen_coefficient_square
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (W : Etale.DerivedCategoryModule A X) (K : Etale.DerivedCategoryModule A Y)
    (hW : DerivedCategory.TStructure.t.plus W)
    (hM : DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.ordinaryFinitePullback A f).obj K)).obj W)) :
    let c := HasCompactification.compactification f
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) K).hom.app
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((comparison A Y).obj K)).map
        ((compactSupportSiteComparison A c).inv.app ⟨W, hW⟩) ≫
      comparedModuleProjection A c W K =
      (comparison A Y).map (Etale.compactProjectionMapCoeffFirst A f K W) ≫
        (compactSupportSiteComparison A c).inv.app ⟨_, hM⟩ := by
  have h := coefficientFirstCompactSupportCoefficientSquare A f
    (HasCompactification.compactification f) W K hW hM
  simpa only [coefficient_projection_formula, compact_projection_choice,
    Etale.rightDerivedLowerShriek] using h

attribute [-instance] Etale.cartierAbelianPro Etale.cartierAbelianEtale in
/-- The coefficient-first square at the fixed vector-bundle compactification.
Source: Stacks Tags 0944 and 0GL1 for the specified coefficient-first projection,
and Tag 099R for comparison of compact support.
(blueprint: lem-route-coefficient-first-compact-support-site-square-specialized).

Proof: apply coefficientFirstCompactSupportCoefficientSquare to the vector-bundle
projection, its fixed compactification, the vector integration coefficient W and K.
The hypothesis hM is exactly the required boundedness of pullback K tensor W.
Replace e by its component using he, and pe.inv by the actual projection using hpe.
For an arbitrary chosen compactification, identify the coefficient-first projection
with symmetry, compactified projection, and compact support of symmetry using their
defining equations. Apply that chosen-compactification square to the vector projection.
Unfold just the vector integration source and the fixed compactification.
The tensor comparison is its named component. Thus the generic equation specializes
to the displayed one without geometric or cohomological hypotheses beyond those given.
-/
theorem coefficientFirstCompactSupportSpecializedSquare
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule A S)
    (hW : DerivedCategory.TStructure.t.plus
      (Etale.vectorIntegrationCoefficient A N hA S d F))
    (hM : DerivedCategory.TStructure.t.plus
      (Etale.vectorBundlePurityTwistedPullback A N hA S d F K))
    (pe : (Etale.vectorBundlePurityLower A S d F).obj
        (Etale.vectorBundlePurityTwistedPullback A N hA S d F K) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) S).obj K).obj
        (Etale.vectorIntegrationSource A N hA S d F))
    (hpe : pe.inv = Etale.vectorBundlePurityProjectionMap A N hA S d F K)
    (e : genericVectorSource A N hA S d F ≅
      (comparison A S).obj (Etale.vectorIntegrationSource A N hA S d F))
    (he : e = (compactSupportSiteComparison A
      (Etale.vectorBundlePurityCompactification S d F)).app ⟨_, hW⟩) :
    (tensorComparison A S K (Etale.vectorIntegrationSource A N hA S d F)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj ((comparison A S).obj K)).map e.inv ≫
        comparedModuleProjection A
          (Etale.vectorBundlePurityCompactification S d F)
          (Etale.vectorIntegrationCoefficient A N hA S d F) K =
      (comparison A S).map pe.inv ≫
        (compactSupportSiteComparison A
          (Etale.vectorBundlePurityCompactification S d F)).inv.app ⟨_, hM⟩ := by
  let := (Etale.vectorIntegration_geometry S d F).1
  let := (Etale.vectorIntegration_geometry S d F).2.1
  have h := chosen_coefficient_square A (VectorBundleZeroSection.π S d F)
    (Etale.vectorIntegrationCoefficient A N hA S d F) K hW hM
  rw [he, hpe]
  simpa only [tensorComparison, Iso.app_hom, Iso.app_inv, Functor.comp_obj,
    Etale.vectorBundlePurityTwistedPullback, Etale.vectorBundlePurityProjectionMap,
    Etale.vectorIntegrationSource, Etale.vectorBundlePurityCompactification] using h

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
