/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTensorSiteEquations
import WeilConjectures.AlgebraicGeometry.CoefficientFirstCompactSupportSiteSquareConstructedIso
import WeilConjectures.AlgebraicGeometry.CoefficientFirstCompactSupportSiteSquareSpecializedSquare

/-! # Coefficient-first compact-support projection square
Source: Stacks 099R, 0944, 0GL1; the proper/open site comparison square.
-/
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
attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory

private theorem composite_iso_square
    {C : Type*} [Category C] {X Y Z T U : C}
    (a : X ≅ Y) (b : Y ≅ Z) (c : Z ≅ T) (d : T ≅ U) :
    c.hom ≫ d.hom ≫ (a ≪≫ b ≪≫ c ≪≫ d).inv = b.inv ≫ a.inv := by
  simp only [Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- Inverting the coefficient-first compact-support square gives the actual pro-etale
projection inverse and its comparison equation. Source: Stacks 099R, 0944, 0GL1 and the
proper/open projection calculation in lem-pur-projection-comparison-etale-origin.
(blueprint: lem-route-coefficient-first-compact-support-site-square).

Proof: the proved pasting square applies the twist-first compact-support square to
W and K, then uses naturality of compact-support comparison at the ordinary tensor
symmetry, compatibility of the tensorator with signed symmetry, the pullback symmetry
square, and naturality of pro-etale symmetry. Postcomposition by the inverse tensor/
pullback comparison gives the coefficient-first square. Its specialization to the
fixed vector compactification identifies the ordinary projection using hpe and the
source comparison using he.

Construct pp as compact-support comparison at pullback K tensor W, followed by C(pe),
tensorComparison at K and ordinary compact support of W, and tensor(CK) of e inverse.
Every factor is a specified isomorphism. The specialized square and cancellation of
tensorComparison followed by tensor(CK) of e inverse identify pp inverse with
comparedModuleProjection. Separately, cancelling the inverse pairs in the four-factor
composite proves its displayed equation. Boundedness is used precisely for the two
compact-support comparison components and its symmetry transport. The construction
and cancellation apply also to zero objects and empty schemes.
-/
theorem coefficientFirstCompactSupportSiteSquare
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
    ∃ pp : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Etale.vectorBundlePurityCompactification S d F)).obj
          ((comparison A _).obj
            (Etale.vectorBundlePurityTwistedPullback A N hA S d F K)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj ((comparison A S).obj K)).obj
        (genericVectorSource A N hA S d F),
      HEq pp.inv (comparedModuleProjection A
        (Etale.vectorBundlePurityCompactification S d F)
        (Etale.vectorIntegrationCoefficient A N hA S d F) K) ∧
      (tensorComparison A S K (Etale.vectorIntegrationSource A N hA S d F)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj ((comparison A S).obj K)).map
          e.inv ≫ pp.inv =
        (comparison A S).map pe.inv ≫
          (compactSupportSiteComparison A
            (Etale.vectorBundlePurityCompactification S d F)).inv.app ⟨_, hM⟩ := by
  let c := Etale.vectorBundlePurityCompactification S d F
  let W := Etale.vectorIntegrationCoefficient A N hA S d F
  let P := Etale.vectorIntegrationSource A N hA S d F
  let V := comparison A S
  let L := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let T := derivedTensor (ModuleCat.{u + 1} A) S
  let pp : L.obj ((comparison A _).obj
      (Etale.vectorBundlePurityTwistedPullback A N hA S d F K)) ≅
      (T.obj (V.obj K)).obj (genericVectorSource A N hA S d F) :=
    (compactSupportSiteComparison A c).app ⟨_, hM⟩ ≪≫
      V.mapIso pe ≪≫ tensorComparison A S K P ≪≫ (T.obj (V.obj K)).mapIso e.symm
  have hs := coefficientFirstCompactSupportSpecializedSquare A N hA S d F K
    hW hM pe hpe e he
  refine ⟨pp, ?_, ?_⟩
  · exact heq_of_eq (coefficientFirstCompactSupportInverseCancellation
      ((compactSupportSiteComparison A c).app ⟨_, hM⟩) (V.mapIso pe)
      (tensorComparison A S K P) ((T.obj (V.obj K)).mapIso e.symm)
      (comparedModuleProjection A c W K) hs)
  · exact composite_iso_square ((compactSupportSiteComparison A c).app ⟨_, hM⟩)
      (V.mapIso pe) (tensorComparison A S K P) ((T.obj (V.obj K)).mapIso e.symm)

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
