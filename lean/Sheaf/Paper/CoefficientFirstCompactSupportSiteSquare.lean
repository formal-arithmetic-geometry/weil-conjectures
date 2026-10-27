/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Paper.VectorTensorSiteEquations

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

attribute [local instance high] CategoryTheory.SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local implicit_reducible] Scheme.Modules
  Etale.vectorBundlePurityLower Etale.vectorBundlePurityCompactification
  Etale.vectorIntegrationSource
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  Etale.derivedTensorSymmetry
  Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso
  Etale.derivedTensor derivedTensor
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Etale.projectionMapOfCompactification projectionMapOfCompactification
  derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso compactSupportSiteComparison

/-- Inverting the coefficient-first compact-support square gives the actual pro-etale
projection inverse and its comparison equation. Source: Stacks 099R, 0944, 0GL1 and the
proper/open projection calculation in lem-pur-projection-comparison-etale-origin.
(blueprint: lem-pur-coefficient-first-compact-support-site-square).

Proof: write W for the vector coefficient, f for the vector projection and c for its
fixed compactification. Boundedness in the opposite tensor order follows from hM by
signed symmetry. Apply compact_projection_square at W and K. Its comparison at W tensor pullback K
is the inverse proper counit mate followed by the proper direct image of the exact
open-extension comparison. By compact_comparison_inv_mate this is a natural transformation
on the unbounded derived category. Apply naturality to symmetry from W tensor pullback K
to pullback K tensor W. The derived tensor comparison commutes with symmetry on both
sites, by comparisonTensor_braiding. Naturality of pro-etale symmetry moves the pullback
comparison to the first factor and moves the inverse comparison at W across symmetry.
Pasting these squares gives the coefficient-first compact-support square. The tensor/
pullback comparison is tensorComparison followed by tensor of pullback, and pullback
equals comparisonOpenDerivedPullbackIso by supportComparison_eq.

Define pp as the compact-support comparison at pullback K tensor W, followed by C(pe),
tensorComparison at K and ordinary compact support of W, and tensor(CK) of e inverse.
Every factor is a specified isomorphism. Cancelling inverse pairs gives the displayed
projection square. Substitute hpe in the coefficient-first square, postcompose with the
compact-support image of the inverse tensor/pullback comparison, and cancel the tensor
comparison followed by tensor(CK) of e inverse. This identifies pp inverse with the actual
comparedModuleProjection, not merely with an unspecified isomorphism. Boundedness of these three
objects places the comparison components in their domains. No integration or adjunction
is involved. The geometry is the fixed vector compactification. Zero objects and
the empty scheme obey exactly the same cancellation equations.
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
            (Etale.vectorBundlePurityCompactification S d F)).inv.app ⟨_, hM⟩ := by sorry

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
