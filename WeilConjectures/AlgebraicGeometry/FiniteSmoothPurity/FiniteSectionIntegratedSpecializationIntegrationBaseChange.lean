/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteBundleSectionAdjointBaseChange

/-! # Normal-cone integration and arbitrary base change

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-purity-bc,
sk-prop-sp-purity-bc-factors.proof.md, proof (1).
(blueprint: lem-sp-finite-section-integrated-specialization-integration-factor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver Scheme.instCategory
  Scheme.Modules
  ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
attribute [local instance 20002] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
-- Use the localization instances already cached by the ordinary inverse image.
set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13
attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory
  VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  leftDerivedUpperStarComp leftDerivedUpperStarCompSectionIso
  rightDerivedLowerShriek rightDerivedUpperShriek rightDerivedUpperShriekAdjunction
  vectorBundleIntegration

end AlgebraicGeometry.Etale.FiniteSmoothPurity
