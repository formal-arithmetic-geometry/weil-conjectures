/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteModuleEquivalence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.ProperBaseChange.ConstantCompletionCore
public import WeilConjectures.CategoryTheory.ConstantRingSectionRigidity
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedEquivalenceSlices
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantCompletionInverseImageSupplement
public import WeilConjectures.ProperBaseChange.ConstantCompletionOrdinaryPullComparison
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFlatAndQuotientsQuotient
public import WeilConjectures.SmoothPurity.ConstantCompletionOrdinaryFinitePullExistence
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.QuotientTowerEvaluationComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
public import WeilConjectures.CategoryTheory.ProperBaseChange.SmallModuleDiagramsGrothendieck
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantDirectImagePreservesComplete
public import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.AdicSites.PerfectStrictReductionProjection

/-! # Invertibility of the strict projection comparison

Source: Stacks Project, Tags 0944 and 0B56; smooth-purity blueprint,
`fix-lem-exchanges`, Proof Step 4
(blueprint: lem-sp-completion-mate-projection-is-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.AdicSites

/-- Perfect quotients make the specified strict projection comparison invertible.

Source: Stacks Project, Tags 0944 and 0B56
(blueprint: lem-sp-completion-mate-projection-is-iso).

Proof: perfectStrictReductionProjection applies the perfect projection formula at
all quotient levels and uses cohomology to detect isomorphisms of strict towers.
Apply the horizontal tower pullback to this isomorphism. Its composite with the
inverse reduction/pullback comparison is the prescribed projectionComparison.
No completeness or condition on the square is needed for this clause. In particular,
the proof also covers the zero quotient and empty sites.
-/
theorem completionMateProjectionIsIso
    {Y X Y' : Site.{u}} {f : Morphism Y X} {g : Morphism Y Y'}
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (hperfect : PerfectQuotients A I) (K : X.derived A) :
    IsIso (projectionComparison (f := f) (g := g) A I K) := by
  have := perfectStrictReductionProjection f A I hperfect K
  dsimp only [projectionComparison]
  infer_instance

end CategoryTheory.AdicSites
