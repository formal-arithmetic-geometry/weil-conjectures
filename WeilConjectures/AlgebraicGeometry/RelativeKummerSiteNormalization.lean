/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KummerSiteAbelianEvaluation
public import WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
public import WeilConjectures.CategoryTheory.ProperBaseChange.ModuleAbelianEvaluationComparison
public import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
public import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonGlobalCohomologyFiniteNormalized
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import Mathlib.Algebra.Polynomial.Laurent
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
public import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeForgetCoefficients
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.AlgebraicGeometry.SiteComparisonEdgeSection2
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedImage
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantDerivedEncoding
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleTransportSupplement
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleInverseImageCoherence
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
public import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
public import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import WeilConjectures.CategoryTheory.SiteMorphismComposition
public import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleTransportSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleInverseImageCoherence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.CategoryTheory.DeltaFunctor
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange

import WeilConjectures.AlgebraicGeometry.KummerSiteAbelianEvaluation
import WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import WeilConjectures.CategoryTheory.ProperBaseChange.ModuleAbelianEvaluationComparison
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonGlobalCohomologyFiniteNormalized
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import Mathlib.Algebra.Polynomial.Laurent
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeForgetCoefficients
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import WeilConjectures.AlgebraicGeometry.SiteComparisonEdgeSection2
import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedImage
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantDerivedEncoding
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import WeilConjectures.AlgebraicGeometry.RelativeKummerSiteNormalizationMate
import WeilConjectures.AlgebraicGeometry.RelativeKummerSiteNormalizationBaseChange
/-! # Relative scalar Kummer classes and the normalized site comparison

Source: latest blueprint sk-prop-a1-kummer/prop-pur-gm-relative-kummer.proof.md,
opening paragraph and Step 3; Stacks Tags 03FD, 099W, 09A6 and 072W
(blueprint: lem-pur-relative-kummer-site-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale


theorem relativeKummerSiteNormalization_mate {k : Type u} [Field k] [IsAlgClosed k]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hN : 1 ≤ N) (hℓk : IsUnit (ℓ : k))
    (A : Type (u + 1)) [CommRing A] [Algebra (ZMod (ℓ ^ N)) A]
    [Module.Finite (ZMod (ℓ ^ N)) A] [Module.Free (ZMod (ℓ ^ N)) A]
  : (∀ {X B : Scheme.{u}} (a : X ⟶ B) (_b : B ⟶ Spec (.of k))
      [QuasiCompact a] [QuasiSeparated a]
      (M : DerivedCategory.Plus (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))),
  (comparisonUpperStar (ModuleCat.{u + 1} A) B).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) a).unit.app M) ≫
      (fixedComparisonDirectImageMatePlus A a).app
        ((Etale.upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategoryPlus.obj M) =
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) a).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) B).mapDerivedCategoryPlus.obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctorPlus.map
        ((fixedComparisonPullbackPlus A a).inv.app M)) := by
  exact relativeKummerSiteNormalization_mate_fact ℓ N hℓ hN hℓk A

theorem relativeKummerSiteNormalization_baseChange {k : Type u} [Field k] [IsAlgClosed k]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hN : 1 ≤ N) (hℓk : IsUnit (ℓ : k))
    (A : Type (u + 1)) [CommRing A] [Algebra (ZMod (ℓ ^ N)) A]
    [Module.Finite (ZMod (ℓ ^ N)) A] [Module.Free (ZMod (ℓ ^ N)) A]
  : (∀ {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
      {a : X ⟶ B} {g : B' ⟶ B} (_b : B ⟶ Spec (.of k))
      [QuasiCompact a] [QuasiSeparated a] [QuasiCompact a'] [QuasiSeparated a']
      (sq : ChosenCartesianSquare v a' a g)
      (F : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
  (((comparisonUpperStar (ModuleCat.{u + 1} A) B').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq).app F)) ≫
      (baseChangeTargetComparisonIso v a' A).hom.app F =
        (baseChangeSourceComparisonIso a g A).hom.app F ≫
          (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
              (DerivedCategory.Plus.ι.obj F))) ∧
    (IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq).app F) →
      IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj F)))))) := by
  exact relativeKummerSiteNormalization_baseChange_fact ℓ N hℓ hN hℓk A

end AlgebraicGeometry.ProEtale
