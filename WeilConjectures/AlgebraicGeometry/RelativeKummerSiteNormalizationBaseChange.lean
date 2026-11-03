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
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
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
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Lower-level pointwise fact for the baseChange clause.
The universal clause in the parent is obtained by introducing exactly these displayed
arguments. The comparison calculation is the unresolved proof step recorded here.
(blueprint: new-relative-kummer-site-normalization-baseChange). -/
theorem relativeKummerSiteNormalization_baseChange_fact {k : Type u} [Field k] [IsAlgClosed k]
    (ℓ N : ℕ) (_hℓ : ℓ.Prime) (_hN : 1 ≤ N) (_hℓk : IsUnit (ℓ : k))
    (A : Type (u + 1)) [CommRing A] [Algebra (ZMod (ℓ ^ N)) A]
    [Module.Finite (ZMod (ℓ ^ N)) A] [Module.Free (ZMod (ℓ ^ N)) A]
  {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
      {a : X ⟶ B} {g : B' ⟶ B} (_b : B ⟶ Spec (.of k))
      [QuasiCompact a] [QuasiSeparated a] [QuasiCompact a'] [QuasiSeparated a']
      (sq : ChosenCartesianSquare v a' a g)
      (F : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
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
          (DerivedCategory.Plus.ι.obj F))))) := by
  constructor
  · exact (discrete_exchange_site_comparison A sq F).1
  · intro hEt
    haveI : IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} A)
        sq.toCommSq).app F) := hEt
    have hαβ := (discrete_exchange_site_comparison A sq F).1
    have hs : IsIso ((comparisonUpperStar (ModuleCat.{u + 1} A) B').mapDerivedCategory.map
        ((DerivedCategory.Plus.ι (C := Sheaf B'.smallEtaleTopology
          (ModuleCat.{u + 1} A))).map
          ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} A)
            sq.toCommSq).app F))) := inferInstance
    have hmap : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A)
        sq.toCommSq).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj F))) := by
      exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
        (Arrow.isoMk'
          ((comparisonUpperStar (ModuleCat.{u + 1} A) B').mapDerivedCategory.map
            (((DerivedCategory.Plus.ι (C := Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} A))).map
              ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} A)
                sq.toCommSq).app F))))
          ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
              (DerivedCategory.Plus.ι.obj F)))
          ((baseChangeSourceComparisonIso a g A).app F)
          ((baseChangeTargetComparisonIso v a' A).app F) hαβ.symm)).1 hs
    exact hmap

end AlgebraicGeometry.ProEtale
