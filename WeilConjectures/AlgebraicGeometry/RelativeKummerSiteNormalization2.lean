/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import WeilConjectures.SmoothPurity.Sf.SfCommonStageWeilCohomology
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedImage
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantDerivedEncoding
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
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

/-- The specified comparison on higher direct images: exact comparison followed by
cohomology of the canonical counit mate. Source: Stacks 099W and 09A6
(blueprint: lem-pur-relative-kummer-site-normalization). -/
@[irreducible]
def kummerSiteHigherMap (A : Type (u + 1)) [CommRing A]
    {X B : Scheme.{u}} (a : X ⟶ B)
    (F : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (q : ℤ) :=
  (Functor.mapDerivedCategoryPlusHomologyFunctorIso
    (comparisonUpperStar (ModuleCat.{u + 1} A) B) q).hom.app
      ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) a).obj F) ≫
    (DerivedCategory.Plus.homologyFunctor _ q).map
      ((fixedComparisonDirectImageMatePlus A a).app F)

/-- Pullback of the pro-etale root line through the specified inverse-image square
and scalar extension on roots. Source: Stacks 099R and the relative Kummer proof, Step 3
(blueprint: lem-pur-relative-kummer-site-normalization). -/
@[irreducible]
def kummerSiteProCoefficient (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X T : Scheme.{u}} (f : X ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) :=
  (sheafComposeForget₂CompUpperStarIso A f).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Scheme.finiteEtaleTateLine T m A hA)) ≫
    (sheafForget₂ A X).map
      ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
          (Scheme.finiteEtaleTateLine T m A hA) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
          ((Scheme.finiteEtaleTwistPullbackData A m hm hA).c f hT hX 1).hom)

/-- Canonical pro-etale abelian cohomology pullback with the specified root-line
coefficient identification. Source: Stacks 099R and 08J6
(blueprint: lem-pur-relative-kummer-site-normalization). -/
@[irreducible]
def kummerSiteProPullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {X T : Scheme.{u}} (f : X ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hX : IsUnit (m : Γ(X, ⊤))) (q : ℕ)
    (x : Sheaf.H ((sheafForget₂ A T).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Scheme.finiteEtaleTateLine T m A hA))) q) :=
  Sheaf.H.map (kummerSiteProCoefficient A m hm hA f hT hX) q
    (Sheaf.H.mapFunctor (upperStar AddCommGrpCat.{u + 1} f)
      ((constantSheafCompUpperStarIso AddCommGrpCat.{u + 1} f).symm.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) _ q x)

/-- The integral generator on the comparison pullback of the constant module sheaf.
Source: Stacks 03FD and 099W (blueprint: lem-pur-relative-kummer-site-normalization). -/
@[irreducible]
def kummerSiteProIntegralGenerator (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (comparisonConstantSheafIso T).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
    (comparisonUpperStar AddCommGrpCat.{u + 1} T).map
      (Etale.ordinaryFiniteIntegralGenerator A T) ≫
    (sheafComposeForget₂CompComparisonUpperStarIso A T).hom.app
      (Etale.ordinaryFiniteConstant A T)

/-- Realize a pro-etale module Ext class in underlying abelian cohomology, with the
specified integral generator. Source: Stacks 03FD
(blueprint: lem-pur-relative-kummer-site-normalization). -/
@[irreducible]
def kummerSiteProExtClass (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    (x : Abelian.Ext
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Etale.ordinaryFiniteConstant A T)) F 1) :
    Sheaf.H ((sheafForget₂ A T).obj F) 1 :=
  (Abelian.Ext.mk₀ (kummerSiteProIntegralGenerator A T)).comp
    (x.mapExactFunctor (sheafForget₂ A T)) (zero_add 1)

end AlgebraicGeometry.ProEtale
