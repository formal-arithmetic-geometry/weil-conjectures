/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionTower
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCompletionReduction
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CompletionMap
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
import WeilConjectures.CategoryTheory.AdicSites.SmallSiteReducedCompletionUnit
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.Algebra.Homology.Ringed.RingedSiteEquivalenceTensor
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenFlatResolution
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionModel
import all WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionModel

/-!
# Strict reduction of completed extension by zero

Source: blueprint fix-lem-exchanges, integral open factor, Steps 1–2;
Stacks Project Tags 099M, 099N and 0941
(blueprint: lem-sf-cbc-extension-zero-completion).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
universe t
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] sfCbcConstantSliceIso constantSheaf
  sfCbcModelModules sfCbcModelRingMap sfCbcModelDerived
  SheafOfModules.monoidalCategory
  sfCbcOpenExtension sfCbcExtensionModel
attribute [-instance] sfCbcTensorTotal sfCbcSliceTransport_additive

/-- Ordinary tensor projection comparison, as one isomorphism of strict quotient diagrams.
Its equation fixes the map by the actual quotient units, not just its endpoints.
Source: Stacks Tag 0E8I; Step 2 of the node.
Proof: use the ringed-slice tensor projection formula on every quotient.
Both unit composites send m to the extension of 1 tensor m. Quotient units
are epimorphisms, so this equation determines each component uniquely.
Naturality of tensor in the quotient coefficient makes the components commute
with every quotient transition, giving the isomorphism of strict diagrams.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcOrdinaryTensorComparison_existsUnique {U X : Scheme.{t}}
    (j : U ⟶ X) [IsOpenImmersion j] {A : Type t} [CommRing A]
    (d : CompleteCoefficientDatum A) :
    ∃! e : sfCbcModelExtension j A ⋙
        ConstantCompletion.reductionTower (proEtaleModelTopology X)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false ≅
      ConstantCompletion.reductionTower (proEtaleModelTopology U)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false ⋙ sfCbcTowerExtension j A,
      ∀ (M : ConstantCompletion.Mod (sfCbcModelRing U A)) (n : ℕ),
        ((ConstantCompletion.reductionUnit (proEtaleModelTopology X)
            (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).app
              ((sfCbcModelExtension j A).obj M)).app (op n) ≫
            (e.hom.app M).app (op n) =
          (sfCbcModelExtension j A).map
            (((ConstantCompletion.reductionUnit (proEtaleModelTopology U)
              (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).app M).app (op n)) := by
  sorry

/-- The unique strict ordinary tensor comparison with the quotient-unit normalization.
Source: Stacks Tag 0E8I (blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcOrdinaryTensorComparison {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :=
  (sfCbcOrdinaryTensorComparison_existsUnique j d).exists.choose

attribute [local semireducible] sfCbcModelDerived

/-- Canonical transport of the exact derived extension functor.
Source: Stacks Tags 00VC and 05RU
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcExtensionTransport {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : Type t) [CommRing A] :
    sfCbcDerivedExtension j A ⋙ (sfCbcModelDerived X A).functor ≅
      (sfCbcModelDerived U A).functor ⋙ sfCbcModelDerivedExtension j A :=
  (Functor.mapDerivedCategoryCompIso (sfCbcOpenExtension j A)
      (sfCbcModelModules X A)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (isoWhiskerRight (sfCbcModelModules U A).asEquivalence.unitIso
        (sfCbcOpenExtension j A ⋙ sfCbcModelModules X A)) ≪≫
    Functor.mapDerivedCategoryCompIso (sfCbcModelModules U A) (sfCbcModelExtension j A)

attribute [local irreducible] sfCbcModelDerived

attribute [local irreducible] sfCbcExtensionTransport sfCbcOrdinaryTensorComparison
  ConstantCompletion.quotientPresentation sfCbcModelExtension
  NatIso.mapHomologicalComplex Functor.mapHomologicalComplexCompIso
  ConstantCompletion.reductionUnit
  ConstantCompletion.reductionTower
  sfCbcModelDerivedFactors sfCbcModelExtensionFactors sfCbcTowerExtensionFactors

/-- Normalization of the derived tensor comparison on every flat-term K-flat complex.
Both sides use the universal quotient counits and the ordinary tensor comparison.
Source: Stacks Tag 06YY; Step 2 of the node
(blueprint: lem-sf-cbc-extension-zero-completion). -/
def sfCbcTensorComparisonNormalized {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    (e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
      (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A) : Prop := by
  letI := ConstantCompletion.reductionTower_additive (proEtaleModelTopology X)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  letI := ConstantCompletion.reductionTower_additive (proEtaleModelTopology U)
    (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false
  let c : (sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ) ⋙
      (ConstantCompletion.reductionTower (proEtaleModelTopology X)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).mapHomologicalComplex (.up ℤ) ≅
      (ConstantCompletion.reductionTower (proEtaleModelTopology U)
        (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false).mapHomologicalComplex (.up ℤ) ⋙
          (sfCbcTowerExtension j A).mapHomologicalComplex (.up ℤ) :=
    Functor.mapHomologicalComplexCompIso
      (sfCbcOrdinaryTensorComparison j d) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (F := ConstantCompletion.reductionTower (proEtaleModelTopology U)
          (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false)
        (G := sfCbcTowerExtension j A) (Iso.refl _) (.up ℤ)).symm
  exact ∀ P : ConstantCompletion.Cx (sfCbcModelRing U A), P.IsAcyclicTensorKFlat →
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) →
      HEq (e.hom.app ((ConstantCompletion.Q (sfCbcModelRing U A)).obj P) ≫
          (sfCbcDerivedTowerExtension j A).map
            ((sfCbcQuotientPresentation U d).comparison.app P) ≫
          (sfCbcTowerExtensionFactors j A).hom.app
            (ConstantCompletion.reductionComplex (proEtaleModelTopology U)
              (ULift.{t + 1, t} A) (sfCbcModelIdeal d) false P))
        ((sfCbcQuotientPresentation X d).tower.map
            ((sfCbcModelExtensionFactors j A).hom.app P) ≫
          (sfCbcQuotientPresentation X d).comparison.app
            (((sfCbcModelExtension j A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (ConstantCompletion.TQ (sfCbcModelRing X A)).map
            (c.hom.app P))

/-- The tensor projection comparison descends uniquely to derived strict towers.
Source: Stacks Tags 06YY, 0E8I and 0941; Steps 1–2 of the node.
Proof: extension preserves flat K-flat complexes by Step 1. The ordinary
comparison is a strict quotient-diagram isomorphism. Apply it degreewise on
one such complex and localize in the tower category. The universal quotient
counits give the displayed formula. All complexes have flat K-flat resolutions;
localization at quasi-isomorphisms therefore extends the comparison uniquely,
naturally in the input, and preserves its inverse.
(blueprint: lem-sf-cbc-extension-zero-completion). -/
theorem sfCbcTensorComparison_existsUnique {U X : Scheme.{t}} (j : U ⟶ X)
    [IsOpenImmersion j] {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A) :
    ∃! e : sfCbcModelDerivedExtension j A ⋙ (sfCbcQuotientPresentation X d).tower ≅
      (sfCbcQuotientPresentation U d).tower ⋙ sfCbcDerivedTowerExtension j A,
      sfCbcTensorComparisonNormalized j d e := by
  sorry

attribute [local instance 1000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

attribute [local semireducible] sfCbcOpenExtension

open Classical in
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

attribute [local irreducible] sfCbcOpenExtension

attribute [local irreducible] sfCbcDerivedRestrictExtensionIso

attribute [local irreducible] adicReductionHomEquiv

attribute [local irreducible] adicDerivedRestrictFactors
  adicCompletionEvaluation
  adicDerivedRestrict

attribute [local irreducible] adicReductionDerivedUnit

attribute [local irreducible] sfCbcFiniteCompletedHom sfCbcFiniteTensorHom

attribute [local irreducible] sfCbcEvaluateFactors

set_option backward.isDefEq.respectTransparency true in
attribute [local irreducible] sfCbcFiniteModelFactors

attribute [local instance 1000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

end AlgebraicGeometry.Scheme
