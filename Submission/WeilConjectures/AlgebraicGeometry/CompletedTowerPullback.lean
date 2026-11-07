/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
public import Submission.WeilConjectures.AlgebraicGeometry.IntrinsicCompletionCompleted
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.Localization.Pi
import Mathlib.Topology.Separation.DisjointCover
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import Submission.WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import Submission.WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Submission.WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Submission.WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Submission.WeilConjectures.AlgebraicGeometry.FourCorners
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Submission.WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Submission.WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Submission.WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
import Submission.WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculus
import Submission.WeilConjectures.AlgebraicGeometry.StrictTowerOperations
import Submission.WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.ExactDerivedAdjunction
import Submission.WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Submission.WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import Submission.WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import Submission.WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import Submission.WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import Submission.WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import Submission.WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import Submission.WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses
import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import Submission.WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence
import Submission.WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivation
import Submission.WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import Submission.WeilConjectures.RingTheory.FactorsThroughLocalization
import Submission.WeilConjectures.RingTheory.FilteredColimitOfFactorization
import Submission.WeilConjectures.SecSmoothPurity.CochainInverseComparison
import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import Submission.WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-!
# Pullback of strict completed-coefficient towers

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1261;
Stacks Project, Tag 099N (blueprint: def-weil-pbc-completed-pullback).

The structure map into the completed coefficient ring is built from its finite
projections. It is a morphism, with no invertibility assumption. The functor here
precedes derived inverse limit and acts on every strict derived tower.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Functor

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

/-- The finite coefficient identification transported by the published constant comparison.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners). -/
noncomputable def AdicCoefficientDatum.finiteRingIso {U V : Scheme.{u}} (f : U ⟶ V)
    (n : ℕ) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj (d.finiteRing V n) ≅
      d.finiteRing U n :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso
      (pbcLevelConstantComparison V d n).symm ≪≫
    @asIso _ _ _ _ ((proEtaleConstantComparison f).app (d.ringTower.obj (op n)))
      (by exact exchangeConstantComparison_isIso f (A ⧸ d.ideal ^ (n + 1))) ≪≫
    pbcLevelConstantComparison U d n

/-- The finite coefficient comparisons retain every quotient transition.
Source: blueprint four corners; Stacks 098T (blueprint: def-weil-pbc-four-corners).
Proof: the published constants-to-functions comparison commutes with quotient maps.
The constant inverse-image comparison is natural in the finite coefficient ring.
Combining their naturality squares with the limit cone equations gives this equation. -/
theorem AdicCoefficientDatum.integralRingComponent_naturality {U V : Scheme.{u}}
    (f : U ⟶ V) {m n : ℕᵒᵖ} (a : m ⟶ n) :
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (d.projection V m.unop) ≫
        (d.finiteRingIso f m.unop).hom ≫ (reductionCoefficientSystem U d).map a =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (d.projection V n.unop) ≫
        (d.finiteRingIso f n.unop).hom := by
  let eU := pbcConstantSystemComparison U d
  let eV := pbcConstantSystemComparison V d
  let t : adicLisseRingSystem V d.ideal ⋙
      proEtaleSheafInverseImage f CommRingCat.{u + 1} ⟶
      adicLisseRingSystem U d.ideal :=
    NatTrans.ofOpSequence (fun k ↦ (proEtaleConstantComparison f).app
      (CommRingCat.of (A ⧸ d.ideal ^ (k + 1)))) (by
        intro k
        simpa only [Functor.comp_map, adicLisseRingSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
          (proEtaleConstantComparison f).naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (k + 1))))
  have hn := congrArg (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
    (eV.inv.naturality a)
  have ht := t.naturality a
  have hu := eU.hom.naturality a
  simp only [Functor.map_comp] at hn
  change (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      ((reductionCoefficientSystem V d).map a) ≫
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (pbcLevelConstantComparison V d n.unop).inv =
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      (pbcLevelConstantComparison V d m.unop).inv ≫
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          ((adicLisseRingSystem V d.ideal).map a) at hn
  change (adicLisseRingSystem V d.ideal ⋙
    proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a ≫
      (proEtaleConstantComparison f).app (d.ringTower.obj n) =
    (proEtaleConstantComparison f).app (d.ringTower.obj m) ≫
      (adicLisseRingSystem U d.ideal).map a at ht
  change (adicLisseRingSystem U d.ideal).map a ≫
      (pbcLevelConstantComparison U d n.unop).hom =
    (pbcLevelConstantComparison U d m.unop).hom ≫
      (reductionCoefficientSystem U d).map a at hu
  dsimp only [finiteRingIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    asIso_hom]
  simp only [Category.assoc]
  rw [← hu, ← Category.assoc _ _ ((pbcLevelConstantComparison U d n.unop).hom)]
  rw [← ht]
  simp only [Functor.comp_map, Category.assoc]
  rw [← reassoc_of% hn]
  simp only [← Functor.map_comp_assoc]
  simp only [AdicCoefficientDatum.projection, completedReductionProjection,
    ← Category.assoc, limit.w]

/-- Finite coefficient comparison obtained from constant sections, with its fixed
constant-section normalization. Source: blueprint order 1261
(blueprint: def-weil-pbc-completed-pullback). -/
def completedFiniteCoefficientMap (n : ℕ) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        ((pbcAdicRings Y d).obj (op n)) ⟶ (pbcAdicRings X d).obj (op n) :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (pbcLevelConstantComparison Y d n).inv ≫
    proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
      (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) ≫
    (pbcLevelConstantComparison X d n).hom

/-- The components of the completed coefficient structure map.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedCoefficientComponent (n : ℕ) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ⟶
      (pbcAdicRings X d).obj (op n) :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (pbcAdicProjection Y d n) ≫
    completedFiniteCoefficientMap g d n

/-- The coefficient components form a limit cone.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback).
Proof: the completion projections commute with quotient maps. The finite coefficient
comparison is induced by constant sections, so is natural in the quotient homomorphism.
Apply inverse-image functoriality and these two equalities. -/
theorem completedCoefficientComponent_naturality {b a : ℕᵒᵖ} (f : b ⟶ a) :
    completedCoefficientComponent g d b.unop ≫ (pbcAdicRings X d).map f =
      completedCoefficientComponent g d a.unop := by
  exact d.integralRingComponent_naturality g f

/-- The canonical coefficient structure map into the actual completed limit.
Source: blueprint order 1261 (blueprint: def-weil-pbc-completed-pullback). -/
def completedCoefficientMap :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d) ⟶
      pbcAdicCompletion X d :=
  limit.lift (pbcAdicRings X d)
    { pt := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (pbcAdicCompletion Y d)
      π := { app n := completedCoefficientComponent g d n.unop
             naturality _ _ f := (Category.id_comp _).trans
               (completedCoefficientComponent_naturality g d f).symm } }

open CategoryTheory.Functor

-- Exact-presentation proof utilities from CompletedOpenExchangeTransport.
-- They are private here because that downstream module cannot be imported.
section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private instance exactTowerFiniteLimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

private instance exactTowerFiniteColimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

end

attribute [-instance] exactTowerFiniteLimits exactTowerFiniteColimits

end AlgebraicGeometry.Scheme
