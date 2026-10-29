/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
public import WeilConjectures.AlgebraicGeometry.IntrinsicCompletionCompleted
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.Localization.Pi
import Mathlib.Topology.Separation.DisjointCover
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.FourCorners
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculus
import WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence
import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.RingTheory.FactorsThroughLocalization
import WeilConjectures.RingTheory.FilteredColimitOfFactorization
import WeilConjectures.SecSmoothPurity.CochainInverseComparison
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
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

attribute [irreducible] completedTowerPullback completedOrdinaryPullback

open CategoryTheory.Functor

-- Exact-presentation proof utilities from CompletedOpenExchangeTransport.
-- They are private here because that downstream module cannot be imported.
section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] constantDerivedSquare transportedSquare

end

attribute [-instance] exactTowerFiniteLimits exactTowerFiniteColimits

end AlgebraicGeometry.Scheme
