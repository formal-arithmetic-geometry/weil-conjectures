/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
public import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
public import Submission.WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison
public import Submission.WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import Submission.WeilConjectures.Compactification.Refinement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Submission.WeilConjectures.Algebra.Homology.HomComplexComponents
import Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Submission.WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Submission.WeilConjectures.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase
import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import Submission.WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import Submission.WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Submission.WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import Submission.WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.WeilConjectures.SixFunctors.Etale.Derived.HeartGluing
import Submission.WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import Submission.WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction
import Submission.WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Coherence of normalized etale sum right adjoints

proof.md, Step 1; Stacks Tags 03S6, 0F7J, 0F7K
(auxiliary; not a blueprint node).

The comparisons below use the actual proper/open compositor and exchange. The map to sum
extension is the constructed graph comparison, rather than a choice of a bare isomorphism.
Right adjoints and their adjunctions are quantified, so no choice of Brown adjoint is imposed.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso
  unboundedEtaleCompactSupportBaseChange exactEtaleSumExchange

/-- The specified compact-support-to-sum identification for the chosen compactification.
Source: Stacks Tags 0F4L, 0F7J, and the blueprint Step 1
(auxiliary; not a blueprint node). -/
noncomputable def etaleSumSupportIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  (rightDerivedLowerShriekIso A (HasCompactification.compactification e)).symm ≪≫
    canonicalEtaleCompactSupportComparison A e (HasCompactification.compactification e)

/-- The normalization rho is the adjunction conjugate of the inverse specified comparison.
Source: blueprint Step 1; Stacks Tags 0037 and 03S6
(auxiliary; not a blueprint node). -/
noncomputable def etaleSumRightAdjointIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e]
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G) :
    G ≅ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory :=
  conjugateIsoEquiv adj
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
    (etaleSumSupportIso A e).symm

/-- The canonical pullback identification of the coefficient unit, in the exact derived model.
Source: blueprint Step 1, pullback-unit identification
(auxiliary; not a blueprint node). -/
noncomputable def etaleSumPullbackUnitIso
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (e : U ⟶ X) :
    (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj (constantComplex A X) ≅
      constantComplex A U :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm.app
      (constantComplex A X) ≪≫
    leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) e

end AlgebraicGeometry.Etale
