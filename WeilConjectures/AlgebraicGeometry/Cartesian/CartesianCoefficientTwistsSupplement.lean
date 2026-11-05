/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChange
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import all WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorSquare
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying

import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTateTowerLimit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteScalarRestrictionConstructible
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.CategoryTheory.TorsionSheafConstantModule
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Module.ZMod
import all WeilConjectures.AlgebraicGeometry.Tate.TateInverseLimitBaseChangeSupplement
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwists

/-! # Cartesian coefficients and Tate twists

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`sk-prop-sfb-cartesian-coefficients-twists.md`
(blueprint: det-prop-sfb-cartesian-coefficients-twists).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u u₁ v₁ u₂ v₂ uI vI uJ vJ

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj ChangeOfRings

section ModuleComparisons

universe w₁ vM₁ w₂ vM₂
variable {C : Type w₁} [Category.{vM₁} C] [MonoidalCategory C]
  {D : Type w₂} [Category.{vM₂} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] (R : C) [MonObj R]

open CategoryTheory.Limits

attribute [local irreducible] inverseSemilinear

end ModuleComparisons

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory

-- Keep the scalar-extension object abstract; its coequalizer equations are the API.
attribute [local irreducible] Mod.extendScalarsObj Mod.extendScalarsIsoComapInv
  AlgebraicGeometry.ProEtale.CondensedRing.pullIso

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

-- Fixed-universe presentations cache the categorical instance arguments.

-- Cache these propositional instances: reconstructing the internal-module limit
-- through its condensed coefficient presentation is expensive at each projection.
-- Cache the sheafification proofs used throughout the section.

attribute [local irreducible] abelianPullbackForgetIso ringPullbackForgetIso
  noncommPullbackForgetIso
  condensedPushforwardHom

attribute [local irreducible] spCoefficientIso

attribute [local irreducible] integralComparisonSystem

attribute [local irreducible] profinitePointModuleForgetPullbackIso

attribute [local irreducible] spIntegralComparison

attribute [local irreducible] spTwistFunctor

section SignedComparisonStatement
attribute [local irreducible] Scheme.proEtaleRingModulePullback
  Scheme.proEtaleRingModuleAdjunction

end SignedComparisonStatement

section SignedPullbackProof

attribute [local irreducible] Scheme.proEtaleModuleInverseImage
  Scheme.proEtaleRingModuleAdjunction Scheme.proEtaleRingModulePullback
  SheafOfModules.siteSheafTensorRight

attribute [local irreducible] moduleStructuralMap modulePullbackComparison

end SignedPullbackProof

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
attribute [local irreducible] Scheme.proEtaleModuleInverseImage

end

section

variable (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
include T
include hN

end

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable
    (RY SY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (RX SX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (cR : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cS : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (pY : RY ⟶ SY) (pX : RX ⟶ SX)
    (hsq : pY ≫ Scheme.proEtaleRingDirectImageMap f SY SX cS =
      Scheme.proEtaleRingDirectImageMap f RY RX cR ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map pX)

attribute [local irreducible] tensorPullbackHomEquiv' directScalarIso'

attribute [local irreducible] tensorMap'

end

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

attribute [local irreducible] finiteFirstComparison rootModuleComparison
  rootModuleDirect tensorMap' directScalarIso' tensorPullbackHomEquiv'

section

end

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] spIntegersMap spEllMap spIntegralTwistMap
  spRationalTwistMap

end

attribute [local irreducible] spRationalTwistMap spIntegralTwistMap spEllMap
  spIntegersMap
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section
variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CondensedRing.upperStarLowerStarAdjunction
  InternalModuleOperations.lowerComparison InternalModuleOperations.coefficientMap

end

attribute [local irreducible] SpInternalCartesian

-- Keep the native inverse-limit construction abstract when applying scalar extension.
attribute [local irreducible] spIntegralTwist

-- Use only the comparison APIs for these module objects below.
set_option backward.defeqAttrib.useBackward false

attribute [local irreducible] InternalAbelianSheafModule.sectionModuleEquivalence
  InternalAbelianSheafModule.sectionRingSheaf
  Scheme.proEtaleRingModulePullback Scheme.proEtaleRingModuleAdjunction

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end AlgebraicGeometry.ProEtale
