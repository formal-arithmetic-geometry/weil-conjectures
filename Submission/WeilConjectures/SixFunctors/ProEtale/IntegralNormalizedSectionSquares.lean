/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentationSupplement
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Submission.WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralSectionProjectionNormalization
import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentationSupplement
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Submission.WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback
import Submission.WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquaresSupplement
import Submission.WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Submission.WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import Submission.WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Submission.WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import Submission.WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Submission.WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import Submission.WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import Submission.WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Restriction squares for a fixed normalized integral section comparison

Source: blueprint integral-criterion-reductions, final interpretation; Stacks 00YV and 03EK.
(blueprint: lem-pe-fixed-integral-section-squares).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralPresentation
attribute [local irreducible] upperStarFromPoint
  InternalAbelianSheafModule.sectionScalarMap

private def restrictComp
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{u + 1}} (f : R ⟶ S) (g : S ⟶ T) :
    SheafOfModules.restrictScalars.{u + 1} g ⋙ SheafOfModules.restrictScalars f ≅
      SheafOfModules.restrictScalars (f ≫ g) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (f.hom.app U).hom (g.hom.app U).hom
        ((f ≫ g).hom.app U).hom rfl (M.val.obj U)).symm)
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)

end AlgebraicGeometry.ProEtale.IntegralPresentation
