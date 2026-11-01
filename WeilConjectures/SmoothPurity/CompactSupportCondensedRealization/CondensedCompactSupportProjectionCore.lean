/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientComparisons
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperIntegralRationalScalarComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenCoefficientSquareActionIdentification
import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedOpenRestrictedCounit
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

import all WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus

/-! # Condensed compact-support projection constructions

Source: blueprint sk-thm-purity-transport, Steps 2--3; the compact-support
realization prerequisite, proof Steps 6--17 (agent-formulated constructions).
(blueprint: def-pur-condensed-compact-support-projection-core). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.privateModule false
set_option linter.unusedSimpArgs false
set_option genSizeOf false
set_option genInjectivity false
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

/-- The existing Abelian structure of the fixed pro-etale sheaf category.
Source: CategoryTheory.sheafIsAbelian, with its original sheafification adjunction.
(blueprint: def-pur-condensed-compact-support-projection). -/
@[instance_reducible]
def fieldSheafAbelian (X : Scheme.{u}) :
    Abelian (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  sheafIsAbelian

attribute [local instance] fieldSheafAbelian

/-- The existing Grothendieck abelian property of the fixed pro-etale sheaf category.
Source: the Grothendieck abelian sheaf instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldSheafGrothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (ProEt.topology X) Ab.{u + 1}) := by
  infer_instance

attribute [local instance] fieldSheafGrothendieck

/-- The large colimits used by the fixed pro-etale sheaf category.
Source: the existing Grothendieck abelian sheaf instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldSheafBigColimits (X : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1} (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  IsGrothendieckAbelian.hasColimits _

attribute [local instance] fieldSheafBigColimits

/-- The coequalizers used by the fixed pro-etale sheaf category.
Source: the existing sheaf colimit instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldSheafCoequalizers (X : Scheme.{u}) :
    HasCoequalizers (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  Sheaf.instHasColimitsOfShape

attribute [local instance] fieldSheafCoequalizers

/-- Additivity of the fixed sheaf tensor product.
Source: the existing monoidal preadditive sheaf instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldSheafMonoidalPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive (Sheaf (ProEt.topology X) Ab.{u + 1}) := by
  infer_instance

attribute [local instance] fieldSheafMonoidalPreadditive

/-- The existing Abelian module structure with its fixed sheaf category named.
Source: Mod.instAbelian; its constructor and all selected data are unchanged.
(blueprint: def-pur-condensed-compact-support-projection). -/
@[instance_reducible]
def fieldModuleAbelian (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    Abelian (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  inferInstance

attribute [local instance] fieldModuleAbelian

/-- Internal modules over a monoid in this sheaf category are Grothendieck abelian.
Source: Mod.isGrothendieckAbelian; tensoring in the base preserves colimits.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleGrothendieck (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    IsGrothendieckAbelian.{u + 1}
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  Mod.isGrothendieckAbelian.{u + 1} R

attribute [local instance] fieldModuleGrothendieck

/-- Internal modules admit the existing K-injective resolutions of a Grothendieck category.
Source: the Grothendieck abelian K-injective-resolution instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleKInjectiveResolutions (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    CategoryTheory.Abelian.HasKInjectiveResolutions
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) := by
  infer_instance

attribute [local instance] fieldModuleKInjectiveResolutions

/-- The existing derived category of internal modules, with the sheaf site fixed.
Source: HasDerivedCategory.ofIsGrothendieckAbelian. This names exactly its
K-injective-resolution construction, with the original universe of morphisms.
(blueprint: def-pur-condensed-compact-support-projection). -/
@[instance_reducible]
def fieldModuleDerivedCategory (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    HasDerivedCategory.{u + 1} (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

attribute [local instance] fieldModuleDerivedCategory

/-- The existing small colimits of internal modules on the fixed sheaf site.
Source: module-object colimits are created by the forgetful functor.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleColimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    HasColimitsOfSize.{0, 0} (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  ⟨fun _ _ ↦ inferInstance⟩

attribute [local instance] fieldModuleColimits

/-- The existing large colimits of internal modules on the fixed sheaf site.
Source: the Grothendieck abelian module property.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleBigColimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  IsGrothendieckAbelian.hasColimits _

attribute [local instance] fieldModuleBigColimits

/-- The existing functorial flat resolutions on the fixed pro-etale sheaf category.
Source: ProEtale.hasFunctorialFlatResolution_sheaf.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldSheafFlatResolution (X : Scheme.{u}) :
    CategoryTheory.Abelian.HasFunctorialFlatResolution
      (Sheaf (ProEt.topology X) Ab.{u + 1}) := by
  infer_instance

attribute [local instance] fieldSheafFlatResolution

/-- The existing functorial flat resolutions of internal modules over a condensed ring.
Source: the existing module-object functorial flat-resolution instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleFlatResolution (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    CategoryTheory.Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) := by
  infer_instance

attribute [local instance] fieldModuleFlatResolution

/-- The countable coproducts used by the module K-flat derivability structure.
Source: the existing internal-module colimit instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleCountableCoproducts (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    HasCountableCoproducts (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) := by
  infer_instance

attribute [local instance] fieldModuleCountableCoproducts

/-- The integer colimits used by module K-flat derivation.
Source: the existing internal-module colimit instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleIntegerColimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    HasColimitsOfShape ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) := by
  infer_instance

attribute [local instance] fieldModuleIntegerColimits

/-- Exactness of the integer colimits used by module K-flat derivation.
Source: the existing exact-colimit instance for Grothendieck module categories.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleIntegerExactColimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    HasExactColimitsOfShape ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) := by
  infer_instance

attribute [local instance] fieldModuleIntegerExactColimits

/-- Left tensor preserves the integer colimits used by K-flat derivation.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldTensorColimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ ((curriedTensor _).obj M) := by
  intro M
  infer_instance

attribute [local instance] fieldTensorColimits

/-- Right tensor preserves the integer colimits used by K-flat derivation.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldTensorColimitsRight (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj M) := by
  intro M
  infer_instance

attribute [local instance] fieldTensorColimitsRight

-- Cache the graded tensor colimit instances used by each K-flat derived functor.
/-- The existing tensor has every graded binary coproduct.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldGradedTensor (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A B : GradedObject ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)) :
    A.HasTensor B := by
  intro n
  infer_instance

attribute [local instance] fieldGradedTensor

/-- Left tensor preserves the graded triple coproduct.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldGradedFour (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A B C D : GradedObject ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)) :
    GradedObject.HasTensor₄ObjExt A B C D := by
  intro i j
  infer_instance

attribute [local instance] fieldGradedFour

/-- Right tensor preserves the graded binary coproduct.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldGradedLeft (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A B C : GradedObject ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := by
  intro i j
  infer_instance

attribute [local instance] fieldGradedLeft

/-- Left tensor preserves the graded binary coproduct.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldGradedRight (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A B C : GradedObject ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := by
  intro i j
  infer_instance

attribute [local instance] fieldGradedRight

/-- Scalar extension has the existing K-flat quasi-isomorphism preservation property.
Source: Mod.preservesKFlatQuasiIso, proved by tensoring a K-flat acyclic cone.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldExtendScalarsKFlat (X : Scheme.{u})
    (R S : Sheaf (ProEt.topology X) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    (Mod.extendScalars φ).PreservesKFlatQuasiIso := by
  infer_instance

attribute [local instance] fieldExtendScalarsKFlat

namespace WeilConjectures.CompactSupportCondensedRealization

universe a av b bv d dv e ev h hv z zv

/-- Pasting the proper coefficient mate with the open coefficient square.
Source: blueprint proof Step 6; archived ChangeOfCoefficients.lean
(blueprint: def-pur-condensed-compact-support-projection). -/
def pasteScalar {C : Type a} {D : Type b} {H : Type d}
    {C' : Type e} {D' : Type h} {H' : Type z}
    [Category.{av} C] [Category.{bv} D] [Category.{dv} H]
    [Category.{ev} C'] [Category.{hv} D'] [Category.{zv} H']
    (j : C ⥤ D) (r : D ⥤ H) (j' : C' ⥤ D') (r' : D' ⥤ H')
    (tx : C ⥤ C') (tz : D ⥤ D') (ty : H ⥤ H')
    (p : r ⋙ ty ⟶ tz ⋙ r') (q : j ⋙ tz ⟶ tx ⋙ j') :
    (j ⋙ r) ⋙ ty ⟶ tx ⋙ (j' ⋙ r') :=
  (Functor.associator j r ty).hom ≫ Functor.whiskerLeft j p ≫
    (Functor.associator j tz r').inv ≫ Functor.whiskerRight q r' ≫
      (Functor.associator tx j' r').hom

/-- Shorthand for the existing sectionwise finite-limit preservation instances.
Source: blueprint proof Steps 6 and 13; archived coefficient-change hypotheses
(blueprint: def-pur-condensed-compact-support-projection). -/
abbrev FlatCoefficientMap
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] : Prop :=
  ∀ W : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a W))

section CoefficientCompositionHelpers
set_option backward.defeqAttrib.useBackward false
end CoefficientCompositionHelpers

section Projection
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [FlatCoefficientMap a]

/-- The actual small-Hom-universe derived extension of condensed coefficients.
Source: blueprint proof Steps 6 and 13
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedScalar (W : Scheme.{u}) :
    DerivedCategory
        (Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) ⥤
      DerivedCategory
        (Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ' W)) :=
  (Mod.extendScalars (coefficientMap a W)).leftDerivedFunctor

/-- The original scalar/restriction adjunction with its canonical scalar functors named.
Source: the existing derived extension/restriction adjunction; blueprint Step 17.
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedScalarAdjunction (W : Scheme.{u}) :
    condensedScalar a W ⊣ (Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
      (coefficientMap a W)).mapDerivedCategory :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a W)

attribute [local irreducible] condensedScalarAdjunction condensedScalar

/-- The tensor shift is induced by the exact restriction-of-scalars adjunction.
Source: blueprint proof Step 17; the canonical derived tensor adjunction
(blueprint: def-pur-condensed-compact-support-projection). -/
instance condensedScalarShift (W : Scheme.{u}) : (condensedScalar a W).CommShift ℤ :=
  (condensedScalarAdjunction a W).leftAdjointCommShift ℤ

/-- The archived proper coefficient comparison with its canonical scalar functors named.
Source: CondensedRing.derivedPushHom, the proper adjunction mate.
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedPushScalar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙ condensedScalar a Y ⟶
      condensedScalar a X ⋙ (CondensedRing.lowerStar Λ' f).rightDerivedFunctor :=
  Adjunction.pushHomOfComapIso
    (condensedScalarAdjunction a X) (condensedScalarAdjunction a Y)
    (CondensedRing.derivedComapLowerStarIso a f)

/-- The archived open coefficient comparison with its canonical scalar functors named.
Source: CondensedRing.derivedOpenImmersionShriekIso, the open adjunction mate.
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedOpenScalar {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        condensedScalar a Z ≅
      condensedScalar a X ⋙
        (CondensedRing.openImmersionLowerShriek Λ' j).mapDerivedCategory :=
  (conjugateIsoEquiv
    ((condensedScalarAdjunction a X).comp
      (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j))
    ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (condensedScalarAdjunction a Z))).symm
    (CondensedRing.derivedComapUpperStarIso a j)

private theorem scalarPush_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    condensedPushScalar a f = Adjunction.pushHomOfComapIso
      (condensedScalarAdjunction a X) (condensedScalarAdjunction a Y)
      (CondensedRing.derivedComapLowerStarIso a f) := by
  unfold condensedPushScalar
  rfl

omit [FlatCoefficientMap a] in
omit [FlatCoefficientMap a] in
attribute [local irreducible] condensedPushScalar condensedOpenScalar

/-- The canonical coefficient projection for a fixed compactification, in proper-then-open
order, exactly as in the archived condensed module-object construction.
Source: archived ChangeOfCoefficients.lean, derivedLowerShriekHom; blueprint proof Step 6
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification Λ c ⋙
        (condensedScalar a Y) ⟶
      (condensedScalar a X) ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ' c :=
  pasteScalar
    (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
    (CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ' c.g).rightDerivedFunctor
    (condensedScalar a X) (condensedScalar a c.Z) (condensedScalar a Y)
    (condensedPushScalar a c.g)
    (condensedOpenScalar a c.i).hom

/-- The inherited shift of the archived proper/open support composite.
Source: blueprint proof Step 17; archived derived open and proper operations
(blueprint: def-pur-condensed-compact-support-projection). -/
instance condensedSupportShift
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ₀ c).CommShift ℤ :=
  inferInstance

variable {Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ''] [IsCommMonObj Λ''] (b : Λ' ⟶ Λ'') [IsMonHom b]
  [FlatCoefficientMap b]
  [FlatCoefficientMap (a ≫ b)]

/-- Tensor transitivity is uniquely induced by the actual restriction compositor.
Source: blueprint proof Steps 9 and 13; Stacks 06YY
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedScalarComp (W : Scheme.{u}) :
    condensedScalar a W ⋙ condensedScalar b W ≅ condensedScalar (a ≫ b) W :=
  ((condensedScalarAdjunction a W).comp
      (condensedScalarAdjunction b W)).leftAdjointUniq
    ((condensedScalarAdjunction (a ≫ b) W).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso
          (Mod.comapCongr (coefficientMap_comp a b W) ≪≫ Mod.comapComp _ _) ≪≫
        Functor.mapDerivedCategoryCompIso
          _ _))

section CoefficientCompositionProof

set_option backward.defeqAttrib.useBackward false
set_option linter.unusedSectionVars false
private def coefficientRestrictionComp (W : Scheme.{u}) :
    Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
      (coefficientMap (a ≫ b) W) ≅
      Mod.comap (coefficientMap b W) ⋙ Mod.comap (coefficientMap a W) :=
  Mod.comapCongr (coefficientMap_comp a b W) ≪≫ Mod.comapComp _ _

private def derivedCoefficientRestrictionComp (W : Scheme.{u}) :
    (Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
      (coefficientMap (a ≫ b) W)).mapDerivedCategory ≅
    (Mod.comap (coefficientMap b W)).mapDerivedCategory ⋙
      (Mod.comap (coefficientMap a W)).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (coefficientRestrictionComp a b W) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private theorem derivedRestrictionComp_symm (W : Scheme.{u}) :
    exact_comp _ _ _ (coefficientRestrictionComp a b W).symm =
      (derivedCoefficientRestrictionComp a b W).symm := by
  apply Iso.ext
  dsimp only [exact_comp]
  simp only [derivedCoefficientRestrictionComp, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm]

private theorem scalarComp_eq (W : Scheme.{u}) :
    condensedScalarComp a b W =
      ((condensedScalarAdjunction a W).comp (condensedScalarAdjunction b W)).leftAdjointUniq
        ((condensedScalarAdjunction (a ≫ b) W).ofNatIsoRight
          (derivedCoefficientRestrictionComp a b W)) := by
  unfold condensedScalarComp derivedCoefficientRestrictionComp coefficientRestrictionComp
  rfl

attribute [local instance] fieldTensorColimits fieldTensorColimitsRight
  fieldGradedTensor fieldGradedFour fieldGradedLeft fieldGradedRight
attribute [local irreducible]
  CondensedRing.derivedComapLowerStarIso Mod.derivedExtendMapDerivedCategoryAdjunction
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars condensedScalarComp condensedProjection

attribute [local irreducible] CondensedRing.lowerStar CondensedRing.upperStar
  CondensedRing.openImmersionLowerShriek

private theorem scalarPush_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (condensedScalar b Y).map ((condensedPushScalar a f).app K) ≫
      (condensedPushScalar b f).app ((condensedScalar a X).obj K) ≫
      (CondensedRing.lowerStar Λ'' f).rightDerivedFunctor.map
        ((condensedScalarComp a b X).hom.app K) =
    (condensedScalarComp a b Y).hom.app
      ((CondensedRing.lowerStar Λ f).rightDerivedFunctor.obj K) ≫
      (condensedPushScalar (a ≫ b) f).app K := by
  simp only [scalarPush_eq, scalarComp_eq]
  let rx := derivedCoefficientRestrictionComp a b X
  let ry := derivedCoefficientRestrictionComp a b Y
  have hr (W : Scheme.{u}) : CondensedRing.restriction_comp a b W =
      (coefficientRestrictionComp a b W).symm := by
    apply Iso.ext
    rfl
  have hc := square_horizontal
    (CondensedRing.lowerStar Λ'' f) (CondensedRing.lowerStar Λ' f)
    (CondensedRing.lowerStar Λ f)
    (Mod.comap (coefficientMap b X)) (Mod.comap (coefficientMap a X))
    (Mod.comap (coefficientMap (a ≫ b) X))
    (Mod.comap (coefficientMap b Y)) (Mod.comap (coefficientMap a Y))
    (Mod.comap (coefficientMap (a ≫ b) Y))
    (CondensedRing.comapLowerStarIso b f) (CondensedRing.comapLowerStarIso a f)
    (CondensedRing.comapLowerStarIso (a ≫ b) f)
    (CondensedRing.restriction_comp a b X) (CondensedRing.restriction_comp a b Y)
    (CondensedRing.coefficient_square_comp a b f)
  dsimp only [derived_square] at *
  simp only [hr, derivedRestrictionComp_symm] at hc
  have hp := push_pasting_canonical
    (condensedScalarAdjunction a X)
    (condensedScalarAdjunction b X)
    (condensedScalarAdjunction (a ≫ b) X)
    (condensedScalarAdjunction a Y)
    (condensedScalarAdjunction b Y)
    (condensedScalarAdjunction (a ≫ b) Y)
    (CondensedRing.derivedComapLowerStarIso a f)
    (CondensedRing.derivedComapLowerStarIso b f)
    (CondensedRing.derivedComapLowerStarIso (a ≫ b) f) rx ry (by
      simpa only [CondensedRing.derivedComapLowerStarIso, Iso.symm_hom, rx, ry] using hc) K
  dsimp only [rx, ry] at hp
  exact hp.symm

attribute [local irreducible] CondensedRing.comapUpperStarIso
  CondensedRing.openCoefficientCollapse

attribute [local irreducible] CondensedRing.derivedComapUpperStarIso

  CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction

end CoefficientCompositionProof

set_option backward.defeqAttrib.useBackward false in
attribute [local irreducible]
  Mod.derivedExtendMapDerivedCategoryAdjunction
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Mod.extendScalars condensedScalarComp in
attribute [instance] identityScalar_flat

section CoefficientIdentityProof
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor

attribute [local irreducible]
  CondensedRing.derivedComapLowerStarIso
  CondensedRing.derivedComapUpperStarIso
  Mod.derivedExtendMapDerivedCategoryAdjunction Mod.extendScalars

attribute [-instance] CategoryTheory.catToReflQuiver in
end CoefficientIdentityProof

end Projection

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- A named presentation of the original derived pullback.
Source: the existing condensed upper-star construction.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedUpperStar (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) :=
  (CondensedRing.upperStar Λ f).leftDerivedFunctor

/-- A named presentation of the original derived direct image.
Source: the existing condensed lower-star construction.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedLowerStar (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  (CondensedRing.lowerStar Λ f).rightDerivedFunctor

/-- A named presentation of the original exact open extension.
Source: the existing condensed open extension construction.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedOpenShriek (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  (CondensedRing.openImmersionLowerShriek Λ f).mapDerivedCategory

/-- The original derived adjunction in the named functor presentation.
Source: the archived derived upper-star/lower-star adjunction.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    fieldDerivedUpperStar Λ f ⊣ fieldDerivedLowerStar Λ f :=
  CondensedRing.derivedUpperStarLowerStarAdjunction Λ f

/-- The original pullback compositor in the named functor presentation.
Source: the archived derived upper-star compositor.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedPullComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fieldDerivedUpperStar Λ (f ≫ g) ≅ fieldDerivedUpperStar Λ g ⋙ fieldDerivedUpperStar Λ f :=
  CondensedRing.leftDerivedUpperStarComp Λ f g

/-- The exact open adjunction expressed using the actual left-derived pullback.
Source: archived open-immersion derived adjunction; blueprint Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldOpenAdjunction {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    (fieldDerivedOpenShriek Λ j) ⊣
      (fieldDerivedUpperStar Λ j) :=
  (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm

attribute [local irreducible] CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarComp
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

/-- Compose an inverse-image comparison with the proper counit.
Source: blueprint proof Steps 15--16; naturality of the compositor and counit.
(blueprint: def-pur-condensed-compact-support-projection). -/
def counitRestrictionNat
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : C ⥤ D) {P : E ⥤ D} {R : D ⥤ E} (ad : P ⊣ R)
    (V : D ⥤ C) (U : E ⥤ C) (α : U ≅ P ⋙ V) :
    (J ⋙ R) ⋙ U ⟶ J ⋙ V where
  app K := α.hom.app (R.obj (J.obj K)) ≫ V.map (ad.counit.app (J.obj K))
  naturality {K L} v := by
    have hα : U.map (R.map (J.map v)) ≫ α.hom.app (R.obj (J.obj L)) =
        α.hom.app (R.obj (J.obj K)) ≫ V.map (P.map (R.map (J.map v))) :=
      α.hom.naturality (R.map (J.map v))
    have hε : P.map (R.map (J.map v)) ≫ ad.counit.app (J.obj L) =
        ad.counit.app (J.obj K) ≫ J.map v := ad.counit.naturality (J.map v)
    change U.map (R.map (J.map v)) ≫
        (α.hom.app (R.obj (J.obj L)) ≫ V.map (ad.counit.app (J.obj L))) =
      (α.hom.app (R.obj (J.obj K)) ≫ V.map (ad.counit.app (J.obj K))) ≫ V.map (J.map v)
    rw [← Category.assoc, hα, Category.assoc, ← V.map_comp, hε, V.map_comp,
      Category.assoc]

/-- The original restriction normalization, assembled naturally in the input.
Source: blueprint proof Steps 15--16.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpenRestrictionNat {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    (fieldDerivedOpenShriek Λ c.i ⋙ fieldDerivedLowerStar Λ r.hom) ⋙
        fieldDerivedUpperStar Λ d.i ⟶
      fieldDerivedOpenShriek Λ c.i ⋙ fieldDerivedUpperStar Λ c.i :=
  counitRestrictionNat
    (fieldDerivedOpenShriek Λ c.i)
    (fieldDerivedAdjunction Λ r.hom)
    (fieldDerivedUpperStar Λ c.i)
    (fieldDerivedUpperStar Λ d.i)
    ((eqToIso (congrArg (fun h : X ⟶ d.Z ↦
      (fieldDerivedUpperStar Λ h)) r.i_hom.symm)) ≪≫
      fieldDerivedPullComp Λ c.i r.hom)

attribute [local irreducible] fieldProperOpenRestrictionNat

/-- The restriction normalization of a proper refinement, before its invertibility
is asserted. Source: blueprint proof Steps 15--16
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpenRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (fieldDerivedUpperStar Λ d.i).obj
        ((fieldDerivedLowerStar Λ r.hom).obj ((fieldDerivedOpenShriek Λ c.i).obj K)) ⟶
      (fieldDerivedUpperStar Λ c.i).obj ((fieldDerivedOpenShriek Λ c.i).obj K) :=
  (fieldProperOpenRestrictionNat Λ r).app K

private theorem unique_normalized_lift
    {C D : Type*} [Category C] [Category D] {J : C ⥤ D} {U : D ⥤ C}
    (ad : J ⊣ U) (K : C) (M : D) {N : C} (β : U.obj M ⟶ N) [IsIso β]
    (z : K ⟶ N) : ∃! e : J.obj K ⟶ M, ad.homEquiv _ _ e ≫ β = z := by
  let e₀ := (ad.homEquiv K M).symm (z ≫ inv β)
  have h₀ : ad.homEquiv K M e₀ ≫ β = z := by
    simp only [e₀, Equiv.apply_symm_apply, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
  refine ⟨e₀, h₀, fun e he ↦ ?_⟩
  apply (ad.homEquiv K M).injective
  exact (cancel_mono β).mp (he.trans h₀.symm)

/-- The proper/open refinement is uniquely fixed by the original open unit.
Source: blueprint proof Steps 15--16; Stacks 0F7B
(blueprint: def-pur-condensed-compact-support-projection).
Proof: restriction of direct image to the open is the direct image of the open
restriction, since open extension is an exact left adjoint. In the pulled-back square
the section defined by the refinement is clopen. Extension by zero restricts to the
original input on that component and vanishes on its complement. Thus the displayed
restriction normalization is invertible. The open Hom bijection supplies a unique
arrow with this transpose; no proper base change outside the open is needed. -/
theorem fieldProperOpen_existsUnique {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    ∃! e : (fieldDerivedOpenShriek Λ d.i).obj K.obj ⟶
        (fieldDerivedLowerStar Λ r.hom).obj
          ((fieldDerivedOpenShriek Λ c.i).obj K.obj),
      (fieldOpenAdjunction Λ d.i).homEquiv _ _ e ≫
          fieldProperOpenRestriction Λ r K.obj =
        (fieldOpenAdjunction Λ c.i).unit.app K.obj := by
  have hc := condensedOpen_restrictedCounit_isIso Λ r K.obj
  have : IsIso ((fieldDerivedUpperStar Λ c.i).map
      ((fieldDerivedAdjunction Λ r.hom).counit.app
        ((fieldDerivedOpenShriek Λ c.i).obj K.obj))) := hc
  have : IsIso (fieldProperOpenRestriction Λ r K.obj) := by
    unfold fieldProperOpenRestriction fieldProperOpenRestrictionNat counitRestrictionNat
    dsimp only
    infer_instance
  exact unique_normalized_lift (fieldOpenAdjunction Λ d.i) K.obj _
    (fieldProperOpenRestriction Λ r K.obj) ((fieldOpenAdjunction Λ c.i).unit.app K.obj)

/-- The unit-normalized refinement arrow, without an arbitrary splitting.
Source: blueprint proof Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpen {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldDerivedOpenShriek Λ d.i).obj K.obj ⟶
      (fieldDerivedLowerStar Λ r.hom).obj
        ((fieldDerivedOpenShriek Λ c.i).obj K.obj) :=
  (fieldProperOpen_existsUnique Λ r K).exists.choose

private theorem fieldProperOpen_spec {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldOpenAdjunction Λ d.i).homEquiv _ _ (fieldProperOpen Λ r K) ≫
        fieldProperOpenRestriction Λ r K.obj =
      (fieldOpenAdjunction Λ c.i).unit.app K.obj :=
  (fieldProperOpen_existsUnique Λ r K).exists.choose_spec

attribute [local irreducible] fieldProperOpen fieldOpenAdjunction
  DerivedCategory.instPreadditive

section NaturalityProof

attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.openImmersionLowerShriek

attribute [local instance] fieldHomology_additive

private theorem fieldHomology_biprod
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (n : ℤ) (K L : DerivedCategory C) :
    PreservesBinaryBiproduct K L (DerivedCategory.homologyFunctor C n) :=
  preservesBinaryBiproduct_of_preservesBinaryProduct _

attribute [local instance] fieldHomology_biprod

private theorem fieldBounded_biprod {X : Scheme.{u}}
    (K L : BoundedConstructible (condensedRingObj Λ X)) :
    boundedConstructible (condensedRingObj Λ X) (K.obj ⊞ L.obj) := by
  let P : ObjectProperty (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := IsConstructibleModuleObject (condensedRingObj Λ X)
  let : ObjectProperty.IsClosedUnderExtensions P :=
    (CondensedRing.constructible_cokernels_extensions X (condensedRingObj Λ X)).2
  have hK := (mem_boundedConstructible_iff (condensedRingObj Λ X) K.obj).mp K.property
  have hL := (mem_boundedConstructible_iff (condensedRingObj Λ X) L.obj).mp L.property
  rw [mem_boundedConstructible_iff]
  refine ⟨?_, fun n ↦ ?_⟩
  · obtain ⟨a, b, hK⟩ := hK.1
    obtain ⟨c, d, hL⟩ := hL.1
    refine ⟨min a c, max b d, fun n hn ↦ ?_⟩
    have hk : n < a ∨ b < n := by omega
    have hl : n < c ∨ d < n := by omega
    exact ((biprod_isZero_iff _ _).mpr ⟨hK n hk, hL n hl⟩).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapBiprod K.obj L.obj)
  · exact (P.prop_biprod (hK.2 n) (hL.2 n)).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapBiprod K.obj L.obj).symm

private theorem fieldProperOpen_naturality_retract {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    {K L : BoundedConstructible (condensedRingObj Λ X)}
    (M : BoundedConstructible (condensedRingObj Λ X))
    (i : K.obj ⟶ M.obj) (p : M.obj ⟶ K.obj)
    (j : L.obj ⟶ M.obj) (q : M.obj ⟶ L.obj)
    (hip : i ≫ p = 𝟙 K.obj) (hjq : j ≫ q = 𝟙 L.obj) (v : K ⟶ L) :
    (fieldDerivedOpenShriek Λ d.i).map v.hom ≫
        fieldProperOpen Λ r L =
      fieldProperOpen Λ r K ≫ (fieldDerivedLowerStar Λ r.hom).map
        ((fieldDerivedOpenShriek Λ c.i).map v.hom) := by
  exact normalized_lift_naturality_of_unique (fieldOpenAdjunction Λ d.i) _ _
    (fieldProperOpenRestrictionNat Λ r) (fieldOpenAdjunction Λ c.i).unit
    i p j q hip hjq v.hom (fieldProperOpen_existsUnique Λ r M)
    (fieldProperOpen Λ r K) (fieldProperOpen Λ r L)
    (fieldProperOpen_spec Λ r K) (fieldProperOpen_spec Λ r L)

/-- Naturality of the original unit-normalized proper/open comparison.
Source: blueprint Steps 15--16, using uniqueness at a binary sum.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldProperOpen_naturality {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    {K L : BoundedConstructible (condensedRingObj Λ X)} (v : K ⟶ L) :
    (fieldDerivedOpenShriek Λ d.i).map v.hom ≫
        fieldProperOpen Λ r L =
      fieldProperOpen Λ r K ≫ (fieldDerivedLowerStar Λ r.hom).map
        ((fieldDerivedOpenShriek Λ c.i).map v.hom) := by
  exact fieldProperOpen_naturality_retract Λ r
    ⟨K.obj ⊞ L.obj, fieldBounded_biprod Λ K L⟩
    biprod.inl biprod.fst biprod.inr biprod.snd biprod.inl_fst biprod.inr_snd v

end NaturalityProof

/-- Proper-image composition is the conjugate of the actual pullback composition.
Source: archived module-object derived operations; blueprint Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldPushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (fieldDerivedLowerStar Λ f) ⋙
        (fieldDerivedLowerStar Λ g) ≅
      fieldDerivedLowerStar Λ (f ≫ g) :=
  conjugateIsoEquiv
    ((fieldDerivedAdjunction Λ g).comp
      (fieldDerivedAdjunction Λ f))
    (fieldDerivedAdjunction Λ (f ≫ g))
    (fieldDerivedPullComp Λ f g)

/-- Apply direct image to a natural lift and then its natural compositor.
Source: blueprint Step 15, functoriality of composition.
(blueprint: def-pur-condensed-compact-support-projection). -/
def assembleLiftNat
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (F : C ⥤ D) (G : C ⥤ E) (P : E ⥤ D) (R : D ⥤ H) (S : E ⥤ H)
    (lift : F ⟶ G ⋙ P) (cmp : P ⋙ R ⟶ S) : F ⋙ R ⟶ G ⋙ S where
  app K := R.map (lift.app K) ≫ cmp.app (G.obj K)
  naturality {K L} v := by
    change R.map (F.map v) ≫ (R.map (lift.app L) ≫ cmp.app (G.obj L)) =
      (R.map (lift.app K) ≫ cmp.app (G.obj K)) ≫ S.map (G.map v)
    rw [← R.map_comp_assoc, lift.naturality, R.map_comp, Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun z ↦ R.map (lift.app K) ≫ z) (cmp.naturality (G.map v))

/-- The original normalized lift on bounded constructible inputs.
Source: blueprint Step 15.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpenNat {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        (fieldDerivedOpenShriek Λ d.i) ⟶
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙
        (fieldDerivedOpenShriek Λ c.i)) ⋙
          (fieldDerivedLowerStar Λ r.hom) where
  app := fieldProperOpen Λ r
  naturality := fun _ _ v ↦ fieldProperOpen_naturality Λ r v

/-- The original proper/open refinement assembled naturally.
Source: blueprint Step 15.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldRefinementNat {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ d.i) ⋙
        fieldDerivedLowerStar Λ d.g ⟶
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ c.i) ⋙
        fieldDerivedLowerStar Λ c.g :=
  assembleLiftNat _ _ _
    (fieldDerivedLowerStar Λ d.g)
    (fieldDerivedLowerStar Λ c.g)
    (fieldProperOpenNat Λ r)
    ((fieldPushComp Λ r.hom d.g).hom ≫
      (eqToIso (congrArg (fun h : c.Z ⟶ Y ↦
        (fieldDerivedLowerStar Λ h)) r.hom_g)).hom)

/-- The canonical refinement component, in the direction from coarser to finer.
Source: blueprint proof Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldRefinementApp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ d).obj K.obj ⟶
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K.obj :=
  (fieldRefinementNat Λ r).app K

/-- Naturality of the fixed refinement components.
Source: blueprint proof Step 15
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the two composites under the open adjunction. Naturality of its
unit and of the proper counit makes the transposes equal; the Hom bijection then
gives the equation. Proper-image composition is itself natural. -/
theorem fieldRefinementApp_naturality {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    {K L : BoundedConstructible (condensedRingObj Λ X)} (v : K ⟶ L) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ d).map v.hom ≫
        fieldRefinementApp Λ r L =
      fieldRefinementApp Λ r K ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).map v.hom := by
  exact (fieldRefinementNat Λ r).naturality v

/-- The specified condensed refinement as a whole natural transformation.
Source: blueprint proof Steps 15--16
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldRefinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ d ⟶
      (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ c where
  app := fieldRefinementApp Λ r
  naturality := fun _ _ v ↦ fieldRefinementApp_naturality Λ r v

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local irreducible] CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarComp

end WeilConjectures.CompactSupportCondensedRealization

-- Export the proved property caches after checking the canonical constructions.
