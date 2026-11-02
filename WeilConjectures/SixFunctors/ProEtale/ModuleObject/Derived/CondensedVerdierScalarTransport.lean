/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import WeilConjectures.Algebra.Homology.Monoidal.Dual
public import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
public import WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalBounded
public import WeilConjectures.CategoryTheory.SixFunctors.CohomologicalSolutionSetRepresentability
public import WeilConjectures.CategoryTheory.SixFunctors.SetGeneratedDerivedSolutionSet
public import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

/-! # Exact symmetric scalar transport for Verdier normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

variable {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]

/-- The ordinary total derived extension along a coefficient isomorphism.
Source: blueprint coefficient normalization in finite biduality
(blueprint: lem-sf-condensed-verdier-scalar-transport). -/
abbrev condensedVerdierScalarTransport (e : Mon.mk Λ ≅ Mon.mk Γ) (X : Scheme.{u}) :=
  (Mod.extendScalars (coefficientMap e.hom.hom X)).leftDerivedFunctor

/-- The canonical K-flat monoidal structure, without a new global instance.
Source: blueprint coefficient normalization in finite biduality
(blueprint: lem-sf-condensed-verdier-scalar-transport). -/
@[instance_reducible] def condensedVerdierScalarMonoidal
    (e : Mon.mk Λ ≅ Mon.mk Γ) (X : Scheme.{u}) :
    (condensedVerdierScalarTransport e X).Monoidal :=
  letI := Mod.extendScalarsMonoidal (coefficientMap e.hom.hom X)
  (Mod.extendScalars (coefficientMap e.hom.hom X)).leftDerivedFunctorMonoidal

end AlgebraicGeometry.ProEtale.CondensedRing
