/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PointDualityCoefficientsFiber
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Data.Finset.Max
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.WeakContractibleEquivalences
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalBounded
import WeilConjectures.CategoryTheory.SixFunctors.CohomologicalSolutionSetRepresentability
import WeilConjectures.CategoryTheory.SixFunctors.SetGeneratedDerivedSolutionSet
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZetaWeil.ContractibleLisseEvaluation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationUnderivedModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationOrdinaryUnit
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import WeilConjectures.CategoryTheory.RingedKFlatModel.RingedKFlatNativeModelIdentification
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.ZetaWeil.RingDerivedDualizablePerfect
import WeilConjectures.RingTheory.ProEtale.WContractible
/-! # Dualizing complex of the geometric point
Source: current blueprint, sec-six-functors/sk-thm-sf-package/
lem-pod-point-dualizing-complex.md (blueprint: lem-pod-point-dualizing-complex).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
/-- The point assertion in the ordinary condensed derived category. The two functors
are the restriction of the actual identity compact-support composite and its right
adjoint. The last two natural isomorphisms are the fibre and realization dual formulas.
Source: current blueprint lem-pod-point-dualizing-complex, displayed formulas
(blueprint: lem-pod-point-dualizing-complex). -/
def PointDualizingComplexStatement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] : Prop :=
  ∃ (hu : (constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) (𝟙_ (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k)))))))
    (F G : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)) ⥤
      ConstantModelConstructibleFiniteTor Λ (Spec (.of k))),
    Nonempty (F ⋙ (constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι ≅
      (constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ
          (pointDualityCompactification k)) ∧
    Nonempty (F ⊣ G) ∧ Nonempty (G ≅ 𝟭 _) ∧
    Nonempty ((G.obj ⟨𝟙_ _, hu⟩).obj ≅ 𝟙_ _) ∧
    Nonempty (((constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι.op ⋙
      (CondensedRing.derivedHom Λ (Spec (.of k))).flip.obj (G.obj ⟨𝟙_ _, hu⟩).obj) ⋙
        pointDualityFiber Λ k ≅
      ((constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι ⋙ pointDualityFiber Λ k).op ⋙
        (Functor.curry.obj (ordinaryModuleDerivedInternalHom
          (condensedScalarRing Λ))).flip.obj
            ((DerivedCategory.singleFunctor
              (ModuleCat.{u + 1} (condensedScalarRing Λ)) 0).obj
                (ModuleCat.of (condensedScalarRing Λ) (condensedScalarRing Λ)))) ∧
    Nonempty ((constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι.op ⋙
      (CondensedRing.derivedHom Λ (Spec (.of k))).flip.obj (G.obj ⟨𝟙_ _, hu⟩).obj ≅
      (((constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _).ι ⋙ pointDualityFiber Λ k).op ⋙
        (Functor.curry.obj (ordinaryModuleDerivedInternalHom
          (condensedScalarRing Λ))).flip.obj
            ((DerivedCategory.singleFunctor
              (ModuleCat.{u + 1} (condensedScalarRing Λ)) 0).obj
                (ModuleCat.of (condensedScalarRing Λ) (condensedScalarRing Λ)))) ⋙
        condensedScalarRealization Λ (Spec (.of k)))
end AlgebraicGeometry.ProEtale
