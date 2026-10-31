/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import WeilConjectures.AlgebraicGeometry.PbcScalarExtension
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
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
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingScalarExtension
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.ScalarLocalizationSheafExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.CategoryTheory.ScalarLocalization
import WeilConjectures.CategoryTheory.ScalarLocalizationTriangulated
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all WeilConjectures.CategoryTheory.SiteInverseImageTensor
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Actual scalar extension on raw integral rationalizations

Source: Bhatt--Scholze, Lemma 6.8.2 and Propositions 6.8.11(3), 6.8.14(2).
(blueprint: lem-weil-pbc-realization-scalar-functor)

The coefficient encodings are the published constructions. The record below retains
only the scalar functor and its normalization; it contains no equivalence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (T : Scheme.{u}) [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

set_option synthInstance.checkSynthOrder false in
/-- Continuous field coefficients in the scheme universe have the inherited bounded
constructible triangulation. Source: Bhatt--Scholze, Proposition 6.8.11(1),(3).
(blueprint: lem-weil-pbc-realization-scalar-functor)

Proof. Local finite presentations over these coefficients are pro-etale locally finite
free. The constructible Serre argument therefore supplies kernel, cokernel and extension
closure on the noetherian strata. The bounded homology Serre criterion gives triangulated
closure, including zero ranks and the empty scheme. -/
instance realizationScalarTargetTriangulated :
    (boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).IsTriangulated := by
  obtain ⟨hk, he⟩ := condensed_constructible_serre_of_locally_free freeEpiLocalSplitting
    (Profinite.continuousCoefficientRingObj E)
    (exists_finiteFree_cover_of_condensedField_lfp l E) T
  let R := condensedRingObj (Profinite.continuousCoefficientRingObj E) T
  let : ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R) :=
    ⟨by
      rintro _ ⟨f, s, hs, hf⟩
      exact IsConstructibleModuleObject.of_iso (R := R) (limit.isoLimitCone ⟨s, hs⟩)
        (hk _ _ f hf.1 hf.2).1⟩
  let : ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R) :=
    ⟨by
      rintro _ ⟨f, s, hs, hf⟩
      exact IsConstructibleModuleObject.of_iso (R := R) (colimit.isoColimitCocone ⟨s, hs⟩)
        (hk _ _ f hf.1 hf.2).2⟩
  let : ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R) := ⟨he _⟩
  exact isTriangulated_boundedConstructible_of_serre R

/-- The coefficient-normalized scalar functor, with the actual extension and restriction
on the ambient derived categories. The integral comparison expresses J(K)=F(K) in
sectionwise coordinates; the fraction equation uses that same comparison.
Source: Bhatt--Scholze, 6.8.2, 6.8.11(3), 6.8.14(2).
(blueprint: lem-weil-pbc-realization-scalar-functor) -/
structure RealizationScalarFunctorData where
  coefficientIso : Mon.mk (condensedRingObj (Profinite.continuousCoefficientRingObj E) T) ≅
    Mon.mk ((sheafCompose (ProEt.topology T) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (AlgebraicGeometry.ProEtale.continuousCoefficientRingSheaf T E))
  coefficient_normalization : ∀ (S : Profinite.{u}) (f : C(S, E)),
    (((pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))).homEquiv
        _ _ coefficientIso.hom.hom).hom.app (op S)) (ULift.up f) =
      ULift.up (f.comp (profiniteTestProjection T S))
  sectionIso : (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (ProEt.topology T)
    (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)) ≅ rationalCoefficientSheaf l T
    E
  section_normalization : ∀ (U : T.ProEtᵒᵖ) (s : ((InternalAbelianSheafModule.sectionRingSheaf.{u +
    1, u + 1, u} (ProEt.topology T) (condensedRingObj (Profinite.continuousCoefficientRingObj E)
    T))).obj.obj U)
      (x : U.unop.left),
    rationalCoefficientValue l E T U (sectionIso.hom.hom.app U s) x =
      (((coefficientIso.hom.hom).hom.app U) s).down x
  integralIso : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
    AlgebraicGeometry.Scheme.integralCoefficientSheaf l T E
  finiteIso : ∀ n : ℕ,
    (pbcAdicRings T (pbcIntegralDatum l E)).obj (op n) ≅
      finiteContinuousCoefficientSheaf l T E n
  finite_normalization : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
      (a : PbcIntegralRing l E ⧸ (pbcIntegralDatum l E).ideal ^ (n + 1)) (x : U.unop.left),
    finiteContinuousCoefficientValue l E T n U
      ((finiteIso n).hom.hom.app U
        (pbcFunctionScalars T (pbcIntegralDatum l E) n |>.app U |>.hom <| a)) x =
      integralCoefficientULift l E n a
  integral_normalization : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
      (s : (AlgebraicGeometry.Scheme.integralCoefficientSheaf l T E).obj.obj U) (x : U.unop.left),
    (finiteContinuousCoefficientValue l E T n U
      ((integralIso.inv ≫ pbcAdicProjection T (pbcIntegralDatum l E) n ≫
        (finiteIso n).hom).hom.app U s) x).down =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (integralCoefficientValue l E T U s x)
  inclusion : AlgebraicGeometry.Scheme.integralCoefficientSheaf l T E ⟶ rationalCoefficientSheaf
    l T E
  inclusion_normalization : integralRationalCoefficientNormalized l E T inclusion
  [encodingAdditive : ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T) (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
    (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso sectionIso).symm)).functor.Additive]
  [encodingInverseAdditive : ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology T) (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
    (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso sectionIso).symm)).inverse.Additive]
  extension_exact : PreservesFiniteLimits (pbcExtend (integralIso.hom ≫ inclusion))
  extension_colimits : PreservesFiniteColimits (pbcExtend (integralIso.hom ≫ inclusion))
  restriction_exact : PreservesFiniteLimits (pbcRestrict (integralIso.hom ≫ inclusion))
  restriction_colimits : PreservesFiniteColimits (pbcRestrict (integralIso.hom ≫ inclusion))
  [restriction_shift : (pbcDerivedRestrict (integralIso.hom ≫ inclusion)).CommShift ℤ]
  restriction_derived_exact : (pbcDerivedRestrict (integralIso.hom ≫ inclusion)).IsTriangulated
  [ambient_shift : (pbcDerivedExtend (integralIso.hom ≫ inclusion)).CommShift ℤ]
  ambient_exact : (pbcDerivedExtend (integralIso.hom ≫ inclusion)).IsTriangulated
  unit : ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
    (pbcDerivedScalarAdjunction (integralIso.hom ≫ inclusion)).unit.app
        (DerivedCategory.Q.obj P) ≫
      (pbcDerivedRestrict (integralIso.hom ≫ inclusion)).map
        (pbcComplexCounit (integralIso.hom ≫ inclusion) P) ≫
      (pbcRestrict (integralIso.hom ≫ inclusion)).mapDerivedCategoryFactors.hom.app
        (((pbcExtend (integralIso.hom ≫ inclusion)).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (pbcScalarAdjunction (integralIso.hom ≫ inclusion)).unit (.up ℤ)).app P)
  computes : ∀ P : CochainComplex (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
    IsIso (pbcComplexCounit (integralIso.hom ≫ inclusion) P)
  tensor_unit : ∀ (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
      (U : T.ProEtᵒᵖ) (m : M.val.obj U),
    ((pbcScalarAdjunction (integralIso.hom ≫ inclusion)).unit.app M).val.app U m =
      pbcTensorSection (integralIso.hom ≫ inclusion) M U 1 m
  J : PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤ BoundedConstructible
    (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)
  [additive : J.Additive]
  [shift : J.CommShift ℤ]
  exact : J.IsTriangulated
  integral : pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
      J ⋙ (boundedConstructible (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).ι ⋙
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (ProEt.topology T)
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
          (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso
          sectionIso).symm)).mapDerivedCategory.functor ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
      pbcDerivedExtend (integralIso.hom ≫ inclusion)
  linearity : ∀ (K L : PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)) (f : K ⟶
    L) (a : E),
    (((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
      (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso
      sectionIso).symm)).mapDerivedCategory.functor).map
        (J.map (a • f)).hom =
      @SMul.smul _ _
        (@Linear.homModule _ _ _ _ _
          (@DerivedCategory.instLinear _ _ _ _ _
            (SheafOfModules.homLinear (rationalCoefficientSheaf l T E).obj
              (((adicLisseForget T).obj (rationalCoefficientSheaf l T E)).property)) _)
          _ _).toSMul
        ⟨fun _ ↦ @ContinuousMap.const _ (ULift E) _
          (@ULift.topologicalSpace E
            (coefficientExtensionNormedField l E).toUniformSpace.toTopologicalSpace)
          (ULift.up a), fun _ ↦ rfl⟩
        ((((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (ProEt.topology
        T) (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
        (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso
        sectionIso).symm)).mapDerivedCategory.functor).map (J.map f).hom)
  fractions : ∀ (K L : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) (f : K ⟶ L) (n :
    ℕ),
    (((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)).trans
      (ringModuleEquivalenceOfIso T ((adicLisseForget T).mapIso
      sectionIso).symm)).mapDerivedCategory.functor).map
        (J.map ((pbcRationalCoefficientEquiv l E).symm
          (((pbcUniformizer l E).down : E) ^ n)⁻¹ •
            (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map f)).hom ≫
      integral.hom.app L =
    integral.hom.app K ≫
      (@SMul.smul _ _
        (@Linear.homModule _ _ _ _ _
          (@DerivedCategory.instLinear _ _ _ _ _
            (SheafOfModules.homLinear (rationalCoefficientSheaf l T E).obj
              (((adicLisseForget T).obj (rationalCoefficientSheaf l T E)).property)) _)
          _ _).toSMul
        ⟨fun _ ↦ @ContinuousMap.const _ (ULift E) _
          (@ULift.topologicalSpace E
            (coefficientExtensionNormedField l E).toUniformSpace.toTopologicalSpace)
          (ULift.up (((pbcUniformizer l E).down : E) ^ n)⁻¹), fun _ ↦ rfl⟩
        ((pbcDerivedExtend (integralIso.hom ≫ inclusion)).map f.hom))

/-- Actual scalar extension is exact, takes integral objects to the archived bounded
constructible category, and factors through the raw rationalization by the stated fractions.
Source: Bhatt--Scholze, 6.8.2, 6.8.11(3), 6.8.14(2).
(blueprint: lem-weil-pbc-realization-scalar-functor)

Proof:
1. Identify the completed coefficient ring with continuous integral functions using
lem-weil-pbc-continuous-coefficients-immersion-restriction, normalized on every finite
quotient. The inclusion is postcomposition with A→E. The continuous coefficient
realization and module encoding identify the specified internal and sectionwise maps.
2. Apply lem-weil-pbc-scalar-localization-sheaf-exact to this sheaf localization.
Exact-functor derived factorization and lem-weil-pbc-exact-functor-derived-functor
identify termwise extension with the total left derived tensor, with its shift comparison.
3. Apply lem-pur-sheaf-ring-derived-coefficient-adjunction on the identity site.
Restriction is exact; the ambient adjunction has the pure-tensor unit. Its K-flat
normalization extends to every complex by naturality and exactness of both functors.
4. Integral stratified perfect characterization gives bounded cohomology with finitely
presented integral local models. Their finite presentations and the module encoding,
followed by bounded constructible exact scalar extension, give the archived local finite
presentation condition in the target. No local freeness characterization is used.
5. Send K to F(K) and u/varpi^n to varpi^(-n) F(u). The localization relation is respected
because varpi acts invertibly in E. Addition, composition, identities and E-linearity
follow from the tensor balancing relation and the common denominator calculation.
6. Integral closure under shifts and cones and scalar localization triangulation identify
every rational distinguished triangle with an integral image. Exactness of F and step 4
show its J-image is distinguished in the full target. Naturality of the shift comparison
extends from integral arrows to fractions. The constructible Serre theorem and bounded
constructible triangulation give the target's induced triangulated structure. -/
theorem realization_scalar_functor (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [T.Over (Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))] :
    Nonempty (RealizationScalarFunctorData l E T) := by
  sorry

end WeilConjectures
