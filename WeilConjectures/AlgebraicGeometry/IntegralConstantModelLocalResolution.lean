/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleObjects

public import WeilConjectures.AlgebraicGeometry.IntegralDerivedCoefficientData
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedClosedSupportAdjunction
public import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.IntegralTensorShriek
import WeilConjectures.AlgebraicGeometry.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import all Mathlib.Topology.MetricSpace.Ultra.Basic
import all Mathlib.Analysis.Normed.Field.Basic
import all Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Analysis.Normed.Group.Ultra
import all Mathlib.Data.Finset.Max
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.SiteInverseImageTensor
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all Mathlib.Algebra.Field.ULift
import all WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import all WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import all Mathlib.CategoryTheory.Preadditive.Biproducts
import all Mathlib.Data.Fin.Tuple.Basic
import all WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
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
import all WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import all WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import all WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import all Mathlib.CategoryTheory.Sites.Adjunction
import all Mathlib.Algebra.Category.Grp.Adjunctions
import all WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import all WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRingSupplement
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteProjectiveDualizable

/-! # Local two-term resolutions of finite constant integral models -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  Mod.extendScalarsIsoComapInv Mod.monoidalClosed

private theorem localCoefficientSmallIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∃ (F : Type) (_ : NormedField F) (_ : NormedAlgebra ℚ_[l] F)
      (_ : FiniteDimensional ℚ_[l] F),
      Nonempty (Mon.mk (integralCoefficientRing l E) ≅
        Mon.mk (integralCoeff.{u} l F)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : NormedAlgebra ℚ_[l] E := ⟨fun a x ↦ by
    change spectralNorm (Padic l) E (a • x) ≤ ‖a‖ * spectralNorm (Padic l) E x
    exact le_of_eq (map_smul_eq_mul (spectralMulAlgNorm (Padic l) E) a x)⟩
  let : Small.{0} E := Module.Finite.small (Padic l) E
  let F := Shrink.{0} E
  let e : F ≃ₐ[Padic l] E := Shrink.algEquiv (Padic l) E
  let : NormedField F := NormedField.induced F E e.toRingHom e.injective
  let : NormedAlgebra ℚ_[l] F := ⟨fun a x ↦ by
    change ‖e (a • x)‖ ≤ ‖a‖ * ‖e x‖
    change ‖e.toLinearMap (a • x)‖ ≤ ‖a‖ * ‖e x‖
    rw [e.toLinearMap.map_smul]
    exact norm_smul_le a (e x)⟩
  let : FiniteDimensional ℚ_[l] F := e.symm.toLinearEquiv.finiteDimensional
  refine ⟨F, inferInstance, inferInstance, inferInstance, ?_⟩
  have hm (x : E) : x ∈ Padic.coefficientExtensionIntegers l E ↔ ‖x‖ ≤ 1 := by
    exact (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1 x
  have hmem (x : F) : x ∈ continuousIntegers l F ↔ e x ∈
      Padic.coefficientExtensionIntegers l E := by
    rw [hm]
    change ‖x‖₊ ≤ 1 ↔ ‖e x‖ ≤ 1
    exact NNReal.coe_le_coe.symm
  let ei : continuousIntegers l F ≃+* Padic.coefficientExtensionIntegers l E :=
    { toFun := fun x ↦ ⟨e x, (hmem x).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x, (hmem _).mpr (by
        simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x y)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x y) }
  have hei : Isometry ei := fun _ _ ↦ rfl
  have heis : Isometry ei.symm := hei.right_inv ei.right_inv
  let : CommRing (continuousIntegers l F) := inferInstance
  let : CommRing (Padic.coefficientExtensionIntegers l E) := inferInstance
  obtain ⟨er⟩ := continuousCoefficientIso (continuousIntegers l F)
    (Padic.coefficientExtensionIntegers l E) ei hei.continuous heis.continuous
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  exact ⟨(Mon.mkIso ea).symm⟩

private theorem localModelResolution (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : pulledBackModuleObjects (integralCoefficientRing l E) X)
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (integralCoefficientRing l E) X) P) :
    ∃ S : ShortComplex (pulledBackModuleObjects (integralCoefficientRing l E) X),
      S.ShortExact ∧ Nonempty (S.X₃ ≅ P) ∧
      ResolutionLF (condensedRingObj (integralCoefficientRing l E) X) S.X₁ ∧
      ResolutionLF (condensedRingObj (integralCoefficientRing l E) X) S.X₂ := by
  obtain ⟨F, nf, na, fd, ⟨e⟩⟩ := localCoefficientSmallIso l E
  let := nf
  let := na
  let := fd
  let φ : condensedRingObj (integralCoefficientRing l E) X ⟶
      condensedRingObj (integralCoeff l F) X := (upperStarFromPoint X).map e.hom.hom
  have : IsMonHom e.hom.hom := inferInstance
  have : IsMonHom φ := inferInstance
  let G : pulledBackModuleObjects (integralCoeff l F) X ⥤
      pulledBackModuleObjects (integralCoefficientRing l E) X := Mod.comap φ
  obtain ⟨F₁, F₀, f, g, w, hs, h₁, h₀⟩ := integral_lfp_locallyFree_resolution X l F
    ((Mod.comap (inv φ)).obj P) (lfp_comap (inv φ) hP)
  refine ⟨(ShortComplex.mk f g w).map G, hs.map_of_exact G,
    ⟨(Mod.comapEquivalenceOfIsIso φ).counitIso.app P⟩, ?_, ?_⟩
  · exact locally_free_comap φ h₁
  · exact locally_free_comap φ h₀

/-- Finite constant integral models admit local two-term resolutions by dualizable
module sheaves.
Source: blueprint sk-lem-int-integral-heart-dualizable.proof.md, first paragraph,
and the recorded integral locally finite free resolution theorem.
(blueprint: lem-integral-constant-model-local-resolution).

Proof: the finite constant local models give a locally finite presentation. Equip E
with its coefficient-extension spectral norm, replace it by its small equivalent field,
and identify their valuation rings isometrically. Continuous scalar realization transports
this ring isomorphism to the condensed coefficient rings. The integral locally free
resolution theorem gives a short exact two-term resolution, and restriction along the
coefficient isomorphism transports it back to the stated coefficient ring. Refine the
two locally finite free covers to a common cover. Exact module inverse image transports
the short exact sequence. On each chart its first two terms are finite free after the
canonical scalar-transport comparison. A finite free module is dualizable, so this is
the asserted local resolution. The quotient is identified with the inverse image of M
by the transported counit. Zero ranks and empty covers are included. -/
theorem integral_constantModel_localResolution
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : supportModules (integralCoefficientRing l E) X)
    (hM : HasFiniteConstantLocalModel (integralCoefficientRing l E) X M) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ a : U.I₀,
      ∃ T : ShortComplex (supportModules (integralCoefficientRing l E) (U.X a)),
        T.ShortExact ∧ IsDualizable T.X₁ ∧ IsDualizable T.X₂ ∧
        Nonempty (T.X₃ ≅ (upperStar (integralCoefficientRing l E) (U.f a)).obj M) := by
  classical
  obtain ⟨T, hT, ⟨eT⟩, h₁, h₂⟩ := localModelResolution l E X M
    (HasFiniteConstantLocalModel.isLocallyFinitelyPresented (integralCoefficientRing l E) M hM)
  obtain ⟨U, hU⟩ := common_free_cover h₁ h₂
  refine ⟨U, fun a ↦ ?_⟩
  let F := upperStar (integralCoefficientRing l E) (U.f a)
  have : F.Additive := inferInstanceAs
    ((upperStar (integralCoefficientRing l E) (U.f a)).Additive)
  have : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (upperStar (integralCoefficientRing l E) (U.f a)))
  have : PreservesFiniteColimits F := inferInstanceAs
    (PreservesFiniteColimits (upperStar (integralCoefficientRing l E) (U.f a)))
  have hf (N : supportModules (integralCoefficientRing l E) X)
      (hN : Mod.IsFree
        ((ProEtale.upperStar Ab.{u + 1} (U.f a)).obj
          (condensedRingObj (integralCoefficientRing l E) X))
        (((ProEtale.upperStar Ab.{u + 1} (U.f a)).mapMod _).obj N)) :
      IsDualizable (F.obj N) := by
    let α := condensedPullbackHom (integralCoefficientRing l E) (U.f a)
    have hn := free_of_iso (free_comap (inv α) hN)
      ((Mod.extendScalarsIsoComapInv α).app _).symm
    have hn' : Mod.IsFree (condensedRingObj (integralCoefficientRing l E) (U.X a))
        (F.obj N) := by
      simpa only [F, upperStar, α, Functor.comp_obj] using hn
    obtain ⟨n, ⟨e⟩⟩ := hn'
    exact finiteFree_retract_isDualizable (integralCoefficientRing l E)
      (U.X a) n (F.obj N) e.hom e.inv e.hom_inv_id
  exact ⟨T.map F, hT.map_of_exact F, hf T.X₁ (hU a).1,
    hf T.X₂ (hU a).2, ⟨F.mapIso eT⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
