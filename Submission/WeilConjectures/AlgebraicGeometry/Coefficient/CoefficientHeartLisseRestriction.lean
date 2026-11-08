/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all Submission.WeilConjectures.CategoryTheory.ModuleObjects.Free
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import all Submission.WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Submission.WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all Submission.WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all Submission.WeilConjectures.CategoryTheory.Sites.MonObj
import all Submission.WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import all Mathlib.Algebra.Category.Grp.AB
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.AlgebraicGeometry.Limits
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all Submission.WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Submission.WeilConjectures.ConstructibleSheaf.Refinement
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all Submission.WeilConjectures.ConstructibleSheaf.Pullback
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all Submission.WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all Submission.WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all Submission.WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.WeilConjectures.ConstructibleSheaf.Defs
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all Submission.WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Submission.WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all Submission.WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all Submission.WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all Submission.WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all Submission.WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all Submission.WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all Submission.WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all Submission.WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import Submission.WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
import Submission.WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Lisse restriction to common refinements

Source: blueprint common-stratification clause (2).
(blueprint: new-det-lem-coefficient-heart-common-stratification-lisse).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The pullback of module objects over `Λ` is the pullback of underlying sheaves followed by
restriction along the inverse of the comparison of coefficient rings. -/
private noncomputable def CondensedRing.normalizedPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X) :
    CondensedRing.upperStar Λ f ≅
      (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X) ⋙
        Mod.comap (inv (condensedPullbackHom Λ f)) :=
  Functor.isoWhiskerLeft _ (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))

private theorem lisse_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLisseCoefficientModule Λ M) :
    IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ f).obj M) := by
  exact (isLocallyFree_iff _).1 (IsLocallyFree.upperStar Λ f ((isLocallyFree_iff M).2 hM))

private theorem finitePresentation_fromPoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (hP : Mod.IsFinitelyPresented Λ P) :
    Mod.IsFinitelyPresented (condensedRingObj Λ X) (((upperStarFromPoint X).mapMod Λ).obj P) := by
  let F := (upperStarFromPoint X).mapMod Λ
  let e : F.obj (Mod.regular Λ) ≅ Mod.regular (condensedRingObj Λ X) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  obtain ⟨n, m, f, ⟨i⟩⟩ := hP
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let en (n : ℕ) : F.obj (Mod.finiteFree Λ n) ≅
      Mod.finiteFree (condensedRingObj Λ X) n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫ biproduct.mapIso (fun _ ↦ e)
  let f' := (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

private theorem constantModel_lfp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : HasFiniteConstantLocalModel Λ X M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hC a
  have h := fp_of_iso (finitePresentation_fromPoint Λ (C.X a) P hP) e.symm
  have h' := fp_of_iso h ((CondensedRing.normalizedPullbackIso Λ (C.f a)).app M)
  exact fp_of_comap (inv (condensedPullbackHom Λ (C.f a))) h'

private theorem lisse_of_raw_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ a,
      Mod.IsFree ((upperStar Ab.{u + 1} (C.f a)).obj (condensedRingObj Λ X))
        (((upperStar Ab.{u + 1} (C.f a)).mapMod (condensedRingObj Λ X)).obj M)) :
    IsLisseCoefficientModule Λ M := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun a ↦ (CondensedRing.isFree_mapMod_iff Λ (C.f a) M).1 (hC a)⟩

private theorem lfp_lisse
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) X))
    (hp : IsLocallyFinitelyPresented (condensedRingObj (coefficientHeartRingObj Λ) X) M) :
    IsLisseCoefficientModule (coefficientHeartRingObj Λ) M := by
  apply lisse_of_raw_free
  rcases hΛ with ⟨E, hE, rfl⟩ | rfl
  · exact finite_lf ℓ ⟨E, hE⟩ X M hp
  · exact algcl_lf ℓ X M hp

attribute [local irreducible] IsLisseCoefficientModule
  CondensedRing.upperStarComp
  CondensedRing.upperStarLowerStarAdjunction

private theorem lfp_range_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S T : Scheme.{u}}
    (i : S ⟶ X) [IsImmersion i] (j : T ⟶ X)
    (hji : Set.range j ⊆ Set.range i)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsLocallyFinitelyPresented (condensedRingObj Λ S)
      ((CondensedRing.upperStar Λ i).obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj Λ T)
      ((CondensedRing.upperStar Λ j).obj M) := by
  have hraw := lfp_of_comap (inv (condensedPullbackHom Λ i))
    (lfp_of_iso hM ((CondensedRing.normalizedPullbackIso Λ i).app M))
  have ht := localFinitePresentation_upperStar_of_range_subset
    i j hji (condensedRingObj Λ X) M hraw
  exact lfp_of_iso (lfp_comap (inv (condensedPullbackHom Λ j)) ht)
    ((CondensedRing.normalizedPullbackIso Λ j).app M).symm

private theorem lisse_on_refined_stratum
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] {X S T : Scheme.{u}}
    [IsNoetherian X]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (i : S ⟶ X) [IsImmersion i] (j : T ⟶ X) [IsImmersion j]
    (hji : Set.range j ⊆ Set.range i)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (coefficientHeartRingObj Λ) X))
    (hM : HasFiniteConstantLocalModel (coefficientHeartRingObj Λ) S
      ((CondensedRing.upperStar (coefficientHeartRingObj Λ) i).obj M)) :
    IsLisseCoefficientModule (coefficientHeartRingObj Λ)
      ((CondensedRing.upperStar (coefficientHeartRingObj Λ) j).obj M) := by
  have : TopologicalSpace.NoetherianSpace T :=
    j.isEmbedding.isInducing.noetherianSpace
  exact lfp_lisse ℓ Λ T hΛ _
    (lfp_range_restriction (coefficientHeartRingObj Λ) i j hji M
      (constantModel_lfp (coefficientHeartRingObj Λ) S _ hM))

/-- Lisse modules restrict to every locally closed refinement, including its given scheme
structure. Source: blueprint det-lem-coefficient-heart-common-stratification, steps (5)--(6),
and the finite-presentation pullback and immersion-range arguments of
`CondensedConstructibleSerre.lean` and `ProEtaleModuleLfpImmersionTransport.lean`.
(blueprint: new-det-lem-coefficient-heart-common-stratification-lisse).

Proof: base change a trivializing cover to prove that lisse modules stay lisse under any
scheme pullback. A finite constant local model is locally finitely presented: inverse
image from the point preserves regular modules, finite direct sums and cokernels, so it
preserves a finite presentation. Transport the presentation across the model isomorphism
and the normalized coefficient-pullback comparison.

For a refined stratum T with image contained in an adapted stratum S, undo the
normalized coefficient comparison to get local finite presentation over the raw
inverse-image ring on S. Apply the existing immersion-range transfer theorem. It
forms T times_X S and reflects local finite presentation through the surjective
closed immersion to T. Normalize the coefficient comparison on T again. This gives
local finite presentation of the actual restriction, without a factorization T to S.

The underlying space of T is Noetherian because its immersion into X is an embedding.
For each of the finite-subfield and algebraic-closure coefficient cases, the existing
local-triviality lemma makes every locally finitely presented module on T pro-etale
locally finite free. Transport its raw pullbacks to normalized coefficient pullbacks.
This is the required lisse cover. Empty schemes and rank zero are included by the
existing finite-presentation and covering lemmas.
-/
theorem coefficientHeart_commonStratification_lisse
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)] (X : Scheme.{u}) [IsNoetherian X]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ) :
    (∀ (S T : Scheme.{u}) (i : S ⟶ X), IsImmersion i →
      ∀ j : T ⟶ S, IsImmersion j →
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj
        (coefficientHeartRingObj Λ) S),
        IsLisseCoefficientModule (coefficientHeartRingObj Λ) M →
          IsLisseCoefficientModule (coefficientHeartRingObj Λ) ((CondensedRing.upperStar
            (coefficientHeartRingObj Λ) j).obj M)) ∧
    (∀ (P R : X.FiniteLocallyClosedStratification)
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj
        (coefficientHeartRingObj Λ) X)),
      (∀ a : Fin P.n,
        HasFiniteConstantLocalModel (coefficientHeartRingObj Λ) (P.domain a)
          ((CondensedRing.upperStar (coefficientHeartRingObj Λ) (P.immersion a)).obj M)) →
      (∀ a : Fin R.n, ∃ b : Fin P.n, R.stratum a ⊆ P.stratum b) →
        ∀ a : Fin R.n,
          IsLisseCoefficientModule (coefficientHeartRingObj Λ) ((CondensedRing.upperStar
            (coefficientHeartRingObj Λ) (R.immersion a)).obj M)) := by
  constructor
  · intro S T i hi j hj M hM
    exact lisse_pullback _ j M hM
  · intro P R M hM hR a
    obtain ⟨b, hb⟩ := hR a
    have : IsImmersion (P.immersion b) := P.isImmersion b
    have : IsImmersion (R.immersion a) := R.isImmersion a
    apply lisse_on_refined_stratum ℓ Λ hΛ (P.immersion b) (R.immersion a) _ M (hM b)
    simpa only [P.range_immersion, R.range_immersion] using hb

end AlgebraicGeometry.ProEtale
