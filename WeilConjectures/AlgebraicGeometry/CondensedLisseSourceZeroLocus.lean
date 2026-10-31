/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleObjects
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all WeilConjectures.AlgebraicGeometry.CoefficientHeartClosure
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
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
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
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
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
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
import WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import all WeilConjectures.AlgebraicGeometry.UnboundedLocalizingPullback
import all WeilConjectures.AlgebraicGeometry.CondensedLisseRankLoci
import WeilConjectures.AlgebraicGeometry.GeometricSpecializationStrictLocalLift
import all WeilConjectures.AlgebraicGeometry.CoefficientHeartCommonStratification
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughImmersion
import WeilConjectures.AlgebraicGeometry.CondensedFibreSpecialization
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet

/-! # Zero locus of a morphism from a lisse condensed module

Source: Bhatt--Scholze, The pro-etale topology for schemes, Section 6.8,
Proposition 6.8.4, Corollary 6.8.5, Proposition 6.8.14 and Remark 6.8.15;
latest blueprint sk-l-dl-a1-endpoints.proof.md, first two sentences.
The zero-locus consequence is agent-formulated; Stacks 04FR and 04FT give the
analogous discrete etale result (blueprint: lem-a1-condensed-lisse-source-zero-locus).

The coefficients are the finite-subextension-valued condensed algebraic closure.
Fibres and open restrictions use the actual coefficient-module inverse image.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp
  CondensedRing.upperStarId CondensedQbarGeometricEvaluation.fieldFiber

/-- The locus where the actual module pullback of a morphism vanishes at every
algebraically closed geometric point over the given point. Geometric points are in
the universe of the small pro-etale site, with their image read by SpecToEquivOfField.
Source: the defining formula for W(u) in the agent-formulated zero-locus consequence
of Bhatt--Scholze Section 6.8
(blueprint: lem-a1-condensed-lisse-source-zero-locus). -/
def condensedMorphismZeroLocus (ℓ : ℕ) [Fact ℓ.Prime] {T : Scheme.{u}}
    {L M : condensedModuleCategory T (Mon.mk (Profinite.padicAlgClRingObj ℓ))}
    (f : L ⟶ M) : Set T :=
  {x | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ T),
    (Scheme.SpecToEquivOfField Ω T b).1 = x →
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).map f = 0}

private lemma zeroLocus_lisse_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    {L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hL : IsLisseCoefficientModule Λ L) : IsConstantModelConstructible Λ X L := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  exact ⟨Scheme.Stratification.trivial X, fun _ ↦
    pullback_finiteConstantLocalModel Λ (𝟙 X) L (heart_free_model Λ L hL)⟩

private lemma zeroLocus_comp_map_eq_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    {L M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)}
    (f : L ⟶ M) :
    (CondensedRing.upperStar Λ (g ≫ h)).map f = 0 ↔
      (CondensedRing.upperStar Λ g).map ((CondensedRing.upperStar Λ h).map f) = 0 := by
  let e := CondensedRing.upperStarComp Λ g h
  constructor
  · intro hf
    apply (cancel_epi (e.hom.app L)).mp
    simpa only [Functor.comp_map, hf, zero_comp, comp_zero] using (e.hom.naturality f).symm
  · intro hf
    apply (cancel_mono (e.hom.app M)).mp
    simpa only [Functor.comp_map, hf, zero_comp, comp_zero] using e.hom.naturality f

private lemma zeroLocus_open_of_constructible_generalization
    {X : Scheme.{u}} {C : Set X} (hC : Topology.IsConstructible C)
    (hgen : StableUnderGeneralization C) : IsOpen C := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨q, hq⟩ := X.affineCover.covers p
  let j := X.affineCover.f (X.affineCover.idx p)
  have hpre : IsOpen (j ⁻¹' C) :=
    PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible
      (hgen.preimage j.continuous)
      (hC.isLocallyConstructible.preimage_of_isOpenEmbedding j.isOpenEmbedding).isConstructible
  have hopen : IsOpen (j '' (j ⁻¹' C)) := j.isOpenEmbedding.isOpenMap _ hpre
  have hmem : p ∈ j '' (j ⁻¹' C) := by
    refine ⟨q, ?_, hq⟩
    change j q ∈ C
    rw [show j q = p from hq]
    exact hp
  exact Filter.mem_of_superset (hopen.mem_nhds hmem) (Set.image_preimage_subset j C)

private lemma zeroLocus_coefficient_isField (ℓ : ℕ) [Fact ℓ.Prime] :
    IsField (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) := by
  have h10 : (1 : MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) ≠ 0 := by
    intro h
    apply Profinite.PadicAlgCl.one_ne_zero_end_regular.{u} ℓ
    simpa only [map_one, map_zero] using congrArg Mod.regularEndRingHom h
  refine ⟨⟨1, 0, h10⟩, mul_comm, ?_⟩
  intro s hs
  obtain ⟨c, rfl⟩ := Profinite.PadicAlgCl.constRingHom_surjective ℓ s
  have hc : c ≠ 0 := by
    intro h
    apply hs
    rw [h, map_zero]
  exact ⟨Profinite.PadicAlgCl.constRingHom ℓ c⁻¹,
    by rw [← map_mul, mul_inv_cancel₀ hc, map_one]⟩

private lemma zeroLocus_free_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : IsZero (Mod.finiteFree (condensedRingObj Λ X) 0) := by
  rw [IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext
  intro i
  exact Fin.elim0 i

private lemma zeroLocus_isZero_of_free_rank
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    {N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (n : ℕ) (e : N ≅ Mod.finiteFree (condensedRingObj Λ X) n) (hn : n = 0) :
    IsZero N := by
  subst n
  exact (zeroLocus_free_zero Λ X).of_iso e

private lemma zeroLocus_eval_free_rank
    (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω)))}
    (n : ℕ) (e : N ≅ Mod.finiteFree
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))) n) :
    IsZero ((CondensedQbarGeometricEvaluation.fieldFiber Ω ℓ).obj N) ↔ n = 0 := by
  let F := CondensedQbarGeometricEvaluation.fieldFiber Ω ℓ
  let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω))
  let eV : F.obj N ≅ ModuleCat.of (PadicAlgCl ℓ) (Fin n → F.obj (Mod.regular A)) :=
    F.mapIso e ≪≫ F.mapBiproduct (fun _ : Fin n ↦ Mod.regular A) ≪≫
      ModuleCat.biproductIsoPi (fun _ : Fin n ↦ F.obj (Mod.regular A))
  let d : F.obj N ≃ₗ[PadicAlgCl ℓ] (Fin n → PadicAlgCl ℓ) :=
    eV.toLinearEquiv.trans (LinearEquiv.piCongrRight fun _ : Fin n ↦
      CondensedQbarGeometricEvaluation.fieldRegularCoordinates Ω ℓ)
  constructor
  · intro hz
    have : Subsingleton (F.obj N) := ModuleCat.subsingleton_of_isZero hz
    have hd : (fun _ : Fin n ↦ (1 : PadicAlgCl ℓ)) = (fun _ : Fin n ↦ 0) :=
      (d.surjective.subsingleton).elim _ _
    by_contra hn
    exact one_ne_zero (congrFun hd ⟨0, Nat.pos_of_ne_zero hn⟩)
  · rintro rfl
    exact F.map_isZero ((zeroLocus_free_zero (Profinite.padicAlgClRingObj ℓ)
      (Spec (.of Ω))).of_iso e)

private lemma zeroLocus_image_zero_iff
    {C : Type*} [Category C] [Abelian C] {L M : C} (f : L ⟶ M) :
    IsZero (Abelian.image f) ↔ f = 0 := by
  constructor
  · intro hz
    rw [← Abelian.image.fac f, hz.eq_of_tgt (Abelian.factorThruImage f) 0, zero_comp]
  · rintro rfl
    exact isZero_kernel_of_mono _

private lemma zeroLocus_image_property
    {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    {L M : C} (f : L ⟶ M) (hL : P L) (hM : P M) : P (Abelian.image f) := by
  exact P.prop_kernel (cokernel.π f) hM (P.prop_cokernel f hL hM)

private lemma zeroLocus_map_zero_iff_image
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {L M : C} (f : L ⟶ M) : F.map f = 0 ↔ IsZero (F.obj (Abelian.image f)) := by
  exact (zeroLocus_image_zero_iff (F.map f)).symm.trans
    (Abelian.PreservesImage.iso F f).isZero_iff.symm

private lemma zeroLocus_immersion_noetherian {X Y : Scheme.{u}} [IsNoetherian X]
    (i : Y ⟶ X) [IsImmersion i] : IsNoetherian Y := by
  have : TopologicalSpace.NoetherianSpace Y := i.isEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian i
  exact ⟨⟩

private lemma zeroLocus_lisse_support_aux
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (hField : IsField (MonObj.Γ R))
    (F : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
        (condensedRingObj R (Spec (.of K))) ⥤ ModuleCat.{u + 1} (PadicAlgCl ℓ))
    (hFzero : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (A : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
        (condensedRingObj R (Spec (.of K)))), IsZero A → IsZero ((F K).obj A))
    (hFree : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (A : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
        (condensedRingObj R (Spec (.of K)))) (n : ℕ)
      (_e : A ≅ Mod.finiteFree (condensedRingObj R (Spec (.of K))) n),
      IsZero ((F K).obj A) ↔ n = 0)
    (X : Scheme.{u}) [IsNoetherian X]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X))
    (hN : IsLisseCoefficientModule R N) :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧
      IsZero ((CondensedRing.upperStar R U.ι).obj N) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ X),
        (IsZero ((CondensedRing.upperStar R b).obj N) ↔
          (Scheme.SpecToEquivOfField Ω X b).1 ∈ U) ∧
        (IsZero ((F Ω).obj
          ((CondensedRing.upperStar R b).obj N)) ↔
          (Scheme.SpecToEquivOfField Ω X b).1 ∈ U) := by
  obtain ⟨r, hfib, U, heq, hclosed, hzero⟩ :=
    zeroLocusRankDataOfCover R hField X N hN
  refine ⟨U, hclosed, hzero, ?_⟩
  intro Ω _ _ b
  obtain ⟨e⟩ := hfib Ω b
  have hEval := hFree Ω _ _ e
  have hrank : r (Scheme.SpecToEquivOfField Ω X b).1 = 0 ↔
      (Scheme.SpecToEquivOfField Ω X b).1 ∈ U := by
    change _ ↔ (Scheme.SpecToEquivOfField Ω X b).1 ∈ (U : Set X)
    rw [heq]
    rfl
  refine ⟨⟨?_, ?_⟩, hEval.trans hrank⟩
  · intro hz
    exact hrank.mp (hEval.mp
      (hFzero Ω _ hz))
  · intro hb
    exact zeroLocus_isZero_of_free_rank R
      (Spec (.of Ω)) _ e (hrank.mpr hb)


private lemma zeroLocus_lisse_support
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) N) :
    ∃ U : X.Opens, IsClosed (U : Set X) ∧
      IsZero ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) U.ι).obj N) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ X),
        (IsZero ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj N) ↔
          (Scheme.SpecToEquivOfField Ω X b).1 ∈ U) ∧
        (IsZero ((CondensedQbarGeometricEvaluation.fieldFiber Ω ℓ).obj
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj N)) ↔
          (Scheme.SpecToEquivOfField Ω X b).1 ∈ U) := by
  exact zeroLocus_lisse_support_aux ℓ (Profinite.padicAlgClRingObj ℓ)
    (zeroLocus_coefficient_isField ℓ)
    (fun K _ _ ↦ CondensedQbarGeometricEvaluation.fieldFiber K ℓ)
    (fun K _ _ A hA ↦ (CondensedQbarGeometricEvaluation.fieldFiber K ℓ).map_isZero hA)
    (fun K _ _ A n e ↦ zeroLocus_eval_free_rank ℓ K n e) X N hN

private lemma zeroLocus_top_pullback_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hN : IsZero ((CondensedRing.upperStar Λ (⊤ : X.Opens).ι).obj N)) : IsZero N := by
  let e : (CondensedRing.upperStar Λ X.topIso.inv).obj
      ((CondensedRing.upperStar Λ (⊤ : X.Opens).ι).obj N) ≅ N :=
    ((CondensedRing.upperStarComp Λ X.topIso.inv (⊤ : X.Opens).ι).app N).symm ≪≫
      eqToIso (by rw [Scheme.toIso_inv_ι]) ≪≫ (CondensedRing.upperStarId Λ X).app N
  exact ((CondensedRing.upperStar Λ X.topIso.inv).map_isZero hN).of_iso e.symm

private lemma zeroLocus_lisse_zero
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) N)
    (hzero : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ X),
      IsZero ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj N)) :
    IsZero N := by
  obtain ⟨U, _, hU, hb⟩ := zeroLocus_lisse_support ℓ X N hN
  have htop : U = ⊤ := by
    apply top_unique
    intro x hx
    let Ω := AlgebraicClosure (X.residueField x)
    let b : Spec (.of Ω) ⟶ X := (Scheme.SpecToEquivOfField Ω X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) Ω)⟩
    have hx' : (Scheme.SpecToEquivOfField Ω X b).1 = x :=
      congrArg Sigma.fst ((Scheme.SpecToEquivOfField Ω X).apply_symm_apply _)
    simpa only [hx'] using ((hb Ω b).1.mp (hzero Ω b))
  rw [htop] at hU
  exact zeroLocus_top_pullback_zero (Profinite.padicAlgClRingObj ℓ) X N hU

-- Use the generic coefficient-heart characterization at the actual coefficient ring.
private lemma zeroLocus_constructible_strata
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X N ↔
      ∃ S : X.FiniteLocallyClosedStratification, ∀ i : Fin S.n,
        IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ)
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (S.immersion i)).obj N) := by
  refine heart_stratified_lisse (Profinite.padicAlgClRingObj ℓ) (fun Y _ M ↦ ?_) X N
  exact ⟨heart_lfp_of_lisse (Profinite.padicAlgClRingObj ℓ), fun h ↦
    heart_lisse_of_free (Profinite.padicAlgClRingObj ℓ) (algcl_lf ℓ Y M h)⟩

private lemma zeroLocus_support_of_strata
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (F : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Mod (Sheaf (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1})
        (condensedRingObj R (Spec (.of K))) ⥤ ModuleCat.{u + 1} (PadicAlgCl ℓ))
    (X : Scheme.{u}) [IsNoetherian X]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (S : X.FiniteLocallyClosedStratification) (U : ∀ i : Fin S.n, (S.domain i).Opens)
    (hpoint : ∀ (i : Fin S.n) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (.of Ω) ⟶ S.domain i),
      (IsZero ((CondensedRing.upperStar R b).obj
        ((CondensedRing.upperStar R (S.immersion i)).obj N)) ↔
        (Scheme.SpecToEquivOfField Ω (S.domain i) b).1 ∈ U i) ∧
      (IsZero ((F Ω).obj ((CondensedRing.upperStar R b).obj
        ((CondensedRing.upperStar R (S.immersion i)).obj N))) ↔
        (Scheme.SpecToEquivOfField Ω (S.domain i) b).1 ∈ U i)) :
    ∃ C : Set X, Topology.IsConstructible C ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ X),
        (IsZero ((CondensedRing.upperStar R b).obj N) ↔
          (Scheme.SpecToEquivOfField Ω X b).1 ∈ C) ∧
        (IsZero ((F Ω).obj ((CondensedRing.upperStar R b).obj N)) ↔
          (Scheme.SpecToEquivOfField Ω X b).1 ∈ C) := by
  classical
  have (i : Fin S.n) : IsImmersion (S.immersion i) := S.isImmersion i
  let C : Set X := ⋃ i, S.immersion i '' (U i : Set (S.domain i))
  have hcons : Topology.IsConstructible C := by
    apply Topology.IsConstructible.iUnion
    intro i
    exact ((U i).isOpen.isLocallyClosed.image (S.immersion i).isEmbedding.isInducing
      (S.immersion i).isLocallyClosed_range).isConstructible_of_noetherianSpace
  have hmem (i : Fin S.n) (z : S.domain i) : S.immersion i z ∈ C ↔ z ∈ U i := by
    constructor
    · intro hz
      obtain ⟨j, y, hy, heq⟩ := Set.mem_iUnion.mp hz
      have hij : i = j := by
        by_contra hij
        apply Set.disjoint_left.mp (S.pairwise_disjoint_stratum hij)
          (show S.immersion i z ∈ S.stratum i by
            rw [← S.range_immersion i]; exact ⟨z, rfl⟩)
        rw [← S.range_immersion j]
        exact ⟨y, heq⟩
      subst j
      exact (S.immersion i).isEmbedding.injective heq ▸ hy
    · intro hz
      exact Set.mem_iUnion.mpr ⟨i, z, hz, rfl⟩
  refine ⟨C, hcons, ?_⟩
  intro Ω _ _ b
  have hx : (Scheme.SpecToEquivOfField Ω X b).1 ∈ ⋃ i, S.stratum i := by
    rw [S.iUnion_stratum_eq_univ]
    exact Set.mem_univ _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  rw [← S.range_immersion i] at hi
  obtain ⟨z, hz⟩ := hi
  have hz' : b default = S.immersion i z := by
    rw [show (default : Spec (.of Ω)) = IsLocalRing.closedPoint Ω from Subsingleton.elim _ _]
    exact hz.symm
  obtain ⟨⟨c, hc, _⟩, _⟩ :=
    (fieldPoint_factorsThrough_immersion (S.immersion i) z).2 Ω b hz'
  subst b
  let e := (CondensedRing.upperStarComp R
    c (S.immersion i)).app N
  have hzmem :
      (Scheme.SpecToEquivOfField Ω X (c ≫ S.immersion i)).1 ∈ C ↔
        (Scheme.SpecToEquivOfField Ω (S.domain i) c).1 ∈ U i :=
    hmem i (Scheme.SpecToEquivOfField Ω (S.domain i) c).1
  constructor
  · exact e.isZero_iff.trans ((hpoint i Ω c).1.trans hzmem.symm)
  · exact ((F Ω).mapIso e).isZero_iff.trans
      ((hpoint i Ω c).2.trans hzmem.symm)

private lemma zeroLocus_support_on_chosen_strata
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (S : X.FiniteLocallyClosedStratification)
    (U : ∀ i : Fin S.n, (S.domain i).Opens)
    (hpoint : ∀ (i : Fin S.n) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (b : Spec (.of Ω) ⟶ S.domain i),
      (IsZero ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (S.immersion i)).obj N)) ↔
        (Scheme.SpecToEquivOfField Ω (S.domain i) b).1 ∈ U i) ∧
      (IsZero ((CondensedQbarGeometricEvaluation.fieldFiber Ω ℓ).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
            (S.immersion i)).obj N))) ↔
        (Scheme.SpecToEquivOfField Ω (S.domain i) b).1 ∈ U i)) :
    ∃ C : Set X, Topology.IsConstructible C ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ X),
        (IsZero ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj N) ↔
          (Scheme.SpecToEquivOfField Ω X b).1 ∈ C) ∧
        (IsZero ((CondensedQbarGeometricEvaluation.fieldFiber Ω ℓ).obj
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj N)) ↔
          (Scheme.SpecToEquivOfField Ω X b).1 ∈ C) := by
  exact zeroLocus_support_of_strata ℓ (Profinite.padicAlgClRingObj ℓ)
    (fun K _ _ ↦ CondensedQbarGeometricEvaluation.fieldFiber K ℓ) X N S U hpoint

private lemma zeroLocus_select_data
    {I : Type*} {A : I → Type*} {P Q R : ∀ i, A i → Prop}
    (h : ∀ i, ∃ a, P i a ∧ Q i a ∧ R i a) :
    ∃ a : ∀ i, A i, ∀ i, R i (a i) := by
  classical
  choose a hP hQ hR using h
  exact ⟨a, hR⟩

private lemma zeroLocus_constructible_support
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hN : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X N) :
    ∃ C : Set X, Topology.IsConstructible C ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ X),
        (IsZero ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj N) ↔
          (Scheme.SpecToEquivOfField Ω X b).1 ∈ C) ∧
        (IsZero ((CondensedQbarGeometricEvaluation.fieldFiber Ω ℓ).obj
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj N)) ↔
          (Scheme.SpecToEquivOfField Ω X b).1 ∈ C) := by
  classical
  obtain ⟨S, hS⟩ := (zeroLocus_constructible_strata ℓ X N).mp hN
  have (i : Fin S.n) : IsImmersion (S.immersion i) := S.isImmersion i
  have (i : Fin S.n) : IsNoetherian (S.domain i) :=
    zeroLocus_immersion_noetherian (S.immersion i)
  have hsupp (i : Fin S.n) := zeroLocus_lisse_support ℓ (S.domain i)
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) (S.immersion i)).obj N) (hS i)
  obtain ⟨U, hpoint⟩ := zeroLocus_select_data hsupp
  exact zeroLocus_support_on_chosen_strata ℓ X N S U hpoint

private lemma zeroLocus_constructible_image
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    {L M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)}
    (hL : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X L)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X M)
    (f : L ⟶ M) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X (Abelian.image f) := by
  let P : ObjectProperty _ := IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X
  have hcl := (coefficientHeart_closure ℓ (Profinite.padicAlgClCondensedRing ℓ)
    (Or.inr rfl)).2 X
  have : P.IsClosedUnderKernels := hcl.1
  have : P.IsClosedUnderCokernels := hcl.2.1
  exact zeroLocus_image_property P f hL hM

private lemma zeroLocus_zero_on_lisse_strata
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [IsNoetherian X]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hstrat : IsConstantModelConstructible Λ X N →
      ∃ S : X.FiniteLocallyClosedStratification, ∀ i : Fin S.n,
        IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ (S.immersion i)).obj N))
    (hN : IsConstantModelConstructible Λ X N)
    (hLisseZero : ∀ (Y : Scheme.{u}) [IsNoetherian Y]
      (A : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLisseCoefficientModule Λ A →
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ Y),
        IsZero ((CondensedRing.upperStar Λ b).obj A)) → IsZero A)
    (hzero : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ X),
      IsZero ((CondensedRing.upperStar Λ b).obj N)) : IsZero N := by
  obtain ⟨S, hS⟩ := hstrat hN
  have (i : Fin S.n) : IsImmersion (S.immersion i) := S.isImmersion i
  apply coefficientModuleZero Λ S N
  intro i
  have : IsNoetherian (S.domain i) := zeroLocus_immersion_noetherian (S.immersion i)
  apply hLisseZero (S.domain i) _ (hS i)
  intro K _ _ b
  exact (hzero K (b ≫ S.immersion i)).of_iso
    ((CondensedRing.upperStarComp Λ b (S.immersion i)).app N).symm

private lemma zeroLocus_constructible_zero
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hN : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X N)
    (hzero : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ X),
      IsZero ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).obj N)) :
    IsZero N := by
  exact zeroLocus_zero_on_lisse_strata (Profinite.padicAlgClRingObj ℓ) X N
    (fun h ↦ (zeroLocus_constructible_strata ℓ X N).mp h) hN
    (fun Y _ A hA hz ↦ zeroLocus_lisse_zero ℓ Y A hA hz) hzero

private lemma zeroLocus_constructible_open
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hN : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X N)
    (V : X.Opens) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) V
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) V.ι).obj N) := by
  have : IsNoetherian V := zeroLocus_immersion_noetherian V.ι
  exact pullback_constructible (Profinite.padicAlgClRingObj ℓ) V.ι N hN

private lemma zeroLocus_constructible_map_zero
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    {L M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)}
    (hL : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X L)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X M)
    (f : L ⟶ M)
    (hzero : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ X),
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).map f = 0) : f = 0 := by
  apply (zeroLocus_image_zero_iff f).mp
  apply zeroLocus_constructible_zero ℓ X _ (zeroLocus_constructible_image ℓ X hL hM f)
  intro Ω _ _ b
  exact (zeroLocus_map_zero_iff_image
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b) f).mp (hzero Ω b)

private lemma zeroLocus_fieldFiber_limits
    (K : Type u) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] :
    PreservesFiniteLimits (CondensedQbarGeometricEvaluation.fieldFiber K ℓ) := by
  let e : PadicAlgCl ℓ ≃+* ULift.{u + 1} (PadicAlgCl ℓ) := ULift.ringEquiv.symm
  let G : ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl ℓ)) ⥤
      ModuleCat.{u + 1} (PadicAlgCl ℓ) := ModuleCat.restrictScalars e.toRingHom
  have : G.IsRightAdjoint :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction.isRightAdjoint
  unfold CondensedQbarGeometricEvaluation.fieldFiber
  infer_instance

private lemma zeroLocus_map_zero_of_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (g h : X ⟶ Y) (heq : g = h)
    {L M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (f : L ⟶ M) (hf : (CondensedRing.upperStar Λ g).map f = 0) :
    (CondensedRing.upperStar Λ h).map f = 0 := by
  subst h
  exact hf

private lemma zeroLocus_functor_map_zero
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {L M : C} (f : L ⟶ M) (hf : f = 0) :
    F.map f = 0 := by
  subst f
  exact F.map_zero L M

private lemma zeroLocus_cancel_square
    {C : Type*} [Category C] [HasZeroMorphisms C] {A B C' D : C}
    (e : A ⟶ B) [Epi e] (g : B ⟶ D) (h : A ⟶ C') (d : C' ⟶ D)
    (hnat : e ≫ g = h ≫ d) (hh : h = 0) : g = 0 := by
  apply (cancel_epi e).mp
  simpa only [hh, zero_comp, comp_zero] using hnat

private lemma zeroLocus_specialization_zero
    (k : Type u) [Field k] [IsAlgClosed k]
    (p ℓ : ℕ) [Fact p.Prime] [CharP k p] [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    {L M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T)}
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) L)
    (hLC : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T L)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T M)
    (f : L ⟶ M) (Ωs : Type u) [Field Ωs] [IsAlgClosed Ωs]
    (b : Spec (.of Ωs) ⟶ T) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (d : Spec (.of Ω) ⟶ Scheme.strictHenselizationScheme b)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).map f = 0) :
    (CondensedQbarGeometricEvaluation.fieldFiber Ω ℓ).map
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
        (d ≫ Scheme.strictHenselizationStructuralMap b)).map f) = 0 := by
  obtain ⟨sp, hsp, hnat⟩ := condensed_fibre_specialization k p ℓ hℓp T Ωs b Ω d
  have : IsIso (sp.app ⟨L, hLC⟩) := hsp ⟨L, hLC⟩ hL
  exact zeroLocus_cancel_square (sp.app ⟨L, hLC⟩) _ _ (sp.app ⟨M, hM⟩)
    (hnat ⟨L, hLC⟩ ⟨M, hM⟩ (ObjectProperty.homMk f))
    (zeroLocus_functor_map_zero (CondensedQbarGeometricEvaluation.fieldFiber Ωs ℓ) _ hf)

private lemma zeroLocus_geometric_generalization
    (T : Scheme.{u})
    (P : ∀ (K : Type u) [Field K] [IsAlgClosed K], (Spec (.of K) ⟶ T) → Prop)
    (hP : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ T)
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (d : Spec (.of Ω) ⟶ Scheme.strictHenselizationScheme b),
      P K b → P Ω (d ≫ Scheme.strictHenselizationStructuralMap b)) :
    StableUnderGeneralization {x : T |
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ T),
        (Scheme.SpecToEquivOfField K T b).1 = x → P K b} := by
  intro s t hts hs Ω _ _ c hc
  let Ωs := AlgebraicClosure (T.residueField s)
  let b : Spec (.of Ωs) ⟶ T := (Scheme.SpecToEquivOfField Ωs T).symm
    ⟨s, CommRingCat.ofHom (algebraMap (T.residueField s) Ωs)⟩
  have hb : (Scheme.SpecToEquivOfField Ωs T b).1 = s :=
    congrArg Sigma.fst ((Scheme.SpecToEquivOfField Ωs T).apply_symm_apply _)
  obtain ⟨d, hd⟩ := Scheme.exists_geometricPoint_strictHenselization_lift t s hts c b hc hb
  rw [← hd]
  exact hP Ωs b Ω d (hs Ωs b hb)

private lemma zeroLocus_generalization
    (k : Type u) [Field k] [IsAlgClosed k]
    (p ℓ : ℕ) [Fact p.Prime] [CharP k p] [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    {L M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) T)}
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) L)
    (hLC : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T L)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T M)
    (f : L ⟶ M)
    (hreflect : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ T),
      (CondensedQbarGeometricEvaluation.fieldFiber Ω ℓ).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).map f) = 0 →
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).map f = 0) :
    StableUnderGeneralization (condensedMorphismZeroLocus ℓ f) := by
  let : T.Over (Spec (.of k)) := ⟨a⟩
  have : LocallyOfFiniteType (T ↘ Spec (.of k)) := ‹LocallyOfFiniteType a›
  have : QuasiCompact (T ↘ Spec (.of k)) := ‹QuasiCompact a›
  have : IsSeparated (T ↘ Spec (.of k)) := ‹IsSeparated a›
  apply zeroLocus_geometric_generalization T
    (fun K _ _ b ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).map f = 0)
  intro Ωs _ _ b Ω _ _ d hs
  exact hreflect Ω (d ≫ Scheme.strictHenselizationStructuralMap b)
    (zeroLocus_specialization_zero k p ℓ hℓp T hL hLC hM f Ωs b Ω d hs)

/-- The zero locus of a morphism from a lisse module to a constructible module is
Zariski open, detects vanishing on every open subscheme, and can be tested at any
one algebraically closed geometric point over each point. The open W supplied here
has exactly the carrier of condensedMorphismZeroLocus; its bundled openness expresses
the first assertion. No properness, smoothness or finite-field descent is assumed.

Source: agent-formulated consequence of Bhatt--Scholze Section 6.8,
Proposition 6.8.4, Corollary 6.8.5, Proposition 6.8.14 and Remark 6.8.15;
latest blueprint sk-l-dl-a1-endpoints.proof.md, first two sentences
(blueprint: lem-a1-condensed-lisse-source-zero-locus).

Proof, following the node's five steps:
1. Finite type over the field makes T Noetherian. A lisse module has finite constant
local models and hence is constructible on the trivial stratification. Kernel and
cokernel closure make I = image f constructible. Choose finitely many locally closed
lisse strata. Each stratum is Noetherian: its immersion is locally of finite type,
and its underlying space embeds in the Noetherian space T. Constant scalar sections
surject onto the terminal coefficient ring, whose identity is nonzero, so this ring
is a field. The lisse rank theorem supplies clopen rank-zero pieces on the strata.
2. A field point in a stratum's image lifts through its immersion by
lem-weil-pbc-field-point-factors-through-immersion. The pullback compositor and
lisse rank theorem identify the pulled-back image with a finite free module of
rank r. The constructed field evaluation preserves finite biproducts and sends the
regular module to the scalar field, so its value is Q^r. Both actual-module and
evaluated vanishing are equivalent to r = 0. The union C of the rank-zero pieces'
images is constructible; disjointness of strata identifies its intersection with
each stratum. Exactness of pullback and field evaluation computes the images of
the pulled-back and evaluated maps. Thus either map vanishes precisely over C.
Choosing an algebraic closure of each residue field gives C = condensedMorphismZeroLocus.
3. Lift a generalization through the strict henselization of a geometric point over
the specialization. The naturality square of condensed_fibre_specialization makes
the evaluated general-fibre map zero: the special-fibre map vanishes and the
specialization map on the lisse source is invertible. Step 2 gives actual-module
vanishing. The zero locus is therefore stable under generalization.
4. The constructible, generalization-stable locus is open on every affine chart by
the prime-spectrum criterion. The open chart embeddings give openness on T.
5. Geometric pullbacks detect zero constructible modules: on each lisse stratum,
zero fibres force the rank-zero open to contain every point, hence the restriction
is zero. Stratum detection then gives zero on the whole scheme. Apply this to
constructible images to detect zero morphisms. For an open V, constructibility
under pullback makes L|V and M|V constructible, so vanishing of all their geometric
fibre maps gives f|V = 0. Conversely every field point over V factors through its
open immersion, and the pullback compositor transfers vanishing of f|V to that
point. Take V equal to the zero locus. Step 2 gives the final criterion using any
one geometric point. Empty schemes, empty opens and rank zero are included. -/
theorem condensedLisseSource_zero_locus (k : Type u) [Field k] [IsAlgClosed k]
    (p ℓ : ℕ) [Fact p.Prime] [CharP k p] [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (T : Scheme.{u}) (a : T ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    {L M : condensedModuleCategory T (Mon.mk (Profinite.padicAlgClRingObj ℓ))}
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) L)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) T M)
    (f : L ⟶ M) :
    ∃ W : T.Opens,
      (W : Set T) = condensedMorphismZeroLocus ℓ f ∧
      (∀ V : T.Opens,
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) V.ι).map f = 0 ↔
          (V : Set T) ⊆ (W : Set T)) ∧
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) W.ι).map f = 0 ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ T),
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).map f = 0 ↔
          (Scheme.SpecToEquivOfField Ω T b).1 ∈ W := by
  classical
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian a
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian T := ⟨⟩
  have hLC := zeroLocus_lisse_constructible (Profinite.padicAlgClRingObj ℓ) hL
  have hI := zeroLocus_constructible_image ℓ T hLC hM f
  obtain ⟨C, hC, hb⟩ := zeroLocus_constructible_support ℓ T (Abelian.image f) hI
  have hfib (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ T) :
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).map f = 0 ↔
        (Scheme.SpecToEquivOfField Ω T b).1 ∈ C) ∧
      ((CondensedQbarGeometricEvaluation.fieldFiber Ω ℓ).map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).map f) = 0 ↔
        (Scheme.SpecToEquivOfField Ω T b).1 ∈ C) := by
    let F := CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b
    let E := CondensedQbarGeometricEvaluation.fieldFiber Ω ℓ
    have : PreservesFiniteLimits E := zeroLocus_fieldFiber_limits Ω ℓ
    constructor
    · exact (zeroLocus_map_zero_iff_image F f).trans (hb Ω b).1
    · exact (zeroLocus_map_zero_iff_image (F ⋙ E) f).trans (hb Ω b).2
  have hcarrier : C = condensedMorphismZeroLocus ℓ f := by
    ext x
    constructor
    · intro hx Ω _ _ b hb
      exact (hfib Ω b).1.mpr (by simpa only [hb] using hx)
    · intro hx
      let Ω := AlgebraicClosure (T.residueField x)
      let b : Spec (.of Ω) ⟶ T := (Scheme.SpecToEquivOfField Ω T).symm
        ⟨x, CommRingCat.ofHom (algebraMap (T.residueField x) Ω)⟩
      have hb : (Scheme.SpecToEquivOfField Ω T b).1 = x :=
        congrArg Sigma.fst ((Scheme.SpecToEquivOfField Ω T).apply_symm_apply _)
      simpa only [hb] using (hfib Ω b).1.mp (hx Ω b hb)
  have hopen : IsOpen (condensedMorphismZeroLocus ℓ f) :=
    zeroLocus_open_of_constructible_generalization (by rwa [← hcarrier])
      (zeroLocus_generalization k p ℓ hℓp T a hL hLC hM f
        (fun Ω _ _ b hz ↦ (hfib Ω b).1.mpr ((hfib Ω b).2.mp hz)))
  let W : T.Opens := ⟨condensedMorphismZeroLocus ℓ f, hopen⟩
  have hrestrict (V : T.Opens) :
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) V.ι).map f = 0 ↔
        (V : Set T) ⊆ (W : Set T) := by
    constructor
    · intro hf x hx Ω _ _ b hb
      have hrange : Set.range b ⊆ Set.range V.ι := by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        have hy : y = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
        subst y
        change (Scheme.SpecToEquivOfField Ω T b).1 ∈ V
        rwa [hb]
      let c := IsOpenImmersion.lift V.ι b hrange
      have hc : c ≫ V.ι = b := IsOpenImmersion.lift_fac V.ι b hrange
      have hz : (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
          (c ≫ V.ι)).map f = 0 :=
        (zeroLocus_comp_map_eq_zero (Profinite.padicAlgClRingObj ℓ) c V.ι f).mpr
          (by rw [hf, Functor.map_zero])
      exact zeroLocus_map_zero_of_eq (Profinite.padicAlgClRingObj ℓ)
        (c ≫ V.ι) b hc f hz
    · intro hV
      have : IsNoetherian V := zeroLocus_immersion_noetherian V.ι
      apply zeroLocus_constructible_map_zero ℓ V
        (zeroLocus_constructible_open ℓ T L hLC V)
        (zeroLocus_constructible_open ℓ T M hM V)
      intro Ω _ _ c
      have hx : (Scheme.SpecToEquivOfField Ω T (c ≫ V.ι)).1 ∈ V :=
        (c (IsLocalRing.closedPoint Ω)).property
      exact (zeroLocus_comp_map_eq_zero (Profinite.padicAlgClRingObj ℓ) c V.ι f).mp
        (hV hx Ω (c ≫ V.ι) rfl)
  refine ⟨W, rfl, hrestrict, (hrestrict W).mpr (Set.Subset.refl _), ?_⟩
  intro Ω _ _ b
  change (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) b).map f = 0 ↔
    (Scheme.SpecToEquivOfField Ω T b).1 ∈ condensedMorphismZeroLocus ℓ f
  rw [← hcarrier]
  exact (hfib Ω b).1

end AlgebraicGeometry.ProEtale
