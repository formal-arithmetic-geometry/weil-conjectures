/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QbarPerverseSubcategories
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.AffineSpace
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.FormalClosedSupportSheaves
import all WeilConjectures.AlgebraicGeometry.CoefficientHeartLisseRestriction
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.Finite
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
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
import all WeilConjectures.CategoryTheory.SiteInverseImageTensor
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import all WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import all Mathlib.AlgebraicGeometry.Limits
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
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.Pullback
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
import all Mathlib.Topology.Category.Profinite.AsLimit
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
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
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
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # Geometric decomposition of a finite-support punctual module

Source: blueprint latest, sec-deligne-laumon-a1/sk-p-dl-a1-middle,
prop-a1-fourier-middle-extension.proof.md, Step 3
(blueprint: lem-a1-geometric-punctual-decomposition).

The statement is in the ordinary category of modules over the pulled-back condensed
coefficient ring. Its degree-zero interpretation needs no derived-category choices.
The support is written by the vanishing-neighbourhood criterion: outside the finite
closed set the restriction vanishes locally, and each point of the set belongs to the
support. The point maps are the inclusions over k, with their specified singleton images.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStarComp CondensedRing.upperStarId
  CondensedRing.upperStarLowerStarAdjunction CondensedRing.upperStarCongr

/-- Keep zero-object transport abstract while instantiating large coefficient functors. -/
private theorem punctual_zero_of_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms D] [HasZeroMorphisms E]
    (F : C ⥤ D) (G : D ⥤ E) [G.PreservesZeroMorphisms] (H : C ⥤ E)
    (e : H ≅ F ⋙ G) (M : C) (hM : IsZero (F.obj M)) : IsZero (H.obj M) := by
  exact (G.map_isZero hM).of_iso (e.app M)

/-- The triangle identity and an invertible counit make the pulled-back unit invertible. -/
private theorem punctual_unit_map_iso
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) (hc : IsIso adj.counit) (M : C) :
    IsIso (F.map (adj.unit.app M)) := by
  have := hc
  have : IsIso (F.map (adj.unit.app M) ≫ adj.counit.app (F.obj M)) := by
    rw [adj.left_triangle_components M]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ (adj.counit.app _)

/-- Normalized coefficient pullback preserves finite free modules. -/
private theorem punctual_free_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : Mod.IsFree (condensedRingObj Λ X) M) :
    Mod.IsFree (condensedRingObj Λ Y) ((CondensedRing.upperStar Λ f).obj M) := by
  exact CondensedRing.free_standardPullback Λ f M (free_pullback f hM)

/-- A split covering turns a local finite free model into a model on the whole point. -/
private theorem punctual_lisse_point_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (M : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))
    (hM : IsLisseCoefficientModule Λ M) :
    Mod.IsFree (condensedRingObj Λ (Spec (.of k))) M := by
  obtain ⟨C, hC⟩ := hM
  obtain ⟨a, g, hg⟩ := C.exists_comp_eq_of_isSepClosed_of_proetale (𝟙 _)
  have h := punctual_free_pullback Λ g _ (hC a)
  exact free_of_iso h
    (((CondensedRing.upperStarComp Λ g (C.f a)).app M).symm ≪≫
      (CondensedRing.upperStarCongr Λ hg).app M ≪≫
      (CondensedRing.upperStarId Λ _).app M)

/-- The point image lies in one constructible stratum; transfer finite presentation there. -/
private theorem punctual_point_free
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hM : IsFiniteConstantStratified (Profinite.padicAlgClRingObj ℓ) X M)
    (f : Spec (.of k) ⟶ X) :
    Mod.IsFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k)))
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).obj M) := by
  obtain ⟨S, hS⟩ := hM
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
    (S.iUnion_stratum_eq_univ ▸ Set.mem_univ (f (IsLocalRing.closedPoint k)))
  have : IsImmersion (S.immersion a) := S.isImmersion a
  have hsub : Set.range f ⊆ Set.range (S.immersion a) := by
    rintro _ ⟨z, rfl⟩
    rw [S.range_immersion]
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint k)] using ha
  have hp := lfp_range_restriction (Profinite.padicAlgClRingObj ℓ)
    (S.immersion a) f hsub M
    (constantModel_lfp (Profinite.padicAlgClRingObj ℓ) _ _ (hS a))
  exact punctual_lisse_point_free (Profinite.padicAlgClRingObj ℓ) k _
    (lfp_lisse ℓ (Profinite.padicAlgClCondensedRing ℓ) _ (Or.inr rfl) _ hp)

/-- Factor through the open complement of a closed immersion to get vanishing. -/
private theorem punctual_disjoint_pullpush_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y W : Scheme.{u}}
    (i : Y ⟶ X) [IsClosedImmersion i] (g : W ⟶ X)
    (hg : Disjoint (Set.range i) (Set.range g))
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    IsZero ((CondensedRing.upperStar Λ g).obj ((CondensedRing.lowerStar Λ i).obj M)) := by
  let V : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hV : Set.range g ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    intro x hx hx'
    exact Set.disjoint_left.mp hg hx' hx
  let v := IsOpenImmersion.lift V.ι g hV
  have hz := CondensedRing.openRestrictionPushforwardZero Λ i V.ι
    (by exact Scheme.Opens.range_ι V) M
  exact punctual_zero_of_comparison (CondensedRing.upperStar Λ V.ι)
    (CondensedRing.upperStar Λ v) (CondensedRing.upperStar Λ g)
    (CondensedRing.upperStarCongr Λ (IsOpenImmersion.lift_fac V.ι g hV).symm ≪≫
      CondensedRing.upperStarComp Λ v V.ι) _ hz

private theorem punctual_biproduct_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {I : Type*} (F : I → C) [HasBiproduct F] (hF : ∀ a, IsZero (F a)) : IsZero (⨁ F) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro a
  exact (hF a).eq_of_tgt _ _

private theorem punctual_biproduct_projection_iso {C : Type*} [Category C]
    [HasZeroMorphisms C] {I : Type*}
    (F : I → C) [HasBiproduct F] (a : I) (hF : ∀ b, b ≠ a → IsZero (F b)) :
    IsIso (biproduct.π F a) := by
  classical
  refine ⟨⟨biproduct.ι F a, ?_, by simp⟩⟩
  apply biproduct.hom_ext
  intro b
  by_cases h : b = a
  · subst b
    simp
  · exact (hF b h).eq_of_tgt _ _

/-- Check a biproduct lift using one nonzero pulled-back coordinate. -/
private theorem punctual_lift_pullback_iso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    {I : Type*} [Finite I] (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]
    (M : C) (F : I → C) (η : ∀ a, M ⟶ F a) (a : I)
    (hz : ∀ b, b ≠ a → IsZero (G.obj (F b))) (hu : IsIso (G.map (η a))) :
    IsIso (G.map (biproduct.lift η)) := by
  classical
  have : IsIso (biproduct.π (G.obj ∘ F) a) :=
    punctual_biproduct_projection_iso (G.obj ∘ F) a hz
  have hπ : IsIso (G.map (biproduct.π F a)) := by
    have he : G.map (biproduct.π F a) =
        (G.mapBiproduct F).hom ≫ biproduct.π (G.obj ∘ F) a := by simp
    rw [he]
    infer_instance
  have : IsIso (G.map (biproduct.lift η) ≫ G.map (biproduct.π F a)) := by
    rw [← G.map_comp, biproduct.lift_π]
    exact hu
  exact IsIso.of_isIso_comp_right _ (G.map (biproduct.π F a))

/-- A map becomes invertible when its source and every target coordinate pull back to zero. -/
private theorem punctual_lift_pullback_zero
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasZeroObject D]
    {I : Type*} [Finite I] (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]
    (M : C) (F : I → C) (φ : M ⟶ ⨁ F)
    (hs : IsZero (G.obj M)) (ht : ∀ a, IsZero (G.obj (F a))) : IsIso (G.map φ) := by
  have hz : IsZero (⨁ (G.obj ∘ F)) := punctual_biproduct_zero _ ht
  have ht' : IsZero (G.obj (⨁ F)) := hz.of_iso (G.mapBiproduct F)
  exact isIso_of_source_target_iso_zero _ hs.isoZero ht'.isoZero

/-- Combine geometric detecting families only at the level of abelian sheaves. -/
private theorem punctual_ab_detect_two
    {X : Scheme.{u}} {I J : Type u} [Finite I] [Finite J]
    {Y : I → Scheme.{u}} {W : J → Scheme.{u}}
    (g : ∀ a, Y a ⟶ X) (h : ∀ b, W b ⟶ X)
    [∀ a, QuasiCompact (g a)] [∀ b, QuasiCompact (h b)]
    (hg : ∀ x, (∃ a, x ∈ Set.range (g a)) ∨ ∃ b, x ∈ Set.range (h b))
    {M N : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (f : M ⟶ N)
    (hf : ∀ a, (upperStar Ab.{u + 1} (g a)).map f = 0)
    (hf' : ∀ b, (upperStar Ab.{u + 1} (h b)).map f = 0) : f = 0 := by
  let V : I ⊕ J → Scheme.{u} := Sum.elim Y W
  let v : ∀ a : I ⊕ J, V a ⟶ X := fun a ↦ match a with
    | .inl a => g a
    | .inr b => h b
  have : ∀ a, QuasiCompact (v a) := by
    rintro (a | b) <;> dsimp [v] <;> infer_instance
  apply abDetectMaps v (fun x ↦ ?_) f (by
    rintro (a | b)
    · exact hf a
    · exact hf' b)
  rcases hg x with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨.inl a, ha⟩
  · exact ⟨.inr b, hb⟩

/-- Detect zero modules using two finite geometric families. -/
private theorem punctual_joint_zero_two
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {I J : Type u} [Finite I] [Finite J] {Y : I → Scheme.{u}} {W : J → Scheme.{u}}
    (g : ∀ a, Y a ⟶ X) (h : ∀ b, W b ⟶ X)
    [∀ a, QuasiCompact (g a)] [∀ b, QuasiCompact (h b)]
    (hg : ∀ x, (∃ a, x ∈ Set.range (g a)) ∨ ∃ b, x ∈ Set.range (h b))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hf : ∀ a, IsZero ((CondensedRing.upperStar Λ (g a)).obj M))
    (hf' : ∀ b, IsZero ((CondensedRing.upperStar Λ (h b)).obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  apply (Mod.forget _).map_injective
  apply punctual_ab_detect_two g h hg (𝟙 M.X)
  · intro a
    have hz := ((Mod.forget _).map_isZero (hf a)).of_iso
      ((profinitePointModuleForgetPullbackIso Λ (g a)).app M).symm
    exact hz.eq_of_src _ _
  · intro b
    have hz := ((Mod.forget _).map_isZero (hf' b)).of_iso
      ((profinitePointModuleForgetPullbackIso Λ (h b)).app M).symm
    exact hz.eq_of_src _ _

/-- Exact pullbacks from two detecting families detect isomorphisms. -/
private theorem punctual_joint_iso_two
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {I J : Type u} [Finite I] [Finite J] {Y : I → Scheme.{u}} {W : J → Scheme.{u}}
    (g : ∀ a, Y a ⟶ X) (h : ∀ b, W b ⟶ X)
    [∀ a, QuasiCompact (g a)] [∀ b, QuasiCompact (h b)]
    (hg : ∀ x, (∃ a, x ∈ Set.range (g a)) ∨ ∃ b, x ∈ Set.range (h b))
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : M ⟶ N) (hf : ∀ a, IsIso ((CondensedRing.upperStar Λ (g a)).map f))
    (hf' : ∀ b, IsIso ((CondensedRing.upperStar Λ (h b)).map f)) : IsIso f := by
  have hker {V : Scheme.{u}} (v : V ⟶ X)
      (hv : IsIso ((CondensedRing.upperStar Λ v).map f)) :
      IsZero ((CondensedRing.upperStar Λ v).obj (kernel f)) := by
    have := hv
    exact (isZero_kernel_of_mono ((CondensedRing.upperStar Λ v).map f)).of_iso
      (PreservesKernel.iso _ f)
  have hcoker {V : Scheme.{u}} (v : V ⟶ X)
      (hv : IsIso ((CondensedRing.upperStar Λ v).map f)) :
      IsZero ((CondensedRing.upperStar Λ v).obj (cokernel f)) := by
    have := hv
    exact (isZero_cokernel_of_epi ((CondensedRing.upperStar Λ v).map f)).of_iso
      (PreservesCokernel.iso _ f)
  have hk : IsZero (kernel f) := punctual_joint_zero_two Λ g h hg _
    (fun a ↦ hker (g a) (hf a)) (fun b ↦ hker (h b) (hf' b))
  have hc : IsZero (cokernel f) := punctual_joint_zero_two Λ g h hg _
    (fun a ↦ hcoker (g a) (hf a)) (fun b ↦ hcoker (h b) (hf' b))
  have := Preadditive.mono_of_isZero_kernel f hk
  have := Preadditive.epi_of_isZero_cokernel f hc
  exact isIso_of_mono_of_epi f

/-- Exact pullbacks along one abstract detecting family detect isomorphisms. -/
private theorem punctual_joint_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {I : Type u} [Finite I]
    {Y : I → Scheme.{u}} (g : ∀ a, Y a ⟶ X) [∀ a, QuasiCompact (g a)]
    (hg : ∀ x, ∃ a, x ∈ Set.range (g a))
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : M ⟶ N) (hf : ∀ a, IsIso ((CondensedRing.upperStar Λ (g a)).map f)) :
    IsIso f := by
  have hg' : ∀ x, (∃ a, x ∈ Set.range (g a)) ∨ ∃ a, x ∈ Set.range (g a) :=
    fun x ↦ Or.inl (hg x)
  exact punctual_joint_iso_two Λ g g hg' f hf hf

/-- The actual reconstruction map is the biproduct of the adjunction units. -/
@[irreducible] private noncomputable def punctualSupportMap
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {I : Type u} [Finite I] (Y : Scheme.{u}) (i : I → (Y ⟶ X)) :
    M ⟶ ⨁ fun a ↦ (CondensedRing.lowerStar Λ (i a)).obj
      ((CondensedRing.upperStar Λ (i a)).obj M) :=
  biproduct.lift fun a ↦ (CondensedRing.upperStarLowerStarAdjunction Λ (i a)).unit.app M

/-- Closed-point restrictions of the reconstruction map are isomorphisms. -/
private theorem punctual_support_map_point
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (Z : Finset X) (Y : Scheme.{u}) (i : Z → (Y ⟶ X))
    [∀ a, IsClosedImmersion (i a)] (hi : ∀ a, Set.range (i a) = {a.val}) (a : Z) :
    IsIso ((CondensedRing.upperStar Λ (i a)).map (punctualSupportMap Λ M Y i)) := by
  unfold punctualSupportMap
  apply punctual_lift_pullback_iso _ _ _ _ a
  · intro b hba
    apply punctual_disjoint_pullpush_zero Λ (i b) (i a)
    rw [hi b, hi a]
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact hba (Subtype.ext ((Set.mem_singleton_iff.mp hx).symm.trans
      (Set.mem_singleton_iff.mp hx')))
  · exact punctual_unit_map_iso _ _ (CondensedRing.upperStarLowerStarAdjunction Λ (i a))
      (CondensedRing.moduleCounitOfAbelian Λ (i a) (abelian_closed_counit (i a))) M

/-- The reconstruction map is invertible on any open missing the support and killing M. -/
private theorem punctual_support_map_open
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (Z : Finset X) (Y : Scheme.{u}) (i : Z → (Y ⟶ X))
    [∀ a, IsClosedImmersion (i a)] (hi : ∀ a, Set.range (i a) = {a.val})
    (hs : ∀ x : X, x ∈ Z ↔ ∀ U : X.Opens, x ∈ U →
      ¬ IsZero ((CondensedRing.upperStar Λ U.ι).obj M))
    (U : X.Opens) (hU : IsZero ((CondensedRing.upperStar Λ U.ι).obj M)) :
    IsIso ((CondensedRing.upperStar Λ U.ι).map (punctualSupportMap Λ M Y i)) := by
  apply punctual_lift_pullback_zero _ _ _ _ hU
  intro a
  apply punctual_disjoint_pullpush_zero Λ (i a) U.ι
  rw [hi a, Scheme.Opens.range_ι]
  apply Set.disjoint_left.mpr
  intro x hx hxU
  have hxa : x = a.val := Set.mem_singleton_iff.mp hx
  subst x
  exact (hs a.val).mp a.property U hxU hU

/-- Construct an isomorphism abstractly, without unfolding a concrete coefficient map. -/
private theorem punctual_nonempty_iso
    {C : Type*} [Category C] {M N : C} (f : M ⟶ N) (hf : IsIso f) :
    Nonempty (M ≅ N) := by
  have := hf
  exact ⟨asIso f⟩

/-- Choose a finite cover of the complement by opens satisfying an arbitrary predicate. -/
private theorem punctual_finite_neighborhoods
    {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    (Z : Finset X) (P : TopologicalSpace.Opens X → Prop)
    (hs : ∀ x : X, x ∉ Z → ∃ U : TopologicalSpace.Opens X, x ∈ U ∧ P U) :
    ∃ t : Finset (TopologicalSpace.Opens X), (∀ U ∈ t, P U) ∧
      ∀ x : X, x ∉ Z → ∃ U ∈ t, x ∈ U := by
  classical
  let V := {U : TopologicalSpace.Opens X // P U}
  have hcover : (Z : Set X)ᶜ ⊆ ⋃ U : V, (U.val : Set X) := by
    intro x hx
    obtain ⟨U, hxU, hU⟩ := hs x hx
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact ((Z : Set X)ᶜ))
    |>.elim_finite_subcover (fun U : V ↦ (U.val : Set X)) (fun U ↦ U.val.isOpen) hcover
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro U hU
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hU
    exact v.property
  · intro x hx
    obtain ⟨v, hvt, hxv⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact ⟨v.val, Finset.mem_image.mpr ⟨v, hvt, rfl⟩, hxv⟩

/-- A finite jointly surjective family retaining any property true on points and good opens. -/
private theorem punctual_detecting_family
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (Z : Finset X) (Y : Scheme.{u}) (i : Z → (Y ⟶ X))
    [∀ a, QuasiCompact (i a)] (hi : ∀ a, Set.range (i a) = {a.val})
    (R : X.Opens → Prop) (hs : ∀ x : X, x ∉ Z → ∃ U : X.Opens, x ∈ U ∧ R U)
    (P : ∀ S : Scheme.{u}, (S ⟶ X) → Prop)
    (hp : ∀ a, P Y (i a)) (ho : ∀ U : X.Opens, R U → P U.toScheme U.ι) :
    ∃ (I : Type u) (_ : Finite I) (W : I → Scheme.{u}) (g : ∀ a, W a ⟶ X),
      (∀ a, QuasiCompact (g a)) ∧ (∀ x, ∃ a, x ∈ Set.range (g a)) ∧
        ∀ a, P (W a) (g a) := by
  classical
  obtain ⟨t, ht0, ht⟩ := punctual_finite_neighborhoods Z R hs
  let W : Z ⊕ t → Scheme.{u} := Sum.elim (fun _ ↦ Y) (fun U ↦ Scheme.Opens.toScheme U.val)
  let g : ∀ a : Z ⊕ t, W a ⟶ X := fun a ↦ match a with
    | .inl a => i a
    | .inr U => Scheme.Opens.ι U.val
  refine ⟨Z ⊕ t, inferInstance, W, g, ?_, ?_, ?_⟩
  · rintro (a | U)
    · change QuasiCompact (i a)
      infer_instance
    · change QuasiCompact (Scheme.Opens.ι (X := X) U.val)
      have : TopologicalSpace.NoetherianSpace (Scheme.Opens.toScheme (X := X) U.val) :=
        (Scheme.Opens.ι (X := X) U.val).isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
      infer_instance
  · intro x
    by_cases hx : x ∈ Z
    · refine ⟨.inl ⟨x, hx⟩, ?_⟩
      change x ∈ Set.range (i ⟨x, hx⟩)
      rw [hi]
      exact Set.mem_singleton x
    · obtain ⟨U, hUt, hxU⟩ := ht x hx
      refine ⟨.inr ⟨U, hUt⟩, ?_⟩
      change x ∈ Set.range (Scheme.Opens.ι (X := X) U)
      rwa [Scheme.Opens.range_ι]
  · rintro (a | U)
    · exact hp a
    · exact ho U.val (ht0 U.val U.property)

/-- A finite point family and vanishing neighborhoods detect invertibility. -/
private theorem punctual_iso_of_neighborhoods
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X]
    (Z : Finset X) (Y : Scheme.{u}) (i : Z → (Y ⟶ X))
    [∀ a, QuasiCompact (i a)] (hi : ∀ a, Set.range (i a) = {a.val})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : M ⟶ N)
    (hs : ∀ x : X, x ∉ Z → ∃ U : X.Opens, x ∈ U ∧
      IsZero ((CondensedRing.upperStar Λ U.ι).obj M))
    (hp : ∀ a, IsIso ((CondensedRing.upperStar Λ (i a)).map f))
    (ho : ∀ U : X.Opens, IsZero ((CondensedRing.upperStar Λ U.ι).obj M) →
      IsIso ((CondensedRing.upperStar Λ U.ι).map f)) : IsIso f := by
  obtain ⟨I, hI, W, g, hqc, hcover, hP⟩ := punctual_detecting_family Z Y i hi
    (fun U : X.Opens ↦ IsZero ((CondensedRing.upperStar Λ U.ι).obj M)) hs
    (fun S v ↦ IsIso ((CondensedRing.upperStar Λ v).map f)) hp ho
  have : Finite I := hI
  have : ∀ a, QuasiCompact (g a) := hqc
  exact punctual_joint_iso Λ g hcover f hP

/-- The adjunction units reconstruct a finite-support module from its point restrictions. -/
private theorem punctual_support_decomposition
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (Z : Finset X) (Y : Scheme.{u}) (i : Z → (Y ⟶ X))
    [∀ a, IsClosedImmersion (i a)] (hi : ∀ a, Set.range (i a) = {a.val})
    (hs : ∀ x : X, x ∈ Z ↔ ∀ U : X.Opens, x ∈ U →
      ¬ IsZero ((CondensedRing.upperStar Λ U.ι).obj M)) :
    Nonempty (M ≅ ⨁ fun a : Z ↦ (CondensedRing.lowerStar Λ (i a)).obj
      ((CondensedRing.upperStar Λ (i a)).obj M)) := by
  classical
  have hout : ∀ x : X, x ∉ Z → ∃ U : X.Opens, x ∈ U ∧
      IsZero ((CondensedRing.upperStar Λ U.ι).obj M) := by
    intro x hx
    have hn : ¬ ∀ U : X.Opens, x ∈ U →
        ¬ IsZero ((CondensedRing.upperStar Λ U.ι).obj M) :=
      fun h ↦ hx ((hs x).mpr h)
    push Not at hn
    exact hn
  exact punctual_nonempty_iso (punctualSupportMap Λ M Y i)
    (punctual_iso_of_neighborhoods Λ Z Y i hi _ hout
      (punctual_support_map_point Λ M Z Y i hi)
      (punctual_support_map_open Λ M Z Y i hi hs))

/-- Map a finite free model through an additive functor preserving finite limits. -/
private theorem punctual_image_free
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (M R : C)
    (hM : ∃ n : ℕ, Nonempty (M ≅ ⨁ fun _ : Fin n ↦ R)) :
    ∃ n : ℕ, Nonempty (F.obj M ≅ ⨁ fun _ : Fin n ↦ F.obj R) := by
  obtain ⟨n, ⟨e⟩⟩ := hM
  exact ⟨n, ⟨F.mapIso e ≪≫ F.mapBiproduct _⟩⟩

/-- A finite free point module has a finite free skyscraper image. -/
private theorem punctual_lowerStar_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (i : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : Mod.IsFree (condensedRingObj Λ Y) M) :
    ∃ n : ℕ, Nonempty ((CondensedRing.lowerStar Λ i).obj M ≅
      ⨁ fun _ : Fin n ↦ (CondensedRing.lowerStar Λ i).obj
        (Mod.regular (condensedRingObj Λ Y))) := by
  exact punctual_image_free (CondensedRing.lowerStar Λ i) M
    (Mod.regular (condensedRingObj Λ Y)) hM

/-- Combine object-level finite sum models and obtain a positive integral multiplicity. -/
private theorem punctual_multiplicities
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasFiniteBiproducts C]
    {I : Type*} [Finite I] (N δ : I → C) (T : C) (hne : ¬ IsZero T)
    (r : I → ℕ) (er : ∀ a, N a ≅ ⨁ fun _ : Fin (r a) ↦ δ a)
    (e₀ : T ≅ ⨁ N) :
    ∃ n : I → ℤ, (∀ a, 0 ≤ n a) ∧ (∃ a, 0 < n a) ∧
      Nonempty (T ≅ ⨁ fun a ↦ ⨁ fun _ : Fin (n a).toNat ↦ δ a) := by
  classical
  let e : T ≅ ⨁ fun a ↦ ⨁ fun _ : Fin (r a) ↦ δ a := e₀ ≪≫ biproduct.mapIso er
  have hr : ∃ a, 0 < r a := by
    by_contra hn
    push Not at hn
    have hr0 (a : I) : r a = 0 := Nat.eq_zero_of_le_zero (hn a)
    apply hne
    have hzδ (a : I) : IsZero (⨁ fun _ : Fin (r a) ↦ δ a) := by
      exact punctual_biproduct_zero _ fun j ↦
        (Nat.not_lt_zero j.val ((hr0 a) ▸ j.isLt)).elim
    exact (punctual_biproduct_zero _ hzδ).of_iso e
  refine ⟨fun a ↦ (r a : ℤ), fun a ↦ Int.natCast_nonneg _, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hr
    exact ⟨a, Int.ofNat_lt.mpr ha⟩
  · exact ⟨e⟩

/-- Choose ranks only after the summands have been abstracted as categorical objects. -/
private theorem punctual_multiplicities_exists
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasFiniteBiproducts C]
    {I : Type*} [Finite I] (N δ : I → C) (T : C) (hne : ¬ IsZero T)
    (hfree : ∀ a, ∃ r : ℕ, Nonempty (N a ≅ ⨁ fun _ : Fin r ↦ δ a))
    (he : Nonempty (T ≅ ⨁ N)) :
    ∃ n : I → ℤ, (∀ a, 0 ≤ n a) ∧ (∃ a, 0 < n a) ∧
      Nonempty (T ≅ ⨁ fun a ↦ ⨁ fun _ : Fin (n a).toNat ↦ δ a) := by
  classical
  choose r er using hfree
  obtain ⟨e₀⟩ := he
  exact punctual_multiplicities N δ T hne r (fun a ↦ (er a).some) e₀

/-- Combine free modules on a common point before choosing their pullback origins. -/
private theorem punctual_free_skyscraper_family
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}}
    {I : Type*} [Finite I] (i : I → (S ⟶ X))
    (M : I → Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (T : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hne : ¬ IsZero T) (hfree : ∀ a, Mod.IsFree (condensedRingObj Λ S) (M a))
    (he : Nonempty (T ≅ ⨁ fun a ↦ (CondensedRing.lowerStar Λ (i a)).obj (M a))) :
    ∃ n : I → ℤ, (∀ a, 0 ≤ n a) ∧ (∃ a, 0 < n a) ∧
      Nonempty (T ≅ ⨁ fun a ↦ ⨁ fun _ : Fin (n a).toNat ↦
        (CondensedRing.lowerStar Λ (i a)).obj (Mod.regular (condensedRingObj Λ S))) := by
  classical
  exact punctual_multiplicities_exists
    (fun a ↦ (CondensedRing.lowerStar Λ (i a)).obj (M a))
    (fun a ↦ (CondensedRing.lowerStar Λ (i a)).obj
      (Mod.regular (condensedRingObj Λ S))) T hne
    (fun a ↦ punctual_lowerStar_free Λ (i a) (M a) (hfree a)) he

attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar

/-- Reconstruct support when all the chosen closed points have a common source. -/
private theorem punctual_constant_support
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X]
    (T : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (Z : Finset X) (i : Z → (S ⟶ X))
    [∀ a, IsClosedImmersion (i a)] (hi : ∀ a, Set.range (i a) = {a.val})
    (hs : ∀ x : X, x ∈ Z ↔ ∀ U : X.Opens, x ∈ U →
      ¬ IsZero ((CondensedRing.upperStar Λ U.ι).obj T)) :
    Nonempty (T ≅ ⨁ fun a : Z ↦ (CondensedRing.lowerStar Λ (i a)).obj
      ((CondensedRing.upperStar Λ (i a)).obj T)) := by
  exact punctual_support_decomposition Λ T Z S i hi hs

/-- Supply free restriction models to a specified reconstruction isomorphism. -/
private theorem punctual_restriction_models
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}}
    {I : Type*} [Finite I] (i : I → (S ⟶ X))
    (T : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hne : ¬ IsZero T)
    (hfree : ∀ a, Mod.IsFree (condensedRingObj Λ S)
      ((CondensedRing.upperStar Λ (i a)).obj T))
    (he : Nonempty (T ≅ ⨁ fun a ↦ (CondensedRing.lowerStar Λ (i a)).obj
      ((CondensedRing.upperStar Λ (i a)).obj T))) :
    ∃ n : I → ℤ, (∀ a, 0 ≤ n a) ∧ (∃ a, 0 < n a) ∧
      Nonempty (T ≅ ⨁ fun a ↦ ⨁ fun _ : Fin (n a).toNat ↦
        (CondensedRing.lowerStar Λ (i a)).obj (Mod.regular (condensedRingObj Λ S))) := by
  exact punctual_free_skyscraper_family Λ i
    (fun a ↦ (CondensedRing.upperStar Λ (i a)).obj T) T hne hfree he

/-- Finite free restrictions and support reconstruction give a skyscraper decomposition. -/
private theorem punctual_finite_free_support
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X]
    (T : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hne : ¬ IsZero T) (Z : Finset X) (i : Z → (S ⟶ X))
    [∀ a, IsClosedImmersion (i a)] (hi : ∀ a, Set.range (i a) = {a.val})
    (hs : ∀ x : X, x ∈ Z ↔ ∀ U : X.Opens, x ∈ U →
      ¬ IsZero ((CondensedRing.upperStar Λ U.ι).obj T))
    (hfree : ∀ a, Mod.IsFree (condensedRingObj Λ S)
      ((CondensedRing.upperStar Λ (i a)).obj T)) :
    ∃ n : Z → ℤ, (∀ a, 0 ≤ n a) ∧ (∃ a, 0 < n a) ∧
      Nonempty (T ≅ ⨁ fun a ↦ ⨁ fun _ : Fin (n a).toNat ↦
        (CondensedRing.lowerStar Λ (i a)).obj (Mod.regular (condensedRingObj Λ S))) := by
  exact punctual_restriction_models Λ i T hne hfree
    (punctual_constant_support Λ T Z i hi hs)

/-- Combine the support isomorphism and point freeness before specializing the scheme. -/
private theorem punctual_geometric_finite
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (T : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hT : IsFiniteConstantStratified (Profinite.padicAlgClRingObj ℓ) X T)
    (hne : ¬ IsZero T) (Z : Finset X) (i : Z → (Spec (.of k) ⟶ X))
    [∀ a, IsClosedImmersion (i a)] (hi : ∀ a, Set.range (i a) = {a.val})
    (hs : ∀ x : X, x ∈ Z ↔ ∀ U : X.Opens, x ∈ U →
      ¬ IsZero ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) U.ι).obj T)) :
    ∃ n : Z → ℤ, (∀ a, 0 ≤ n a) ∧ (∃ a, 0 < n a) ∧
      Nonempty (T ≅ ⨁ fun a ↦ ⨁ fun _ : Fin (n a).toNat ↦
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) (i a)).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))))) := by
  classical
  exact punctual_finite_free_support (Profinite.padicAlgClRingObj ℓ) T hne Z i hi hs
    (fun a ↦ punctual_point_free k ℓ T hT (i a))

-- Keep the specified target binder names, including its nondependent point index.
set_option linter.unusedVariables false in
/-- A nonzero constructible condensed Qbar module on the geometric affine line with
finite closed support is a finite direct sum of copies of the geometric skyscrapers.
There is no Weil action or equivariance condition on the chosen decomposition.

Source: blueprint latest, prop-a1-fourier-middle-extension.proof.md, Step 3
(blueprint: lem-a1-geometric-punctual-decomposition).

Proof:
1. Restrict to each geometric point. Its image lies in a constructible stratum, so
local finite presentation transfers from that stratum to the point. Over the
condensed algebraic closure this implies lissity. A pro-etale cover of the
algebraically closed point has a section through a member; pulling a finite free
local trivialization along that section makes the point restriction finite free.
2. The adjunction units give a map T -> sum_x i_x* i_x^*T. At a support point,
all off-diagonal summands vanish because the point images are disjoint. The
remaining component is invertible by the closed-immersion counit and the triangle
identity. Thus the map becomes an isomorphism at every support point.
3. Off the support choose open neighborhoods on which T vanishes. Such an open
misses the support, so each point pushforward also restricts to zero there.
Noetherian compactness gives finitely many such opens covering the complement.
Together with the point inclusions these form a jointly surjective quasi-compact
family. Its exact pullbacks detect zero kernels and cokernels, hence detect that
the unit map is an isomorphism. The detection uses the existing abelian sheaf
result and the canonical forgetful-pullback comparison for coefficient modules.
4. Substitute the finite free point trivializations and commute each additive
point pushforward with the finite biproduct. If every rank were zero, T would be
zero. Hence some natural rank is positive; cast the ranks to integers.
-/
theorem geometric_punctual_decomposition
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k))
    (T : Mod (Sheaf (Scheme.ProEt.topology (𝔸(ULift.{u} (Fin 1); Spec (.of k)))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (𝔸(ULift.{u} (Fin 1); Spec (.of k)))))
    (hT : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ)
      (𝔸(ULift.{u} (Fin 1); Spec (.of k))) T)
    (hne : ¬ IsZero T) (Z : Finset (𝔸(ULift.{u} (Fin 1); Spec (.of k))))
    (i : ∀ ξ : Z, Spec (.of k) ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k)))
    [∀ ξ : Z, (i ξ).IsOver (Spec (.of k))]
    [∀ ξ : Z, IsClosedImmersion (i ξ)]
    (hi : ∀ ξ : Z, Set.range (i ξ) = {ξ.val})
    (hsupport : ∀ x : 𝔸(ULift.{u} (Fin 1); Spec (.of k)),
      x ∈ Z ↔ ∀ U : (𝔸(ULift.{u} (Fin 1); Spec (.of k))).Opens, x ∈ U →
        ¬ IsZero ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) U.ι).obj T)) :
    ∃ n : Z → ℤ, (∀ ξ : Z, 0 ≤ n ξ) ∧ (∃ ξ : Z, 0 < n ξ) ∧
      Nonempty (T ≅ ⨁ fun ξ : Z ↦ ⨁ fun _ : Fin (n ξ).toNat ↦
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) (i ξ)).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))))) := by
  classical
  have _ := hℓ
  let X := 𝔸(ULift.{u} (Fin 1); Spec (.of k))
  let Λ := Profinite.padicAlgClRingObj ℓ
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have hfinite : IsFiniteConstantStratified Λ X T := by
    unfold IsConstantModelConstructible at hT
    split at hT
    · exact hT
    · rename_i hc
      exact (hc ⟨inferInstance, inferInstance⟩).elim
  exact punctual_geometric_finite k ℓ T hfinite hne Z i hi hsupport

end AlgebraicGeometry.ProEtale
