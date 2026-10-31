/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedLisseDualityDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
import all WeilConjectures.AlgebraicGeometry.UnboundedLocalizingPullback
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
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
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

/-! # Canonical open restriction of condensed internal Hom

Source: thm-a1-curve-perverse-heart, Step 2, open restriction.
(blueprint: lem-per-condensed-lisse-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseDual
variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)

private theorem restrictionMap_naturality {k : Type u} [Field k]
    {V T : Space k} (AV : AdjointData ell c V) (AT : AdjointData ell c T)
    (j : V.scheme ⟶ T.scheme)
    (e : (pull ell c j).obj (AT.omega ell c) ≅ AV.omega ell c)
    {M N : D ell c T.scheme} (f : M ⟶ N) :
    (pull ell c j).map ((AT.dual ell c).map f.op) ≫
        restrictionMap ell c AV AT j e M =
      restrictionMap ell c AV AT j e N ≫
        (AV.dual ell c).map ((pull ell c j).map f).op := by
  change (pull ell c j).map ((MonoidalClosed.pre f).app (AT.omega ell c)) ≫
      ((Functor.LaxMonoidal.ihomComparison (pull ell c j) M).natTrans.app
        (AT.omega ell c) ≫ (ihom ((pull ell c j).obj M)).map e.hom) = _
  rw [← Category.assoc,
    Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app, Category.assoc]
  change _ ≫ _ ≫ _ = (_ ≫ _) ≫ (MonoidalClosed.pre ((pull ell c j).map f)).app _
  rw [Category.assoc]
  exact congrArg
    (fun g ↦ (Functor.LaxMonoidal.ihomComparison (pull ell c j) N).natTrans.app
      (AT.omega ell c) ≫ g)
    ((MonoidalClosed.pre ((pull ell c j).map f)).naturality e.hom).symm

private theorem open_ihomComparison_isIso {V T : Scheme.{u}}
    (j : V ⟶ T) [IsOpenImmersion j] (M : D ell c T) :
    IsIso (Functor.LaxMonoidal.ihomComparison (pull ell c j) M).natTrans := by
  let tau : (CondensedRing.upperStar (c.obj ell) j).leftDerivedFunctor ≅ pull ell c j :=
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) j
  have ht : NatTrans.IsMonoidal tau.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport tau
  have hs : IsIso (Functor.LaxMonoidal.ihomComparison
      (CondensedRing.upperStar (c.obj ell) j).leftDerivedFunctor M).natTrans :=
    CondensedRing.isIso_ihomComparison_leftDerivedUpperStar_of_isOpenImmersion
      (c.obj ell) j M
  have ht' : NatTrans.IsMonoidal tau.symm.hom :=
    (show NatTrans.IsMonoidal tau.inv from inferInstance)
  exact Functor.LaxMonoidal.isIso_ihomComparison_of_iso tau.symm M

/-- Exact inverse image preserves bounded constructibility and lisse cohomology.
Source: smooth-lisse duality, open-restriction paragraph of Step 2
(blueprint: lem-per-condensed-lisse-restriction).

Proof: pull back each finite constant local model on the adapted stratification.
Exactness of inverse image preserves the cohomological bounds and identifies its
cohomology with inverse image of cohomology. A trivializing pro-etale cover of each
cohomology module pulls back to a trivializing cover; inverse image preserves the
finite free module on every member. Transport along the exact homology comparison.
The argument includes empty covers, the zero complex, and rank zero.
-/
theorem open_lisse {k : Type u} [Field k] : OpenLisse ell c k := by
  intro V T j hj M
  let : IsOpenImmersion j := hj
  have hcompact (S : Space k) : CompactSpace S.scheme :=
    QuasiCompact.compactSpace_of_compactSpace S.map
  have hqs (S : Space k) : QuasiSeparatedSpace S.scheme := by
    have : IsLocallyNoetherian S.scheme := LocallyOfFiniteType.isLocallyNoetherian S.map
    infer_instance
  let : CompactSpace V.scheme := hcompact V
  let : CompactSpace T.scheme := hcompact T
  let : QuasiSeparatedSpace V.scheme := hqs V
  let : QuasiSeparatedSpace T.scheme := hqs T
  refine ⟨?_, ?_⟩
  · have := (constantModelConstructibleFiniteTor_wellDefined (c.obj ell) V.scheme).2.1
    have hc := pullback_bounded_constructible (c.obj ell) j
      (fun N hN ↦ pullback_constructible (c.obj ell) j N hN) M.obj M.property.1
    exact (constantModelBoundedConstructible (c.obj ell) V.scheme).prop_of_iso
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) j).app M.obj) hc
  · intro n
    obtain ⟨C, hC⟩ := CondensedRing.locFree_pullback (c.obj ell) j _ (M.property.2 n)
    refine ⟨C, fun t ↦ ?_⟩
    obtain ⟨r, ⟨e⟩⟩ := hC t
    exact ⟨r, ⟨(CondensedRing.upperStar (c.obj ell) (C.f t)).mapIso
      ((CondensedRing.upperStar (c.obj ell) j).mapDerivedCategoryHomologyFunctorIso n
        |>.app M.obj).symm ≪≫ e⟩⟩

/-- Open inverse image commutes with the canonical internal-Hom restriction map.
Source: Step 2, restriction of duality
(blueprint: lem-per-condensed-lisse-restriction).

Proof: the upstream open-immersion theorem makes the canonical total-derived
internal-Hom comparison invertible. Transfer it to exact inverse image along the
monoidal comparison. Compose
with the chosen isomorphism on dualizing objects. Naturality is the source-variable
naturality of the closed comparison followed by naturality of precomposition.
-/
theorem open_restriction {k : Type u} [Field k]
    (A : ∀ T : Space k, AdjointData ell c T)
    (e : OpenDualizingComparisons ell c A) :
    OpenIsomorphism ell c A e ∧ OpenNaturality ell c A e := by
  constructor
  · intro V T j hj hbase M
    let : IsOpenImmersion j := hj
    have := open_ihomComparison_isIso ell c j M.obj
    dsimp only [restrictionMap]
    infer_instance
  · intro V T j hj hbase M N f
    exact restrictionMap_naturality ell c (A V) (A T) j (e V T j hbase) f.hom

end AlgebraicGeometry.ProEtale.CondensedLisseDual
