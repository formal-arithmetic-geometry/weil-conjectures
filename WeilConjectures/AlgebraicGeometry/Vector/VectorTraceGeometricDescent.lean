/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationDirectSumLocal
import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseChangeLocal
import WeilConjectures.CategoryTheory.Etale.EtaleDegreeZeroHom
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRankZeroLocal
import WeilConjectures.SixFunctors.Etale.Derived.Exchange
import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-! # Geometric descent and ordered multiplication of vector integration

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-vector-trace-geometric-descent).

The maps of total spaces are specified on symmetric-algebra generators. The coefficient
maps use the existing ordered tensor of shifted ordinary Tate lines. All integrations
are the actual sheaf-glued maps, and compact support uses the proper/open normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor ZeroObject

namespace AlgebraicGeometry

namespace Etale

attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  vectorBundleIntegration vectorIntegrationGluing

private theorem derived_isIso_of_cover (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {I : Type u} {U : I → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    (ha : ∀ x : X, ∃ (i : I) (y : U i), (a i).base y = x)
    {M N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (φ : M ⟶ N)
    (h : ∀ i, IsIso ((upperStar (ModuleCat.{u + 1} A) (a i)).mapDerivedCategory.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} A)
    a ha _ fun i ↦ ?_
  exact (NatIso.isIso_map_iff
    ((upperStar (ModuleCat.{u + 1} A) (a i)).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (DerivedCategory.homologyFunctor _ n)
      ((upperStar (ModuleCat.{u + 1} A) (a i)).mapDerivedCategory.map φ))

private theorem derived_eq_of_cover (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} {I : Type u} {U : I → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    [∀ i, Etale (a i)]
    (ha : ∀ x : X, ∃ (i : I) (y : U i), (a i).base y = x)
    {K : DerivedCategoryModule A X}
    {M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj M)
    (φ ψ : K ⟶ (_root_.DerivedCategory.singleFunctor _ 0).obj N)
    (h : ∀ i, (ordinaryFinitePullback A (a i)).map φ =
      (ordinaryFinitePullback A (a i)).map ψ) : φ = ψ := by
  obtain ⟨ell, hell⟩ := (_root_.DerivedCategory.singleFunctor _ 0).map_surjective (α.inv ≫ φ)
  obtain ⟨mu, hmu⟩ := (_root_.DerivedCategory.singleFunctor _ 0).map_surjective (α.inv ≫ ψ)
  have he : α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell = φ := by
    rw [hell, ← Category.assoc, α.hom_inv_id, Category.id_comp]
  have hm : α.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map mu = ψ := by
    rw [hmu, ← Category.assoc, α.hom_inv_id, Category.id_comp]
  have hf : JointlyFaithful (fun i ↦ upperStar (ModuleCat.{u + 1} A) (a i)) := by
    apply JointlyReflectIsomorphisms.jointlyFaithful
    constructor
    intro P Q z hz
    exact isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} A) a ha z hz
  have heq : ell = mu := by
    apply hf.map_injective
    intro i
    have hh := congrArg (etaleDegreeZeroHomEquiv A (a i) α) (h i)
    rw [← he, ← hm, etaleDegreeZeroHomEquiv_map, etaleDegreeZeroHomEquiv_map] at hh
    rw [← NatIso.naturality_2 (upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} A) (a i) inferInstance) ell,
      ← NatIso.naturality_2 (upperStarIsoLocalizationRestriction
        (ModuleCat.{u + 1} A) (a i) inferInstance) mu, hh]
  rw [← he, ← hm, heq]

attribute [local irreducible] unboundedEtaleLowerShriekId affineLinearPullbackId
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensorSymmetry projectionMapOfCompactification

attribute [local implicit_reducible] ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor in
/-- Canonical coefficient comparison in a Cartesian bundle square, including Tate pullback.
Source: blueprint base-change display (blueprint: lem-pur-vector-trace-geometric-descent). -/
def vectorTraceCoefficientBaseChange (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] :
    (ordinaryFinitePullback A (VectorTraceGeometry.baseChange f r F)).obj
        (vectorIntegrationCoefficient A N hA S r F) ≅
      vectorIntegrationCoefficient A N hA T r ((Scheme.Modules.tensorPullback f).obj F) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (VectorTraceGeometry.baseChange f r F) (VectorBundleZeroSection.π S r F)).symm.app _ ≪≫
  (eqToIso (congrArg (ordinaryFinitePullback A)
    (VectorTraceGeometry.baseChange_isPullback f r F).w)).app _ ≪≫
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F)) f).app _ ≪≫
  (ordinaryFinitePullback A
    (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F))).mapIso
      (vectorIntegrationBaseCoefficientPullback A N hA t f hS r)

/-- Arbitrary Noetherian base change preserves the actual vector integration.
Source: blueprint paragraph 2, base-change equation
(blueprint: lem-pur-vector-trace-geometric-descent).
Proof: choose frames of F and pull them back along f. The generator-normalized Cartesian
square gives exactly the pulled-back frames. Paste exchange with each open restriction;
Tate pullback respects composition. The affine-space trace base-change equation gives
the displayed equality locally. Both sides have degree-zero source and target, since
exact inverse image preserves concentration. Degree-zero map gluing gives the equality
on T. No flatness, separation, or finite-type condition on f is used. -/
theorem vectorBundleIntegration_baseChange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] :
    (rightDerivedLowerShriekBaseChangeMap A
        (VectorTraceGeometry.baseChange_isPullback f r F)).app
        (vectorIntegrationCoefficient A N hA S r F) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F))).map
        (vectorTraceCoefficientBaseChange A N hA t f hS r F).hom ≫
      vectorBundleIntegration N hN A hA T (affineTracePullbackInvertible N f hS) r
        ((Scheme.Modules.tensorPullback f).obj F) =
      (ordinaryFinitePullback A f).map (vectorBundleIntegration N hN A hA S hS r F) ≫
        (ordinaryFiniteUnitPullback A f).hom := by
  classical
  let F' := (Scheme.Modules.tensorPullback f).obj F
  let c := vectorTraceCoefficientBaseChange A N hA t f hS r F
  have hex := isIso_rightDerivedLowerShriekBaseChangeMap A
    (VectorTraceGeometry.baseChange_isPullback f r F)
  have hexa := @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hex
    (vectorIntegrationCoefficient A N hA S r F)
  let b : (ordinaryFinitePullback A f).obj (vectorIntegrationSource A N hA S r F) ≅
      vectorIntegrationSource A N hA T r F' :=
    @asIso _ _ _ _ ((rightDerivedLowerShriekBaseChangeMap A
      (VectorTraceGeometry.baseChange_isPullback f r F)).app
      (vectorIntegrationCoefficient A N hA S r F)) hexa ≪≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π T r F')).mapIso c
  have hnS : VectorIntegrationNormalization N hN A hA S hS r F
      (vectorBundleIntegration N hN A hA S hS r F) := by
    unfold vectorBundleIntegration vectorIntegrationGluing
    exact (existsUnique_vectorIntegrationGluing N hN A hA S hS r F).2.exists.choose_spec.2
  have hnT : VectorIntegrationNormalization N hN A hA T
      (affineTracePullbackInvertible N f hS) r F'
      (vectorBundleIntegration N hN A hA T (affineTracePullbackInvertible N f hS) r F') := by
    unfold vectorBundleIntegration vectorIntegrationGluing
    exact (existsUnique_vectorIntegrationGluing N hN A hA T
      (affineTracePullbackInvertible N f hS) r F').2.exists.choose_spec.2
  obtain ⟨I, V, hV, eS⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := r)
  obtain ⟨J, U, hU, eT⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F' (r := r)
  let O : I × J → T.Opens := fun ij ↦ (f ⁻¹ᵁ V ij.1) ⊓ U ij.2
  have hO : ∀ x : T, ∃ (ij : I × J) (y : (O ij).toScheme), (O ij).ι.base y = x := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ (f.base x)) : f.base x ∈ ⨆ i, V i)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hU.ge (Set.mem_univ x) : x ∈ ⨆ j, U j)
    exact ⟨(i, j), ⟨x, hi, hj⟩, rfl⟩
  have heq : b.hom ≫
      vectorBundleIntegration N hN A hA T (affineTracePullbackInvertible N f hS) r F' =
      (ordinaryFinitePullback A f).map (vectorBundleIntegration N hN A hA S hS r F) ≫
        (ordinaryFiniteUnitPullback A f).hom := by
    apply derived_eq_of_cover A (fun ij : I × J ↦ (O ij).ι) hO
      (b ≪≫ (vectorIntegrationGluing N hN A hA T
        (affineTracePullbackInvertible N f hS) r F').1)
    intro ij
    let W := O ij
    let : TopologicalSpace.NoetherianSpace W.toScheme :=
      W.ι.isOpenEmbedding.isInducing.noetherianSpace
    let : IsNoetherian W.toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    obtain ⟨t', D, _, _⟩ := exists_affineSpaceTopTrace N hN A hA
    have ht : t' = t := ordinaryFiniteTwistTransport_unique A N hA t' t
    subst t'
    apply vectorIntegration_baseChange_local N hN A hA t f hS r F c rfl b rfl D
      (V ij.1) (eS ij.1).some (U ij.2) (eT ij.2).some W.toScheme W.ι
      (T.homOfLE (inf_le_right : W ≤ U ij.2))
      (T.homOfLE (inf_le_left : W ≤ f ⁻¹ᵁ V ij.1) ≫ (f ∣_ V ij.1))
    · exact Scheme.homOfLE_ι T _
    · rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    · exact hnS t D (V ij.1) (eS ij.1).some
    · exact hnT t D (U ij.2) (eT ij.2).some
  exact (Category.assoc _ _ _).symm.trans heq

/-- The fibre bundle q over E(G), formed from the actual module pullback p^*F.
Source: blueprint paragraph 2, direct sums
(blueprint: lem-pur-vector-trace-geometric-descent). -/
abbrev vectorTraceFibreModule (S : Scheme.{u}) [IsNoetherian S] (s : ℕ) (F G : S.Modules)
    [G.IsFiniteLocallyFreeOfRank s] : (VectorBundleZeroSection.scheme S s G).Modules :=
  (Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F

/-- q is the structural map of the pulled-back rank-r bundle.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent). -/
abbrev vectorTraceQ (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :=
  VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
    (vectorTraceFibreModule S s F G)

/-- The composite projection h=pq on the canonical product presentation.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent). -/
abbrev vectorTraceH (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :=
  vectorTraceQ S r s F G ≫ VectorBundleZeroSection.π S s G

/-- W_h on the product presentation, before the ordered coefficient decomposition.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent). -/
abbrev vectorTraceSumCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :=
  (ordinaryFinitePullback A (vectorTraceH S r s F G)).obj
    (affineLinearBaseCoefficient A N hA S (r + s))

/-- The actual exchange as an isomorphism, transported to the existing derived pullback.
Invertibility is supplied by the unbounded comparison theorem, with its specified maps.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent). -/
def vectorTraceExchangeIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v' f' f v) (W : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A v).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W) ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').obj
        ((ordinaryFinitePullback A v').obj W) := by
  letI := (unboundedEtaleCompactSupport_baseChange A sq).1
  exact (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).app _ ≪≫
    asIso ((unboundedEtaleCompactSupportBaseChange A sq).app W) ≪≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v').symm.app W)

/-- Coefficient transport along the canonical product identification of total spaces.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent). -/
def vectorTraceSumTransport (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    (ordinaryFinitePullback A (VectorTraceGeometry.sumIso S r s F G).hom).obj
        (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G)) ≅
      vectorTraceSumCoefficient A N hA S r s F G :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (VectorTraceGeometry.sumIso S r s F G).hom
    (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))
    (vectorTraceH S r s F G)
    (by simpa only [Category.comp_id] using
      (VectorTraceGeometry.sumIso_isPullback S r s F G).w.symm)).symm.app _

attribute [instance] vectorTrace_projection_isIso
attribute [local instance 2000] compact_projection_isIso
attribute [local irreducible] compactSupportProjectionMap

attribute [local irreducible] vectorTraceSumDecomposition vectorTraceSumIntegration
  vectorTraceSumTransport vectorTraceExchangeIso vectorTraceCoefficientBaseChange

section DirectSumDescent

attribute [local irreducible] Scheme.Modules.tensorPullback affineLinearBaseCoefficient
  VectorTraceGeometry.sumIso unboundedEtaleLowerShriekCompIso
  unboundedEtaleCompactSupportBaseChange derivedTensorSingleUnitIso

attribute [local irreducible] AlgebraicGeometry.Etale.rightDerivedLowerShriek
  AlgebraicGeometry.Etale.upperStar AlgebraicGeometry.Etale.lowerStar
  AlgebraicGeometry.VectorBundleZeroSection.π AlgebraicGeometry.VectorBundleZeroSection.scheme
  AlgebraicGeometry.Etale.leftDerivedUpperStarComp
  AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory

end DirectSumDescent

end Etale
end AlgebraicGeometry
