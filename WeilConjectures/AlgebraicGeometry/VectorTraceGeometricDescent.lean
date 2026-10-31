/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.AlgebraicGeometry.ShriekTensorCompositionSupplement
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

import WeilConjectures.AlgebraicGeometry.VectorIntegrationDirectSumLocal
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSwapLocal
import WeilConjectures.AlgebraicGeometry.VectorIntegrationBaseChangeLocal
import WeilConjectures.AlgebraicGeometry.EtaleDegreeZeroHom
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
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
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
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
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
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
import WeilConjectures.AlgebraicGeometry.VectorIntegrationRankZeroLocal
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
private theorem vectorIntegration_eq_of_normalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r]
    (k : vectorIntegrationSource A N hA S r F ⟶ ordinaryFiniteUnit A S)
    (hk : VectorIntegrationNormalization N hN A hA S hS r F k) :
    k = vectorBundleIntegration N hN A hA S hS r F := by
  let p := vectorIntegrationGluing N hN A hA S hS r F
  obtain ⟨ell, hell⟩ := (_root_.DerivedCategory.singleFunctor _ 0).map_surjective
    (p.1.inv ≫ k)
  have he : p.1.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ell = k := by
    rw [hell, ← Category.assoc, p.1.hom_inv_id, Category.id_comp]
  have hp' : (_root_.DerivedCategory.homologyFunctor _ 0).map p.1.hom ≫
      (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app
        (vectorIntegrationSheaf A N hA S r F) =
        𝟙 (vectorIntegrationSheaf A N hA S r F) ∧
      VectorIntegrationNormalization N hN A hA S hS r F
        (p.1.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map p.2) := by
    dsimp only [p]
    unfold vectorIntegrationGluing
    exact (existsUnique_vectorIntegrationGluing N hN A hA S hS r F).2.exists.choose_spec
  have heq : (p.1, ell) = p :=
    (existsUnique_vectorIntegrationGluing N hN A hA S hS r F).2.unique
      ⟨hp'.1, by rw [he]; exact hk⟩ hp'
  have hell' : ell = p.2 := congrArg Prod.snd heq
  rw [← he, hell']
  unfold vectorBundleIntegration
  rfl

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

/-- The actual t_h, transported from the existing integration on E(F direct-sum G)
through the canonical product isomorphism and its normalized exchange.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent). -/
def vectorTraceSumIntegration (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (vectorTraceH S r s F G)).obj
        (vectorTraceSumCoefficient A N hA S r s F G) ⟶ ordinaryFiniteUnit A S :=
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (vectorTraceH S r s F G)).map
      (vectorTraceSumTransport A N hA S r s F G).inv ≫
    (vectorTraceExchangeIso A (VectorTraceGeometry.sumIso_isPullback S r s F G)
      (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))).inv ≫
    (affineLinearPullbackId A S).hom.app _ ≫
    vectorBundleIntegration N hN A hA S hS (r + s) (VectorTraceGeometry.sum S F G)

/-- The ordered identification W_h = q^*W_p tensor W_q. Every factor uses the ordinary
Tate pullback and shifted tensor comparisons, without a chosen orientation.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent). -/
def vectorTraceSumDecomposition (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    vectorTraceSumCoefficient A N hA S r s F G ≅
      ((ordinaryFiniteTensor A _).obj
        ((upperStar (ModuleCat.{u + 1} A) (vectorTraceQ S r s F G)).mapDerivedCategory.obj
          (vectorIntegrationCoefficient A N hA S s G))).obj
        (vectorIntegrationCoefficient A N hA (VectorBundleZeroSection.scheme S s G) r
          (vectorTraceFibreModule S s F G)) :=
  (ordinaryFinitePullback A (vectorTraceH S r s F G)).mapIso
      (eqToIso (congrArg (affineLinearBaseCoefficient A N hA S) (Nat.add_comm r s)) ≪≫
        WeilConjectures.PurityFiniteSetting.purityPowerAdd A N hA S s r) ≪≫
    ordinaryFiniteTensorPullback A (vectorTraceH S r s F G)
      (affineLinearBaseCoefficient A N hA S s) (affineLinearBaseCoefficient A N hA S r) ≪≫
    ordinaryFiniteTensorRightMapIso A _
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (vectorTraceQ S r s F G)
        (VectorBundleZeroSection.π S s G)).app _ ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
          (vectorTraceQ S r s F G)).app (vectorIntegrationCoefficient A N hA S s G))
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (vectorTraceQ S r s F G)
        (VectorBundleZeroSection.π S s G)).app _ ≪≫
        (ordinaryFinitePullback A (vectorTraceQ S r s F G)).mapIso
          (vectorIntegrationBaseCoefficientPullback A N hA t
            (VectorBundleZeroSection.π S s G) hS r))

private theorem compact_projection_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    IsIso (compactSupportProjectionMap A f M K) := by
  let := isIso_projectionMap_of_finite A f
  have hp : IsIso (((projectionMap (ModuleCat.{u + 1} A) f).app M).app K) :=
    inferInstance
  have hpull : IsIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K) :=
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app K).isIso_hom
  have htensor : IsIso (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)) :=
    Functor.map_isIso _ _
  have hmap : IsIso ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K))) :=
    Functor.map_isIso _ _
  have (Z : Scheme.{u}) (L Q : DerivedCategoryModule A Z) :
      IsIso (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).hom.app L).app Q) :=
    (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).app L).app Q).isIso_hom
  have (Z : Scheme.{u}) (L Q : DerivedCategoryModule A Z) :
      IsIso (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).inv.app L).app Q) :=
    (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).app L).app Q).isIso_inv
  change IsIso
    (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
      ((projectionMap (ModuleCat.{u + 1} A) f).app M).app K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).app M))
  apply IsIso.comp_isIso' (by infer_instance)
  apply IsIso.comp_isIso' hp
  apply IsIso.comp_isIso' hmap
  have hs : IsIso (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).app M) :=
    (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).app
      ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).app M).isIso_inv
  exact Functor.map_isIso _ _

/-- The canonical proper/open projection map for q is invertible for these coefficients.
Source: blueprint proof Step 5 (blueprint: lem-pur-vector-trace-geometric-descent).
Proof: on a compactification the proper projection is invertible for arbitrary unbounded
complexes by lem-amb-proper-coproducts-projection. The open tensor comparison is an
isomorphism by lem-pur-etale-open-derived-tensor. The exact-derived inverse-image and
signed symmetries are isomorphisms. Their composite is the specified projection map. -/
theorem vectorTrace_projection_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r]
    (M : DerivedCategoryModule A (VectorBundleZeroSection.scheme S r F))
    (K : DerivedCategoryModule A S) :
    IsIso (compactSupportProjectionMap A (VectorBundleZeroSection.π S r F) M K) := by
  exact compact_projection_isIso A (VectorBundleZeroSection.π S r F) M K

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

/-- The ordered direct-sum integration equation, with the actual coefficient-first
projection and the actual compact-support compositor.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent).
Proof: choose simultaneous frames of F and G. The symmetric-algebra product comparison
puts the s base coordinates before the r fibre coordinates. Expand the ordered affine
adjunction counits; their composite is the same counit, by associativity and units of
lem-amb-unbounded-compact-support-comparisons. Apply
lem-pur-ordinary-affine-counit-tensor-normalization at K=W_p to identify the inner counit
with the inverse projection, tensor with t_q, and the right unitor. Restrictions respect
these maps by lem-asd-compact-projection-exchange and lem-amb-shriek-tensor-composition.
The base-change equation identifies t_q on each frame. The common source has only H^0,
so lem-pur-degree-zero-derived-map-gluing descends the equality. No affine intersection
is needed. -/
theorem vectorBundleIntegration_directSum (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    (unboundedEtaleLowerShriekCompIso A (vectorTraceQ S r s F G)
        (VectorBundleZeroSection.π S s G)).hom.app
        (vectorTraceSumCoefficient A N hA S r s F G) ≫
      vectorTraceSumIntegration N hN A hA S hS r s F G =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (VectorBundleZeroSection.π S s G)).map
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (vectorTraceQ S r s F G)).map
          (vectorTraceSumDecomposition A N hA t S hS r s F G).hom ≫
        inv (compactSupportProjectionMap A (vectorTraceQ S r s F G)
          (vectorIntegrationCoefficient A N hA (VectorBundleZeroSection.scheme S s G) r
            (vectorTraceFibreModule S s F G)) (vectorIntegrationCoefficient A N hA S s G)) ≫
        ((ordinaryFiniteTensor A _).obj (vectorIntegrationCoefficient A N hA S s G)).map
          (vectorBundleIntegration N hN A hA (VectorBundleZeroSection.scheme S s G)
            (affineTracePullbackInvertible N (VectorBundleZeroSection.π S s G) hS) r
            (vectorTraceFibreModule S s F G)) ≫
        (derivedTensorSingleUnitIso (vectorIntegrationCoefficient A N hA S s G)).hom) ≫
      vectorBundleIntegration N hN A hA S hS s G := by
  classical
  obtain ⟨I, V, hV, eF⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := r)
  obtain ⟨J, U, hU, eG⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free G (r := s)
  let O : I × J → S.Opens := fun ij ↦ V ij.1 ⊓ U ij.2
  have hO : ∀ x : S, ∃ (ij : I × J) (y : (O ij).toScheme), (O ij).ι.base y = x := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ x) : x ∈ ⨆ i, V i)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hU.ge (Set.mem_univ x) : x ∈ ⨆ j, U j)
    exact ⟨(i, j), ⟨x, hi, hj⟩, rfl⟩
  let b :=
    (unboundedEtaleLowerShriekCompIso A (vectorTraceQ S r s F G)
      (VectorBundleZeroSection.π S s G)).app
        (vectorTraceSumCoefficient A N hA S r s F G) ≪≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (vectorTraceH S r s F G)).mapIso
      (vectorTraceSumTransport A N hA S r s F G).symm ≪≫
    (vectorTraceExchangeIso A (VectorTraceGeometry.sumIso_isPullback S r s F G)
      (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))).symm ≪≫
    (affineLinearPullbackId A S).app _ ≪≫
    (vectorIntegrationGluing N hN A hA S hS (r + s) (VectorTraceGeometry.sum S F G)).1
  have hsum : vectorTraceSumIntegration N hN A hA S hS r s F G =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (vectorTraceH S r s F G)).map
          (vectorTraceSumTransport A N hA S r s F G).inv ≫
        (vectorTraceExchangeIso A (VectorTraceGeometry.sumIso_isPullback S r s F G)
          (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G))).inv ≫
        (affineLinearPullbackId A S).hom.app _ ≫
        vectorBundleIntegration N hN A hA S hS (r + s) (VectorTraceGeometry.sum S F G) := by
    unfold vectorTraceSumIntegration
    rfl
  apply derived_eq_of_cover A (fun ij : I × J ↦ (O ij).ι) hO b
  intro ij
  have hlocal := vectorIntegration_directSum_local N hN A hA t S hS r s F G
    (V ij.1) (U ij.2) (eF ij.1).some (eG ij.2).some (O ij) inf_le_left inf_le_right
  specialize hlocal (vectorTraceSumTransport A N hA S r s F G)
    (by unfold vectorTraceSumTransport; rfl)
  specialize hlocal
    (vectorTraceExchangeIso A (VectorTraceGeometry.sumIso_isPullback S r s F G)
      (vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G)))
    (by unfold vectorTraceExchangeIso; rfl)
  specialize hlocal (vectorTraceSumDecomposition A N hA t S hS r s F G)
    (by unfold vectorTraceSumDecomposition; rfl)
  exact (congrArg (fun z ↦ (ordinaryFinitePullback A (O ij).ι).map
    ((unboundedEtaleLowerShriekCompIso A (vectorTraceQ S r s F G)
      (VectorBundleZeroSection.π S s G)).hom.app
        (vectorTraceSumCoefficient A N hA S r s F G) ≫ z)) hsum).trans hlocal

end DirectSumDescent

/-- Every actual compactification triangle gives the same multiplication equation.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent).
Proof: expand purityCompactComposition into its proper/open comparison, composition,
and independence maps. The unbounded comparison theorem identifies this with the
specified compositor, independently of the two compactifications and their refinements.
Evaluating at W_h and composing with the actual trace gives this equality. -/
theorem vectorBundleIntegration_compactificationTriangle (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (c : Compactification (VectorBundleZeroSection.π S s G))
    (e : Compactification (vectorTraceQ S r s F G ≫ c.i)) :
    (WeilConjectures.PurityFiniteSetting.purityCompactComposition A
        (vectorTraceQ S r s F G) (VectorBundleZeroSection.π S s G)
        (vectorTraceH S r s F G) rfl c e).inv.app
        (vectorTraceSumCoefficient A N hA S r s F G) ≫
      vectorTraceSumIntegration N hN A hA S hS r s F G =
    (unboundedEtaleLowerShriekCompIso A (vectorTraceQ S r s F G)
        (VectorBundleZeroSection.π S s G)).hom.app
        (vectorTraceSumCoefficient A N hA S r s F G) ≫
      vectorTraceSumIntegration N hN A hA S hS r s F G := by
  rw [unboundedEtaleLowerShriekCompIso_tower A (vectorTraceQ S r s F G)
    (VectorBundleZeroSection.π S s G) c e]
  simp only [WeilConjectures.PurityFiniteSetting.purityCompactComposition,
    Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.hcomp_app, Category.assoc]

/-- Tate/shift transport for the actual coordinate permutation of the two blocks.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent). -/
def vectorTraceSwapCoefficient (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    (ordinaryFinitePullback A (VectorTraceGeometry.swap S r s F G)).obj
        (vectorIntegrationCoefficient A N hA S (s + r) (VectorTraceGeometry.sum S G F)) ≅
      vectorIntegrationCoefficient A N hA S (r + s) (VectorTraceGeometry.sum S F G) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (VectorTraceGeometry.swap S r s F G)
    (VectorBundleZeroSection.π S (s + r) (VectorTraceGeometry.sum S G F))
    (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))
    (by simpa only [Category.comp_id] using
      (VectorTraceGeometry.swap_isPullback S r s F G).w.symm)).symm.app _ ≪≫
  (ordinaryFinitePullback A
    (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))).mapIso
    (eqToIso (congrArg (affineLinearBaseCoefficient A N hA S) (Nat.add_comm s r)))

/-- Swapping the ordered blocks leaves the integration, hence either ordered formula,
unchanged under the canonical coordinate and coefficient comparisons.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent).
Proof: choose simultaneous frames. The map is the permutation of the two coordinate
blocks because its symmetric-algebra map is specified by the biproduct braiding.
Linear trace invariance fixes the affine trace. The shifts have interchange sign
(-1)^(4rs)=1, and the powers of the same rank-one Tate line have symmetric multiplication.
Degree-zero map gluing descends this equality from the simultaneous frame cover. -/
theorem vectorBundleIntegration_swap (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r s : ℕ)
    (F G : S.Modules) [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    (rightDerivedLowerShriekBaseChangeMap A
        (VectorTraceGeometry.swap_isPullback S r s F G)).app
        (vectorIntegrationCoefficient A N hA S (s + r) (VectorTraceGeometry.sum S G F)) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))).map
        (vectorTraceSwapCoefficient A N hA S r s F G).hom ≫
      vectorBundleIntegration N hN A hA S hS (r + s) (VectorTraceGeometry.sum S F G) =
    (ordinaryFinitePullback A (𝟙 S)).map
        (vectorBundleIntegration N hN A hA S hS (s + r) (VectorTraceGeometry.sum S G F)) ≫
      (ordinaryFiniteUnitPullback A (𝟙 S)).hom := by
  have hex := isIso_rightDerivedLowerShriekBaseChangeMap A
    (VectorTraceGeometry.swap_isPullback S r s F G)
  have hexa := @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hex
    (vectorIntegrationCoefficient A N hA S (s + r) (VectorTraceGeometry.sum S G F))
  let c := vectorTraceSwapCoefficient A N hA S r s F G
  let b := @asIso _ _ _ _ ((rightDerivedLowerShriekBaseChangeMap A
      (VectorTraceGeometry.swap_isPullback S r s F G)).app
      (vectorIntegrationCoefficient A N hA S (s + r) (VectorTraceGeometry.sum S G F))) hexa ≪≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π S (r + s) (VectorTraceGeometry.sum S F G))).mapIso c
  let k : vectorIntegrationSource A N hA S (r + s) (VectorTraceGeometry.sum S F G) ⟶
      ordinaryFiniteUnit A S :=
    b.inv ≫ (ordinaryFinitePullback A (𝟙 S)).map
      (vectorBundleIntegration N hN A hA S hS (s + r) (VectorTraceGeometry.sum S G F)) ≫
        (ordinaryFiniteUnitPullback A (𝟙 S)).hom
  have hk : k = vectorBundleIntegration N hN A hA S hS (r + s)
      (VectorTraceGeometry.sum S F G) := by
    apply vectorIntegration_eq_of_normalization N hN A hA S hS (r + s) _ k
    intro t D V e
    let e' : VectorBundleZeroSection.Trivialization S (s + r)
        (VectorTraceGeometry.sum S G F) V :=
      (Scheme.Modules.restrictFunctor V.ι).mapIso (biprod.braiding G F) ≪≫ e ≪≫
        eqToIso (congrArg (fun d ↦ SheafOfModules.free
          (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d))) (Nat.add_comm r s))
    have hn : VectorIntegrationNormalization N hN A hA S hS (s + r)
        (VectorTraceGeometry.sum S G F)
        (vectorBundleIntegration N hN A hA S hS (s + r) (VectorTraceGeometry.sum S G F)) := by
      unfold vectorBundleIntegration vectorIntegrationGluing
      exact (existsUnique_vectorIntegrationGluing N hN A hA S hS (s + r)
        (VectorTraceGeometry.sum S G F)).2.exists.choose_spec.2
    exact vectorIntegration_swap_local N hN A hA S hS r s F G c rfl b rfl t D V e e'
      (vectorBundleIntegration N hN A hA S hS (s + r) (VectorTraceGeometry.sum S G F))
      (hn t D V e')
  have he : b.hom ≫ k = (ordinaryFinitePullback A (𝟙 S)).map
        (vectorBundleIntegration N hN A hA S hS (s + r) (VectorTraceGeometry.sum S G F)) ≫
      (ordinaryFiniteUnitPullback A (𝟙 S)).hom := by
    dsimp only [k]
    exact b.hom_inv_id_assoc _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ b.hom ≫ z) hk.symm).trans he)

/-- Every trace source is concentrated in degree zero, and its actual trace is invertible.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent).
Proof: on every frame open, exchange identifies the source and trace with the affine
space source and trace. Affine top trace is an isomorphism to A[0]. Exact restriction
commutes with cohomology; jointly surjective restriction detects both vanishing and
isomorphisms. This applies to all ranks, the zero ring, and the empty scheme. -/
theorem vectorBundleIntegration_concentration_and_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r] :
    (∀ q : ℤ, q ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (vectorIntegrationSource A N hA S r F))) ∧
    IsIso (vectorBundleIntegration N hN A hA S hS r F) := by
  refine ⟨vectorIntegration_cohomology_zero N hN A hA S hS r F, ?_⟩
  classical
  obtain ⟨t, D, htD, htrace⟩ := exists_affineSpaceTopTrace N hN A hA
  obtain ⟨I, V, hV, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := r)
  have hn : VectorIntegrationNormalization N hN A hA S hS r F
      (vectorBundleIntegration N hN A hA S hS r F) := by
    unfold vectorBundleIntegration vectorIntegrationGluing
    exact (existsUnique_vectorIntegrationGluing N hN A hA S hS r F).2.exists.choose_spec.2
  let := (vectorIntegration_geometry S r F).1
  let := (vectorIntegration_geometry S r F).2.1
  apply derived_isIso_of_cover A (fun i : I ↦ (V i).ι)
    (φ := vectorBundleIntegration N hN A hA S hS r F) ?_
  · intro i
    let : TopologicalSpace.NoetherianSpace (V i).toScheme :=
      (V i).ι.isOpenEmbedding.isInducing.noetherianSpace
    let : IsNoetherian (V i).toScheme :=
      { toIsLocallyNoetherian := inferInstance
        isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
    let hi := affineTracePullbackInvertible N (V i).ι hS
    let := (htrace (V i).toScheme hi r).2.2.1
    have hl : IsIso (vectorIntegrationLocalTrace N hN A hA t D S hS r F
        (V i) (e i).some) := by
      dsimp only [vectorIntegrationLocalTrace]
      have hex := isIso_rightDerivedLowerShriekBaseChangeMap A
        (vectorIntegrationChart_isPullback S r F (V i) (e i).some)
      have hexa := @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hex
        (vectorIntegrationCoefficient A N hA S r F)
      apply IsIso.comp_isIso' hexa
      apply IsIso.comp_isIso' (by infer_instance)
      apply IsIso.comp_isIso' (by infer_instance)
      infer_instance
    have heq := hn t D (V i) (e i).some
    rw [← heq] at hl
    apply (NatIso.isIso_map_iff
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (V i).ι) _).1
    exact (isIso_comp_right_iff _ (ordinaryFiniteUnitPullback A (V i).ι).hom).1 hl
  · intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ x) : x ∈ ⨆ i, V i)
    exact ⟨i, ⟨x, hi⟩, rfl⟩

/-- Rank zero is the identity-adjunction trace under the canonical E(0)=S comparison.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent).
Proof: each rank-zero frame has the empty coordinate tower, whose adjunction is the
identity and whose counit is the identity map. Its source comparison is precisely the
exchange with the identity bundle and the unit comparisons displayed here. Frame
normalization of the existing glued trace gives this equation, including on empty S. -/
theorem vectorBundleIntegration_zero (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank 0] :
    (rightDerivedLowerShriekBaseChangeMap A
        (VectorTraceGeometry.zero_isPullback S F)).app (ordinaryFiniteUnit A S) ≫
      vectorBundleIntegration N hN A hA S hS 0 F =
    (ordinaryFinitePullback A (𝟙 S)).map
        ((unboundedEtaleLowerShriekId A S).hom.app (ordinaryFiniteUnit A S)) ≫
      (affineLinearPullbackId A S).hom.app (ordinaryFiniteUnit A S) := by
  let := isIso_rightDerivedLowerShriekBaseChangeMap A
    (VectorTraceGeometry.zero_isPullback S F)
  let b := asIso ((rightDerivedLowerShriekBaseChangeMap A
    (VectorTraceGeometry.zero_isPullback S F)).app (ordinaryFiniteUnit A S))
  let k : vectorIntegrationSource A N hA S 0 F ⟶ ordinaryFiniteUnit A S :=
    b.inv ≫ (ordinaryFinitePullback A (𝟙 S)).map
      ((unboundedEtaleLowerShriekId A S).hom.app (ordinaryFiniteUnit A S)) ≫
        (affineLinearPullbackId A S).hom.app (ordinaryFiniteUnit A S)
  have hk : k = vectorBundleIntegration N hN A hA S hS 0 F := by
    apply vectorIntegration_eq_of_normalization N hN A hA S hS 0 F k
    intro t D V e
    exact vectorIntegration_rankZero_localIdentity N hN A hA S hS F b rfl t D V e
  rw [← hk]
  change b.hom ≫ (b.inv ≫ _) = _
  rw [← Category.assoc, b.hom_inv_id, Category.id_comp]

/-- On the empty base the trace is the unique arrow of its indicated type.
Source: blueprint paragraph 2 (blueprint: lem-pur-vector-trace-geometric-descent).
Proof: every module sheaf on the empty etale site is zero, and consequently every
complex in its derived category is zero. Its Hom sets are subsingletons, so every arrow
of this type equals the actual trace. -/
theorem vectorBundleIntegration_empty (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] [IsEmpty S] (hS : IsUnit (N : Γ(S, ⊤))) (r : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r]
    (k : vectorIntegrationSource A N hA S r F ⟶ ordinaryFiniteUnit A S) :
    k = vectorBundleIntegration N hN A hA S hS r F := by
  have hz : IsIso (0 : ordinaryFiniteUnit A S ⟶ 0) := by
    apply derived_isIso_of_cover A (I := PEmpty.{u + 1})
      (U := fun i ↦ PEmpty.elim i) (fun i ↦ PEmpty.elim i)
      (φ := (0 : ordinaryFiniteUnit A S ⟶ 0))
    · intro x
      exact isEmptyElim x
    · intro i
      exact PEmpty.elim i
  exact ((isZero_zero _).of_iso (asIso (0 : ordinaryFiniteUnit A S ⟶ 0))).eq_of_tgt _ _

end Etale
end AlgebraicGeometry
