/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorIntegrationCartesianTrace
import WeilConjectures.AlgebraicGeometry.Section.SectionPullbackCoefficientNaturality
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteUnitCoordinateIdentifications
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
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
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitSquare
import WeilConjectures.AlgebraicGeometry.EtaleSectionUnitNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.CategoryTheory.SectionConjugateComparison
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantPullbackHom
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The zero-section restriction of vector integration base change -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteRingSectionDeformation

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local implicit_reducible] CategoryTheory.catToReflQuiver Scheme.instCategory
  Scheme.Modules
  ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
attribute [local instance 20002] Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
-- Use the localization instances already cached by the ordinary inverse image.
set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13
attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory
  VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence
  leftDerivedUpperStarComp leftDerivedUpperStarCompSectionIso
  rightDerivedLowerShriek rightDerivedUpperShriek rightDerivedUpperShriekAdjunction
  vectorBundleIntegration

private theorem integration_mate_square
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
    (ex : L ⋙ H ≅ G ⋙ L') {W : C} {W' : C'} {U : D} {U' : D'}
    (a : G.obj W ⟶ W') (t : L.obj W ⟶ U) (t' : L'.obj W' ⟶ U')
    (c : H.obj U ⟶ U')
    (ht : ex.hom.app W ≫ L'.map a ≫ t' = H.map t ≫ c) :
    G.map (adj.homEquiv W U t) ≫ (mateEquiv adj adj' ex.inv).app U ≫ R'.map c =
      a ≫ adj'.homEquiv W' U' t' := by
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := adj'.counit.naturality c
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  have ht' : L'.map (adj'.homEquiv W' U' t') ≫ adj'.counit.app U' = t' := by
    simpa only [Adjunction.homEquiv_counit] using
      (adj'.homEquiv W' U').symm_apply_apply t'
  rw [ht']
  rw [reassoc_of% (mateEquiv_counit adj adj' ex.inv U)]
  have he := ex.inv.naturality (adj.homEquiv W U t)
  dsimp only [Functor.comp_map] at he
  rw [reassoc_of% he]
  rw [← H.map_comp_assoc]
  rw [← adj.homEquiv_counit, Equiv.symm_apply_apply]
  have h := congrArg (fun k ↦ ex.inv.app W ≫ k) ht
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using h.symm

/-- Restrict the integration adjunct square to zero sections in a Cartesian bundle
presentation. Source: latest blueprint, sec-smooth-purity/sk-prop-sp-purity-bc,
sk-prop-sp-purity-bc-factors.proof.md, proof (1), normal-bundle integration step.
(blueprint: lem-sp-finite-bundle-section-adjoint-base-change).

Cancel the coefficient-to-unit isomorphism from scalar trace base change. Transpose
under the compact-support adjunctions; the mate is the exceptional exchange map with
its unit coordinates. Restrict the resulting coefficient square along the zero
sections using sectionPullback_coefficient_naturality. The section equations and
pullback unit comparisons identify the two coefficient restrictions. This also
covers rank zero and empty schemes without a case distinction. -/
theorem bundleSectionAdjoint_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (hB : IsUnit (N : Γ(B, ⊤))) (hB' : IsUnit (N : Γ(B', ⊤)))
    (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    (b : B' ⟶ B)
    (v : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F)
    (sq : IsPullback v (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) b)
    (hz : VectorBundleZeroSection.zero B' d F' ≫ v =
      b ≫ VectorBundleZeroSection.zero B d F) :
    (ordinaryFinitePullback A b).map
        (FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA B hB d F) ≫
      NoetherianSectionSpecialization.sectionMap A
        (VectorBundleZeroSection.π B d F) (VectorBundleZeroSection.π B' d F') b v sq
        (VectorBundleZeroSection.zero B d F) (VectorBundleZeroSection.zero B' d F') hz =
      (vectorIntegrationBaseCoefficientPullback A N hA
        (WeilConjectures.PurityFiniteSetting.purityTwistTransport A N hN hA) b hB d).hom ≫
        FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA B' hB' d F' := by
  let π := VectorBundleZeroSection.π B d F
  let π' := VectorBundleZeroSection.π B' d F'
  let C := affineLinearBaseCoefficient A N hA B d
  let C' := affineLinearBaseCoefficient A N hA B' d
  let c := vectorIntegrationBaseCoefficientPullback A N hA
    (WeilConjectures.PurityFiniteSetting.purityTwistTransport A N hN hA) b hB d
  let a := (WeilConjectures.PurityFiniteSetting.purityPullbackSquare A sq C ≪≫
    (ordinaryFinitePullback A π').mapIso c).hom
  let adj := vectorBundlePurityAdjunction A B d F
  let adj' := vectorBundlePurityAdjunction A B' d F'
  let t := vectorBundleIntegration N hN A hA B hB d F
  let t' := vectorBundleIntegration N hN A hA B' hB' d F'
  have htrace := WeilConjectures.PurityFiniteSetting.vectorIntegration_cartesianTrace
    A N hN hA hB hB' d F F' sq
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  let ex := asIso (rightDerivedLowerShriekBaseChangeMap A sq)
  have ht : ex.hom.app _ ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) π').map a ≫ t' =
      (ordinaryFinitePullback A b).map t ≫ (ordinaryFiniteUnitPullback A b).hom := by
    apply (cancel_mono (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B').hom).1
    simp only [Category.assoc]
    erw [ordinaryFiniteUnitPullback_hom_unit]
    dsimp only [ex, a, t, t', π, π', C, c,
      WeilConjectures.PurityFiniteSetting.RfPullback,
      WeilConjectures.PurityFiniteSetting.RfShriek, vectorIntegrationCoefficient] at htrace ⊢
    simpa only [asIso_hom, Functor.map_comp, Category.assoc] using htrace
  have hm := integration_mate_square adj adj' (ordinaryFinitePullback A v)
    (ordinaryFinitePullback A b) ex a t t' (ordinaryFiniteUnitPullback A b).hom ht
  rw [FiniteSmoothPurity.ordinaryFiniteUnitPullback_eq_unitCoordinates] at hm
  change (ordinaryFinitePullback A v).map
      (FiniteRingSectionDeformation.bundleAdjoint N hN A hA B hB d F) ≫
        dualizingComplexBaseChangeMap A sq =
      a ≫ FiniteRingSectionDeformation.bundleAdjoint N hN A hA B' hB' d F' at hm
  dsimp only [a, WeilConjectures.PurityFiniteSetting.purityPullbackSquare,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom] at hm
  simp only [Category.assoc] at hm
  have hc := sectionPullback_coefficient_naturality A b π π' v
    (VectorBundleZeroSection.zero B d F) (VectorBundleZeroSection.zero B' d F')
    sq.w hz (VectorBundleZeroSection.zero_spec B d F).1
    (VectorBundleZeroSection.zero_spec B' d F').1 C C' _ _ c.hom
    (FiniteRingSectionDeformation.bundleAdjoint N hN A hA B hB d F)
    (FiniteRingSectionDeformation.bundleAdjoint N hN A hA B' hB' d F')
    (dualizingComplexBaseChangeMap A sq) hm
  dsimp only [FiniteRingSectionDeformation.bundleSectionAdjoint,
    NoetherianSectionSpecialization.sectionMap, sectionInvariant, ordinaryFinitePullback,
    Iso.app_hom, Iso.app_inv, c, C, C', π, π'] at hc ⊢
  simp only [Functor.map_comp, Category.assoc] at hc ⊢
  exact hc

end AlgebraicGeometry.Etale.FiniteRingSectionDeformation
