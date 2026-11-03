/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothDualityBaseChangeCompat
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
public import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportMapCompatibility
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.Finite.Smooth.FiniteSmoothGammaConstructions
import WeilConjectures.AlgebraicGeometry.SfEtaleUnitTensorArbitraryBase
import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability
import Mathlib.CategoryTheory.Triangulated.Yoneda
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetract
import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetractData
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GrothendieckDerivedCompactLocalizationModel
import WeilConjectures.CategoryTheory.CompactlyGenerated
import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Equivalence
import WeilConjectures.CategoryTheory.GabrielPopescuAbelianCore
import WeilConjectures.CategoryTheory.GabrielPopescuLargeHomRightAdjoint
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import WeilConjectures.CategoryTheory.DerivedLargeCoproductsTransfer
import WeilConjectures.CategoryTheory.DerivedHomologyInjective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveSurjective
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveInjective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.LargeHomSolutionSet
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.CategoryTheory.CompactDerivedSourceCore
import WeilConjectures.CategoryTheory.DerivedModuleCompactGeneration
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedModuleRankOneProperties
import Mathlib.Algebra.Module.ULift
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.CategoryTheory.DerivedModuleRankOneGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneNonzeroMap
import WeilConjectures.CategoryTheory.DerivedModuleNonzeroClassMap
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GrothendieckDerivedExactLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.ProjectionFormulaCoproducts
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import WeilConjectures.CategoryTheory.CoproductsOfCopowers
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointCoherenceSupplement
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase
import WeilConjectures.AlgebraicGeometry.ExactPullbackTensorComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphUnitTensor
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphExchangeTensor
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphTransferTensor
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphTensorCore
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
import all WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
import all WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality

/-! # The tensor mate in etale unit coordinates

Source: blueprint sec-smooth-purity/sk-thm-smooth-purity, tensor mate formula
(blueprint: lem-pur-finite-smooth-omega-tensor-coordinates).
-/

@[expose] public noncomputable section
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory

private theorem normalizedComparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (C : FiniteSmoothCompactSupportComparisons A)
    (hC : FiniteSmoothComparisonNormalized A C)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f]
    (c : Compactification f) :
    (C f c).inv = compactificationEtaleComparison A f c := by
  obtain ⟨a, ha⟩ := hC
  let N := canonicalEtaleCompactSupportNormalization A
  have he : a f c = N.sheafComparison f c := by
    apply NatTrans.ext
    funext M
    have : Mono ((openImmersionLowerShriekToLowerStar
        (ModuleCat.{u + 1} A) c.i).app M) := open_compare_mono A c.i M
    have : Mono ((compactificationSheafToDirectImage A c).app M) := by
      dsimp only [compactificationSheafToDirectImage, NatTrans.comp_app,
        Functor.whiskerRight_app]
      have : Mono ((lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M)) :=
          Functor.map_mono _ _
      exact mono_comp
        ((lowerStar (ModuleCat.{u + 1} A) c.g).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M))
        ((lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) c.i c.g f c.comm).app M).hom
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app M)).1
    exact ((ha f c).1 M).trans (N.sheaf_normalization f c M).symm
  have hd : (C f c).inv = (N.comparison f c).inv := by
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (.up ℤ))
    intro P
    rw [(ha f c).2 P, N.derived_normalization f c P, he]
  exact hd.trans (normalizedComparison_eq_source A N f c)

private theorem rightAdjointUniq_ofNatIsoLeft
    {C D : Type*} [Category C] [Category D]
    {F S : C ⥤ D} {G E : D ⥤ C} (adj : F ⊣ G) (sa : S ⊣ E) (s : F ≅ S) :
    (adj.rightAdjointUniq (sa.ofNatIsoLeft s.symm)).hom =
      conjugateEquiv adj sa s.inv := by
  ext K
  simp only [Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.refl_hom, NatTrans.id_app, Iso.symm_hom, Category.assoc]
  simp

end AlgebraicGeometry.Etale.FiniteSmoothPurity
