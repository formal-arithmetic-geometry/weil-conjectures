/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Submission.WeilConjectures.AlgebraicGeometry.Derived.DerivedExtensionZeroBaseChangeSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import all Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all Submission.WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import all Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import all Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import all Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Submission.WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all Submission.WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import all Submission.WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import all Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Sites.Point.Basic
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import all Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import all Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import all Submission.WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import all Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import all Mathlib.CategoryTheory.Sites.Subsheaf
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all Submission.WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import all Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import all Submission.WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Pullbacks
import all Submission.WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import all Submission.WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import all Mathlib.AlgebraicGeometry.Sites.Fpqc
import all Submission.WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import all Submission.WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all Submission.WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import all Submission.WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import all Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import all Submission.WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import all Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import all Submission.WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import all Submission.WeilConjectures.SixFunctors.BaseChange.Square
import all Submission.WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import all Submission.WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import all Submission.WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import all Submission.WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import all Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import all Submission.WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import all Submission.WeilConjectures.Compactification.NagataCompactification
import all Submission.WeilConjectures.Compactification.Defs
import all Submission.WeilConjectures.SixFunctors.OpenClosed.Complex
import all Submission.WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import all Mathlib.FieldTheory.IsAlgClosed.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import all Submission.WeilConjectures.Mathlib.RingTheory.Henselian
import all Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import all Submission.WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import all Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import all Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import all Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import all Mathlib.AlgebraicGeometry.ResidueField
import all Mathlib.FieldTheory.IsSepClosed
import all Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import all Submission.WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import all Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import all Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import all Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import all Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import all Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import all Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import all Submission.WeilConjectures.RingTheory.StrictHenselizationTriples
import all Submission.WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import all Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import all Submission.WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import all Submission.WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import all Submission.WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import all Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all Submission.WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import all Submission.WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import all Submission.WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import all Submission.WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import all Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import all Submission.WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import all Submission.WeilConjectures.Compactification.BaseChange
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Submission.WeilConjectures.SixFunctors.OpenClosed.Exact
import all Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Horizontal pasting for normalized proper/open interchange

Source: Stacks Project, More on Etale Cohomology, Tags 0F7B, 0F7C, 0F7D and 0F7F.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

set_option linter.unusedVariables false in
/-- Horizontal pasting for normalized proper/open interchange.
The ordinary and derived isomorphisms are supplied. The derived map is the
canonical rightDerivedFunctorPlusBaseChange of the ordinary map;
this theorem asserts only the indicated equalities for those fixed isomorphisms.

Source: Stacks Project, More on Etale Cohomology, Tags 0F7B, 0F7C, 0F7D and 0F7F;
the corresponding numbered steps of lem-cbc-proper-open-interchange-coherence.
(blueprint: lem-cbc-normalized-proper-open-pasting)

Proof:
The ordinary normalization determines each delta uniquely: its composite with the support
inclusion into the direct image of the composite map is prescribed, and that inclusion is
monic. For two horizontally adjacent squares, compose the two delta maps and include the
result in the direct image of the outside composite. Naturality of the support inclusions,
the two given normalizations and associativity of direct-image composition give the same
map as the outside delta. Cancel the inclusion. This proves ordinary horizontal pasting,
with the specified extension-zero composition isomorphisms.

Represent K by a bounded-below injective complex J. Choose injective resolutions
t:k!J -> I and v:l!I -> L. The canonical base-change factorization equation, together with
hgamma, says that the first derived comparison is represented by p_*t composed with delta
at J. The second comparison is represented by
q_*v composed with delta at I. Exactness of l! makes w = v composed with l!t a
quasi-isomorphism, so w is also a resolution of l!k!J. Naturality of the second ordinary
delta moves t through it. The ordinary horizontal equation just proved then identifies
the two-square representative with q_*w composed with the outside delta. The derived
comparison for the outside rectangle has exactly this representative, by the same
canonical factorization equation. The specified exact extension-zero compositors descend
from the ordinary ones. Thus these representatives give precisely the displayed equation
in D+, for every K. Their independence of resolutions follows from the canonical
right-derived-unit characterization, already imposed by hgamma.
-/
theorem properOpenInterchangeHorizontalPasting_of_normalization (Λ : Type (u + 1)) [CommRing Λ]
  [Finite Λ]
    (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p))
      (γ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
        ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus) ⋙ (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅ (openImmersionLowerShriek (ModuleCat.{u +
        1} Λ) k).mapDerivedCategoryPlus ⋙ ((lowerStar (ModuleCat.{u + 1} Λ)
          p).rightDerivedFunctorPlus))
    (hδ : (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
      [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F))
    (hγ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
      (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      (γ k i r p h).hom = Functor.rightDerivedFunctorPlusBaseChange (δ k i r p h).hom) :
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (l : B ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j))
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroCompDerivedPlusIso Λ i j).hom.app (((lowerStar (ModuleCat.{u + 1} Λ)
        r).rightDerivedFunctorPlus).obj K) ≫
        (γ (k ≫ l) (i ≫ j) r q h).hom.app K ≫
        ((lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus).map
          ((extensionZeroCompDerivedPlusIso Λ
        k l).inv.app K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map ((γ k i r p
        h₁).hom.app K) ≫
        (γ l j p q h₂).hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
        k).mapDerivedCategoryPlus.obj K)) := by
  intro A B C D E F k l i j r p q _ _ _ _ _ _ _ h₁ h₂ h K
  let e₁ := (δ k i r p h₁).hom
  let e₂ := (δ l j p q h₂).hom
  let e := (δ (k ≫ l) (i ≫ j) r q h).hom
  let ck := openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) k l
  let ci := openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) i j
  have ho := ordinary_horizontal Λ k l r p q i j ⟨h₁⟩ ⟨h₂⟩
    (δ k i r p h₁) (δ l j p q h₂) (δ (k ≫ l) (i ≫ j) r q h)
    (hδ k i r p h₁) (hδ l j p q h₂) (hδ (k ≫ l) (i ≫ j) r q h)
  have hn : Functor.baseChangePaste e₁ e₂ ≫
      Functor.whiskerRight ck.inv (lowerStar (ModuleCat.{u + 1} Λ) q) =
      Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} Λ) r) ci.inv ≫ e := by
    apply NatTrans.ext
    funext M
    apply (cancel_mono ((lowerStar (ModuleCat.{u + 1} Λ) q).map (ck.hom.app M))).1
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.baseChangePaste, Functor.associator_inv_app, Functor.associator_hom_app,
      Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    rw [ho M]
    simp only [ci, e₁, e₂, Iso.inv_hom_id_app_assoc]
    rw [(lowerStar (ModuleCat.{u + 1} Λ) q).map_id]
    erw [Category.comp_id]
  have hnD := Functor.rightDerivedFunctorPlusBaseChange_naturality
    (Functor.baseChangePaste e₁ e₂) e ci.symm ck.symm hn K
  have hpD := Functor.rightDerivedFunctorPlusBaseChange_paste e₁ e₂ K
  rw [hγ, hγ, hγ]
  change (extensionZeroCompDerivedPlusIso Λ i j).hom.app
      ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.obj K) ≫
      (Functor.rightDerivedFunctorPlusBaseChange e).app K ≫
      (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus.map
        ((extensionZeroCompDerivedPlusIso Λ k l).inv.app K) = _
  dsimp only [extensionZeroCompDerivedPlusIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app]
  simp only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hnD]
  dsimp only [ck]
  rw [← (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus.map_comp_assoc,
    Iso.hom_inv_id_app, (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus.map_id,
    Category.id_comp]
  rw [hpD]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

end AlgebraicGeometry.Etale
