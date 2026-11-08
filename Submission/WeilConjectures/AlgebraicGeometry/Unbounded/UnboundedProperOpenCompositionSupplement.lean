/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Submission.WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
public import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import Submission.WeilConjectures.CategoryTheory.RingedToposRingData
public import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Submission.WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import Submission.WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import Submission.WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import Submission.WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Submission.WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import Submission.WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import Submission.WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Submission.WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import Submission.WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Submission.WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import Submission.WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import Submission.WeilConjectures.SixFunctors.BaseChange.Square
import Submission.WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import Submission.WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import Submission.WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import Submission.WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Submission.WeilConjectures.Compactification.NagataCompactification
import Submission.WeilConjectures.Compactification.Defs
import Submission.WeilConjectures.SixFunctors.OpenClosed.Complex
import Submission.WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import Submission.WeilConjectures.Mathlib.RingTheory.Henselian
import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import Submission.WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import Submission.WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import Submission.WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import Submission.WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import Submission.WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Submission.WeilConjectures.RingTheory.StrictHenselizationTriples
import Submission.WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselization
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import Submission.WeilConjectures.RingTheory.ProEtale.HenselianLocalRing
import Submission.WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import Submission.WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import Submission.WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Submission.WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import Submission.WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Submission.WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Submission.WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import Submission.WeilConjectures.AlgebraicGeometry.DerivedGlobalGerm
import Submission.WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Mathlib.Algebra.Homology.Additive
import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import Submission.WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.SixFunctors.OpenClosed.Exact
import Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import Submission.WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Unbounded proper/open composition

Source: Stacks Project, Tags 0F7C and 0F7D.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency false in
private lemma comp_unit_app
    {C D E : Type v} [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (T : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app T =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app T) := by
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) T
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, hi]
  erw [DerivedCategory.Qh.map_id]
  simp only [Category.id_comp, Category.comp_id]
  erw [Category.id_comp]

-- Comparing iterated sheaf functors requires unfolding the derived-category interfaces.

end AlgebraicGeometry.Etale
