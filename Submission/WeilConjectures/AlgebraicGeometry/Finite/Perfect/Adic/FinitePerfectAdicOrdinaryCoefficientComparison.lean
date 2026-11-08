/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicCoefficientLimit
import Mathlib.Algebra.Category.ModuleCat.Products
public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleStalkData
import Submission.WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import Submission.WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Submission.WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Category.Grp.Abelian
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Submission.WeilConjectures.CategoryTheory.LocalModuleHom
import Submission.WeilConjectures.CategoryTheory.LocalModuleIso
import Submission.WeilConjectures.CategoryTheory.ConstantLocalModuleHom
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleUnit
import Mathlib.Algebra.Module.FinitePresentation
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import Submission.WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.RingTheory.Noetherian.Basic
import Submission.WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import Submission.WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import Submission.WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import Submission.WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.RingTheory.Finiteness.Cardinality
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.LinearAlgebra.StdBasis
import Submission.WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Finiteness.Basic
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Category.ULift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Submission.WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.Topology.Connected.Clopen
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Submission.WeilConjectures.RingTheory.FiniteConeFreeModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.Algebra.Homology.Homotopy
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeEtaleAcyclicHomotopy
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Submission.WeilConjectures.RingTheory.RingPseudoCoherent
import Submission.WeilConjectures.RingTheory.FiniteFreeResolution
import Submission.WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.Single
import Submission.WeilConjectures.RingTheory.PseudoCoherentIffAllM
import Submission.WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import Submission.WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import Submission.WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.LinearAlgebra.Dimension.Free
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Submission.WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicIsomorphismPresentation
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.SequentialLimit
import Mathlib.CategoryTheory.CofilteredSystem
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability
import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Submission.WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Submission.WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Submission.WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import all Submission.WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulFiniteQuotientComparison
import Submission.WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Submission.WeilConjectures.CategoryTheory.ConstantModuleDerivedProjection.ConstantModuleGeometricComparisonData
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import Submission.WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import Submission.WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorMonoidalEquations
import Mathlib.CategoryTheory.Monoidal.Functor
import Submission.WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import Mathlib.LinearAlgebra.TensorProduct.Tower

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Ordinary completed realization and the quotient coefficient tensors

Source: Stacks Project, Tag 09C6; Modules on Sites, Tags 093J--093M.
This comparison takes place entirely in the abelian module categories.
(blueprint: lem-weil-pbc-finite-perfect-adic-ordinary-coefficient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
-- Only the binary tensor comparison and its naturality are needed below.
private structure TensorComparison {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) where
  iso : ∀ M N, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N
  natural : ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
    F.map (f ⊗ₘ g) ≫ (iso M' N').hom =
      (iso M N).hom ≫ (F.map f ⊗ₘ F.map g)

private def TensorComparison.comp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    {F : C ⥤ D} {G : D ⥤ E} (f : TensorComparison F) (g : TensorComparison G) :
    TensorComparison (F ⋙ G) where
  iso M N := G.mapIso (f.iso M N) ≪≫ g.iso (F.obj M) (F.obj N)
  natural a b := by
    simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, ← G.map_comp_assoc]
    rw [f.natural]
    simp only [G.map_comp, Category.assoc]
    rw [g.natural]

namespace AlgebraicGeometry.Scheme

-- Pin the coefficient universe of the site instead of inferring an ambient lift.
private theorem comparisonSiteSmall (X : Scheme.{t}) : EssentiallySmall.{t + 1} X.ProEt :=
  EssentiallySmall.mk' (AsSmall.equiv : X.ProEt ≌ AsSmall.{t + 1} X.ProEt)
attribute [local instance] comparisonSiteSmall

@[instance_reducible] private def constantModulesMonoidal
    (X : Scheme.{t}) (A : Type t) [CommRing A] :
    MonoidalCategory (SheafOfModules.{t + 1} (adicModuleRing X A)) :=
  CategoryTheory.ConstantScalarRestriction.ringMonoidal.{t + 1, t}
    (ProEt.topology X) (ULift.{t + 1} A)
attribute [local instance] constantModulesMonoidal

attribute [local instance] finitePerfectModelsAbLocallyBijective

attribute [local irreducible] completedAdicChangeData completedAdicRing

end AlgebraicGeometry.Scheme
