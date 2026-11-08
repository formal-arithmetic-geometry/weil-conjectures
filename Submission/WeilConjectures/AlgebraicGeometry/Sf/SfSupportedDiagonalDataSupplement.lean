/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceContractions
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Submission.WeilConjectures.ConstructibleSheaf.LisseRankOne
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Submission.WeilConjectures.SixFunctors.BaseChange.Square
public import Submission.WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.GroupTheory.Torsion
public import Submission.WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN
public import Submission.WeilConjectures.AlgebraicGeometry.TorsionAssembly
public import Submission.WeilConjectures.SixFunctors.BaseChange.Derived
public import Submission.WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
public import Submission.WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
public import Submission.WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
public import Submission.WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
public import Submission.WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
public import Mathlib.Data.ZMod.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Submission.WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Submission.WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import Submission.WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import Mathlib.Algebra.Category.Ring.Limits
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.CategoryTheory.RingedToposRingData
public import Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Submission.WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Submission.WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
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
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
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
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import Submission.WeilConjectures.AlgebraicGeometry.ProperTorsionProjectionFormula
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorization
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethFactorizationTranspose
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethRouteEquality
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoute
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoutePrecomp
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleKunnethSymmetricFactorization
public import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
public import Submission.WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleKunnethTensorSymmetry
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethRightRoute
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceNormalization
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionUnit
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleEvenLineSelfSymmetry
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleEvenShiftCanonicalSelfSymmetry
public import Mathlib.Tactic.SuppressCompilation
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleLineFlatBraiding
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import Submission.WeilConjectures.ConstructibleSheaf.InternalHom
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSecondCoordinateContraction
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleTraceBaseChangeEvaluation
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleOrderedProjectionComparison
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import Submission.WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Submission.WeilConjectures.CategoryTheory.Monoidal.UnitComparison
public import Submission.WeilConjectures.CategoryTheory.SectionProjectionUnit
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleProjectionTraceTensorInterchange
public import Submission.WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalData

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Canonical maps for compact-support diagonal integration

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the exchange and projection computations in both triangles.
(blueprint: def-sf-supported-diagonal-calculus).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfDiagonalKernel

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

variable {f} {B : DerivedCategoryModule A X} (d : TraceDiagonalDatum A f B)

end AlgebraicGeometry.Etale.SfDiagonalKernel

namespace AlgebraicGeometry.Etale.SupportedTrace

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The inverse projection formula followed by trace and the left unitor.
Source: thm-amb-p1-adjunction.proof.md (blueprint: def-sf-supported-diagonal-calculus). -/
def evaluation {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {B : DerivedCategoryModule A X}
    (t : (push A f).obj B ⟶ derivedTensorUnit (ModuleCat.{u + 1} A) Y)
    (K : DerivedCategoryModule A Y) : (push A f).obj ((CoordinateTrace.pull A f ⋙ (derivedTensor
      (ModuleCat.{u + 1} A) X).obj B).obj K) ⟶ K :=
  (projectionIso A f B).inv.app K ≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map t).app K ≫
      (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) Y).hom.app K

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

section TensorUnit

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

end TensorUnit

end AlgebraicGeometry.Etale.SupportedTrace

namespace AlgebraicGeometry.Etale.SfDiagonalKernel

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
variable {B : DerivedCategoryModule A X} (d : TraceDiagonalDatum A f B)

section Components

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor derivedTensorSymmetry

attribute [local implicit_reducible] rightDerivedLowerShriek derivedTensorRight

end Components

end AlgebraicGeometry.Etale.SfDiagonalKernel
