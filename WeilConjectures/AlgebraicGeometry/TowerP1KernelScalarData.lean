/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TowerP1ProjectiveCoordinates
public import WeilConjectures.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals
public import WeilConjectures.AlgebraicGeometry.FiniteP1KummerNaturality
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
public import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctMate
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
public import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.AlgebraicGeometry.FiniteP1UnitOnPullback
public import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula
public import WeilConjectures.AlgebraicGeometry.FiniteP1KummerSplitting
public import WeilConjectures.AlgebraicGeometry.FiniteP1NoetherianBase
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN
public import WeilConjectures.AlgebraicGeometry.TorsionAssembly
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
public import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
public import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RestrictionRingedToposModuleDirectImageSupplement
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalChernComponents
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalAlpha
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerClasses
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections

/-! # Data for tower trace and diagonal scalar normalization

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md,
Reduction of the triangle identities and Levelwise check
(blueprint: def-sp-tower-p1-kernel-scalar-data).

The helpers specify the unit/Chern splittings, their inverse-projection traces,
and the actual finite etale composites. Positive level n+1 is indexed by n : Nat.
All equalities before evaluation are in the ordinary derived category of towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}

/-- Shift the specified roots-and-coefficients pullback isomorphism.
Source: base change of trace, twist identification
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def kernelShiftedLine {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    {f : X ⟶ Y} {g : SpTowerShriek.Geometry l E b f}
    {cY : Chern l E Y} {cX : Chern l E X} (t : LinePullback l E f g cY cX) :
    (SpTowerShriek.pull l E b g).obj ((line l E cY)⟦(2 : ℤ)⟧) ≅
      (line l E cX)⟦(2 : ℤ)⟧ :=
  ((SpTowerShriek.pull l E b g).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso (t.derivedIso l E)

/-- Unit/Chern splitting at q and at each product projection. Every comparison is
normalized on ordinary sections by CoefficientPullback or LinePullback. The maps
of the splittings are fixed by their two components; they are not arbitrary isomorphisms.
The relative hyperplane for projection a is the pullback along the other projection.
Source: base change of trace, unit and hyperplane components
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
structure KernelSplittingData (p : Presentation l E S hS) where
  coefficientQ : CoefficientPullback l E p.classes.base (ProjectiveLine S ↘ S)
    (p.operations.geometry (ProjectiveLine S ↘ S))
  lineQ : LinePullback l E (ProjectiveLine S ↘ S)
    (p.operations.geometry (ProjectiveLine S ↘ S)) p.classes.chernS p.classes.chernP
  coefficientProjection : ∀ a : Bool,
    CoefficientPullback l E p.classes.base (Etale.projectiveLineDiagonalProjection S a)
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))
  lineProjection : ∀ a : Bool,
    LinePullback l E (Etale.projectiveLineDiagonalProjection S a)
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))
      p.classes.chernP p.classes.chernW
  splittingQ : (line l E p.classes.chernS)⟦(2 : ℤ)⟧ ⊞ unit S (Arings l E S) ≅
    (p.F l E).obj ((line l E p.classes.chernP)⟦(2 : ℤ)⟧)
  splittingQ_hom : splittingQ.hom = biprod.desc
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).homEquiv _ _
        (kernelShiftedLine l E lineQ).hom)
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).homEquiv _ _
        ((coefficientQ.derivedIso l E).hom ≫
          firstChern l E p.classes.chernP (hyperplanePic S)))
  traceQ : splittingQ.inv ≫ biprod.snd = p.trace l E
  splittingProjection : ∀ a : Bool,
    (line l E p.classes.chernP)⟦(2 : ℤ)⟧ ⊞
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ≅
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
      ((line l E p.classes.chernW)⟦(2 : ℤ)⟧)
  splittingProjection_hom : ∀ a : Bool, (splittingProjection a).hom = biprod.desc
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).homEquiv _ _
        (kernelShiftedLine l E (lineProjection a)).hom)
    ((SpTowerShriek.adjunction l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).homEquiv _ _
        (((coefficientProjection a).derivedIso l E).hom ≫
          firstChern l E p.classes.chernW
            (Scheme.Pic.map (Etale.projectiveLineDiagonalProjection S (!a))
              (hyperplanePic S))))

variable {p : Presentation l E S hS}

/-- The trace for either projection is its splitting inverse followed by pr2.
Source: base change of trace (blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def KernelSplittingData.trace (k : KernelSplittingData l E p) (a : Bool) :
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
      ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) ⟶
    unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  (k.splittingProjection a).inv ≫ biprod.snd

/-- The proper exchange mate followed by the canonical shifted Tate-line comparison.
The argument !a chooses the horizontal projection, leaving a as the direct-image edge.
Source: base change of trace (blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def KernelSplittingData.exchange (k : KernelSplittingData l E p) (a : Bool) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj
      ((p.F l E).obj ((line l E p.classes.chernP)⟦(2 : ℤ)⟧)) ⟶
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).obj
      ((line l E p.classes.chernW)⟦(2 : ℤ)⟧) :=
  match a with
  | false => p.exchangeSwap l E ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≫
      (SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (Etale.projectiveLineDiagonalProjection S false))).map
        (kernelShiftedLine l E (k.lineProjection true)).hom
  | true => p.exchange l E ((line l E p.classes.chernP)⟦(2 : ℤ)⟧) ≫
      (SpTowerShriek.push l E p.classes.base
        (p.operations.geometry (Etale.projectiveLineDiagonalProjection S true))).map
        (kernelShiftedLine l E (k.lineProjection false)).hom

/-- Canonical comparison of the two splitting sources, component by component.
Source: base change of trace, d_i
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def KernelSplittingData.sumComparison (k : KernelSplittingData l E p) :
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).obj
      ((line l E p.classes.chernS)⟦(2 : ℤ)⟧ ⊞ unit S (Arings l E S)) ⟶
    (line l E p.classes.chernP)⟦(2 : ℤ)⟧ ⊞
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  biprod.lift
    ((SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map
        (biprod.fst (X := (line l E p.classes.chernS)⟦(2 : ℤ)⟧)
          (Y := unit S (Arings l E S))) ≫ (kernelShiftedLine l E k.lineQ).hom)
    ((SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map
        (biprod.snd (X := (line l E p.classes.chernS)⟦(2 : ℤ)⟧)
          (Y := unit S (Arings l E S))) ≫ (k.coefficientQ.derivedIso l E).hom)

/-- Exactly alpha_i, Rp_i(delta), and the splitting trace, in composition order.
Source: Levelwise check, displayed c_i
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def KernelSplittingData.scalar (k : KernelSplittingData l E p) (a : Bool) :
    unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)) :=
  p.sourceUnitAt l E a (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))) ≫
    (SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map
      (p.delta l E) ≫ k.trace l E a

/-- The ordinary etale trace for p_a, transported from the standard P1 over P.
Source: finite diagonal integrals, comparison of the product projections
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def kernelFiniteTrace (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS))
    (a : Bool) :
    (EtaleWords.push (levelRing l E n) (Etale.projectiveLineDiagonalProjection S a)).obj
      (EtaleWords.line (levelRing l E n) (l ^ (n + 1)) (levelAnnihilates l E n)
        (diagonalSurface S)) ⟶
      Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S) :=
  Etale.ordinaryFiniteP1DiagonalChartMap (levelRing l E n) (l ^ (n + 1))
    (levelAnnihilates l E n) c.transport S (baseExponentUnit l n hS) a ≫ bP.trace

/-- The specified finite composite, including the canonical composition source alpha.
The supported boundary in EtaleWords.delta has the positive divisor-Chern sign.
Source: finite diagonal integrals, c_i at level n+1
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def kernelFiniteScalar (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS))
    (hD : (diagonalImmersion S).ker.IsInvertible) (a : Bool) :
    Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S) ⟶
      Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S) :=
  Etale.projectiveLineDiagonalAlpha (levelRing l E n) S a ≫
    (EtaleWords.push (levelRing l E n) (Etale.projectiveLineDiagonalProjection S a)).map
      (EtaleWords.delta (levelRing l E n) (l ^ (n + 1))
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _) (levelAnnihilates l E n)
        S hD (surfaceExponentUnit l n hS)) ≫ kernelFiniteTrace l E n c bP a

/-- Every part of the finite scalar comparison is an equation of the specified maps.
In particular alpha is the canonical composition source, not a free source isomorphism.
Source: Levelwise check, finite composite and sign
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
structure KernelFiniteNormalization (k : KernelSplittingData l E p)
    (n : ℕ) [Finite (SpTowerShriek.R l E n)] (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS))
    (hD : (diagonalImmersion S).ker.IsInvertible) : Prop where
  alpha : ∀ a : Bool, WordComparison l E n (c.unitP l E n)
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a)
      (c.push l E n (diagonalImmersion S) (c.unitP l E n)))
    (p.sourceUnitAt l E a (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))
    (Etale.projectiveLineDiagonalAlpha (levelRing l E n) S a)
  pushed_delta : ∀ a : Bool, WordComparison l E n
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a)
      (c.push l E n (diagonalImmersion S) (c.unitP l E n)))
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a) (c.lineW l E n))
    ((SpTowerShriek.push l E p.classes.base
      (p.operations.geometry (Etale.projectiveLineDiagonalProjection S a))).map (p.delta l E))
    ((EtaleWords.push (levelRing l E n) (Etale.projectiveLineDiagonalProjection S a)).map
      (EtaleWords.delta (levelRing l E n) (l ^ (n + 1))
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _) (levelAnnihilates l E n)
        S hD (surfaceExponentUnit l n hS)))
  trace : ∀ a : Bool, WordComparison l E n
    (c.push l E n (Etale.projectiveLineDiagonalProjection S a) (c.lineW l E n))
    (c.unitP l E n) (k.trace l E a) (kernelFiniteTrace l E n c bP a)
  composite : ∀ a : Bool, WordComparison l E n (c.unitP l E n) (c.unitP l E n)
    (k.scalar l E a) (kernelFiniteScalar l E n c bP hD a)
  finite_identity : ∀ a : Bool, kernelFiniteScalar l E n c bP hD a =
    𝟙 (Etale.ordinaryFiniteUnit (levelRing l E n) (ProjectiveLine S))

/-- Evaluation at every positive level uses normalized constant, root and site-mate
coordinates, and the ordinary finite unit/Chern splitting over P.
Source: Levelwise check (blueprint: def-sp-tower-p1-kernel-scalar-data). -/
def KernelSplittingData.finiteNormalization (k : KernelSplittingData l E p)
    (hD : (diagonalImmersion S).ker.IsInvertible) (n : ℕ) : Prop :=
  letI : Finite (SpTowerShriek.R l E n) := p.classes.base.finite n
  ∃ (c : ProjectiveCoordinates l E n p)
    (bP : Etale.ArbitraryBaseFiniteP1Splitting (levelRing l E n) (l ^ (n + 1))
      (levelAnnihilates l E n) c.transport (ProjectiveLine S) (lineExponentUnit l n hS)),
    KernelFiniteNormalization l E k n c bP hD

/-- All the asserted equalities in the actual tower derived category, and their
finite etale descriptions. Degree-zero full faithfulness is used only on A_P[0].
Source: base change of trace and Levelwise check
(blueprint: def-sp-tower-p1-kernel-scalar-data). -/
structure KernelScalarNormalization (p : Presentation l E S hS)
    (k : KernelSplittingData l E p) : Prop where
  exchange_iso : ∀ a : Bool, IsIso (k.exchange l E a)
  source_comparison_iso : IsIso (k.sumComparison l E)
  splitting_base_change : ∀ a : Bool,
    (SpTowerShriek.pull l E p.classes.base
      (p.operations.geometry (ProjectiveLine S ↘ S))).map k.splittingQ.hom ≫
        k.exchange l E a = k.sumComparison l E ≫ (k.splittingProjection a).hom
  inverse_base_change : ∀ a : Bool,
    k.exchange l E a ≫ (k.splittingProjection a).inv =
      (SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (ProjectiveLine S ↘ S))).map k.splittingQ.inv ≫
          k.sumComparison l E
  trace_base_change : ∀ a : Bool,
    k.exchange l E a ≫ k.trace l E a =
      (SpTowerShriek.pull l E p.classes.base
        (p.operations.geometry (ProjectiveLine S ↘ S))).map (p.trace l E) ≫
          (k.coefficientQ.derivedIso l E).hom
  alpha_iso : ∀ a : Bool, IsIso (p.sourceUnitAt l E a
    (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S))))
  scalar_identity : ∀ a : Bool, k.scalar l E a =
    𝟙 (unit (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
  cartier : (diagonalImmersion S).ker.IsInvertible
  levels : ∀ n : ℕ, k.finiteNormalization l E cartier n
  degree_zero_lift : ∀ a : Bool,
    ∃! f : coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)),
      (DerivedCategory.singleFunctor
        (Systems (ProjectiveLine S) (Arings l E (ProjectiveLine S))) 0).map f = k.scalar l E a
  degree_zero_detection : ∀ (f g :
    coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)) ⟶
      coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))),
    (∀ n : ℕ, (SpTowerShriek.ev l E (ProjectiveLine S) n).map f =
      (SpTowerShriek.ev l E (ProjectiveLine S) n).map g) → f = g

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
