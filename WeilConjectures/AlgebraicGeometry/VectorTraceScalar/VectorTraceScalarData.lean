/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
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
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
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
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
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
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
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
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1ExchangeIso
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteAdjunctScalarFaithfulness
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassScalarFaithfulness
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
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
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineConstantCoefficientGenerator
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteGeometricPointHomology
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFibreHomologyComparison
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1FibreHomologyCard
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceNormalization
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings

/-! # Canonical scalar maps for vector-bundle traces

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, old Steps 9--10
(blueprint: def-pur-vector-trace-scalar-coefficient-data).

The helper maps express the normalized Tate balancing in the existing ordered-tensor
presentation used by vector integration and the affine coordinate tower. All compact
support maps are the published proper/open maps for the chosen compactification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.Etale (purityScalarUnitMap)
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
namespace VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- The unique ordinary balancing family, selected from the existing normalization
 theorem. Its pure-root/scalar generator equations determine every map uniquely.
Source: blueprint paragraph 2, normalized coefficient identifications
(blueprint: def-pur-vector-trace-scalar-coefficient-data). -/
@[irreducible]
def balancing (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ∀ r : ℕ, (purityScalarSheaf φ T).obj (Scheme.finiteEtaleTateTwist T N A hA r) ≅
      Scheme.finiteEtaleTateTwist T N B hB r :=
  Classical.choose ((finite_tate_scalar_source_normalization φ N hN hA hB T
    (fun x ↦ by
      simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ x trivial).hom)).2.exists)

/-- The degree-one balancing from the uniquely generator-normalized Tate theorem,
shifted using its actual scalar/single comparison. This is l_{T,1}.
Source: blueprint paragraph 2, normalized coefficient identifications
(blueprint: def-pur-vector-trace-scalar-coefficient-data). -/
def line (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    (scalarExtension φ T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ⟶
      (ordinaryFiniteLine B N hB T)⟦(2 : ℤ)⟧ :=
  finiteTateScalarLineMap φ N hA hB T 1 (balancing φ N hN hA hB T hT 1)

/-- Multiplication on the constant coefficient complex, with the published single/unit
identifications. Source: blueprint paragraph 2, u_T
(blueprint: def-pur-vector-trace-scalar-coefficient-data). -/
abbrev unit (φ : A →+* B) (T : Scheme.{u}) :
    (scalarExtension φ T).obj (ordinaryFiniteUnit A T) ⟶ ordinaryFiniteUnit B T :=
  purityScalarUnitMap φ T

/-- The tensor powers of shifted balanced lines, starting with multiplication at rank
zero. This is l in the ordered shifted-Tate presentation already used by integration;
no orientation or new Tate object is chosen.
Source: blueprint paragraph 2, l_{T,d}
(blueprint: def-pur-vector-trace-scalar-coefficient-data). -/
def base (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ∀ d : ℕ, (scalarExtension φ T).obj (affineLinearBaseCoefficient A N hA T d) ⟶
      affineLinearBaseCoefficient B N hB T d
  | 0 => unit φ T
  | d + 1 =>
    (ExceptionalCoefficients.tensorIso φ T).hom.app
      (affineLinearBaseCoefficient A N hA T d, (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) ≫
    ((ordinaryFiniteTensor B T).map (base φ N hN hA hB T hT d)).app
      ((scalarExtension φ T).obj ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) ≫
    ((ordinaryFiniteTensor B T).obj (affineLinearBaseCoefficient B N hB T d)).map
      (line φ N hN hA hB T hT)

/-- The normalized scalar map on the pullback of an ordered Tate coefficient. The
inverse scalar/pullback comparison has source Q_X f^* and target f'^* Q_Y.
Source: blueprint paragraph 2, pullback compatibility of l
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def pullBase (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X T : Scheme.{u}} (f : X ⟶ T) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :
    (scalarExtension φ X).obj
        ((ordinaryFinitePullback A f).obj (affineLinearBaseCoefficient A N hA T d)) ⟶
      (ordinaryFinitePullback B f).obj (affineLinearBaseCoefficient B N hB T d) :=
  (scalarPullbackIso φ f).inv.app (affineLinearBaseCoefficient A N hA T d) ≫
    (ordinaryFinitePullback B f).map (base φ N hN hA hB T hT d)

/-- The actual proper scalar mate followed by the degree-one normalized balancing.
Source: blueprint paragraph 2, tilde q_p
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def projective (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (scalarExtension φ S).obj
        ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) ⟶
      (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine B N hB (ProjectiveLine S))⟦(2 : ℤ)⟧) :=
  (scalarMate φ (ProjectiveLine S ↘ S)).app
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
    (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
      (line φ N hN hA hB (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS))

/-- The comparison d_S is assembled from its two projections l_{S,1} and u_S.
Source: blueprint paragraph 2, projective-line decomposition
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def sum (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (scalarExtension φ S).obj
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ⟶
      ((ordinaryFiniteLine B N hB S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit B S) :=
  biprod.lift ((scalarExtension φ S).map biprod.fst ≫ line φ N hN hA hB S hS)
    ((scalarExtension φ S).map biprod.snd ≫ unit φ S)

/-- Normalized balancing on the coordinate tower's actual right-adjoint input,
transported by the existing coefficient-descent isomorphisms.
Source: blueprint paragraph 2, affine-space composition
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def affineCoefficient (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (scalarExtension φ (affineTraceTower S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶
      (affineTraceRight B N hB S d).obj (ordinaryFiniteUnit B S) :=
  (scalarExtension φ (affineTraceTower S d)).map
      (affineLinearCoefficientDescent A N hA (projectiveLineTraceTransport N hN A hA)
        S hS d).hom ≫
    pullBase φ N hN hA hB (affineTraceProjection S d) hS d ≫
    (affineLinearCoefficientDescent B N hB (projectiveLineTraceTransport N hN B hB)
      S hS d).inv

/-- The actual coordinate-tower counit, on the specified compact-support source.
Source: blueprint paragraph 2, t_{p_d}
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def affineTrace (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
        ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ⟶
      ordinaryFiniteUnit A S :=
  (affineLinearCompactComparison N hN A hA S hS d).inv ≫
    affineTraceCounit A N hA (projectiveLineTraceTransport N hN A hA)
      (projectiveLineTraceDatum N hN A hA) S hS d

/-- The specified compactification scalar map followed by the tower's Tate balancing.
Source: blueprint paragraph 2, affine tilde q
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def affine (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (scalarExtension φ S).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection S d)).obj
          ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S))) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (affineTraceProjection S d)).obj
        ((affineTraceRight B N hB S d).obj (ordinaryFiniteUnit B S)) :=
  (compactScalarChosenMap φ (affineTraceProjection S d)).app
      ((affineTraceRight A N hA S d).obj (ordinaryFiniteUnit A S)) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (affineTraceProjection S d)).map
      (affineCoefficient φ N hN hA hB S hS d)

/-- The specified compact-support comparison for the bundle followed by its actual
pullback/Tate balancing. Geometry instances are furnished by the recorded construction.
Source: blueprint paragraph 2, tilde q_pi
(blueprint: def-pur-vector-trace-scalar-map-data). -/
def vector (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (scalarExtension φ S).obj (vectorIntegrationSource A N hA S d F) ⟶
      vectorIntegrationSource B N hB S d F :=
  letI := (vectorIntegration_geometry S d F).1
  letI := (vectorIntegration_geometry S d F).2.1
  (compactScalarChosenMap φ (VectorBundleZeroSection.π S d F)).app
      (vectorIntegrationCoefficient A N hA S d F) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (VectorBundleZeroSection.π S d F)).map
      (pullBase φ N hN hA hB (VectorBundleZeroSection.π S d F) hS d)

end VectorTraceScalar
end AlgebraicGeometry.Etale
