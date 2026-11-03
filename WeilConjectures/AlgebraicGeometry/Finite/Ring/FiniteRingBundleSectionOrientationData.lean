/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
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
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration

/-! # Canonical maps for finite-ring zero-section orientations

Source: literature/blueprint/latest, sec-smooth-purity/sk-prop-sp-orientation,
orientation-charts proof Step 4, linear normalization and comparison to bundle purity.
(blueprint: def-trf-bundle-section-orientation-data).

The local normalization is an equation on inverse orientations, using the actual
compact-support mate and the actual affine coordinate counit. It simultaneously specifies
all frame restrictions, including restrictions to overlaps, without choosing an orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

/-- Bundle affineness from the recorded geometry, used to synthesize compactifications.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
instance bundleSectionAffine (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    IsAffineHom (VectorBundleZeroSection.π S d M) :=
  (vectorIntegration_geometry S d M).1

/-- The bundle is of finite type locally, as recorded in its integration construction.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
instance bundleSectionFiniteType (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
  (vectorIntegration_geometry S d M).2.1

/-- Every open of the Noetherian base is Noetherian; overlaps need not be affine.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
instance bundleSectionOpenNoetherian (S : Scheme.{u}) [IsNoetherian S] (V : S.Opens) :
    IsNoetherian V.toScheme :=
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  { toIsLocallyNoetherian := inferInstance
    toCompactSpace :=
      { isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ } }

/-- The actual dualizing object for the chosen bundle compact-support adjunction.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionOmega (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    DerivedCategoryModule A (VectorBundleZeroSection.scheme S d M) :=
  (rightDerivedUpperShriek A
    (VectorBundleZeroSection.π S d M)).obj (ordinaryFiniteUnit A S)

/-- The object z^* omega_pi on the ordinary unbounded category of the base.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionObject (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] : DerivedCategoryModule A S :=
  (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
    (bundleSectionOmega A S d M)

/-- Canonical z^* pi^* A_S(d)[2d] = A_S(d)[2d], using pi z = 1.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionCoefficientIso (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    (ordinaryFinitePullback A (VectorBundleZeroSection.zero S d M)).obj
        (vectorIntegrationCoefficient A N hA S d M) ≅
      affineLinearBaseCoefficient A N hA S d :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (VectorBundleZeroSection.zero S d M) (VectorBundleZeroSection.π S d M)
    (VectorBundleZeroSection.zero_spec S d M).1).app _

/-- Inverse images around a commuting square of sections, with their canonical compositors.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionPullbackSquare (A : Type (u + 1)) [CommRing A]
    {X U S T : Scheme.{u}} (z : S ⟶ X) (w : T ⟶ U) (h : U ⟶ X) (v : T ⟶ S)
    (hw : w ≫ h = v ≫ z) (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A v).obj ((ordinaryFinitePullback A z).obj K) ≅
      (ordinaryFinitePullback A w).obj ((ordinaryFinitePullback A h).obj K) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) v z).symm.app K ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w h (v ≫ z) hw.symm).app K

/-- The counit-preserving comparison on section objects: the canonical exceptional mate
of inverse compact-support exchange, followed by the constant-unit pullback comparison.
For the open and isomorphism squares below this is exactly the right-adjoint comparison.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U S T : Scheme.{u}} (p : X ⟶ S) (q : U ⟶ T)
    [HasCompactification p] [HasCompactification q] [QuasiCompact q]
    (h : U ⟶ X) (v : T ⟶ S) (sq : IsPullback h q p v)
    (z : S ⟶ X) (w : T ⟶ U) (hw : w ≫ h = v ≫ z) :
    (ordinaryFinitePullback A v).obj
        ((ordinaryFinitePullback A z).obj
          ((rightDerivedUpperShriek A p).obj
            (ordinaryFiniteUnit A S))) ⟶
      (ordinaryFinitePullback A w).obj
        ((rightDerivedUpperShriek A q).obj
          (ordinaryFiniteUnit A T)) :=
  (bundleSectionPullbackSquare A z w h v hw _).hom ≫
    (ordinaryFinitePullback A w).map
      ((rightDerivedUpperShriekBaseChangeMap A sq).app (ordinaryFiniteUnit A S) ≫
        (rightDerivedUpperShriek A q).map
          (ordinaryFiniteUnitPullback A v).hom)

/-- The zero section expressed in the actual inverse frame, by its Cartesian lifting property.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionChartZero (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d M V) :
    V.toScheme ⟶ affineTraceTower V.toScheme d :=
  (vectorIntegrationChart_isPullback S d M V e).lift
    (V.ι ≫ VectorBundleZeroSection.zero S d M) (𝟙 _)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f ↦ V.ι ≫ f) (VectorBundleZeroSection.zero_spec S d M).1).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- Canonical comparison from a restricted global section object to the frame section object.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionChartComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d M V) :=
  bundleSectionComparison A (VectorBundleZeroSection.π S d M)
    (affineTraceProjection V.toScheme d) (vectorIntegrationChart S d M V e) V.ι
    (vectorIntegrationChart_isPullback S d M V e) (VectorBundleZeroSection.zero S d M)
    (bundleSectionChartZero S d M V e)
    ((vectorIntegrationChart_isPullback S d M V e).lift_fst _ _ _)

/-- The actual affine adjunct alpha_p, not an arbitrary purity isomorphism.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionAffineAdjunct (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) :=
  (rightDerivedUpperShriekAdjunction A
    (affineTraceProjection T d)).homEquiv _ (ordinaryFiniteUnit A T)
      ((affineLinearCompactComparison N hN A hA T hT d).inv ≫
        affineTraceCounit A N hA t D T hT d)

/-- The coefficient identification along the zero section in a frame.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionChartCoefficient (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : VectorBundleZeroSection.Trivialization S d M V) :
    (ordinaryFinitePullback A (bundleSectionChartZero S d M V e)).obj
        ((affineTraceRight A N hA V.toScheme d).obj (ordinaryFiniteUnit A V.toScheme)) ≅
      affineLinearBaseCoefficient A N hA V.toScheme d :=
  (ordinaryFinitePullback A (bundleSectionChartZero S d M V e)).mapIso
      (affineLinearCoefficientDescent A N hA t V.toScheme
        (affineTracePullbackInvertible N V.ι hS) d) ≪≫
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      (bundleSectionChartZero S d M V e) (affineTraceProjection V.toScheme d)
      ((vectorIntegrationChart_isPullback S d M V e).lift_snd _ _ _)).app _

/-- Every affine frame has the specified inverse-affine-adjunct orientation. Using an
inverse equation avoids assuming in advance the invertibility that the theorem asserts.
Since every frame, not a selected cover, occurs, this also states agreement on overlaps
and under every invertible linear change of frames via the same restriction map.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def BundleSectionOrientationNormalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (o : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d) : Prop :=
  ∀ (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (V : S.Opens) (_hV : IsAffine V.toScheme)
    (e : VectorBundleZeroSection.Trivialization S d M V),
    (ordinaryFinitePullback A V.ι).map o.inv ≫
        bundleSectionChartComparison A S d M V e =
      (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS d).hom ≫
        (bundleSectionChartCoefficient N A hA t S hS d M V e).inv ≫
        (ordinaryFinitePullback A (bundleSectionChartZero S d M V e)).map
          (bundleSectionAffineAdjunct N hN A hA t D V.toScheme
            (affineTracePullbackInvertible N V.ι hS) d)

/-- Canonical rank-zero comparison with the identity adjunction, under E = S.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionRankZeroComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [IsNoetherian S]
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank 0]
    (e : VectorBundleZeroSection.scheme S 0 M ≅ S)
    (hz : e.inv = VectorBundleZeroSection.zero S 0 M) :
    bundleSectionObject A S 0 M ⟶ ordinaryFiniteUnit A S :=
  letI : IsIso (VectorBundleZeroSection.zero S 0 M) := hz ▸ inferInstance
  (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app _ ≫
    bundleSectionComparison A (VectorBundleZeroSection.π S 0 M) (𝟙 S)
      (VectorBundleZeroSection.zero S 0 M) (𝟙 S)
      (IsPullback.of_horiz_isIso
        (CommSq.mk ((VectorBundleZeroSection.zero_spec S 0 M).1.trans
          (Category.comp_id _).symm)))
      (VectorBundleZeroSection.zero S 0 M) (𝟙 S) rfl ≫
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app _ ≫
    ((conjugateIsoEquiv
      (rightDerivedUpperShriekAdjunction A (𝟙 S))
      (Adjunction.id)) (unboundedEtaleLowerShriekId A S).symm).hom.app _

/-- The canonical tensor-unit identification pi^* A_S tensor A_E(d)[2d] = A_E(d)[2d].
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionPurityUnitIso (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S) ≅
      vectorIntegrationCoefficient A N hA S d M :=
  ((derivedTensor (ModuleCat.{u + 1} A) (VectorBundleZeroSection.scheme S d M)).mapIso
    (ordinaryFiniteUnitPullback A (VectorBundleZeroSection.π S d M))).app _ ≪≫
      derivedTensorLeftUnitor (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.scheme S d M) _

/-- The actual purity adjunct at the coefficient unit, with the specified projection map.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).
-/
def bundleSectionPurityUnitMap (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (p : (vectorBundlePurityLower A S d M).obj
        (vectorBundlePurityTwistedPullback A N hA S d M (ordinaryFiniteUnit A S)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).obj
        (vectorIntegrationSource A N hA S d M)) :
    vectorIntegrationCoefficient A N hA S d M ⟶ bundleSectionOmega A S d M :=
  (bundleSectionPurityUnitIso N A hA S d M).inv ≫
    (vectorBundlePurityAdjunction A S d M).homEquiv _ (ordinaryFiniteUnit A S)
      (p.hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj (ordinaryFiniteUnit A S)).map
          (vectorBundleIntegration N hN A hA S hS d M) ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) S (ordinaryFiniteUnit A S)).hom)

end AlgebraicGeometry.Etale
