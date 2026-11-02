/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
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
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingLocalTraceAffineHelper
public import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingLevelPowerPullback
public import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingLocalTracePrefixPreCompact
public import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingLocalTracePrefixPreCompactTransition
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedCompactificationScalarSquare
public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateCoefficientComposition

/-! # Frame-prefix Kummer transition

Source: general-ring smooth purity, proof (3), exponent independence.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-prefix-helper).

The prefix consists of inverse-frame exchange, chart coefficient transport and the
compact comparison, stopping before the ordered affine counit. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The inverse-frame and coefficient prefix before the affine counit.

Source: the first three factors in the local trace construction.
(blueprint: def-amb-vector-integration-charts).

Proof: this is the composite of the canonical base-change exchange, chart coefficient
comparison, and compact-support comparison, with the local geometric instances
provided by the vector-bundle frame. -/
def finiteGeneralRingLocalTracePrefix
    (N : ℕ) (hNpos : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hN : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hN)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : SheafOfModules.{u} S.ringCatSheaf)
    [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (eV : VectorBundleZeroSection.Trivialization S d F V) :
    (Etale.ordinaryFinitePullback A V.ι).obj
        (Etale.vectorIntegrationSource A N hN S d F) ⟶
      (Etale.affineTraceLeft A V.toScheme d).obj
        ((Etale.affineTraceRight A N hN V.toScheme d).obj
          (Etale.ordinaryFiniteUnit A V.toScheme)) := by
  letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (Etale.vectorIntegration_geometry S d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (Etale.vectorIntegration_geometry S d F).2.1
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  exact
    (Etale.rightDerivedLowerShriekBaseChangeMap A
      (Etale.vectorIntegrationChart_isPullback S d F V eV)).app
        (Etale.vectorIntegrationCoefficient A N hN S d F) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection V.toScheme d)).map
        (Etale.vectorIntegrationChartCoefficient A N hN t S hS d F V eV).hom ≫
      (Etale.affineLinearCompactComparison N hNpos A hN V.toScheme
        (affineTracePullbackInvertible N V.ι hS) d).inv

/-- The Kummer comparison transports the frame prefix to the affine-left transition.

Source: general-ring smooth purity, proof (3), exponent independence.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-prefix-helper).

Proof: take for `qV` and `bV` the restrictions of `q` and `b` along `V.ι`; both clauses of
`FiniteGeneralRingKummerComparison` are equalities of sheaf maps and generators, so they
restrict to `V`. Expand both prefixes into the base-change exchange, the chart coefficient
comparison and the compact comparison. The exchange map is natural in the coefficient, so
the pulled-back level power moves past it; the chart coefficient comparison is built from
inverse-image composition isomorphisms, which are natural, and the coefficient descent, so
the level power becomes the affine transition `finiteGeneralRingAffineTransition` of `bV`
once the pullback of `finiteGeneralRingLevelPower` along `V.ι` is identified with the level
power of `bV`; finally the compact comparison is natural, which moves the transition to the
affine-left functor. -/
theorem finiteGeneralRingLocalTraceExponent_prefix
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N) (hdiv : N ∣ M)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (M : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (q : S.rootsOfUnitySheaf M ⟶ S.rootsOfUnitySheaf N)
    (b : Scheme.finiteEtaleTateLine S M A hM ≅
      Scheme.finiteEtaleTateLine S N A hN)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN S q b)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (DN : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hN tN T hT)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (DM : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (M : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A M hM tM T hT)
    (V : S.Opens) (eV : VectorBundleZeroSection.Trivialization S d F V) :
    ∃ (qV : V.toScheme.rootsOfUnitySheaf M ⟶ V.toScheme.rootsOfUnitySheaf N)
      (bV : Scheme.finiteEtaleTateLine V.toScheme M A hM ≅
        Scheme.finiteEtaleTateLine V.toScheme N A hN),
      FiniteGeneralRingKummerComparison A M N hM hN V.toScheme qV bV ∧
      (Etale.ordinaryFinitePullback A V.ι).map
        ((Etale.vectorBundlePurityLower A S d F).map
          ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map
            (finiteGeneralRingLevelPower A M N hM hN S b d).hom)) ≫
      finiteGeneralRingLocalTracePrefix N hNpos A hN tN S hS' d F V eV =
      finiteGeneralRingLocalTracePrefix M hMpos A hM tM S hS d F V eV ≫
        (Etale.affineTraceLeft A V.toScheme d).map
          (finiteGeneralRingAffineTransition A M N hM hN V.toScheme
            (by simpa using hS.map V.ι.appTop.hom)
            (by simpa using hS'.map V.ι.appTop.hom) bV tM tN d) := by
  have _ := DN
  have _ := DM
  obtain ⟨qV, bV, -, hbline, hbV⟩ :=
    finiteGeneralRingKummerComparison_restrict A M N hMpos hNpos hM hN S hS hS'
      d F q b hb tN tM V
  refine ⟨qV, bV, hbV, ?_⟩
  have hlevel := finiteGeneralRingLevelPower_pullback A M N hM hN V.ι hS hS' b tM tN d
  rw [← hbline] at hlevel
  have hp := finiteGeneralRingLocalTracePrefix_preCompact_transition A M N hMpos hNpos
    hdiv hM hN S hS hS' d F b V bV tN tM eV hlevel hbline
  have hc := finiteGeneralRingLocalTracePrefix_compact_naturality A M N hMpos hNpos
    hM hN V.toScheme
    (by simpa using hS.map V.ι.appTop.hom)
    (by simpa using hS'.map V.ι.appTop.hom) bV tM tN d
  have h := congrArg (fun f ↦ f ≫
      (Etale.affineLinearCompactComparison N hNpos A hN V.toScheme
        (by simpa using hS'.map V.ι.appTop.hom) d).inv) hp
  simp only [Category.assoc] at h
  rw [hc] at h
  simpa only [finiteGeneralRingLocalTracePrefix,
    finiteGeneralRingLocalTracePrefixPreCompact, Category.assoc] using h

end AlgebraicGeometry.ProEtale
