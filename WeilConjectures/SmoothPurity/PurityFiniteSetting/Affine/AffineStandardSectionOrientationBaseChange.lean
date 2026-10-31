/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationRefinement.VectorZeroSectionIntegrationBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorBundleIntegrationOrientation
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.SmoothSectionExchangeComposition
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
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
import WeilConjectures.SmoothPurity.Ringed.RingedTopoiDerivedTensorPullback
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
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
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Base change of the ordinary affine zero-section orientation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The ordinary affine zero-section orientation commutes with its specified exchange.
Source: latest blueprint, vector-bundle purity base-change paragraph and composition
proof Step 1, restriction to the affine zero section.
(blueprint: lem-pur-affine-standard-section-orientation-base-change).

Proof: present each finite-coordinate affine space as the total space of its standard
free rank-r module, carrying the augmentation to the zero section. The ordinary orientation
normalization and the integration-adjunction equation identify the inverse section
orientation with vectorBetaInverse in these presentations. Apply the zero-section
integration base-change theorem to the Cartesian map induced by f. Paste the two
presentation squares using section-exchange composition and cancel the presentation
isomorphisms. The roots-inclusion and pure-tensor normalizations identify the supplied Tate
transport with the canonical one. Invert the resulting equation, leaving the ordered
coefficient pullback on the left. This is exactly the displayed forward equation with
compatibleStandardBaseChange. For rank zero the comparisons are the identity-pullback
and constant-unit constraints; for the empty base the same construction applies. -/
theorem affine_standard_section_orientation_baseChange (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (r : ℕ) (f : U ⟶ V)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := DiagonalPasting.affineDimension r V
    letI := DiagonalPasting.affineDimension r U
    (Etale.ordinaryFinitePullback P.Coefficient f).mapIso
        (P.chartSectionOrientation r (DiagonalPasting.pr r V) aV
          (DiagonalPasting.zero r V) t) ≪≫
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t f (P.diagonalExponent_isUnit aV) r =
      P.compatibleStandardBaseChange r f aV ≪≫
        P.chartSectionOrientation r (DiagonalPasting.pr r U) (f ≫ aV)
          (DiagonalPasting.zero r U) t := by sorry

end WeilConjectures.PurityFiniteSetting
