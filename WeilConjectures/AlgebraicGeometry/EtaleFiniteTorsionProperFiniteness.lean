/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Constructible
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.GroupTheory.Torsion
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN
import WeilConjectures.AlgebraicGeometry.TorsionAssembly
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.KInjectiveResolutions
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.RestrictionRingedToposModuleDirectImageSupplement
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.NoetherianComplementaryStratifications
import WeilConjectures.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-! # Proper finiteness for ordinary finite-field etale module sheaves

Source: Bhatt--Scholze, The pro-etale topology for schemes, Theorem 6.7.1,
proper alternative, with R = A and maximal ideal zero; Stacks Project, Tags 0A3V,
095U and 0GL0 (blueprint: lem-fd-etale-finite-torsion-proper-finiteness).

The higher direct images use the ordinary small etale sites and the bounded below
right derived direct image of a module sheaf placed in degree zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Proper higher direct images of constructible finite-field etale module sheaves are
constructible and vanish outside one interval [0, d], chosen independently of the sheaf.

Source: Bhatt--Scholze, Theorem 6.7.1, proper alternative, specialized to R = A;
Stacks Project, Tags 0A3V, 095U, 03RW and 0GL0
(blueprint: lem-fd-etale-finite-torsion-proper-finiteness).

Proof plan following the six DAG steps:
1. Properness gives finite type and the Noetherian target is quasi-compact.
   The uniform fibre-dimension lemma lem-fin-finite-type-fibre-dimension-bound
   supplies e with every fibre of h of dimension at most e. Choose d = 2e before F.
2. The underlying abelian sheaf of an A-module sheaf is killed by ell.
   Apply lem-kun-proper-torsion-cd-bound and transfer its vanishing to modules by
   lem-sbc-higher-direct-image-forget-comparison. The forgetful functor reflects zero.
   For q < 0, a nonnegative injective resolution gives zero cohomology, using
   lem-weil-pbc-module-sheaves-enough-injectives and def-weil-pbc-direct-image.
3. Fix F and q in [0, d]. For any nonempty closed T in Y, give T its reduced induced
   structure by lem-weil-pbc-reduced-induced-closed-subscheme. It is Noetherian by
   lem-sfb-noetherian-complementary-stratifications. Choose an irreducible component
   using lem-sc-noetherian-closed-subset-finite-components, and a nonempty open in it
   using lem-sfb-noetherian-component-open. A nonempty affine open S therein is integral
   by def-pc-integral-scheme and Noetherian by
   lem-weil-pbc-noetherian-open-subscheme-noetherian.
4. Base change h to S. Properness persists by lem-pc-proper-base-change, and the
   pullback of F is constructible by prop-constructible-pullback. Proper base change
   lem-kun-proper-base-change-torsion-ring identifies the restriction of Rh_*F with
   this direct image. Exact inverse image, prop-weil-pbc-inverse-image-modules-exact,
   identifies their cohomology. Apply lem-fd-proper-cohomology-generic-local-constancy
   to obtain a nonempty open V of S where the degree-q image is finite locally constant.
5. If a closed subset admits no required finite stratification, choose a minimal one
   using lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. It is nonempty. Steps
   3 and 4 supply V; its proper closed complement has a finite stratification by
   minimality. Adjoin V using lem-sfb-noetherian-complementary-stratifications. The
   strata are constructible by def-weil-constructible-subset, contradicting minimality.
   Taking T = Y proves constructibility by def-weil-pbc-etale-constructible-sheaf.
6. The zero sheaf is finite locally constant with value the zero A-module, hence
   constructible. This covers all remaining degrees from step 2. No ground field,
   absolute dimension bound, or invertibility of ell was used. -/
theorem exists_uniform_bound_constructible_higherDirectImage_of_isProper_finite_field
    (ℓ : ℕ) [Fact ℓ.Prime] (A : Type (u + 1)) [Field A] [Finite A] [CharP A ℓ]
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (h : Z ⟶ Y) [IsProper h] :
    ∃ d : ℕ, ∀ (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
      Scheme.IsConstructibleEtaleModuleSheaf F → ∀ q : ℤ,
        Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage A h q F) ∧
          (q < 0 ∨ (d : ℤ) < q → IsZero (higherDirectImage A h q F)) := by
  sorry

end AlgebraicGeometry.Etale
