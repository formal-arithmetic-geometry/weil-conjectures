/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.GeometricFiberFinite
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover
import WeilConjectures.AlgebraicGeometry.FrobeniusFixedSections
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
import WeilConjectures.AlgebraicGeometry.ModuleLocalConstancyOfFiniteUnderlying
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.RingedSitePerfectProjectionFormula
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierDimension
import WeilConjectures.AlgebraicGeometry.ConnectedFibresConstantDegreeZero
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CoefficientDevissage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension
import WeilConjectures.RingTheory.SimpleFiltration
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.AlgebraicGeometry.PrimeCurveGeometricStalkFinite
import WeilConjectures.AlgebraicGeometry.ProperSmoothConnectedFibreDimensionLoci
import WeilConjectures.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Finite constant coefficients in proper smooth curve families in every characteristic

Source: Stacks Project, more-etale.tex, Tag 0GKW,
lemma-proper-smooth-family-curves-modules; Tag 0GKV for prime coefficients and
morphisms.tex, Tag 02G1 for the open-and-closed fibre-dimension decomposition.
(blueprint: lem-fd-proper-smooth-curves-finite-module-all-char)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- For a proper smooth morphism over a Noetherian base, with nonempty geometrically
connected fibres of dimension at most one, every integer-degree higher direct image of a
finite constant module over a finite commutative ring is constructible, in every
characteristic. `GeometricallyConnected f` is equivalent to geometric connectedness of
each residue-field fibre and includes nonemptiness of those fibres.

Source: Stacks Project, more-etale.tex, Tag 0GKW,
lemma-proper-smooth-family-curves-modules; Tag 0GKV for the prime-field case and
morphisms.tex, Tag 02G1 for the dimension-zero/one decomposition.
(blueprint: lem-fd-proper-smooth-curves-finite-module-all-char)

Proof:
1. Filter the finite module by simple quotients. Constant sheafification is exact, and
   finite-module direct-image devissage reduces constructibility to those quotients.
   The zero module has the empty filtration; negative cohomology vanishes because the
   injective resolution starts in degree zero.
2. Field extension preserves the dimension of the finite-type fibres. Smoothness and
   geometric connectedness therefore give open-and-closed dimension-zero and dimension-one
   loci. On the zero-dimensional locus, proper quasi-finite is finite. Finite direct image
   is exact, so positive degrees vanish; degree zero is constructible by the connected-fibre
   theorem. The module/abelian comparison gives the module-valued assertion.
3. On the one-dimensional locus, first take prime-field coefficients. Split the base into
   the open where the prime is invertible and its closed zero locus. Proper base change,
   exact inverse image, and pullback of constants identify the restrictions and geometric
   stalks with the corresponding fibre calculations. The prime-coefficient curve theorem
   gives constructibility on the open, and the geometric-stalk theorem gives finite stalks.
4. On the closed characteristic-p locus, degree zero is constructible. Proper base change
   identifies geometric stalks in degrees at least two with fibre cohomology, which vanishes
   by Artin--Schreier dimension. Geometric-stalk conservativity gives vanishing sheaves.
5. Frobenius-fixed sections and the finite etale Artin--Schreier covering give the exact
   sequence from the constant prime field to the additive etale structure sheaf, followed
   by Frobenius minus identity on that structure sheaf.
6. Proper smooth structure cohomology identifies degree zero with the base structure sheaf
   and degree one with a finite locally free module. The relative etale/Zariski comparison
   identifies these as etale abelian sheaves and intertwines the semilinear Frobenius maps.
7. The long exact direct-image sequence expresses degree one of the constant prime field
   as an extension of the cokernel of Frobenius minus identity on the structure sheaf by
   its kernel on the degree-one vector bundle. The Frobenius-linear vector-bundle theorem
   makes the cokernel zero and the kernel constructible, allowing rank jumps.
8. On each constructible stratum, local constancy of the finite underlying sheaf implies
   module local constancy. Finite stalks give finite constant module models, and the
   constructibility comparison gives module constructibility on the closed locus.
9. Combine the finite stratifications of the open and closed loci, using proper base
   change to identify the restrictions. This proves the prime-field case.
10. Restriction of scalars is exact. Factoring the same ringed-topos morphism in two ways
    and applying derived pushforward composition identifies restriction of derived direct
    image with derived direct image of restricted scalars, also on cohomology.
11. Each simple quotient is a finite residue field. Choose its finite prime-field basis.
    Its constant sheaf is finite free and perfect. Apply the perfect projection formula
    to the constant prime field and this residue field; pullback preserves constants.
12. In that basis, tensor is a finite direct sum, so cohomology commutes with tensor.
    Constant finite module models tensor to constant finite models. Change of ring first
    from the prime field to the residue field, then from the coefficient ring to the
    residue field, gives constructibility of the simple quotient's direct images.
13. Apply devissage to the filtration. Proper base change and pullback of constants
    identify the restrictions on the two dimension loci. Concatenating their finite
    constructible stratifications proves the assertion over the whole base.
-/
theorem properSmoothCurves_finiteModule_higherDirectImage_constructible_all_char
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  sorry

end AlgebraicGeometry.Etale
