/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImage
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluationEquation
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
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
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
public import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceIntegralKummerClass
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingScalarSquare
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryEndpointMaps
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective
import all WeilConjectures.AlgebraicGeometry.ScalarUnitExtComparison
import all WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralBoundaryBase

/-! # The integral boundary as a hom-level equation of derived single arrows -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  CategoryTheory.Abelian.Ext HasDerivedCategory.standard
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  comparisonUpperStar diagonalFiniteToPadic diagonalForget SpTowerClasses.lineModule

open SpTowerClasses
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open WeilConjectures
attribute [local implicit_reducible] spCoefficientCommRings
  SpTowerShriek.tau Functor.ofOpSequence Functor.ofSequence
  SemilinearSections.evaluation
attribute [local irreducible] SemilinearSections.scalarExtensionSection
  cartierProRootMap

attribute [local semireducible] diagonalForget SpTowerClasses.lineModule

section IntegralBoundaryCalculation

attribute [local instance 3000] CategoryTheory.CategoryStruct.toQuiver
attribute [local implicit_reducible] CategoryTheory.constantSheaf comparisonLowerStar
  Functor.sheafPushforwardContinuous Scheme.toProEt

attribute [local irreducible] Ext.comp Ext.mk₀ Ext.mk₀CompMk₀
  Ext.mapExactFunctor Ext.homEquiv diagonalForget SpTowerClasses.lineModule
attribute [local implicit_reducible] geoCartierLine

attribute [local instance 100000] integralAbDerived

set_option quotPrecheck false in
set_option hygiene false in
/-- The degree-zero single functor of the abelian pro-étale sheaves on `diagonalSurface Y`. -/
local notation "𝒮[" Y "]" =>
  DerivedCategory.singleFunctor.{u + 1} (DiagonalAb (diagonalSurface Y)) 0

/-- Insert the source and root endpoint equations `hs` and `hr` into the glued square. -/
private theorem integralBoundary_hom_of_glue
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (P : (diagonalSurface Y).Pic)
    (b : Ext (Etale.ordinaryFiniteConstant (diagonalResidue.{u} l n)
      (diagonalSurface Y)) (Scheme.finiteEtaleTateLine (diagonalSurface Y)
        (l ^ (n + 1)) (diagonalResidue.{u} l n) (cartierResidue_cast l (n + 1))) 2)
    (hs : finiteQuotient l (ULift.{u} (Padic l)) (diagonalSurface Y) n ≫
      (evalIso l (diagonalSurface Y) r n).inv.app
        (coefficient (diagonalSurface Y) (Arings l (ULift.{u} (Padic l))
          (diagonalSurface Y))) ≫
      (diagonalForget l (diagonalSurface Y)).map a.coefficient.hom ≫
      (diagonalFiniteForgetIso l n (diagonalSurface Y)).inv.app
        (geoCartierConstant (diagonalResidue.{u} l n) (diagonalSurface Y)) =
      siteIntegralGenerator (diagonalResidue.{u} l n) (diagonalSurface Y))
    (hr : finiteRootMap l (ULift.{u} (Padic l)) (diagonalSurface Y) n ≫
      (finiteForget l (ULift.{u} (Padic l)) (diagonalSurface Y) n).map
        (lineEvaluation l (ULift.{u} (Padic l)) c n).inv ≫
      (evalIso l (diagonalSurface Y) r n).inv.app
        (lineModule l (ULift.{u} (Padic l)) c) ≫
      (diagonalForget l (diagonalSurface Y)).map a.line.hom ≫
      (diagonalFiniteForgetIso l n (diagonalSurface Y)).inv.app
        (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
          (cartierResidue_cast l (n + 1)) (diagonalSurface Y)) =
        cartierProRootMap (diagonalResidue.{u} l n) (l ^ (n + 1))
          (cartierResidue_cast l (n + 1)) (diagonalSurface Y)
          (pow_pos (Fact.out : l.Prime).pos _) (diagonalSurface_power_unit l Y hY n))
    (hh :
      ((𝒮[Y]).map (finiteQuotient l (ULift.{u} (Padic l)) (diagonalSurface Y) n) ≫
        ((𝒮[Y]).mapIso ((evalIso l (diagonalSurface Y) r n).app (coefficient (diagonalSurface Y)
          (Arings l (ULift.{u} (Padic l)) (diagonalSurface Y))))).inv ≫
        ((𝒮[Y]).mapIso ((diagonalForget l (diagonalSurface Y)).mapIso a.coefficient)).hom ≫
        ((𝒮[Y]).mapIso ((diagonalFiniteForgetIso l n (diagonalSurface Y)).app
          (geoCartierConstant (diagonalResidue.{u} l n) (diagonalSurface Y)))).inv) ≫
        mapSingleArrow (cartierForget (diagonalResidue.{u} l n) (diagonalSurface Y)) (2 : ℤ)
          (finiteEtaleProImage (diagonalResidue.{u} l n) (diagonalSurface Y) (l ^ (n + 1))
            (cartierResidue_cast l (n + 1)) b).hom =
      evaluatedTowerBoundary l (diagonalSurface Y) n c.kummer P ≫
        ((𝒮[Y]).map (finiteRootMap l (ULift.{u} (Padic l)) (diagonalSurface Y) n) ≫
          ((𝒮[Y]).mapIso ((finiteForget l (ULift.{u} (Padic l)) (diagonalSurface Y) n).mapIso
            (lineEvaluation l (ULift.{u} (Padic l)) c n))).inv ≫
          ((𝒮[Y]).mapIso ((evalIso l (diagonalSurface Y) r n).app
            (lineModule l (ULift.{u} (Padic l)) c))).inv ≫
          ((𝒮[Y]).mapIso ((diagonalForget l (diagonalSurface Y)).mapIso a.line)).hom ≫
          ((𝒮[Y]).mapIso ((diagonalFiniteForgetIso l n (diagonalSurface Y)).app
            (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
              (cartierResidue_cast l (n + 1)) (diagonalSurface Y)))).inv)⟦(2 : ℤ)⟧') :
    (𝒮[Y]).map (siteIntegralGenerator (diagonalResidue.{u} l n) (diagonalSurface Y)) ≫
      mapSingleArrow (cartierForget (diagonalResidue.{u} l n) (diagonalSurface Y)) (2 : ℤ)
        (finiteEtaleProImage (diagonalResidue.{u} l n) (diagonalSurface Y) (l ^ (n + 1))
          (cartierResidue_cast l (n + 1)) b).hom =
    evaluatedTowerBoundary l (diagonalSurface Y) n c.kummer P ≫
      ((𝒮[Y]).map (cartierProRootMap (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y) (pow_pos (Fact.out : l.Prime).pos _)
        (diagonalSurface_power_unit l Y hY n)))⟦(2 : ℤ)⟧' := by
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_inv, ← (𝒮[Y]).map_comp] at hh
  erw [hs, hr] at hh
  exact hh


end IntegralBoundaryCalculation

end AlgebraicGeometry.ProEtale.DiagonalTrace
