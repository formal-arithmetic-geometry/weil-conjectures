/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameKummer
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.CategoryTheory.Sites.SmoothPurity.SupportLongExact
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleClosedConstantTensor
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
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square

import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.Yoneda
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement

import all Mathlib.Logic.Small.Defs

import all Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Pullback and symmetry of supported Kummer cup products

Source: Stacks Project, Tags 0FPL, 0FPM, 09XP, 03PL and 0G78; blueprint
main-20261015, lem-pur-frame-independence, unit multiples, permutations and shears
(blueprint: lem-pur-supported-cup-functoriality).

The Boolean site parameter is false for the small etale site and true for the
small pro-etale site. All constructions use the published sites, coefficients,
Kummer classes, exact inverse images and derived tensors.

## Main definitions and statement

* `functorialCupPullback`: the canonically normalized supported pullback.
* `functorialCup`: the prescribed tensor-morphism cup product on either site.
* `FunctorialCupAlgebraLaws`, `FunctorialCupLocalizationLaws`, and
  `FunctorialCupComparisonLaws`: the clauses of the statement.
* `supportedCupFunctoriality`: all these clauses for both sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u c v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

set_option backward.isDefEq.respectTransparency false in

private theorem functorialDerivedPair_isIso {C : Type c} [hCat : Category.{v} C]
    [hAb : Abelian C] [IsGrothendieckAbelian.{v} C] [hD : HasDerivedCategory.{v} C]
    [HasColimitsOfSize.{0, 0} C] [hM : MonoidalCategory C] [hMP : MonoidalPreadditive C]
    [hClosed : MonoidalClosed C] [hB : BraidedCategory C]
    [hFlat : Abelian.HasFunctorialFlatResolution C]
    (p : Σ m : MonoidalCategory (DerivedCategory C),
      letI := m
      (DerivedCategory.Q (C := C)).LaxMonoidal)
    (e : p = ⟨inferInstance, inferInstance⟩)
    {L M N : C} (μ : L ⊗ M ⟶ N) [hμ : IsIso μ] (hL : ObjectProperty.flat L) :
    letI := p.1
    letI := p.2
    IsIso (ProEtale.cupDerivedCoefficientMap μ) := by
  exact ProEtale.cupDerivedPair_isIso p e μ hL

/-- The selected small site category. -/
abbrev functorialCupSite (pro : Bool) (X : Scheme.{u}) : Type (u + 1) :=
  match pro with
  | false => X.Etale
  | true => X.ProEt

/-- Its existing category. -/
@[reducible] instance functorialCupSiteCategory (pro : Bool) (X : Scheme.{u}) :
    Category.{u} (functorialCupSite pro X) := by cases pro <;> infer_instance

/-- Its existing topology. -/
abbrev functorialCupTopology (pro : Bool) (X : Scheme.{u}) :
    GrothendieckTopology (functorialCupSite pro X) :=
  match pro with
  | false => X.smallEtaleTopology
  | true => Scheme.ProEt.topology X

/-- The actual sheaf category on the selected small site. -/
abbrev functorialCupSheaves (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  Sheaf (functorialCupTopology pro X) (ModuleCat.{u + 1} P.Coefficient)

@[reducible] instance functorialCupCategory (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    Category.{u + 1} (P.functorialCupSheaves pro X) := inferInstance

@[reducible] instance functorialCupAbelian (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    Abelian (P.functorialCupSheaves pro X) := inferInstance

@[reducible] instance functorialCupHasDerived (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : HasDerivedCategory.{u + 1} (P.functorialCupSheaves pro X) :=
  inferInstance

/-- The existing derived category, with its localization shared explicitly.
Source: supported tensor construction (blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupDerived (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  @DerivedCategory (P.functorialCupSheaves pro X) _ _ (P.functorialCupHasDerived pro X)

/-- The existing finite constant module. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupConstant (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    P.functorialCupSheaves pro X :=
  match pro with
  | false => P.constantEtale X
  | true => P.constant X

/-- The published comparison inverse image, with its actual exact structure.
Source: Stacks 099R (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupComparisonFunctor (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    P.functorialCupSheaves false X ⥤ P.functorialCupSheaves true X :=
  ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X

/-- The signed finite Tate sheaf at the actual annihilator ell^n. Source: the
arbitrary-index Kummer prescription in def-pur-frame-class
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwist (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) (r : ℤ) : P.functorialCupSheaves pro X :=
  match pro with
  | false => Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
      P.diagonalExponent_annihilates r
  | true => (P.functorialCupComparisonFunctor X).obj
      (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
        P.diagonalExponent_annihilates r)

/-- The existing degree-zero embedding. Source: supported tensor construction
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSingle (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    P.functorialCupSheaves pro X ⥤ P.FunctorialCupDerived pro X :=
  @DerivedCategory.singleFunctor (P.functorialCupSheaves pro X) _ _
    (P.functorialCupHasDerived pro X) 0

/-- The actual underived direct image of constants from the closed support.
Source: def-pur-supported-cup, supported-Hom model
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSource (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) : P.functorialCupSheaves pro X :=
  match pro with
  | false => (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale C)
  | true => (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant C)

/-- Restriction of local constants, exactly the coefficient map of the supported cup.
Source: def-pur-supported-cup and the etale coefficient lemma
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupRestriction (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupConstant pro X ⟶ P.functorialCupSource pro i :=
  match pro with
  | false => Etale.closedConstantSectionMap P.Coefficient i
  | true => ProEtale.cupCoefficientRestriction P i

/-- The supported degree-zero source, shared before forming Hom types. -/
def functorialCupSourceObject (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) : P.FunctorialCupDerived pro X :=
  (P.functorialCupSingle pro X).obj (P.functorialCupSource pro i)

/-- The shifted coefficient target, shared by all supported Hom types. -/
def functorialCupTarget (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) (a r : ℤ) : P.FunctorialCupDerived pro X :=
  ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r))⟦a⟧

/-- Supported cohomology in the published Hom model, for arbitrary integer degrees.
Source: lem-pur-supported-hom and lem-amb-closed-support-hom
(blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupH (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) (a r : ℤ) : Type (u + 1) :=
  P.functorialCupSourceObject pro i ⟶
    P.functorialCupTarget pro X a r

/-- Exact inverse image on degree-zero Hom. -/
def functorialCupExactHom {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B]
    [hD : HasDerivedCategory.{w} D] (F : B ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S T : B} (a : ℤ)
    (α : (DerivedCategory.singleFunctor B 0).obj S ⟶
      ((DerivedCategory.singleFunctor B 0).obj T)⟦a⟧) :
    (DerivedCategory.singleFunctor D 0).obj (F.obj S) ⟶
      ((DerivedCategory.singleFunctor D 0).obj (F.obj T))⟦a⟧ :=
  (F.mapDerivedCategorySingleFunctor 0).inv.app S ≫
    F.mapDerivedCategory.map α ≫
    (F.mapDerivedCategory.commShiftIso a).hom.app
      ((DerivedCategory.singleFunctor B 0).obj T) ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app T)⟦a⟧'

/-- Normalized single/shift map under an exact functor. -/
def functorialCupNormalizedHom {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B] [hD : HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S T : B} {S' T' : D} (eS : F.obj S ≅ S') (eT : F.obj T ≅ T')
    (a : ℤ) (α : (DerivedCategory.singleFunctor B 0).obj S ⟶
      ((DerivedCategory.singleFunctor B 0).obj T)⟦a⟧) :
    (DerivedCategory.singleFunctor D 0).obj S' ⟶
      ((DerivedCategory.singleFunctor D 0).obj T')⟦a⟧ :=
  (DerivedCategory.singleFunctor D 0).map eS.inv ≫ functorialCupExactHom F a α ≫
    ((DerivedCategory.singleFunctor D 0).map eT.hom)⟦a⟧'

/-- The actual exact inverse image of fixed-scalar modules. Source: Stacks 03Q1
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupInverseImage (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    P.functorialCupSheaves pro X ⥤ P.functorialCupSheaves pro Y :=
  match pro with
  | false => Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v
  | true => ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
@[reducible] instance functorialCupMonoidal (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    MonoidalCategory (P.functorialCupSheaves pro X) := by infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupMonoidalPreadditive (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    MonoidalPreadditive (P.functorialCupSheaves pro X) := by infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
@[reducible] instance functorialCupSymmetric (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    SymmetricCategory (P.functorialCupSheaves pro X) := by infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
@[reducible] instance functorialCupClosed (P : PurityFiniteSetting.{u}) (pro : Bool) (X :
    Scheme.{u}) :
    MonoidalClosed (P.functorialCupSheaves pro X) := by infer_instance

/-- The published functorial flat resolutions, selected by the site.
Source: K-flat tensor construction (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupFlatResolutions (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : Abelian.HasFunctorialFlatResolution (P.functorialCupSheaves pro X) := by
  infer_instance

/-- Share the derived tensor and its localization tensorator as one construction. -/
def functorialCupTensorData {B : Type c} [Category.{v} B] [Abelian B]
    [HasDerivedCategory.{v} B] [IsGrothendieckAbelian.{v} B]
    [HasColimitsOfSize.{0, 0} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [MonoidalClosed B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B] :
    Σ m : MonoidalCategory (DerivedCategory B),
      letI := m
      (DerivedCategory.Q (C := B)).LaxMonoidal := ⟨inferInstance, inferInstance⟩

/-- The monoidal structure projected from the shared construction. -/
instance functorialCupDerivedMonoidal (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : MonoidalCategory (P.FunctorialCupDerived pro X) :=
  (functorialCupTensorData (B := P.functorialCupSheaves pro X)).1

private theorem pairedCoefficient_isIso {B : Type c} [Category.{v} B] [Abelian B]
    [HasDerivedCategory.{v} B] [IsGrothendieckAbelian.{v} B]
    [HasColimitsOfSize.{0, 0} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [MonoidalClosed B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
    {L M N : B} (μ : L ⊗ M ⟶ N) [IsIso μ] (hL : ObjectProperty.flat L) :
    letI := (functorialCupTensorData (B := B)).1
    letI := (functorialCupTensorData (B := B)).2
    IsIso (ProEtale.cupDerivedCoefficientMap μ) := by
  exact functorialDerivedPair_isIso (functorialCupTensorData (B := B)) rfl μ hL

/-- The coefficient multiplication fixed by restriction and local scalar multiplication.
Source: def-pur-supported-cup and its etale analogue
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupMultiplication (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    P.functorialCupSource pro i ⊗ P.functorialCupSource pro j ⟶
      P.functorialCupSource pro (ProEtale.cupIntersection i j) :=
  match pro with
  | false => Etale.closedConstantTensorMap P.Coefficient i j
  | true => ProEtale.cupCoefficientMap P i j

/-- The signed product family together with the equations that uniquely normalize it.
All data are projected from the published signed-twist theorem, with the unit,
positive-power, evaluation, associativity and symmetry equations retained.
Source: Stacks 03PK, 07A4 (blueprint: lem-pur-supported-cup-functoriality). -/
structure FunctorialCupTwistProducts (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) where
  product : ∀ (X : Scheme.{u}), IsUnit (m : Γ(X, ⊤)) → ∀ r s : ℤ,
    Scheme.finiteEtaleTateSheaf A m X hA r ⊗ Scheme.finiteEtaleTateSheaf A m X hA s ≅
      Scheme.finiteEtaleTateSheaf A m X hA (r + s)
  left_unit : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r : ℤ),
    product X hX 0 r = λ_ (Scheme.finiteEtaleTateSheaf A m X hA r) ≪≫
      eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (zero_add r).symm)
  right_unit : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r : ℤ),
    product X hX r 0 = ρ_ (Scheme.finiteEtaleTateSheaf A m X hA r) ≪≫
      eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (add_zero r).symm)
  positive : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (n : ℕ),
    product X hX (.ofNat (n + 1)) 1 = Iso.refl _
  associativity : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r s t : ℤ),
    (product X hX r s).hom ▷ Scheme.finiteEtaleTateSheaf A m X hA t ≫
        (product X hX (r + s) t).hom =
      (α_ (Scheme.finiteEtaleTateSheaf A m X hA r)
        (Scheme.finiteEtaleTateSheaf A m X hA s)
        (Scheme.finiteEtaleTateSheaf A m X hA t)).hom ≫
      Scheme.finiteEtaleTateSheaf A m X hA r ◁ (product X hX s t).hom ≫
        (product X hX r (s + t)).hom ≫
          eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (add_assoc r s t).symm)
  symmetry : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r s : ℤ),
    (β_ (Scheme.finiteEtaleTateSheaf A m X hA r)
        (Scheme.finiteEtaleTateSheaf A m X hA s)).hom ≫
        (product X hX s r).hom ≫
        eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (add_comm s r)) =
      (product X hX r s).hom
  evaluation : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (n : ℕ),
    (product X hX (.ofNat (n + 1)) (.negSucc n)).hom ≫
        eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m X hA)
          (add_neg_cancel (Int.ofNat (n + 1)))) =
      (ihom.ev (Scheme.finiteEtaleTateSheaf A m X hA (.ofNat (n + 1)))).app
        (Scheme.finiteEtaleTateSheaf A m X hA 0)

/-- Extract one coherent normalized family, retaining its characterizing equations.
Source: lem-asd-etale-finite-twist-pullback
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistProducts (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) : FunctorialCupTwistProducts A m hA :=
  let t := Scheme.finiteEtaleTwistPullbackData A m hm hA
  { product := t.p
    left_unit := t.laws.2.2.2.2.2.2.2.2.1
    right_unit := t.laws.2.2.2.2.2.2.2.2.2.1
    positive := t.laws.2.2.2.2.2.2.2.2.2.2.1
    associativity := t.laws.2.2.2.2.2.2.2.2.2.2.2.1
    symmetry := t.laws.2.2.2.2.2.2.2.2.2.2.2.2.1
    evaluation := t.laws.2.2.2.2.2.2.2.2.2.2.2.2.2.1 }

/-- The canonical signed product, projected from its normalized family.
Source: Stacks 03PK, 07A4 (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistProductGeneral (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) (X : Scheme.{u})
    (hX : IsUnit (m : Γ(X, ⊤))) (r s : ℤ) :=
  (functorialCupTwistProducts A m hm hA).product X hX r s

/-- Normalized etale twist multiplication from the signed-root prescription.
This selects the witness together with its generator, evaluation and tensor
normalizations, never an uncharacterized isomorphism. Source: Stacks 03PK and 07A4,
lem-asd-etale-finite-twist-pullback
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupEtaleTwistProduct (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (r s : ℤ) :=
  functorialCupTwistProductGeneral P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit a) r s

/-- The same normalized twist multiplication, transported through the canonical
strong monoidal site comparison on the pro-etale site. Source: Stacks 07A4
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistProduct (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (r s : ℤ) :
    P.functorialCupTwist pro X r ⊗ P.functorialCupTwist pro X s ≅
      P.functorialCupTwist pro X (r + s) :=
  match pro with
  | false => P.functorialCupEtaleTwistProduct X a r s
  | true => (asIso (Functor.OplaxMonoidal.δ
      (P.functorialCupComparisonFunctor X)
        (P.functorialCupTwist false X r) (P.functorialCupTwist false X s))).symm ≪≫
      (P.functorialCupComparisonFunctor X).mapIso
        (P.functorialCupEtaleTwistProduct X a r s)

/-- Flat supported coefficients make the canonical degree-zero tensor comparison
invertible. Source: def-pur-supported-cup and lem-pur-etale-closed-constant-tensor
(blueprint: lem-pur-supported-cup-functoriality).
Proof: on the etale site geometric stalks are A or zero and multiplication is the
identity on the common support. On the pro-etale site use the quotient/idempotent
calculation in def-pur-supported-cup. In both cases the flat degree-zero sheaves
are their own K-flat models, so the canonical localization comparison is invertible. -/
theorem functorialCupCoefficient_isIso (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsIso (ProEtale.cupDerivedCoefficientMap (hD := P.functorialCupHasDerived pro X)
      (hDM := P.functorialCupDerivedMonoidal pro X) (P.functorialCupMultiplication pro i j)) := by
  have hμ : IsIso (P.functorialCupMultiplication pro i j) := by
    cases pro with
    | false => exact (Etale.closedConstantTensor P.Coefficient X i j j (𝟙 X)).2.2.2.2.2.2.2.2.2.1
    | true => exact ProEtale.cupCoefficientMap_isIso P i j
  have hL : ObjectProperty.flat (P.functorialCupSource pro i) := by
    cases pro with
    | false => exact Etale.closedConstantModule_flat _ i
    | true => exact ProEtale.cupCoefficient_flat P i
  exact pairedCoefficient_isIso (P.functorialCupMultiplication pro i j) hL

/-- The prescribed tensor-morphism supported product followed by multiplication
of the twist lines. For pro=true its first composite is the published supportedCup;
for pro=false it is its etale analogue, with exactly the same shift sign.
Source: def-pur-supported-cup, tensor-morphism formula
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCup (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
    (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (a b r s : ℤ) (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s) :
    P.FunctorialCupH pro (ProEtale.cupIntersection i j) (a + b) (r + s) :=
  ProEtale.cupComposite (hM := P.functorialCupDerivedMonoidal pro X)
    (ProEtale.cupDerivedCoefficientMap (hD := P.functorialCupHasDerived pro X)
      (hDM := P.functorialCupDerivedMonoidal pro X) (P.functorialCupMultiplication pro i j))
    (P.functorialCupCoefficient_isIso pro i j) a b α β ≫
      (ProEtale.cupSingleTensorMap (hD := P.functorialCupHasDerived pro X)
        (hDM := P.functorialCupDerivedMonoidal pro X)
          (P.functorialCupTwist pro X r) (P.functorialCupTwist pro X s) ≫
        (P.functorialCupSingle pro X).map (P.functorialCupTwistProduct pro X aX r s).hom)⟦a+b⟧'

section CoefficientProof

set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupHasDerived functorialCupDerivedMonoidal
  functorialCupMonoidal functorialCupAbelian functorialCupCategory
  functorialCupMonoidalPreadditive functorialCupSymmetric functorialCupClosed
  functorialCupFlatResolutions functorialCupMultiplication functorialCupSource

end CoefficientProof

/-- Canonical inverse image of the coefficient unit. Source: constant-sheaf adjunction
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupConstantPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    (P.functorialCupInverseImage pro v).obj (P.functorialCupConstant pro X) ≅
      P.functorialCupConstant pro Y :=
  match pro with
  | false => (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) v).app
      (ModuleCat.of P.Coefficient P.Coefficient)
  | true => P.frameConstantPullback v

/-- The etale part of normalized signed-twist inverse image.
Source: Stacks 03Q1, 07A4 (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupEtaleTwistPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (v : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (r : ℤ) :
    (P.functorialCupInverseImage false v).obj (P.functorialCupTwist false X r) ≅
      P.functorialCupTwist false Y r :=
  Etale.p1DecompositionSheafPullback P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates v (P.diagonalExponent_isUnit aX) r

/-- The same root-normalized inverse image on either site. Pro-etale inverse image
uses the canonical comparison mate. Source: Stacks 03Q1, 07A4
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (r : ℤ) :
    (P.functorialCupInverseImage pro v).obj (P.functorialCupTwist pro X r) ≅
      P.functorialCupTwist pro Y r :=
  match pro with
  | false => P.functorialCupEtaleTwistPullback v aX r
  | true => (ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) v).app (P.functorialCupTwist false X r) ≪≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapIso
        (P.functorialCupEtaleTwistPullback v aX r)

section ClosedSupportProof

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupCategory functorialCupAbelian
  functorialCupMonoidal functorialCupSymmetric functorialCupClosed
  constant constantEtale functorialCupConstant functorialCupComparisonFunctor
  functorialCupSource functorialCupRestriction functorialCupInverseImage
  functorialCupConstantPullback

section EtaleSourceNormalization

open Etale

private theorem transition_unit (A : Type (u + 1)) [CommRing A]
    {V D X : Scheme.{u}} (p : V ⟶ D) (g : D ⟶ X) (h : V ⟶ X)
    (hp : p ≫ g = h) :
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) g) ≫
      constantModulePushforwardMap A (ModuleCat.of A A) g h p hp =
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) h) := by
  unfold constantModulePushforwardMap
  erw [upperStarConstantSheafIso_hom_app_tensorUnit (ModuleCat.{u + 1} A) p]
  erw [Adjunction.unit_app_unit_comp_map_η]
  exact (ε_lowerStar_comp p g h hp.symm).symm

private theorem section_unit (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    closedConstantSectionMap A i =
      Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) i) := by
  unfold closedConstantSectionMap
  erw [← ε_lowerStar_id]
  exact transition_unit A i (𝟙 X) i (by simp)

private theorem section_epi (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    Epi (closedConstantSectionMap A i) := by
  erw [section_unit A i]
  erw [← (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit_app_unit_comp_map_η]
  have : Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) :=
    (shortExact_openClosedShortComplex (ModuleCat.{u + 1} A)
      i.openComplement.ι i
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      i.range_eq_compl_range_openComplement_ι).epi_g
  exact epi_comp _ _

end EtaleSourceNormalization

private theorem comparisonSource_normalized (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ∃! b : (P.functorialCupComparisonFunctor X).obj
        (P.functorialCupSource false i) ≅ P.functorialCupSource true i,
      (P.functorialCupComparisonFunctor X).map
          (P.functorialCupRestriction false i) ≫ b.hom = P.functorialCupRestriction true i := by
  let F := P.functorialCupComparisonFunctor X
  have := section_epi P.Coefficient i
  have : Epi (P.functorialCupRestriction false i) := section_epi P.Coefficient i
  have : Epi (F.map (P.functorialCupRestriction false i)) := F.map_epi _
  have := ProEtale.isIso_lowerStarComparisonUpperStarBaseChange i
    (ModuleCat.{u + 1} P.Coefficient)
  let e := asIso ((ProEtale.lowerStarComparisonUpperStarBaseChange i
    (ModuleCat.{u + 1} P.Coefficient)).app (P.constantEtale C))
  have he : F.map (P.functorialCupRestriction false i) ≫ e.hom =
      P.functorialCupRestriction true i := by
    change (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
      (Etale.closedConstantSectionMap P.Coefficient i) ≫ _ = _
    rw [section_unit]
    exact (ProEtale.comparison_restriction P i).symm
  refine ⟨e, he, ?_⟩
  intro b hb
  apply Iso.ext
  exact (cancel_epi (F.map (P.functorialCupRestriction false i))).1 (hb.trans he.symm)

private theorem etaleExchange_normalized (P : PurityFiniteSetting.{u})
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) :
    ∃! b : (P.functorialCupInverseImage false v).obj (P.functorialCupSource false i) ≅
        P.functorialCupSource false j,
      (P.functorialCupInverseImage false v).map (P.functorialCupRestriction false i) ≫
          b.hom =
        (P.functorialCupConstantPullback false v).hom ≫
          P.functorialCupRestriction false j := by
  let B := ModuleCat.{u + 1} P.Coefficient
  have hs : IsPullback g j i v :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  let b := (baseChangeMap B sq.toCommSq).app (𝟙_ _) ≫
    (lowerStar B j).map (Functor.OplaxMonoidal.η (upperStar B g))
  have hBC := basechange_monoidal P.Coefficient sq.toCommSq
  have hb : (upperStar B v).map (Etale.closedConstantSectionMap P.Coefficient i) ≫ b =
      Functor.OplaxMonoidal.η (upperStar B v) ≫
        Etale.closedConstantSectionMap P.Coefficient j := by
    erw [section_unit, section_unit]
    apply (cancel_epi (Functor.LaxMonoidal.ε (upperStar B v))).1
    dsimp only [b]
    have hu := NatTrans.IsMonoidal.unit (τ := baseChangeMap B sq.toCommSq)
    dsimp only [Functor.LaxMonoidal.comp_ε] at hu
    simp only [Category.assoc] at hu ⊢
    rw [reassoc_of% hu]
    simp only [← Functor.map_comp, Functor.Monoidal.ε_η,
      Functor.Monoidal.ε_η_assoc]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have := isIso_baseChangeMap_of_isFinite B hs
  have : IsIso b := by dsimp only [b]; infer_instance
  have := section_epi P.Coefficient i
  have : Epi (P.functorialCupRestriction false i) := section_epi P.Coefficient i
  have : Epi ((upperStar B v).map (Etale.closedConstantSectionMap P.Coefficient i)) :=
    (upperStar B v).map_epi _
  have he : (P.functorialCupInverseImage false v).map
        (P.functorialCupRestriction false i) ≫ (asIso b).hom =
      (P.functorialCupConstantPullback false v).hom ≫
        P.functorialCupRestriction false j := by
    change (upperStar B v).map (Etale.closedConstantSectionMap P.Coefficient i) ≫ b =
      (Scheme.upperStarConstantSheafIso B v).hom.app (𝟙_ B) ≫
        Etale.closedConstantSectionMap P.Coefficient j
    rw [upperStarConstantSheafIso_hom_app_tensorUnit]
    exact hb
  refine ⟨asIso b, he, ?_⟩
  intro e he'
  apply Iso.ext
  exact (cancel_epi ((upperStar B v).map
    (Etale.closedConstantSectionMap P.Coefficient i))).1 (he'.trans he.symm)

/-- Closed constant exchange is uniquely fixed by restriction of the unit.
Source: Stacks 03Q1 and 099V; supported functoriality, proof Steps 2 and 6
(blueprint: lem-pur-supported-cup-functoriality).
Proof: etale geometric stalks give A on the inverse-image closed subset and zero
elsewhere, so the section-normalized adjoint is invertible. For pro-etale objects
Y over X identify comparison inverse-image sections with etale sections on Y.
The same etale calculation and degree-zero comparison identify the closed source,
with identical local constants and restriction. This yields the asserted map on
both sites. Restriction from the constant unit is epic, so its displayed equation
makes the map unique. Nonreduced and empty closed supports require no modification. -/
private theorem normalizedExchangeTransport
    {B D E F : Type c} [Category.{v} B] [Category.{v} D]
    [Category.{v} E] [Category.{v} F]
    (FX : B ⥤ E) (FY : D ⥤ F) (U : B ⥤ D) (V : E ⥤ F)
    (τ : FX ⋙ V ≅ U ⋙ FY)
    {A S : B} {A' S' : D} {B₀ T : E} {B₀' T' : F}
    (ρ : A ⟶ S) (ρ' : A' ⟶ S') (σ : B₀ ⟶ T) (σ' : B₀' ⟶ T')
    (ei : FX.obj S ≅ T) (ej : FY.obj S' ≅ T')
    (q : U.obj A ≅ A') (q' : V.obj B₀ ≅ B₀')
    (a : FX.obj A ≅ B₀) (a' : FY.obj A' ≅ B₀')
    (e : U.obj S ≅ S')
    (hi : FX.map ρ ≫ ei.hom = a.hom ≫ σ)
    (hj : FY.map ρ' ≫ ej.hom = a'.hom ≫ σ')
    (he : U.map ρ ≫ e.hom = q.hom ≫ ρ')
    (ha : τ.hom.app A ≫ FY.map q.hom ≫ a'.hom = V.map a.hom ≫ q'.hom)
    [Epi (V.map σ)] :
    ∃! b : V.obj T ≅ T', V.map σ ≫ b.hom = q'.hom ≫ σ' := by
  let b := V.mapIso ei.symm ≪≫ τ.app S ≪≫ FY.mapIso e ≪≫ ej
  have hb : V.map σ ≫ b.hom = q'.hom ≫ σ' := by
    apply (cancel_epi (V.map a.hom)).1
    rw [← V.map_comp_assoc, ← hi, V.map_comp]
    simp only [b, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
      Category.assoc, ← V.map_comp_assoc, Iso.hom_inv_id, V.map_id, Category.id_comp]
    rw [reassoc_of% τ.hom.naturality]
    change τ.hom.app A ≫ FY.map (U.map ρ) ≫ FY.map e.hom ≫ ej.hom = _
    rw [← FY.map_comp_assoc, he, FY.map_comp, Category.assoc, hj]
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ σ') ha
  refine ⟨b, hb, ?_⟩
  intro b' hb'
  apply Iso.ext
  exact (cancel_epi (V.map σ)).1 (hb'.trans hb.symm)

private theorem proExchange_normalized (P : PurityFiniteSetting.{u})
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (_sq : ChosenCartesianSquare g j i v) :
    ∃! b : (P.functorialCupInverseImage true v).obj (P.functorialCupSource true i) ≅
        P.functorialCupSource true j,
      (P.functorialCupInverseImage true v).map (P.functorialCupRestriction true i) ≫ b.hom =
        (P.functorialCupConstantPullback true v).hom ≫ P.functorialCupRestriction true j  := by
  let FX := P.functorialCupComparisonFunctor X
  let FY := P.functorialCupComparisonFunctor Y
  let V := P.functorialCupInverseImage true v
  let U := P.functorialCupInverseImage false v
  let ei := (comparisonSource_normalized P i).choose
  let ej := (comparisonSource_normalized P j).choose
  have hi := (comparisonSource_normalized P i).choose_spec.1
  have hj := (comparisonSource_normalized P j).choose_spec.1
  let e := (etaleExchange_normalized P i j v g _sq).choose
  have he := (etaleExchange_normalized P i j v g _sq).choose_spec.1
  have := section_epi P.Coefficient i
  have : Epi (FX.map (P.functorialCupRestriction false i)) := FX.map_epi _
  have hpi : Epi (P.functorialCupRestriction true i) := by
    rw [← hi]
    exact epi_comp _ _
  have : V.PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels V
  have : Epi (V.map (P.functorialCupRestriction true i)) := V.map_epi _
  exact normalizedExchangeTransport FX FY U V
    (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient) v)
    (P.functorialCupRestriction false i) (P.functorialCupRestriction false j)
    (P.functorialCupRestriction true i) (P.functorialCupRestriction true j)
    ei ej (P.functorialCupConstantPullback false v)
    (P.functorialCupConstantPullback true v) (Iso.refl _) (Iso.refl _) e
    (by simpa using hi) (by simpa using hj) he (by
      simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
        functorialCupConstantPullback, frameConstantPullback, Iso.trans_hom,
        Functor.mapIso_hom, Iso.app_hom]
      rfl)

theorem functorialCupExchange_existsUnique (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (_sq : ChosenCartesianSquare g j i v) :
    ∃! b : (P.functorialCupInverseImage pro v).obj (P.functorialCupSource pro i) ≅
        P.functorialCupSource pro j,
      (P.functorialCupInverseImage pro v).map (P.functorialCupRestriction pro i) ≫ b.hom =
        (P.functorialCupConstantPullback pro v).hom ≫ P.functorialCupRestriction pro j  := by
  cases pro with
  | false => exact etaleExchange_normalized P i j v g _sq
  | true => exact proExchange_normalized P i j v g _sq

/-- The uniquely normalized ordinary coefficient exchange; no purity exchange is used.
Source: Stacks 03Q1, supported functoriality formula
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupExchange (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) :
    (P.functorialCupInverseImage pro v).obj (P.functorialCupSource pro i) ≅
      P.functorialCupSource pro j :=
  match pro with
  | false => (P.functorialCupExchange_existsUnique false i j v g sq).choose
  | true => (P.functorialCupExchange_existsUnique true i j v g sq).choose

section EtaleExchangeNormalization

open Etale
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
  SymmetricCategory.toBraidedCategory
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

end EtaleExchangeNormalization

end ClosedSupportProof

section SupportMapProof

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupCategory functorialCupAbelian
  functorialCupMonoidal functorialCupSymmetric functorialCupClosed
  constant constantEtale functorialCupConstant functorialCupComparisonFunctor
  functorialCupSource functorialCupRestriction functorialCupInverseImage
  functorialCupConstantPullback

/-- Change of closed support over a fixed scheme, uniquely determined on local constants.
Source: supported functoriality, Steps 2 and 5
(blueprint: lem-pur-supported-cup-functoriality).
Proof: the map D to C over X restricts each locally constant section on C to D.
The sheaf map is A-linear and carries the restricted unit to the restricted unit.
The constant restriction onto the closed direct image is epic, proving uniqueness. -/
theorem functorialCupSupportMap_existsUnique (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (_h : g ≫ i = j) :
    ∃! b : P.functorialCupSource pro i ⟶ P.functorialCupSource pro j,
      P.functorialCupRestriction pro i ≫ b = P.functorialCupRestriction pro j := by
  let t := Etale.constantModulePushforwardMap P.Coefficient
    (ModuleCat.of P.Coefficient P.Coefficient) i j g _h
  have ht : Etale.closedConstantSectionMap P.Coefficient i ≫ t =
      Etale.closedConstantSectionMap P.Coefficient j := by
    rw [section_unit, section_unit]
    exact transition_unit _ g i j _h
  have := section_epi P.Coefficient i
  have : Epi (P.functorialCupRestriction false i) := section_epi P.Coefficient i
  cases pro with
  | false =>
    refine ⟨t, ht, ?_⟩
    intro b hb
    exact (cancel_epi (Etale.closedConstantSectionMap P.Coefficient i)).1 (hb.trans ht.symm)
  | true =>
    let F := P.functorialCupComparisonFunctor X
    let ei := (comparisonSource_normalized P i).choose
    let ej := (comparisonSource_normalized P j).choose
    have hi := (comparisonSource_normalized P i).choose_spec.1
    have hj := (comparisonSource_normalized P j).choose_spec.1
    change F.map (P.functorialCupRestriction false i) ≫ ei.hom = _ at hi
    change F.map (P.functorialCupRestriction false j) ≫ ej.hom = _ at hj
    have : Epi (F.map (Etale.closedConstantSectionMap P.Coefficient i)) := F.map_epi _
    have hpi : Epi (P.functorialCupRestriction true i) := by
      rw [← hi]
      exact epi_comp _ _
    let b := ei.inv ≫ F.map t ≫ ej.hom
    have hb : P.functorialCupRestriction true i ≫ b =
        P.functorialCupRestriction true j := by
      rw [← hi]
      dsimp only [b]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← F.map_comp_assoc, ht]
      exact hj
    refine ⟨b, hb, ?_⟩
    intro b' hb'
    exact (cancel_epi (P.functorialCupRestriction true i)).1 (hb'.trans hb.symm)

end SupportMapProof

/-- The actual restriction on closed constant sheaves, fixed by its epic unit map.
Source: supported functoriality, Steps 2 and 5
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSupportMap (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (h : g ≫ i = j) :
    P.functorialCupSource pro i ⟶ P.functorialCupSource pro j :=
  (P.functorialCupSupportMap_existsUnique pro i j g h).choose

/-- Precomposition with the canonical closed support map. Source: supported
functoriality, symmetry and associativity clauses
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupChangeSupport (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (h : g ≫ i = j)
    (a r : ℤ) (α : P.FunctorialCupH pro j a r) : P.FunctorialCupH pro i a r :=
  (P.functorialCupSingle pro X).map (P.functorialCupSupportMap pro i j g h) ≫ α

attribute [local instance] functorialCupHasExt

/-- The identity direct-image unitor of the actual supported coefficient source.
Source: the full-support normalization
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupFullSupportIso (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    P.functorialCupSource pro (𝟙 X) ≅ P.functorialCupConstant pro X :=
  match pro with
  | false => (Etale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app
      (P.constantEtale X)
  | true => (ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app (P.constant X)

/-- Ordinary cohomology in the same derived-Hom model. Source: Hom_A(A,-)=sections
(blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupOrdinaryH (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) (a r : ℤ) : Type (u + 1) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupConstant pro X) ⟶
    P.functorialCupTarget pro X a r

/-- Forget supports by the actual restriction of constants to the support.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupForget (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupH pro i a r) : P.FunctorialCupOrdinaryH pro X a r :=
  (P.functorialCupSingle pro X).map (P.functorialCupRestriction pro i) ≫ α

/-- Ordinary pullback, using exact inverse image and the same twist normalization.
Source: Stacks 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOrdinaryPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ)
    (α : P.FunctorialCupOrdinaryH pro X a r) : P.FunctorialCupOrdinaryH pro Y a r :=
  functorialCupNormalizedHom (hB := P.functorialCupHasDerived pro X)
    (hD := P.functorialCupHasDerived pro Y) (P.functorialCupInverseImage pro v)
    (P.functorialCupConstantPullback pro v) (P.functorialCupTwistPullback pro v aX r) a α

/-- The published exact extension by zero for the complementary open.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenExtension (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupSheaves pro i.openComplement.toScheme ⥤ P.functorialCupSheaves pro X :=
  match pro with
  | false => Etale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      i.openComplement.ι
  | true => ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      i.openComplement.ι

/-- Extension by zero of the actual unit on the open complement.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenSource (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :=
  (P.functorialCupOpenExtension pro i).obj
    (P.functorialCupConstant pro i.openComplement.toScheme)

/-- The adjunction counit, with its canonical constant-sheaf restriction.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenInclusion (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupOpenSource pro i ⟶ P.functorialCupConstant pro X :=
  match pro with
  | false => (P.functorialCupOpenExtension false i).map
      (P.functorialCupConstantPullback false i.openComplement.ι).inv ≫
      (Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).counit.app (P.constantEtale X)
  | true => (P.functorialCupOpenExtension true i).map
      (P.functorialCupConstantPullback true i.openComplement.ι).inv ≫
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).counit.app (P.constant X)

section SequenceProof

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupCategory functorialCupAbelian
  constant constantEtale functorialCupConstant functorialCupSource
  functorialCupRestriction functorialCupInverseImage functorialCupConstantPullback
  functorialCupComparisonFunctor functorialCupOpenExtension functorialCupOpenSource
  functorialCupOpenInclusion

end SequenceProof

end WeilConjectures.PurityFiniteSetting
