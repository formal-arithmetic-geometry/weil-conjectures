/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.AlgebraicGeometry.TowerClassCoefficients
public import WeilConjectures.AlgebraicGeometry.TowerClassReduction
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedEquivalence
public import WeilConjectures.AlgebraicGeometry.TowerClassPullback
public import WeilConjectures.AlgebraicGeometry.CompletedCoefficientStructureMap
public import WeilConjectures.AlgebraicGeometry.PurTwistSheavesSupplement
public import WeilConjectures.AlgebraicGeometry.TwistedPullbackReductionData
public import WeilConjectures.AlgebraicGeometry.FieldScalarSystemData
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.AlgebraicGeometry.GeoCartierCycleClassDefsSupplement
public import WeilConjectures.AlgebraicGeometry.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.TowerClassChern
public import WeilConjectures.AlgebraicGeometry.TowerClassDiagonal
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.TowerClassSystems
public import WeilConjectures.AlgebraicGeometry.IntegralStrictReductionModel
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedCoefficientPushforwardModels
public import WeilConjectures.AlgebraicGeometry.PurTwistCoefficientRingsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerCanonical
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
import WeilConjectures.AlgebraicGeometry.GeoCartierCycleClass
import WeilConjectures.AlgebraicGeometry.PurityDivisorClass
import WeilConjectures.AlgebraicGeometry.EffectiveCartier

/-!
# Supported Cartier Kummer morphisms as coherent coefficient-system maps

Source: Stacks Project, Tags 03PL and 0A45; latest blueprint,
`sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md`, Steps 1 and 3
(blueprint: lem-pur-supported-kummer-coherent-system).

The finite Cartier boundary is assembled before evaluation, so the declaration below
records one morphism in the derived category of strict semilinear coefficient towers.
The fields retain the endpoint normalizations, signs, and all functoriality clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived

universe u a av d dv z zv w w'

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale WeilConjectures
open AlgebraicGeometry.ProEtale.SpTowerClasses

namespace AlgebraicGeometry.ProEtale

/-- Exact derived localization of the section-preserving coefficient presentation.
Source: blueprint coefficient systems
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedSystemRealization (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) :
    spDerivedCoefficientTowers l E T A ≌ SpTowerShriek.D l E T :=
  letI := A.hasDerived
  letI := b.realizationAdditive T
  (b.realization T).mapDerivedCategory

/-- The degree-zero comparison determined by the universal derived computation map.
Source: blueprint reduction on flat endpoints
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedSingleComparison
    {C : Type a} [Category.{av} C] [Abelian C] [HasDerivedCategory.{w} C]
    {B : Type d} [Category.{dv} B] [Abelian B] [HasDerivedCategory.{w'} B]
    (F : DerivedCategory C ⥤ DerivedCategory B) (G : C ⥤ B) [G.Additive]
    (ε : DerivedCategory.Q ⋙ F ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (M : C) :
    F.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (DerivedCategory.singleFunctor B 0).obj (G.obj M) :=
  F.map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app M) ≫
    ε.app ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app
      M) ≫ (DerivedCategory.singleFunctorIsoCompQ B 0).inv.app (G.obj M)

/-- A fixed-scalar section in its actual intrinsic sheafification.
Source: Stacks 00YV, blueprint finite coefficient comparison
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedIntrinsicSection (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} B)))
    (U : T.ProEtᵒᵖ) (x : M.obj.obj U) :
    ((finiteCoefficientIntrinsicRealization T B).obj M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
    (finiteCoefficientIntrinsicScalarMap T B)).unit.app
      ((finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} B)).obj M.obj)).app U x

/-- The positive finite coefficient ring at level `m+1` and its lifted fixed-scalar
presentation. The lift is the coefficient universe used by the finite Cartier
comparison, while the target derived category keeps the original quotient ring.
Source: blueprint coefficient convention (blueprint: lem-pur-supported-kummer-coherent-system). -/
abbrev supportedFiniteRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℕ) :=
  Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (m + 1)

/-- The coefficient-universe lift of the same finite quotient.
Source: blueprint coefficient convention (blueprint: lem-pur-supported-kummer-coherent-system). -/
abbrev supportedFiniteRingLift (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℕ) :=
  ULift.{u + 1, u} (supportedFiniteRing l E m)

/-- The quotient kills the positive power used by the finite supported Kummer class.
Source: blueprint Step 2 (blueprint: lem-pur-supported-kummer-coherent-system).

Proof (deferred): the ell power lies in the corresponding power of the principal
ideal (ell), so its quotient is zero. Apply ULift.up to coefficient_annihilates. -/
theorem supportedFiniteAnn (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (m : ℕ) :
    ((l ^ (m + 1) : ℕ) : supportedFiniteRingLift l E m) = 0 := by
  sorry

/-- The finite supported endpoint, using the canonical intrinsic realization of
fixed-scalar pro-etale modules.
Source: blueprint Step 4 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedFiniteEndpoint (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T D : Scheme.{u}) (i : D ⟶ T) [IsClosedImmersion i] (m : ℕ) :
    Scheme.proEtaleDerivedCategory T (supportedFiniteRing l E m) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((finiteCoefficientIntrinsicRealization T (supportedFiniteRing l E m)).obj
      ((lowerStar (ModuleCat.{u + 1} (supportedFiniteRingLift l E m)) i).obj
        (geoCartierConstant (supportedFiniteRingLift l E m) D)))

/-- The finite Tate endpoint, with the same intrinsic coefficient realization.
Source: blueprint Step 4 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def tateFiniteEndpoint (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (m : ℕ) :
    Scheme.proEtaleDerivedCategory T (supportedFiniteRing l E m) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((finiteCoefficientIntrinsicRealization T (supportedFiniteRing l E m)).obj
      (geoCartierLine (supportedFiniteRingLift l E m) (l ^ (m + 1))
        (supportedFiniteAnn l E m) T))

/-- A finite supported Cartier class transported through the canonical intrinsic
coefficient realization.
Source: blueprint Step 4 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def finiteSupportedCartierArrow (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T D : Scheme.{u}) (i : D ⟶ T) [IsClosedImmersion i]
    (_hI : i.ker.IsInvertible) (m : ℕ)
    (_hT : IsUnit ((l ^ (m + 1) : ℕ) : Γ(T, ⊤)))
    (c : GeoCartierClass (supportedFiniteRingLift l E m)
      (l ^ (m + 1)) (supportedFiniteAnn l E m) i) :
    supportedFiniteEndpoint l E T D i m ⟶
      (tateFiniteEndpoint l E T m)⟦(2 : ℤ)⟧ :=
  SpTowerClasses.mapSingleArrow
    (finiteCoefficientIntrinsicRealization T (supportedFiniteRing l E m))
    (2 : ℤ) c.hom

/-- The supported integer sheaf on the original pro-etale site.
Source: Stacks 0A45 (blueprint: lem-pur-supported-kummer-coherent-system). -/
abbrev supportedIntegers {T D : Scheme.{u}} (i : D ⟶ T) :=
  (lowerStar AddCommGrpCat.{u + 1} i).obj
    ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The relative pole extension made constant as one system, before any reduction.
Source: Stacks 0A45 and blueprint Step 1
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedPoleSystem {T D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    (DerivedCategory.singleFunctor (SpTowerClasses.Ab T) 0).obj
      ((SpTowerClasses.constant T).obj (supportedIntegers i)) ⟶
    ((DerivedCategory.singleFunctor (SpTowerClasses.Ab T) 0).obj
      (SpTowerClasses.units T))⟦(1 : ℤ)⟧ :=
  SpTowerClasses.mapSingleArrow (SpTowerClasses.constant T) (1 : ℤ)
    (cartierProBoundary i (Etale.cartierPoleBoundary i hI)).hom

/-- Reduction of the supported integers and actual extension to the valuation ring
quotients, performed on entire strict systems. Source: blueprint Step 3
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedExtendedSource (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) (c : SpTowerClasses.Chern l E T) :
    SpTowerShriek.D l E T :=
  c.scalar.T.obj (c.reduction.derived.obj
    ((DerivedCategory.singleFunctor (SpTowerClasses.Ab T) 0).obj
      ((SpTowerClasses.constant T).obj (supportedIntegers i))))

/-- Ordinary tensor reduction of the supported integer system.
Source: blueprint Step 3 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedSourceModule (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) (c : SpTowerClasses.Chern l E T) :=
  c.scalar.model.E.obj (c.reduction.ordinary.obj
    ((SpTowerClasses.constant T).obj (supportedIntegers i)))

/-- The supported integer generator from the two actual ordinary tensor units.
Source: blueprint supported unit (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedSourceGenerator (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) (c : SpTowerClasses.Chern l E T) :=
  c.reduction.model.adjunction.unit.app
      ((SpTowerClasses.constant T).obj (supportedIntegers i)) ≫
    c.reduction.forget.F.map (c.scalar.ordinaryAdjunction.unit.app
      (c.reduction.ordinary.obj ((SpTowerClasses.constant T).obj (supportedIntegers i))))

/-- The supported source comparison is the product of the two universal counits.
Source: blueprint Step 3 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedSourceComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) (c : SpTowerClasses.Chern l E T) :
    supportedExtendedSource l E i c ⟶
      (DerivedCategory.singleFunctor _ 0).obj (supportedSourceModule l E i c) :=
  c.scalar.T.map (supportedSingleComparison c.reduction.derived c.reduction.ordinary
    c.reduction.model.epsilon ((SpTowerClasses.constant T).obj (supportedIntegers i))) ≫
    supportedSingleComparison c.scalar.T c.scalar.model.E c.scalar.model.ε
      (c.reduction.ordinary.obj ((SpTowerClasses.constant T).obj (supportedIntegers i)))

/-- The canonical system arrow: scalar extension of the relative pole extension,
followed by the positive Kummer connecting comparison. This is a construction,
not an arbitrary arrow with prescribed finite evaluations.
Source: blueprint Steps 1--5 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedKummerSystemArrow (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (c : SpTowerClasses.Chern l E T) :
    supportedExtendedSource l E i c ⟶ (SpTowerClasses.line l E c)⟦(2 : ℤ)⟧ :=
  c.scalar.T.map
    (c.reduction.derived.map (supportedPoleSystem i hI) ≫ c.rootIso.hom) ≫
    (c.scalar.T.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor (SpTowerClasses.Systems T
        (SpTowerClasses.Rrings l T)) 0).obj c.rootModule) ≫
    (SpTowerClasses.lineComparison l E c)⟦(2 : ℤ)⟧'

/-- The actual supported completed coefficient unit, before placement in degree zero.
Source: blueprint Step 7 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedIntegralModule (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) :=
  (WeilConjectures.CompletedCoefficientPushforward.push.{u, u} i
    (WeilConjectures.CompletedCoefficientPushforward.completedStructure_existsUnique.{u, u}
      i l E).exists.choose).obj
    (SheafOfModules.unit
      (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E D))

/-- The supported integral unit is induced by the actual completed structural ring map.
Source: blueprint supported-one normalization
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedIntegralUnit (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T) ⟶
      supportedIntegralModule l E i := by
  let φ := (CompletedCoefficientPushforward.completedStructure_existsUnique.{u, u}
    i l E).exists.choose
  exact
    { val :=
      { app := fun U ↦ ModuleCat.homMk
          ((forget₂ RingCat AddCommGrpCat).map (φ.hom.app U)) (fun r ↦ by
            ext x
            exact ((φ.hom.app U).hom.map_mul r x).symm)
        naturality := fun {_ _} f ↦ by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact ConcreteCategory.congr_hom (φ.hom.naturality f) x } }

/-- The computation map from completed reduction of a module in degree zero to its
ordinary tensor reduction. It is the recorded universal counit, not a chosen iso.
Source: blueprint Step 7 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedCompletedSingleComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T A)
    (M : scalarReductionSource l E T) :=
  supportedSingleComparison
    (spCompletedReduction l E T A R ⋙ (supportedSystemRealization l E b T A).functor)
    (SpTwistedPullback.ordinaryReduction l E b T A R)
    (SpTwistedPullback.reductionCounit l E b T A R) M

/-- Identify a local tensor generator in the section-preserving realization of R.
Source: blueprint quotient-unit formula
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def SupportedReductionGenerator (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T A)
    (M : scalarReductionSource l E T) (m : ℕ) (U : T.ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E T m).obj.obj U) (x : M.val.obj U)
    (y : ((SpTowerShriek.ev l E T m).obj
      ((SpTwistedPullback.ordinaryReduction l E b T A R).obj M)).val.obj U) : Prop :=
  HEq y (spReductionGenerator l E T A R.coefficient R.ordinary R.level
    ((SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        R.coefficient.hom)).obj M) m U a x)

/-- Actual completed supported coefficients in degree zero. The completed ring map
is the unique one inducing the canonical map on every quotient and on constants.
Source: Stacks 0D6E and blueprint Step 7
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedIntegralEndpoint (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) :
    DerivedCategory (WeilConjectures.scalarReductionSource l E T) :=
  (DerivedCategory.singleFunctor _ 0).obj (supportedIntegralModule l E i)

/-- The prescribed completed integral Tate line in degree zero.
Source: blueprint Step 7 and sk-def-sp-tate-twist
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedIntegralTateEndpoint (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) :
    DerivedCategory (WeilConjectures.scalarReductionSource l E T) :=
  (DerivedCategory.singleFunctor _ 0).obj (Scheme.purTwistIntegralModule T l E)

/-- The canonical supported integral generator, using the exact site comparisons.
Source: Stacks 0A45, blueprint Step 3
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedIntegerUnit {T D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    ((constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶ supportedIntegers i :=
  (SpTowerClasses.integerComparison T).inv ≫
    (comparisonUpperStar AddCommGrpCat.{u + 1} T).map (Etale.supportedIntegralUnit i) ≫
      (cartierIntegralSourceIso i).hom

/-- The supported coefficient unit induced by the same two normalized scalar functors.
Source: blueprint Steps 3 and 8 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedExtendedUnit (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (c : SpTowerClasses.Chern l E T) :
    SpTowerClasses.unit T (SpTowerClasses.Arings l E T) ⟶
      supportedExtendedSource l E i c :=
  c.scalarUnit.inv ≫ c.scalar.T.map
    (c.unitIso.inv ≫ c.reduction.derived.map
      ((DerivedCategory.singleFunctor (SpTowerClasses.Ab T) 0).map
        ((SpTowerClasses.constant T).map (supportedIntegerUnit i))))

/-- The concrete endpoint comparisons, normalization, completeness and finite Cartier
boundary equations for the constructed whole-system arrow. All fields are conclusions.
The sequence-site model is identified with the recorded strict category by the
section-preserving derived equivalence.
Source: blueprint Steps 1--7 (blueprint: lem-pur-supported-kummer-coherent-system). -/
structure SupportedKummerCoherentSystem (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T D : Scheme.{u}) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (b : SpTowerShriek.Base l E)
    (A : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T A) where
  chern : SpTowerClasses.Chern l E T
  chern_normalized : chern.Normalized l E
  source_evaluation : ∀ m : ℕ,
    (SpTowerShriek.Ev l E T m).obj (supportedExtendedSource l E i chern) ≅
      supportedFiniteEndpoint l E T D i m
  target_evaluation : ∀ m : ℕ,
    (SpTowerShriek.Ev l E T m).obj (SpTowerClasses.line l E chern) ≅
      tateFiniteEndpoint l E T m
  source_ordinary : ∀ m : ℕ,
    (SpTowerShriek.ev l E T m).obj (supportedSourceModule l E i chern) ≅
      (finiteCoefficientIntrinsicRealization T (supportedFiniteRing l E m)).obj
        ((lowerStar (ModuleCat.{u + 1} (supportedFiniteRingLift l E m)) i).obj
          (geoCartierConstant (supportedFiniteRingLift l E m) D))
  source_sections : ∀ (m : ℕ) (U : T.ProEtᵒᵖ)
    (z : (supportedIntegers i).obj.obj U)
    (y : ((SpTowerShriek.ev l E T m).obj (supportedSourceModule l E i chern)).val.obj U),
    HEq y (((supportedSourceGenerator l E i chern).app (op m)).hom.app U z) →
    (source_ordinary m).hom.val.app U y =
      supportedIntrinsicSection T (supportedFiniteRing l E m) _ U
        ((cartierProIntegralGenerator (supportedFiniteRingLift l E m) i).hom.app U z)
  source_evaluation_normalized : ∀ m : ℕ, (source_evaluation m).hom =
    (SpTowerShriek.Ev l E T m).map (supportedSourceComparison l E i chern) ≫
      ((SpTowerShriek.ev l E T m).mapDerivedCategorySingleFunctor 0).hom.app
        (supportedSourceModule l E i chern) ≫
      (DerivedCategory.singleFunctor _ 0).map (source_ordinary m).hom
  target_ordinary : ∀ m : ℕ,
    (SpTowerShriek.ev l E T m).obj (SpTowerClasses.lineModule l E chern) ≅
      (finiteCoefficientIntrinsicRealization T (supportedFiniteRing l E m)).obj
        (geoCartierLine (supportedFiniteRingLift l E m) (l ^ (m + 1))
          (supportedFiniteAnn l E m) T)
  target_sections : ∀ (m : ℕ) (hT : IsUnit ((l ^ (m + 1) : ℕ) : Γ(T, ⊤)))
    (U : T.ProEtᵒᵖ) (a : (SpTowerShriek.B l E T m).obj.obj U)
    (x : chern.rootModule.val.obj (op (m, U.unop)))
    (x' : ((chern.reduction.forget.F.obj chern.rootModule).obj (op m)).obj.obj U)
    (y : ((SpTowerShriek.ev l E T m).obj (SpTowerClasses.lineModule l E chern)).val.obj U),
    HEq x x' →
    HEq y (a • SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
      (SpTowerClasses.coefficientSystemMap l E T) chern.scalar chern.rootModule
        (op (m, U.unop)) x) →
    (target_ordinary m).hom.val.app U y = a •
      supportedIntrinsicSection T (supportedFiniteRing l E m) _ U
        ((cartierProRootMap (supportedFiniteRingLift l E m) (l ^ (m + 1))
          (supportedFiniteAnn l E m) T (pow_pos (Fact.out : l.Prime).pos _) hT).hom.app U
            ((chern.rootForget.hom.app (op m)).hom.app U x'))
  target_evaluation_normalized : ∀ m : ℕ, (target_evaluation m).hom =
    ((SpTowerShriek.ev l E T m).mapDerivedCategorySingleFunctor 0).hom.app
      (SpTowerClasses.lineModule l E chern) ≫
        (DerivedCategory.singleFunctor _ 0).map (target_ordinary m).hom
  evaluation_is_cartier_kummer : ∀ (m : ℕ)
    (hT : IsUnit ((l ^ (m + 1) : ℕ) : Γ(T, ⊤))),
    ∃ c : GeoCartierClass (supportedFiniteRingLift l E m)
      (l ^ (m + 1)) (supportedFiniteAnn l E m) i,
      CartierProReductionSpec (supportedFiniteRingLift l E m)
        (l ^ (m + 1)) (supportedFiniteAnn l E m) i hI
        (pow_pos (Fact.out : l.Prime).pos _) hT c ∧
      (source_evaluation m).hom ≫ finiteSupportedCartierArrow l E T D i hI m hT c =
        (SpTowerShriek.Ev l E T m).map (supportedKummerSystemArrow l E i hI chern) ≫
          ((SpTowerShriek.Ev l E T m).commShiftIso (2 : ℤ)).hom.app
            (SpTowerClasses.line l E chern) ≫ ((target_evaluation m).hom⟦(2 : ℤ)⟧')
  endpoints_normalized :
    spNormalizedConstructibleTorTowers l E T A
      ((supportedSystemRealization l E b T A).inverse.obj
        (supportedExtendedSource l E i chern)) ∧
    spNormalizedConstructibleTorTowers l E T A
      ((supportedSystemRealization l E b T A).inverse.obj
        (SpTowerClasses.line l E chern))
  normalization : SpNormalizedEquivalence l E T A R
  source_complete : WeilConjectures.IntegralOnSlice.IsComplete l E T none
    (supportedIntegralEndpoint l E i)
  target_complete : WeilConjectures.IntegralOnSlice.IsComplete l E T none
    (supportedIntegralTateEndpoint l E T)
  source_unit_isIso : IsIso (normalization.adjunction.unit.app
    (supportedIntegralEndpoint l E i))
  target_unit_isIso : IsIso (normalization.adjunction.unit.app
    (supportedIntegralTateEndpoint l E T))
  source_reduction :
    (supportedSystemRealization l E b T A).functor.obj
      ((spCompletedReduction l E T A R).obj (supportedIntegralEndpoint l E i)) ≅
        supportedExtendedSource l E i chern
  target_reduction :
    (supportedSystemRealization l E b T A).functor.obj
      ((spCompletedReduction l E T A R).obj (supportedIntegralTateEndpoint l E T)) ≅
        SpTowerClasses.line l E chern

  coefficient_reduction_ordinary :
    (SpTwistedPullback.ordinaryReduction l E b T A R).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)) ≅
        SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T)
  coefficient_reduction_sections : ∀ (m : ℕ) (U : T.ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E T m).obj.obj U)
    (y : ((SpTowerShriek.ev l E T m).obj
      ((SpTwistedPullback.ordinaryReduction l E b T A R).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)))).val.obj U),
    SupportedReductionGenerator l E b T A R _ m U a
      (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) y →
    HEq (((SpTowerShriek.ev l E T m).map coefficient_reduction_ordinary.hom).val.app U y) a
  coefficient_reduction :
    (supportedSystemRealization l E b T A).functor.obj
      ((spCompletedReduction l E T A R).obj ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)))) ≅
          SpTowerClasses.unit T (SpTowerClasses.Arings l E T)
  coefficient_reduction_normalized : coefficient_reduction.hom =
    supportedCompletedSingleComparison l E b T A R _ ≫
      (DerivedCategory.singleFunctor _ 0).map coefficient_reduction_ordinary.hom
  source_reduction_normalized :
    (spCompletedReduction l E T A R ⋙ (supportedSystemRealization l E b T A).functor).map
      ((DerivedCategory.singleFunctor _ 0).map (supportedIntegralUnit l E i)) ≫
        source_reduction.hom = coefficient_reduction.hom ≫ supportedExtendedUnit l E i chern
  target_reduction_ordinary :
    (SpTwistedPullback.ordinaryReduction l E b T A R).obj
      (Scheme.purTwistIntegralModule T l E) ≅ SpTowerClasses.lineModule l E chern
  target_reduction_sections : ∀ (m : ℕ) (U : T.ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E T m).obj.obj U)
    (r : (Scheme.purTwistIntegralConstant T l E).obj.obj U)
    (z : (Scheme.purTwistZlModule T l).val.obj U)
    (y : ((SpTowerShriek.ev l E T m).obj
      ((SpTwistedPullback.ordinaryReduction l E b T A R).obj
        (Scheme.purTwistIntegralModule T l E))).val.obj U),
    SupportedReductionGenerator l E b T A R _ m U a
      (Scheme.purTwistIntegralTensor T l E U r z) y →
    (((SpTowerShriek.ev l E T m).map target_reduction_ordinary.hom ≫
      (SpTowerClasses.lineEvaluation l E chern m).hom).val.app U y) =
      Scheme.tateFiniteTensor T l (SpTowerClasses.FiniteRing l E m) m
        (SpTowerClasses.finiteScalar l E m) U.unop
        (a * (@id ((SpTowerShriek.B l E T m).obj.obj U)
          ((spIntegralEllProjection l E T m).hom.app U
            ((Scheme.purTwistIntegralCompletionMap T l E).hom.app U r))))
        ((limit.π (Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op m)).hom.app
          U z)
  target_reduction_normalized : target_reduction.hom =
    supportedCompletedSingleComparison l E b T A R _ ≫
      (DerivedCategory.singleFunctor _ 0).map target_reduction_ordinary.hom

/-- The relative Cartier Kummer boundary is one normalized morphism of entire strict
coefficient systems, with the canonical complete integral endpoints.
Source: Stacks 03PL, 0A45; latest blueprint rank-one Thom proof, Steps 1--7
(blueprint: lem-pur-supported-kummer-coherent-system).

Proof (deferred): take the unique relative frame-torsor pole extension with the
specified complementary splitting. Apply exact site comparison and the constant
system functor. Normalized Kummer reduction identifies reduction of full units[1]
with the roots[2], by the positive connecting arrow. Extend scalars along the
actual Z/ell-power to valuation-quotient ring-system map. Closed projection and
flatness identify the reduced supported source with i_*B; the root line is locally
free and its scalar comparison is the ordinary tensor comparison. All these are
maps of entire systems. Evaluation is therefore the relative Cartier reduction
specified by CartierProReductionSpec. On a local equation f the complementary
frame is f in the f inverse frame, and the Ext convention gives -partial kappa(f).
Both endpoints have cohomological and Tor interval [0,0], are constructible on the
closed/open stratification, and their quotient-adjoint transitions are invertible.
The completed coefficient unit on D is complete; exact closed pushforward and the
closed projection formula give the supported integral endpoint and its canonical
reduction comparisons. The complete integral Tate line has the prescribed finite
root reductions. The reduction/total-limit adjunction makes both actual unit maps
invertible. Its full faithfulness on complete objects supplies the integral class
and the displayed reduction equation. No regularity of T or flatness of its maps
is used, and the empty Cartier divisor gives the zero supported source.
-/
theorem exists_supportedKummerCoherentSystem
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T D : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    [∀ x : T, Invertible (l : T.residueField x)] :
    ∀ (b : SpTowerShriek.Base l E) (A : SpCoefficientTowersAbelian l E T)
      (R : SpReductionTower l E T A),
      Nonempty (SupportedKummerCoherentSystem l E T D i hI b A R) := by
  sorry

/-- Exact localization of the ordinary, root-normalized Tate-line pullback.
Source: blueprint Steps 8--9 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedLinePullbackIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {b : SpTowerShriek.Base l E} {T T' : Scheme.{u}}
    (h : T' ⟶ T) (g : SpTowerShriek.Geometry l E b h)
    (c : SpTowerClasses.Chern l E T) (c' : SpTowerClasses.Chern l E T')
    (p : SpTowerClasses.LinePullback l E h g c c') :
    (SpTowerShriek.pull l E b g).obj (SpTowerClasses.line l E c) ≅
      SpTowerClasses.line l E c' :=
  (g.pull.mapDerivedCategorySingleFunctor 0).app (SpTowerClasses.lineModule l E c) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso p.iso

/-- A commuting square for a degree-two arrow, in entire derived categories.
Source: blueprint Steps 8--11 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedKummerTransportSquare
    {C : Type a} [Category.{av} C] [HasShift C ℤ]
    {B : Type d} [Category.{dv} B] [HasShift B ℤ]
    (F : C ⥤ B) [F.CommShift ℤ]
    {P Q : C} {P' Q' : B} (f : P ⟶ Q⟦(2 : ℤ)⟧)
    (f' : P' ⟶ Q'⟦(2 : ℤ)⟧) (p : F.obj P ≅ P') (q : F.obj Q ≅ Q') : Prop :=
  F.map f ≫ (F.commShiftIso (2 : ℤ)).hom.app Q ≫ q.hom⟦(2 : ℤ)⟧' = p.hom ≫ f'

/-- Arbitrary Cartier-preserving scheme pullback carries the constructed whole-system
arrow to the constructed arrow. The coefficient and line comparisons are the existing
section-normalized ordinary comparisons; the supported comparison fixes supported one.
Source: blueprint Steps 8--9 (blueprint: lem-pur-supported-kummer-coherent-system).

Proof (deferred): pull back the relative frame torsor and its complementary frame.
The pulled extension has the same pole specification for the new Cartier pair, so
uniqueness gives equality before reduction. Exact inverse image and closed exchange
preserve supported one. The maps on full units commute with all power maps and root
inclusions, hence form a morphism of the short exact Kummer SYSTEMS. Naturality of
the positive connecting roof gives equality of its entire-system arrows. The
normalized derived adjunction transfers this equality to the target comparison.
Apply the canonical derived pullback/scalar associators to the defining formula
for supportedKummerSystemArrow. The supported comparison is fixed by its unit and
the Tate comparison by its root-tensor section formula, giving the displayed square.
No flatness of the base map is used; only the pulled divisor is required Cartier. -/
theorem supportedKummerCoherentSystem_baseChange
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) {T D T' D' : Scheme.{u}}
    [IsNoetherian T] [IsNoetherian T']
    (_hdim : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (_hdim' : ∃ d : ℕ, topologicalKrullDim T' ≤ (d : WithBot ℕ∞))
    [∀ x : T, Invertible (l : T.residueField x)]
    [∀ x : T', Invertible (l : T'.residueField x)]
    (i : D ⟶ T) (i' : D' ⟶ T') [IsClosedImmersion i] [IsClosedImmersion i']
    (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
    (h : T' ⟶ T) (hD : D' ⟶ D) (_sq : IsPullback hD i' i h)
    (c : SpTowerClasses.Chern l E T) (c' : SpTowerClasses.Chern l E T')
    (_hc : c.Normalized l E) (_hc' : c'.Normalized l E)
    (g : SpTowerShriek.Geometry l E b h) :
    ∃ (p : SpTowerClasses.CoefficientPullback l E b h g)
      (q : SpTowerClasses.LinePullback l E h g c c')
      (e : (SpTowerShriek.pull l E b g).obj (supportedExtendedSource l E i c) ≅
        supportedExtendedSource l E i' c'),
      (SpTowerShriek.pull l E b g).map (supportedExtendedUnit l E i c) ≫ e.hom =
        (p.derivedIso l E).hom ≫ supportedExtendedUnit l E i' c' ∧
      supportedKummerTransportSquare (SpTowerShriek.pull l E b g)
        (supportedKummerSystemArrow l E i hI c) (supportedKummerSystemArrow l E i' hI' c')
        e (supportedLinePullbackIso l E h g c c' q) := by
  sorry

/-- Composition of the whole-system squares, with the actual composite functor and
its composite shift comparison. This applies to successive scheme maps, successive
finite field extensions, and mixed changes without reducing the equality to levels.
Source: blueprint Step 10 (blueprint: lem-pur-supported-kummer-coherent-system).

Proof (deferred): apply the second functor to the first square and compose with the
second square. Use naturality of its shift comparison and associativity. The
composite shift comparison is the specified product of the two shift comparisons.
Conjugation by a canonical geometric or tensor compositor then gives the comparison
for the composite; its ordinary normalization fixes supported one and every root
pure tensor, so it is the same endpoint comparison. Identity changes use unitors. -/
theorem supportedKummerCoherentSystem_composition
    {C : Type a} [Category.{av} C] [HasShift C ℤ]
    {B : Type d} [Category.{dv} B] [HasShift B ℤ]
    {H : Type z} [Category.{zv} H] [HasShift H ℤ]
    (F : C ⥤ B) (G : B ⥤ H) [F.CommShift ℤ] [G.CommShift ℤ]
    {P Q : C} {P' Q' : B} {P'' Q'' : H}
    (f : P ⟶ Q⟦(2 : ℤ)⟧) (f' : P' ⟶ Q'⟦(2 : ℤ)⟧)
    (f'' : P'' ⟶ Q''⟦(2 : ℤ)⟧)
    (p : F.obj P ≅ P') (q : F.obj Q ≅ Q')
    (p' : G.obj P' ≅ P'') (q' : G.obj Q' ≅ Q'')
    (_hF : supportedKummerTransportSquare F f f' p q)
    (_hG : supportedKummerTransportSquare G f' f'' p' q') :
    supportedKummerTransportSquare (F ⋙ G) f f''
      (G.mapIso p ≪≫ p') (G.mapIso q ≪≫ q') := by
  sorry

/-- Actual coefficient inclusion on the ringed sequence site, at every quotient.
Source: blueprint Step 10 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedFieldSystemMap (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (A' : SpCoefficientTowersAbelian l F T)
    (R : SpReductionTower l E T A) (R' : SpReductionTower l F T A')
    (k : FieldScalar.Coefficients l E F ι T A A' R R') :=
  SemilinearSections.systemMap.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
    (SpTowerShriek.B l F T) (SpTowerShriek.tau l F T)
    (fun n ↦ k.tower.app (op n))
    (fun n ↦ (k.tower.naturality (homOfLE (Nat.le_succ n)).op).symm)

/-- The unital map between coefficient units under the actual scalar restriction.
Source: blueprint quotient-unit normalization
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedFieldUnitMap (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (A' : SpCoefficientTowersAbelian l F T)
    (R : SpReductionTower l E T A) (R' : SpReductionTower l F T A')
    (k : FieldScalar.Coefficients l E F ι T A A' R R') :
    SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T) ⟶
      (SemilinearSections.res.{u + 1, u, u + 1}
        (supportedFieldSystemMap l E F ι T A A' R R' k)).obj
          (SpTowerClasses.coefficient T (SpTowerClasses.Arings l F T)) := by
  let φ := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (supportedFieldSystemMap l E F ι T A A' R R' k)
  exact
    { val :=
      { app := fun U ↦ ModuleCat.homMk
          ((forget₂ RingCat AddCommGrpCat).map (φ.hom.app U)) (fun r ↦ by
            ext x
            exact ((φ.hom.app U).hom.map_mul r x).symm)
        naturality := fun {_ _} g ↦ by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact ConcreteCategory.congr_hom (φ.hom.naturality g) x } }

/-- The scalar comparison uses the canonical shift structure of its normalized
K-flat scalar model. Source: blueprint Step 10
(blueprint: lem-pur-supported-kummer-coherent-system). -/
instance supportedFieldScalarShift (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (T : Scheme.{u})
    (A : SpCoefficientTowersAbelian l E T) (A' : SpCoefficientTowersAbelian l F T)
    (R : SpReductionTower l E T A) (R' : SpReductionTower l F T A')
    (k : FieldScalar.Coefficients l E F ι T A A' R R')
    (scalar : SemilinearSections.ScalarData.{u + 1, u, u + 1}
      (supportedFieldSystemMap l E F ι T A A' R R' k)) : scalar.T.CommShift ℤ :=
  SheafOfModules.sheafScalarModelCommShift
    (supportedFieldSystemMap l E F ι T A A' R R' k) scalar.model

/-- Canonical scalar associator and its supported and root components. The source
component is literally the associator at the reduced supported integral module;
the target component is its root component followed by the ordinary line comparison.
Source: blueprint Step 10 (blueprint: lem-pur-supported-kummer-coherent-system). -/
structure SupportedKummerScalarComparisons (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) {T D : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (A : SpCoefficientTowersAbelian l E T) (A' : SpCoefficientTowersAbelian l F T)
    (R : SpReductionTower l E T A) (R' : SpReductionTower l F T A')
    (k : FieldScalar.Coefficients l E F ι T A A' R R')
    (c : SpTowerClasses.Chern l E T) (c' : SpTowerClasses.Chern l F T) where
  scalar : SemilinearSections.ScalarData.{u + 1, u, u + 1}
    (supportedFieldSystemMap l E F ι T A A' R R' k)
  common_reduction : c.reduction = c'.reduction
  common_root : c.rootModule = c'.rootModule
  common_boundary : HEq c.rootIso c'.rootIso
  unitIso : scalar.T.obj (SpTowerClasses.unit T (SpTowerClasses.Arings l E T)) ≅
    SpTowerClasses.unit T (SpTowerClasses.Arings l F T)
  unit_normalized : SpTowerClasses.unitNormalization scalar.T
    (SemilinearSections.res.{u + 1, u, u + 1}
      (supportedFieldSystemMap l E F ι T A A' R R' k))
    scalar.adjunction unitIso (supportedFieldUnitMap l E F ι T A A' R R' k)
  associator : c.scalar.T ⋙ scalar.T ≅ c'.scalar.T
  associator_unit : scalar.T.map c.scalarUnit.hom ≫ unitIso.hom =
    associator.hom.app (SpTowerClasses.unit T (SpTowerClasses.Rrings l T)) ≫
      c'.scalarUnit.hom
  sourceIso : scalar.T.obj (supportedExtendedSource l E i c) ≅
    supportedExtendedSource l F i c'
  source_normalized : sourceIso.hom =
    associator.hom.app
      (c.reduction.derived.obj ((DerivedCategory.singleFunctor (SpTowerClasses.Ab T) 0).obj
        ((SpTowerClasses.constant T).obj (supportedIntegers i)))) ≫
      c'.scalar.T.map (eqToHom (congrArg
        (fun r : SpTowerClasses.Reduction T (SpTowerClasses.Rrings l T) ↦
          r.derived.obj ((DerivedCategory.singleFunctor (SpTowerClasses.Ab T) 0).obj
            ((SpTowerClasses.constant T).obj (supportedIntegers i)))) common_reduction))
  targetIso : scalar.T.obj (SpTowerClasses.line l E c) ≅ SpTowerClasses.line l F c'
  target_normalized : scalar.T.map (SpTowerClasses.lineComparison l E c) ≫ targetIso.hom =
    associator.hom.app
      ((DerivedCategory.singleFunctor (SpTowerClasses.Systems T
        (SpTowerClasses.Rrings l T)) 0).obj c.rootModule) ≫
      c'.scalar.T.map ((DerivedCategory.singleFunctor _ 0).map (eqToHom common_root)) ≫
        SpTowerClasses.lineComparison l F c'
  associator_shift : NatTrans.CommShift associator.hom ℤ
  arrow_square : supportedKummerTransportSquare scalar.T
    (supportedKummerSystemArrow l E i hI c) (supportedKummerSystemArrow l F i hI c')
    sourceIso targetIso

/-- Finite coefficient extension preserves the canonical supported system arrow under
its normalized derived tensor endpoint comparisons. The extension field and every
quotient map are the actual specified inclusion, including ramified extensions.
Source: blueprint Step 10 (blueprint: lem-pur-supported-kummer-coherent-system).

Proof (deferred): use the same integral pole class, the same Z/ell-power reduction,
and the same positive Kummer boundary. Extend the latter construction to F using the
actual quotient inclusions of valuation rings. Composition of derived scalar extension
is the canonical tensor associator, determined by multiplication on pure tensors and
its derived adjunction. The unit comparison sends one tensor a to a. Its component on
the supported integral reduction is sourceIso, and its root component, followed by the
ordinary line comparisons, is targetIso. Naturality of the associator applied to the
reduced pole boundary is exactly arrow_square. The canonical integral endpoint
comparisons, completeness and uniform bounds over F are obtained by the same
construction as over E. Thus no quotient-flatness hypothesis is imposed and the
positive root-boundary normalization is retained. -/
theorem supportedKummerCoherentSystem_scalarExtension
    (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (T D : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    [∀ x : T, Invertible (l : T.residueField x)]
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (b : SpTowerShriek.Base l E) (A : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T A)
    (s : SupportedKummerCoherentSystem l E T D i hI b A R) :
    ∃ (b' : SpTowerShriek.Base l F) (A' : SpCoefficientTowersAbelian l F T)
      (R' : SpReductionTower l F T A')
      (s' : SupportedKummerCoherentSystem l F T D i hI b' A' R')
      (k : FieldScalar.Coefficients l E F ι T A A' R R'),
      Nonempty (SupportedKummerScalarComparisons l E F ι i hI A A' R R' k
        s.chern s'.chern) := by
  sorry

/-- Supported finite coefficients for any actual quotient ring.
Source: Stacks 0A45; blueprint Step 11
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedQuotientEndpoint (T D : Scheme.{u}) (i : D ⟶ T)
    (B : Type u) [CommRing B] [Finite B] : Scheme.proEtaleDerivedCategory T B :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((finiteCoefficientIntrinsicRealization T B).obj
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) i).obj
        (geoCartierConstant (ULift.{u + 1} B) D)))

/-- The finite root-tensor Tate endpoint at an arbitrary quotient level.
Source: Stacks 03PL; blueprint Step 11
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedQuotientTateEndpoint (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (N : ℕ) (hB : (N : ULift.{u + 1} B) = 0) : Scheme.proEtaleDerivedCategory T B :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((finiteCoefficientIntrinsicRealization T B).obj (geoCartierLine (ULift.{u + 1} B) N hB T))

/-- The canonical finite derived realization of a supported Cartier Ext class.
Source: Stacks 03PL, 0A45; blueprint Step 11
(blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedQuotientCartierArrow (T D : Scheme.{u}) (i : D ⟶ T)
    (B : Type u) [CommRing B] [Finite B] (N : ℕ) (hB : (N : ULift.{u + 1} B) = 0)
    (c : GeoCartierClass (ULift.{u + 1} B) N hB i) :
    supportedQuotientEndpoint T D i B ⟶ (supportedQuotientTateEndpoint T B N hB)⟦(2 : ℤ)⟧ :=
  SpTowerClasses.mapSingleArrow (finiteCoefficientIntrinsicRealization T B) (2 : ℤ) c.hom

/-- The positive uniformizer quotient, including levels between ell-power levels.
Source: blueprint Step 11 (blueprint: lem-pur-supported-kummer-coherent-system). -/
abbrev supportedUniformizerRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  Padic.coefficientExtensionRing l E (n + 1)

/-- Finiteness of the actual positive uniformizer quotient.
Source: the coefficient DVR theorem; blueprint Step 11
(blueprint: lem-pur-supported-kummer-coherent-system). -/
instance supportedUniformizerRing_finite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (supportedUniformizerRing l E n) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- The supported coefficient-unit map over an arbitrary actual finite quotient.
Source: blueprint Step 11 (blueprint: lem-pur-supported-kummer-coherent-system). -/
def supportedQuotientUnit {T D : Scheme.{u}} (i : D ⟶ T)
    (B : Type u) [CommRing B] :
    geoCartierConstant (ULift.{u + 1} B) T ⟶
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) i).obj
        (geoCartierConstant (ULift.{u + 1} B) D) :=
  Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} (ULift.{u + 1} B))
    (ModuleCat.of (ULift.{u + 1} B) (ULift.{u + 1} B))

/-- Uniformizer reduction of the completed supported endpoint in any supplied
representative-normalized strict reduction model. No nonunique calculus is selected.
Source: blueprint Step 11 (blueprint: lem-pur-supported-kummer-coherent-system). -/
abbrev supportedUniformizerSource (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) (native : IntegralStrictReductionModel l E T) :=
  native.reduction.obj (supportedIntegralEndpoint l E i)

/-- Uniformizer reduction of the integral Tate line in the same supplied model.
Source: blueprint Step 11 (blueprint: lem-pur-supported-kummer-coherent-system). -/
abbrev supportedUniformizerTarget (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (native : IntegralStrictReductionModel l E T) :=
  native.reduction.obj (supportedIntegralTateEndpoint l E T)

/-- Canonical evaluation at every uniformizer quotient. The ordinary source is fixed
by the supported unit and the target by all root tensors. Their derived maps are
literally the universal counit comparisons. Source: blueprint Step 11
(blueprint: lem-pur-supported-kummer-coherent-system). -/
structure SupportedKummerUniformizerLevel (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (native : IntegralStrictReductionModel l E T)
    (arrow : supportedUniformizerSource l E i native ⟶
      (supportedUniformizerTarget l E T native)⟦(2 : ℤ)⟧) (n : ℕ) where
  r : ℕ
  hB : ((l ^ (r + 1) : ℕ) : ULift.{u + 1} (supportedUniformizerRing l E n)) = 0
  hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤))
  unit : (coefficientSequenceEvaluation l E T n).obj (native.ordinary.obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T))) ≅
    (finiteCoefficientIntrinsicRealization T (supportedUniformizerRing l E n)).obj
      (geoCartierConstant (ULift.{u + 1} (supportedUniformizerRing l E n)) T)
  unit_sections : ∀ (U : T.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E T n).obj.obj U),
    unit.hom.val.app U (((native.level n).inv.app _).val.app U
      (unrestrictedIntegralTensorSection l E T n
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T)) U a
          (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U))) =
      a • supportedIntrinsicSection T (supportedUniformizerRing l E n) _ U
        ((toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
          (ModuleCat.of (ULift.{u + 1} (supportedUniformizerRing l E n))
            (ULift.{u + 1} (supportedUniformizerRing l E n))))).app U
            (1 : ULift.{u + 1} (supportedUniformizerRing l E n)))
  source : (coefficientSequenceEvaluation l E T n).obj
      (native.ordinary.obj (supportedIntegralModule l E i)) ≅
    (finiteCoefficientIntrinsicRealization T (supportedUniformizerRing l E n)).obj
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (supportedUniformizerRing l E n))) i).obj
        (geoCartierConstant (ULift.{u + 1} (supportedUniformizerRing l E n)) D))
  source_unit : (coefficientSequenceEvaluation l E T n).map
      (native.ordinary.map (supportedIntegralUnit l E i)) ≫ source.hom =
    unit.hom ≫ (finiteCoefficientIntrinsicRealization T (supportedUniformizerRing l E n)).map
      (supportedQuotientUnit i (supportedUniformizerRing l E n))
  target : (coefficientSequenceEvaluation l E T n).obj
      (native.ordinary.obj (Scheme.purTwistIntegralModule T l E)) ≅
    (finiteCoefficientIntrinsicRealization T (supportedUniformizerRing l E n)).obj
      (geoCartierLine (ULift.{u + 1} (supportedUniformizerRing l E n)) (l ^ (r + 1)) hB T)
  target_roots : ∀ (U : T.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E T n).obj.obj U)
    (b : (Scheme.purTwistIntegralConstant T l E).obj.obj U)
    (z : (Scheme.purTwistZlModule T l).val.obj U),
    target.hom.val.app U (((native.level n).inv.app _).val.app U
      (unrestrictedIntegralTensorSection l E T n (Scheme.purTwistIntegralModule T l E) U a
        (Scheme.purTwistIntegralTensor T l E U b z))) =
      (a * (Scheme.purTwistIntegralQuotient T l E n).hom.app U b) •
        supportedIntrinsicSection T (supportedUniformizerRing l E n) _ U
          ((cartierProRootMap (ULift.{u + 1} (supportedUniformizerRing l E n))
            (l ^ (r + 1)) hB T (pow_pos (Fact.out : l.Prime).pos _) hT).hom.app U
              ((limit.π (Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime))
                (op r)).hom.app U z))
  sourceIso : (coefficientSequenceDerivedEvaluation l E T n).obj
      (supportedUniformizerSource l E i native) ≅
    supportedQuotientEndpoint T D i (supportedUniformizerRing l E n)
  source_normalized : sourceIso.hom =
    (coefficientSequenceDerivedEvaluation l E T n).map
      (supportedSingleComparison native.reduction native.ordinary native.counit
        (supportedIntegralModule l E i)) ≫
    ((coefficientSequenceEvaluation l E T n).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map source.hom
  targetIso : (coefficientSequenceDerivedEvaluation l E T n).obj
      (supportedUniformizerTarget l E T native) ≅
    supportedQuotientTateEndpoint T (supportedUniformizerRing l E n) (l ^ (r + 1)) hB
  target_normalized : targetIso.hom =
    (coefficientSequenceDerivedEvaluation l E T n).map
      (supportedSingleComparison native.reduction native.ordinary native.counit
        (Scheme.purTwistIntegralModule T l E)) ≫
    ((coefficientSequenceEvaluation l E T n).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
    (DerivedCategory.singleFunctor _ 0).map target.hom
  cartier : GeoCartierClass (ULift.{u + 1} (supportedUniformizerRing l E n))
    (l ^ (r + 1)) hB i
  cartier_normalized : CartierProReductionSpec
    (ULift.{u + 1} (supportedUniformizerRing l E n)) (l ^ (r + 1)) hB i hI
      (pow_pos (Fact.out : l.Prime).pos _) hT cartier
  evaluation : supportedKummerTransportSquare (coefficientSequenceDerivedEvaluation l E T n)
    arrow (supportedQuotientCartierArrow T D i (supportedUniformizerRing l E n)
      (l ^ (r + 1)) hB cartier) sourceIso targetIso

/-- Cofinal comparison for this supported system in any normalized native model.
The ordinary comparison is fixed on quotient units and the derived comparison on
resolving complexes. It does not identify native.reduction with a nonunique choice.
Source: blueprint Step 11 (blueprint: lem-pur-supported-kummer-coherent-system). -/
structure SupportedKummerUniformizerComparisons
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (b : SpTowerShriek.Base l E) (A : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T A)
    (s : SupportedKummerCoherentSystem l E T D i hI b A R)
    (native : IntegralStrictReductionModel l E T) where
  cofinal : SpTwistedPullback.CofinalModel l E b T
  ordinary : native.ordinary ⋙ cofinal.ordinary ≅
    SpTwistedPullback.ordinaryReduction l E b T A R
  quotient_units : ∀ (M : scalarReductionSource l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : M.val.obj U)
    (z : ((native.ordinary ⋙ cofinal.ordinary).obj M).val.obj (op (n, U.unop))),
    HEq z (((native.augmentation.app M).app
      (op (b.ramification * (n + 1) - 1))).val.app U x) →
    HEq ((ordinary.hom.app M).val.app (op (n, U.unop)) z)
      (spReductionGenerator l E T A R.coefficient R.ordinary R.level
        ((SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            R.coefficient.hom)).obj M) n U 1 x)
  derived : native.reduction ⋙ cofinal.ordinary.mapDerivedCategory ≅
    spCompletedReduction l E T A R ⋙ (supportedSystemRealization l E b T A).functor
  representative : ∀ P : CochainComplex (scalarReductionSource l E T) ℤ,
    integralOperationsGoodComplex l E T P →
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      (SpTwistedPullback.reductionCounit l E b T A R).app P =
    cofinal.ordinary.mapDerivedCategory.map (native.counit.app P) ≫
      cofinal.ordinary.mapDerivedCategoryFactors.hom.app
        ((native.ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)
  arrow : supportedUniformizerSource l E i native ⟶
    (supportedUniformizerTarget l E T native)⟦(2 : ℤ)⟧
  sourceIso : cofinal.ordinary.mapDerivedCategory.obj
      (supportedUniformizerSource l E i native) ≅ supportedExtendedSource l E i s.chern
  targetIso : cofinal.ordinary.mapDerivedCategory.obj
      (supportedUniformizerTarget l E T native) ≅ SpTowerClasses.line l E s.chern
  source_normalized : sourceIso =
    derived.app (supportedIntegralEndpoint l E i) ≪≫ s.source_reduction
  target_normalized : targetIso =
    derived.app (supportedIntegralTateEndpoint l E T) ≪≫ s.target_reduction
  arrow_square : supportedKummerTransportSquare cofinal.ordinary.mapDerivedCategory
    arrow (supportedKummerSystemArrow l E i hI s.chern) sourceIso targetIso
  evaluation : ∀ n : ℕ, Nonempty (SupportedKummerUniformizerLevel l E i hI native arrow n)

/-- Replacing ell powers by all uniformizer powers gives the same canonical arrow
and the same relative Cartier evaluations, including every intermediate quotient.
Source: blueprint Step 11 (blueprint: lem-pur-supported-kummer-coherent-system).

Proof (deferred): write ell as a unit times pi to the positive ramification index e.
The canonical quotient congruences identify the ell levels with uniformizer levels
e(n+1). Construct the same reduced relative boundary on the uniformizer ringed
sequence site and use the normalized ceiling-index derived left extension from
the cofinal subsequence. At every intermediate level, extension is the derived
quotient tensor; the source is flat and the root line locally free, so the
ordinary tensor endpoints and their quotient-unit comparisons compute it. Every
uniformizer quotient is killed by some positive ell power. Relative Cartier
reduction at that exponent supplies the finite evaluation in the statement;
exponent-independence makes it independent of that exponent. The selected-level
comparison has the prescribed resolving-complex counit and quotient-unit formula,
so it gives the entire-system square with the original constructed arrow, rather
than just equality in separate finite Hom groups. Its transition formula includes
repeated ceiling indices and its composition mate is the canonical tensor associator.
-/
theorem supportedKummerCoherentSystem_uniformizer
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T D : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    [∀ x : T, Invertible (l : T.residueField x)]
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (b : SpTowerShriek.Base l E) (A : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T A)
    (s : SupportedKummerCoherentSystem l E T D i hI b A R)
    (native : IntegralStrictReductionModel l E T) :
    Nonempty (SupportedKummerUniformizerComparisons l E i hI b A R s native) := by
  sorry

end AlgebraicGeometry.ProEtale
