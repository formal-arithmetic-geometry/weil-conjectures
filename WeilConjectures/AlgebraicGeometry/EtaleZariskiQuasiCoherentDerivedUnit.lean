/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Cohomology.Leray
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison

import WeilConjectures.AlgebraicGeometry.FlatEtaleZariskiRingedPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackOpenRestriction
import WeilConjectures.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentificationNaturality
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.Sites.CohomologyOverObjectLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
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
import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence

/-!
# The bounded-below quasi-coherent étale/Zariski equivalence

Source: Stacks Project, Descent, Tag 03DW; Cohomology on Sites, Tags 07A8 and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit).

The ordinary module functors are the existing tensor extension and open restriction.
The comparison of derived sections is the derived adjunction unit followed by the
unit-normalized derived-composition isomorphism. Pullback uses the transpose of the
specified module map, followed by the derived unit on a single object; it does not
require exactness of pullback along the scheme morphism.

## Main definitions and statement

* `EtaleZariskiDerivedContext` packages the canonical functors and their resolution data.
* Its `comparison` and `moduleComparison` are the canonical derived-unit comparisons.
* `EtaleZariskiSectionPullback` specifies canonical coefficient pullback on both sites.
* `etale_zariski_quasiCoherent_derived_unit` states all clauses of the node.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u a b v w dA dB dG

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The standard localization for the category of additive section groups.
Source: Stacks, Derived Categories, Tag 05RU
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
instance etaleZariskiSectionGroupsDerived : HasDerivedCategory.{u + 1} AddCommGrpCat.{u} :=
  HasDerivedCategory.standard _

/-- Canonical small-site change of topology with its exactness and resolution proofs.
The context chooses no module functor: both are the existing open restriction and
its canonical tensor left adjoint. The associated-sheaf identification retains the
scalar action, every module map, and the adjunction unit on every Zariski open.
Source: Stacks, Descent, Tags 03FH, 03DW and 0GNA
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
structure EtaleZariskiDerivedContext (T : Scheme.{u}) where
  ordinary : ZariskiEtaleModuleContext T
  [zariskiDerived : HasDerivedCategory.{u + 1} T.Modules]
  [etaleDerived : HasDerivedCategory.{u + 1} (SmallEtaleModules T)]
  [zariskiInjectives : EnoughInjectives T.Modules]
  [etaleInjectives : EnoughInjectives (SmallEtaleModules T)]
  [extensionAdditive : ordinary.extension.Additive]
  [restrictionAdditive : ordinary.restriction.Additive]
  [extensionLimits : PreservesFiniteLimits ordinary.extension]
  [extensionColimits : PreservesFiniteColimits ordinary.extension]
  [restrictionLimits : PreservesFiniteLimits ordinary.restriction]
  [restrictionInjectives : ordinary.restriction.PreservesInjectiveObjects]
  associated : ∀ (M : T.Modules) [M.IsQuasicoherent],
    (SheafOfModules.toSheaf (smallEtaleModuleRing T)).obj (ordinary.extension.obj M) ≅
      etaleTensorSectionsSheaf M
  associated_linear : ∀ (M : T.Modules) [M.IsQuasicoherent] (V : T.Etale)
      (r : Γ(V.left, ⊤)) (m : (ordinary.extension.obj M).val.obj (op V)),
    (associated M).hom.hom.app (op V) (r • m) =
      r • @id (Γ((tensorPullback V.hom).obj M, ⊤))
        ((associated M).hom.hom.app (op V) m)
  associated_natural : ∀ (M N : T.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
      (f : M ⟶ N) (V : T.Etale),
    ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
      (ordinary.extension.map f)).hom.app (op V) ≫ (associated N).hom.hom.app (op V) =
        (associated M).hom.hom.app (op V) ≫ ((tensorPullback V.hom).map f).app ⊤
  associated_unit : ∀ (M : T.Modules) [M.IsQuasicoherent] (W : T.Opens),
    (ordinary.adjunction.unit.app M).app W ≫
      (associated M).hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
        (tensorOpenSectionIso T M W).hom = 𝟙 _

/-- Sections on the small étale site, evaluated at the terminal open subscheme.
This is ordinary étale global sections, since open restriction evaluated at T is evaluation
at the identity étale T-scheme. No coefficient or section group is changed.
Source: Stacks, Descent, Tag 03DW
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.sections {T : Scheme.{u}} (c : EtaleZariskiDerivedContext T) :
    SmallEtaleModules T ⥤ AddCommGrpCat.{u} :=
  c.ordinary.restriction ⋙ globalSectionsFunctor T

/-- Additivity inherited from restriction and evaluation.
Source: Stacks, Descent, Tag 03DW
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
instance EtaleZariskiDerivedContext.sectionsAdditive {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) : c.sections.Additive :=
  letI := c.restrictionAdditive
  inferInstanceAs (c.ordinary.restriction ⋙ globalSectionsFunctor T).Additive

/-- Left exactness inherited from restriction and evaluation.
Source: Stacks, Descent, Tag 03DW
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
instance EtaleZariskiDerivedContext.sectionsLimits {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) : PreservesFiniteLimits c.sections :=
  letI := c.restrictionLimits
  comp_preservesFiniteLimits c.ordinary.restriction (globalSectionsFunctor T)


/-- The ordinary bounded-below Zariski module derived category.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
abbrev EtaleZariskiDerivedContext.zariskiCategory {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) : Type _ :=
  letI := c.zariskiDerived
  DerivedCategory.Plus T.Modules

/-- The ordinary bounded-below small étale module derived category.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
abbrev EtaleZariskiDerivedContext.etaleCategory {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) : Type _ :=
  letI := c.etaleDerived
  DerivedCategory.Plus (SmallEtaleModules T)

/-- The exact termwise canonical change-of-topology pullback.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.pullback {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) : c.zariskiCategory ⥤ c.etaleCategory :=
  letI := c.zariskiDerived
  letI := c.etaleDerived
  letI := c.extensionAdditive
  letI := c.extensionLimits
  letI := c.extensionColimits
  c.ordinary.extension.mapDerivedCategoryPlus

/-- The canonical right-derived open-restriction functor.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.pushforward {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) : c.etaleCategory ⥤ c.zariskiCategory :=
  letI := c.zariskiDerived
  letI := c.etaleDerived
  letI := c.etaleInjectives
  letI := c.restrictionAdditive
  c.ordinary.restriction.rightDerivedFunctorPlus

/-- The canonical derived adjunction with its specified unit and counit.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.derivedAdjunction {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) : c.pullback ⊣ c.pushforward :=
  letI := c.zariskiDerived
  letI := c.etaleDerived
  letI := c.etaleInjectives
  letI := c.extensionAdditive
  letI := c.restrictionAdditive
  letI := c.extensionLimits
  letI := c.extensionColimits
  c.ordinary.adjunction.derivedPlus

/-- Ordinary bounded-below derived Zariski global sections.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.zariskiSections {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) :
    c.zariskiCategory ⥤ DerivedCategory.Plus AddCommGrpCat.{u} :=
  letI := c.zariskiDerived
  letI := c.zariskiInjectives
  (globalSectionsFunctor T).rightDerivedFunctorPlus

/-- Ordinary bounded-below derived étale global sections.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.etaleSections {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) :
    c.etaleCategory ⥤ DerivedCategory.Plus AddCommGrpCat.{u} :=
  letI := c.etaleDerived
  letI := c.etaleInjectives
  c.sections.rightDerivedFunctorPlus

/-- Place a Zariski module in degree zero.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.zariskiSingle {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) (M : T.Modules) : c.zariskiCategory :=
  letI := c.zariskiDerived
  (DerivedCategory.Plus.singleFunctor T.Modules 0).obj M

/-- Place an étale module in degree zero.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.etaleSingle {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) (L : SmallEtaleModules T) : c.etaleCategory :=
  letI := c.etaleDerived
  (DerivedCategory.Plus.singleFunctor (SmallEtaleModules T) 0).obj L

/-- Place a Zariski module map in degree zero.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.zariskiSingleMap {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) {M N : T.Modules} (f : M ⟶ N) :
    c.zariskiSingle M ⟶ c.zariskiSingle N :=
  letI := c.zariskiDerived
  (DerivedCategory.Plus.singleFunctor T.Modules 0).map f

/-- Place an étale module map in degree zero.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.etaleSingleMap {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) {M N : SmallEtaleModules T} (f : M ⟶ N) :
    c.etaleSingle M ⟶ c.etaleSingle N :=
  letI := c.etaleDerived
  (DerivedCategory.Plus.singleFunctor (SmallEtaleModules T) 0).map f

/-- Acyclicity for ordinary Zariski global sections.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.zariskiSectionsAcyclic {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) (M : T.Modules) : Prop :=
  letI := c.zariskiInjectives
  (globalSectionsFunctor T).rightAcyclic M

/-- Acyclicity for ordinary étale global sections.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tags 0D6E and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.etaleSectionsAcyclic {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) (M : SmallEtaleModules T) : Prop :=
  letI := c.etaleInjectives
  c.sections.rightAcyclic M

/-- The Zariski full-subcategory predicate in D+: quasi-coherent cohomology in every degree.
Source: Stacks, Cohomology on Sites, Tag 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.zariskiQC {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) (K : c.zariskiCategory) : Prop :=
  letI := c.zariskiDerived
  ∀ q : ℤ, ((DerivedCategory.Plus.homologyFunctor T.Modules q).obj K).IsQuasicoherent

/-- An étale module is quasi-coherent here precisely when it is isomorphic, as a module,
to the canonical extension of a quasi-coherent Zariski module. The context's associated
identification is linear and normalized on opens, so this is the specified M_Et notion.
Source: Stacks, Descent, Tags 03DU, 03DX and 03DW
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.etaleModuleQC {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) (L : SmallEtaleModules T) : Prop :=
  ∃ M : T.Modules, M.IsQuasicoherent ∧ Nonempty (c.ordinary.extension.obj M ≅ L)

/-- The étale full-subcategory predicate in D+, with the essential-image notion above.
Source: Stacks, Cohomology on Sites, Tag 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.etaleQC {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) (L : c.etaleCategory) : Prop :=
  letI := c.etaleDerived
  ∀ q : ℤ, c.etaleModuleQC
    ((DerivedCategory.Plus.homologyFunctor (SmallEtaleModules T) q).obj L)

/-- The canonical derived comparison of sections, before placing the module in degree zero.
It is RΓ of the derived unit followed by the inverse derived-composition isomorphism.
Source: Stacks, Descent, Tag 03DW; Cohomology on Sites, Tag 0D6E
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.comparison {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) (K : c.zariskiCategory) :
    c.zariskiSections.obj K ⟶ c.etaleSections.obj (c.pullback.obj K) :=
  letI := c.zariskiDerived
  letI := c.etaleDerived
  letI := c.zariskiInjectives
  letI := c.etaleInjectives
  letI := c.extensionAdditive
  letI := c.restrictionAdditive
  letI := c.extensionLimits
  letI := c.extensionColimits
  letI := c.restrictionInjectives
  (globalSectionsFunctor T).rightDerivedFunctorPlus.map (c.derivedAdjunction.unit.app K) ≫
    (Functor.rightDerivedFunctorPlusCompIso c.ordinary.restriction
      (globalSectionsFunctor T)).inv.app (c.pullback.obj K)

/-- The comparison on a module, using the canonical exact-functor/single-object identification.
Source: Stacks, Descent, Tag 03DW
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.moduleComparison {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) (M : T.Modules) :
    c.zariskiSections.obj (c.zariskiSingle M) ⟶
      c.etaleSections.obj (c.etaleSingle (c.ordinary.extension.obj M)) :=
  letI := c.zariskiDerived
  letI := c.etaleDerived
  letI := c.etaleInjectives
  letI := c.extensionAdditive
  letI := c.extensionLimits
  letI := c.extensionColimits
  c.comparison (c.zariskiSingle M) ≫
    c.sections.rightDerivedFunctorPlus.map
      ((c.ordinary.extension.mapDerivedCategoryPlusSingleFunctor 0).hom.app M)

/-- The comparison isomorphism associated to a proof of invertibility of its canonical map.
No isomorphism is chosen independently of the derived unit and composition.
Source: Stacks, Descent, Tag 03DW
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiDerivedContext.moduleComparisonIso {T : Scheme.{u}}
    (c : EtaleZariskiDerivedContext T) (M : T.Modules) (hi : IsIso (c.moduleComparison M)) :
    c.zariskiSections.obj (c.zariskiSingle M) ≅
      c.etaleSections.obj (c.etaleSingle (c.ordinary.extension.obj M)) :=
  letI := hi
  asIso (c.moduleComparison M)

/-- Proof data for the canonical pullback of sections along an arbitrary scheme morphism.
The right comparison is fixed on every open by the canonical preimage-object isomorphism.
The acyclicity fields justify composition of derived sections, without requiring the
module pullback along h to be exact. All fields beyond the right-adjoint existence proof
are properties of the canonical direct-image functors.
Source: Stacks, Descent, Tags 03FH, 03LC and 03DW; Cohomology, Tag 01FB
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
structure EtaleZariskiSectionPullback {U T : Scheme.{u}} (h : U ⟶ T)
    (cU : EtaleZariskiDerivedContext U) (cT : EtaleZariskiDerivedContext T) where
  etaleRight : (smallEtaleModulePushforward h).IsRightAdjoint
  [etaleAdditive : (smallEtaleModulePushforward h).Additive]
  right : smallEtaleModulePushforward h ⋙ cT.ordinary.restriction ≅
    cU.ordinary.restriction ⋙ pushforward h
  right_sections : ∀ (L : SmallEtaleModules U) (W : T.Opens),
    (right.hom.app L).app W =
      L.val.presheaf.map (AlgebraicGeometry.gabberPreimageEtaleIso h W).hom.op
  zariskiAcyclic : ∀ (I : U.Modules) [Injective I],
    cT.zariskiSectionsAcyclic ((pushforward h).obj I)
  etaleAcyclic : ∀ (I : SmallEtaleModules U) [Injective I],
    cT.etaleSectionsAcyclic ((smallEtaleModulePushforward h).obj I)


/-- The canonical identification of global sections of the étale direct image.
It is the open-restriction comparison evaluated at the full open; Zariski direct image
preserves global sections definitionally.
Source: Stacks, Descent, Tag 03FH
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiSectionPullback.sectionsIso {U T : Scheme.{u}} {h : U ⟶ T}
    {cU : EtaleZariskiDerivedContext U} {cT : EtaleZariskiDerivedContext T}
    (p : EtaleZariskiSectionPullback h cU cT) :
    smallEtaleModulePushforward h ⋙ cT.sections ≅ cU.sections :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight p.right (globalSectionsFunctor T) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft cU.ordinary.restriction (Iso.refl _)

section SectionMaps

variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{dA} A] [HasDerivedCategory.{dB} B]
  [EnoughInjectives A] [EnoughInjectives B]

/-- The canonical map on derived sections of a coefficient map M → R N. It first uses
that map in degree zero and the right-derived single-object unit, then the inverse of
the acyclic derived-composition isomorphism. Thus it is the adjunction-unit pullback
when the coefficient map is the transpose of a map of pulled-back modules.
Source: Stacks, Cohomology, Tags 01FA and 01FB; Cohomology on Sites, Tag 0D6E
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def etaleZariskiDerivedSectionMap (R : A ⥤ B) (G : B ⥤ AddCommGrpCat.{u})
    (H : A ⥤ AddCommGrpCat.{u}) [R.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits G]
    (acyclic : ∀ (I : A) [Injective I], G.rightAcyclic (R.obj I))
    (sections : R ⋙ G ≅ H) {M : B} {N : A} (f : M ⟶ R.obj N) :
    G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj M) ⟶
      H.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj N) :=
  G.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor B 0).map f ≫ R.rightDerivedPlusSingleUnit N) ≫
    (R.rightDerivedFunctorPlusCompIsoOfRightAcyclic G acyclic).inv.app
      ((DerivedCategory.Plus.singleFunctor A 0).obj N) ≫
    (Functor.rightDerivedFunctorPlusNatIso sections).hom.app
      ((DerivedCategory.Plus.singleFunctor A 0).obj N)

end SectionMaps

/-- Pullback of Zariski derived sections for h^*M → N, using its tensor-adjunction transpose.
Source: Stacks, Cohomology, Tags 01F7 and 01FB
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiSectionPullback.zariskiMap {U T : Scheme.{u}} {h : U ⟶ T}
    {cU : EtaleZariskiDerivedContext U} {cT : EtaleZariskiDerivedContext T}
    (p : EtaleZariskiSectionPullback h cU cT) (M : T.Modules) (N : U.Modules)
    (f : (tensorPullback h).obj M ⟶ N) :=
  letI := cT.zariskiDerived
  letI := cU.zariskiDerived
  letI := cT.zariskiInjectives
  letI := cU.zariskiInjectives
  etaleZariskiDerivedSectionMap (pushforward h) (globalSectionsFunctor T)
    (globalSectionsFunctor U) p.zariskiAcyclic (Iso.refl _)
    (((Classical.choose (exists_tensorPullbackAdjunction h)).homEquiv M N) f)

/-- Pullback of étale derived sections. The coefficient map is the tensor-adjunction mate
of the canonical direct-image square, applied to the same module map h^*M → N.
Source: Stacks, Descent, Tags 03FH and 03LC; Cohomology, Tag 01FB
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit). -/
def EtaleZariskiSectionPullback.etaleMap {U T : Scheme.{u}} {h : U ⟶ T}
    {cU : EtaleZariskiDerivedContext U} {cT : EtaleZariskiDerivedContext T}
    (p : EtaleZariskiSectionPullback h cU cT) (M : T.Modules) (N : U.Modules)
    (f : (tensorPullback h).obj M ⟶ N) :=
  letI := cT.etaleDerived
  letI := cU.etaleDerived
  letI := cT.etaleInjectives
  letI := cU.etaleInjectives
  letI := p.etaleAdditive
  etaleZariskiDerivedSectionMap (smallEtaleModulePushforward h) cT.sections cU.sections
    p.etaleAcyclic p.sectionsIso
    (cT.ordinary.extension.map
        (((Classical.choose (exists_tensorPullbackAdjunction h)).homEquiv M N) f) ≫
      zariskiEtalePushforwardComparison h cU.ordinary cT.ordinary p.etaleRight p.right N)

/-- The canonical bounded-below étale/Zariski adjunction is an equivalence on
quasi-coherent cohomology; its sections comparison is natural in coefficients and scheme
pullback. Both directions of the cohomology pullback square use the same comparison.

Source: Stacks Project, Descent, Tag 03DW; Cohomology on Sites, Tags 07A8 and 0D7U
(blueprint: lem-fd-etale-zariski-qcoherent-derived-unit).

Proof, following all seven steps of the node:
1. Flat ringed pullback gives exact tensor extension and its identification with the
   associated étale tensor-section sheaf. Open evaluation and the unit-normalized
   open tensor-pullback/restriction identification make the heart unit identity.
2. The ringed module categories are Grothendieck and have enough injectives. On every
   affine open, the module/abelian evaluation comparison, slice localization, and the
   natural open coefficient identification reduce positive direct images to affine
   étale quasi-coherent cohomology, which vanishes. Cycles are locally boundaries on
   the affine basis, so positive direct-image cohomology sheaves vanish.
3. Apply lem-fd-bounded-below-acyclic-heart-adjunction to the exact extension,
   restriction, and the quasi-coherent heart class. This gives preservation of the
   two D+ full subcategories and the canonical invertible derived unit and counit.
4. Naturality of the counit expresses a map as counit, extension of its direct image,
   and inverse counit. Thus derived restriction reflects isomorphisms on this class.
5. RΓ of the unit followed by derived composition is the comparison defined above.
   Restriction sends injectives to injectives because extension is exact. An étale
   injective resolution restricts to a Zariski resolution of a quasi-coherent module;
   both derived sections are represented by the identical sections complex. The map
   is its identity, naturally in all module maps (acyclicComparison_naturality).
6. For h^*M → N the two ordinary coefficient maps agree on tensor generators:
   1 tensor (1 tensor m) goes to the given image of 1 tensor m. The right square is
   fixed on every open, so its mate is exactly this tensor-composition comparison.
7. Transpose that identity under the sheaf adjunctions. The derived composite-unit
   normalization identifies successive units with the composite unit. Module/abelian
   evaluation comparison and the acyclic-resolution criterion identify this map with
   the common sections-complex map of step 5. Therefore the derived pullback square
   commutes; applying every H^q gives its forward square. Inverting the comparison
   yields the reverse square. This includes degree zero, empty schemes, and arbitrary
   h; no exactness of tensor pullback along h is asserted or assumed.
-/
theorem etale_zariski_quasiCoherent_derived_unit :
    ∃ c : ∀ T : Scheme.{u}, EtaleZariskiDerivedContext T,
      (∀ (T : Scheme.{u}) (K : (c T).zariskiCategory), (c T).zariskiQC K →
        (c T).etaleQC ((c T).pullback.obj K) ∧
          IsIso ((c T).derivedAdjunction.unit.app K)) ∧
      (∀ (T : Scheme.{u}) (L : (c T).etaleCategory), (c T).etaleQC L →
        (c T).zariskiQC ((c T).pushforward.obj L) ∧
          IsIso ((c T).derivedAdjunction.counit.app L)) ∧
      (∀ (T : Scheme.{u}) (L L' : (c T).etaleCategory) (f : L ⟶ L'),
        (c T).etaleQC L → (c T).etaleQC L' →
          IsIso ((c T).pushforward.map f) → IsIso f) ∧
      ∃ hi : ∀ (T : Scheme.{u}) (M : T.Modules) [M.IsQuasicoherent],
          IsIso ((c T).moduleComparison M),
        (∀ (T : Scheme.{u}) (M N : T.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
            (f : M ⟶ N),
          (c T).zariskiSections.map ((c T).zariskiSingleMap f) ≫ (c T).moduleComparison N =
            (c T).moduleComparison M ≫ (c T).etaleSections.map
              ((c T).etaleSingleMap ((c T).ordinary.extension.map f))) ∧
        ∀ (U T : Scheme.{u}) (h : U ⟶ T),
          ∃ p : EtaleZariskiSectionPullback h (c U) (c T),
            ∀ (M : T.Modules) (N : U.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
                (f : (tensorPullback h).obj M ⟶ N) (q : ℤ),
              (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).map
                  ((c T).moduleComparison M) ≫
                (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).map
                  (p.etaleMap M N f) =
              (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).map
                  (p.zariskiMap M N f) ≫
                (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).map
                  ((c U).moduleComparison N) ∧
              ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).mapIso
                  ((c T).moduleComparisonIso M (hi T M))).inv ≫
                (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).map
                  (p.zariskiMap M N f) =
              (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).map
                  (p.etaleMap M N f) ≫
                ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).mapIso
                  ((c U).moduleComparisonIso N (hi U N))).inv := by
  sorry

end AlgebraicGeometry.Scheme.Modules
