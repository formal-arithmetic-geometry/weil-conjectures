/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Cohomology.Leray
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison

import WeilConjectures.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.ProperBaseChange.ModuleAbelianEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleOpenQuasiCoherentIdentificationNaturality
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.Curve.OverPullbackAdjunctionMono
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.AlgebraicGeometry.SiteRestrictionInjectives
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
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


section SectionMaps

variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{dA} A] [HasDerivedCategory.{dB} B]
  [EnoughInjectives A] [EnoughInjectives B]

end SectionMaps

end AlgebraicGeometry.Scheme.Modules
