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
public import WeilConjectures.AlgebraicGeometry.EtaleTensorPositiveDirectImageVanishing
public import WeilConjectures.AlgebraicGeometry.PositiveDirectImageOfObjectAcyclic
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.Adjunction.AcyclicCohomologyDerivedCounit
public import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.FlatEtaleZariskiQuasicoherentUnit
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

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

namespace AlgebraicGeometry.Scheme.Modules

private theorem single_exact_transport {D E : Type*} [Category* D] [Category* E]
    [Abelian D] [Abelian E] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : D) :
    F.mapDerivedCategoryPlus.map (singleTransport D X).hom ≫
      (F.mapDerivedCategoryPlusSingleFunctor 0).hom.app X =
    F.mapDerivedCategoryPlusFactorsh.hom.app
      ((HomotopyCategory.Plus.singleFunctor D 0).obj X) ≫
      DerivedCategory.Plus.Qh.map (homotopySingleIso F X).hom ≫
      (singleTransport E (F.obj X)).hom := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [CategoryTheory.Functor.map_comp, singleTransport_hom, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id,
    ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    ι_map_mapDerivedCategoryPlusFactorsh_hom_app]
  change (F.mapDerivedCategorySingleFunctor 0).hom.app X =
    F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((CochainComplex.singleFunctor D 0).obj X)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι E).map
        (homotopySingleIso F X).hom)
  rw [mapDerivedCategoryFactorsh_hom_app]
  simp only [homotopySingleIso, Functor.preimageIso_hom, Functor.map_preimage,
    Functor.mapIso_hom, Category.assoc]
  change _ = F.mapDerivedCategory.map (𝟙 _) ≫
    F.mapDerivedCategoryFactors.hom.app _ ≫ 𝟙 _ ≫
    DerivedCategory.Qh.map (𝟙 _) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient E (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X))
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  change _ = F.mapDerivedCategoryFactors.hom.app _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X)
  simp only [comp_obj, DerivedCategory.Q_obj_single_obj, mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, isoWhiskerRight_refl, isoWhiskerLeft_refl,
    Iso.refl_symm, Iso.refl_trans, Iso.trans_hom, isoWhiskerLeft_hom, Iso.symm_hom,
    isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app, associator_hom_app,
    whiskerLeft_app, associator_inv_app, whiskerRight_app, NatTrans.id_app,
    Category.comp_id, Category.id_comp]
  erw [Category.id_comp]
  rfl

private theorem derived_single_unit {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    (F : C ⥤ D) (R : D ⥤ C) [F.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ R) (M : C) :
    adj.derivedPlus.unit.app ((DerivedCategory.Plus.singleFunctor C 0).obj M) ≫
        R.rightDerivedFunctorPlus.map
          ((F.mapDerivedCategoryPlusSingleFunctor 0).hom.app M) =
      (DerivedCategory.Plus.singleFunctor C 0).map (adj.unit.app M) ≫
        R.rightDerivedPlusSingleUnit (F.obj M) := by
  let K := (HomotopyCategory.Plus.singleFunctor C 0).obj M
  let e := homotopySingleIso F M
  have hf := single_exact_transport F M
  simp only [singleTransport_hom, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id] at hf
  have hfac := adj.derivedPlus_unit_app_fac K
  have hn := R.rightDerivedFunctorPlusUnit.naturality e.hom
  have hη : DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
      DerivedCategory.Plus.Qh.map (R.mapHomotopyCategoryPlus.map e.hom) ≫
      (R.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (F.obj M)).hom =
    (DerivedCategory.Plus.singleFunctor C 0).map (adj.unit.app M) := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [CategoryTheory.Functor.map_comp, mapHomotopyCategoryPlusSingleFunctorQhObjIso,
      Functor.preimageIso_hom, Functor.map_preimage, Functor.mapIso_hom]
    change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι C).map
        (adj.mapHomotopyCategoryPlus.unit.app K)) ≫
      DerivedCategory.Qh.map (R.mapHomotopyCategory (.up ℤ) |>.map
        ((HomotopyCategory.Plus.ι D).map e.hom)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app
          (F.obj M)) = DerivedCategory.Q.map
        ((CochainComplex.singleFunctor C 0).map (adj.unit.app M))
    rw [ι_map_mapHomotopyCategoryPlus_unit_app]
    erw [mapHomotopyCategory_unit_app_quotient]
    simp only [e, homotopySingleIso, Functor.preimageIso_hom, Functor.map_preimage,
      Functor.mapIso_hom, Functor.mapHomotopyCategory_map]
    change DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app
        ((CochainComplex.singleFunctor C 0).obj M)) ≫
      DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app
          (F.obj M)) = _
    simp only [← CategoryTheory.Functor.map_comp]
    congr 1
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [HomologicalComplex.comp_f, mapHomologicalComplex_unit_app_f,
        Functor.mapHomologicalComplex_map_f,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        CochainComplex.singleFunctor, CochainComplex.singleFunctors,
        HomologicalComplex.single_map_f_self]
      dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
      simp only [CategoryTheory.Functor.map_id, Category.id_comp]
      change adj.unit.app M ≫ R.map (𝟙 (F.obj M)) ≫ 𝟙 _ = adj.unit.app M ≫ 𝟙 _
      rw [CategoryTheory.Functor.map_id]
      simp only [Category.comp_id]
      exact Category.comp_id _
    · simp only [HomologicalComplex.comp_f,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_ne R (.up ℤ) hn,
        CochainComplex.singleFunctor, CochainComplex.singleFunctors,
        comp_zero]
      exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn).eq_of_src _ _
  have hη' : DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
      DerivedCategory.Plus.Qh.map (R.mapHomotopyCategoryPlus.map e.hom) =
    (DerivedCategory.Plus.singleFunctor C 0).map (adj.unit.app M) ≫
      (R.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (F.obj M)).inv := by
    apply (cancel_mono
      (R.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (F.obj M)).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hη
  rw [hf, CategoryTheory.Functor.map_comp, ← Category.assoc]
  erw [hfac]
  rw [Category.assoc]
  erw [← hn]
  rw [← Category.assoc]
  change (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
      DerivedCategory.Plus.Qh.map (R.mapHomotopyCategoryPlus.map e.hom)) ≫
        R.rightDerivedFunctorPlusUnit.app _ = _
  rw [hη']
  change _ = (DerivedCategory.Plus.singleFunctor C 0).map (adj.unit.app M) ≫
    (R.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (F.obj M)).inv ≫
      R.rightDerivedFunctorPlusUnit.app _ ≫
        R.rightDerivedFunctorPlus.map (singleTransport D (F.obj M)).hom
  rw [singleTransport_hom, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  exact Category.assoc _ _ _

private theorem ordinary_unit {U T : Scheme.{u}} (h : U ⟶ T)
    (cU : ZariskiEtaleModuleContext U) (cT : ZariskiEtaleModuleContext T)
    (hp : (smallEtaleModulePushforward h).IsRightAdjoint)
    (r : smallEtaleModulePushforward h ⋙ cT.restriction ≅
      cU.restriction ⋙ pushforward h) (N : U.Modules) :
    cT.adjunction.unit.app ((pushforward h).obj N) ≫
        cT.restriction.map (zariskiEtalePushforwardComparison h cU cT hp r N) ≫
        r.hom.app (cU.extension.obj N) =
      (pushforward h).map (cU.adjunction.unit.app N) := by
  let az := Classical.choose (exists_tensorPullbackAdjunction h)
  let ae := smallEtaleModuleAdjunction h hp
  let α := TwoSquare.mk _ _ _ _ (zariskiEtalePullbackComparison h cU cT hp r).inv
  let δ := mateEquiv az ae α
  have hδ : δ.app N = zariskiEtalePushforwardComparison h cU cT hp r N := by
    dsimp [δ, α, mateEquiv, zariskiEtalePushforwardComparison, az, ae]
    simp only [Category.comp_id, Category.id_comp, Functor.map_comp]
  have hm : (mateEquiv cU.adjunction cT.adjunction δ).natTrans = r.inv := by
    rw [iterated_mateEquiv_conjugateEquiv]
    change conjugateEquiv (az.comp cU.adjunction) (cT.adjunction.comp ae)
      ((conjugateEquiv (az.comp cU.adjunction) (cT.adjunction.comp ae)).symm r.inv) = r.inv
    exact Equiv.apply_symm_apply _ _
  have he := unit_mateEquiv cU.adjunction cT.adjunction δ N
  rw [show (mateEquiv cU.adjunction cT.adjunction δ).app _ = r.inv.app _ from
    congr_app hm _] at he
  change (pushforward h).map (cU.adjunction.unit.app N) ≫
      r.inv.app (cU.extension.obj N) =
    cT.adjunction.unit.app ((pushforward h).obj N) ≫
      cT.restriction.map (δ.natTrans.app N) at he
  change δ.natTrans.app N = _ at hδ
  rw [hδ] at he
  rw [← Category.assoc, ← he, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

end AlgebraicGeometry.Scheme.Modules
