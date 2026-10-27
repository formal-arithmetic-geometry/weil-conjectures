/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.TraceFormula.ZariskiEtaleFunctorComparisonSquare
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedMateEvaluation
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackPreservesQCoh
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf

import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Paper.ProjectionMateExact
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Derived étale–Zariski equivalence

Source: Stacks Project, spaces-perfect.tex, Tags 08H8, 071Q and 08GH;
descent.tex, Tag 03FH (blueprint: lem-sfb-derived-etale-zariski-equivalence).

The data structures package the witnesses of the statement, with universal properties
and representative equations fixing the derived functors and their comparisons.

## Main definitions and statements

* `DerivedEtaleZariskiEquivalenceData`: the canonical adjoint equivalence witnesses.
* `DerivedEtaleZariskiSquareData`: normalized pullback and direct-image comparisons.
* `DerivedEtaleZariskiSystem`: simultaneous witnesses with coherent comparisons.
* `derived_etale_zariski_equivalence`: existence of this canonical system.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
-- Constructor injectivity lemmas for these witness records are not needed.
set_option genInjectivity false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable [∀ T : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
  [∀ T : Scheme.{u}, HasDerivedCategory.{w} (SmallEtaleModules T)]

/-- The canonical structure-module map for epsilon, with the context's proof arguments.
This is Mathlib's adjoint scalar-multiplication map, without a new choice of a map.
Source: Stacks 03FH (blueprint: lem-sfb-derived-etale-zariski-equivalence). -/
def ZariskiEtaleModuleContext.structureMap {T : Scheme.{u}}
    (c : ZariskiEtaleModuleContext T) :
    c.extension.obj (SheafOfModules.unit T.ringCatSheaf) ⟶
      SheafOfModules.unit (smallEtaleModuleRing T) :=
  letI := c.continuous
  letI : (SheafOfModules.pushforward (zariskiEtaleOpenRingMap T)).IsRightAdjoint :=
    c.rightAdjoint
  SheafOfModules.pullbackObjUnitToUnit (zariskiEtaleOpenRingMap T)

/-- The canonical structure-module map for a small étale pullback.
Source: Stacks 03FH (blueprint: lem-sfb-derived-etale-zariski-equivalence). -/
def smallEtaleStructureMap {U T : Scheme.{u}} (h : U ⟶ T)
    (hp : (smallEtaleModulePushforward h).IsRightAdjoint) :
    (smallEtaleModulePullback h hp).obj (SheafOfModules.unit (smallEtaleModuleRing T)) ⟶
      SheafOfModules.unit (smallEtaleModuleRing U) :=
  letI : (SheafOfModules.pushforward (smallEtaleModuleRingMap h)).IsRightAdjoint := hp
  SheafOfModules.pullbackObjUnitToUnit (smallEtaleModuleRingMap h)

/-- Witnesses for the canonical derived adjoint equivalence, including its actual
adjunction maps. Only the cohomology sheaves, not the terms, must be quasi-coherent.
Source: Stacks 08H8 and 071Q
(blueprint: lem-sfb-derived-etale-zariski-equivalence). -/
structure DerivedEtaleZariskiEquivalenceData (T : Scheme.{u}) where
  context : ZariskiEtaleModuleContext T
  [extension_additive : context.extension.Additive]
  [restriction_additive : context.restriction.Additive]
  exact_limits : PreservesFiniteLimits context.extension
  exact_colimits : PreservesFiniteColimits context.extension
  faithful : context.extension.Faithful
  extension : schemeDerivedCategory T ⥤ DerivedCategory (SmallEtaleModules T)
  extension_factors : DerivedCategory.Qh.{w} ⋙ extension ≅
    context.extension.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w}
  restriction : DerivedCategory (SmallEtaleModules T) ⥤ schemeDerivedCategory T
  restriction_unit : context.restriction.mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings T.toRingedSpace)) ⟶
      DerivedCategory.Qh.{w} ⋙ restriction
  restriction_derived : restriction.IsRightDerivedFunctor restriction_unit
    (HomotopyCategory.quasiIso (SmallEtaleModules T) (.up ℤ))
  restriction_injective : ∀ I : CochainComplex (SmallEtaleModules T) ℤ,
    I.IsKInjective →
      IsIso (restriction_unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I))
  adjunction : extension ⊣ restriction
  adjunction_normalized :
    ∀ (P : HomotopyCategory (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (.up ℤ))
      (I : HomotopyCategory (SmallEtaleModules T) (.up ℤ))
      (t : (context.extension.mapHomotopyCategory (.up ℤ)).obj P ⟶ I),
      adjunction.homEquiv (DerivedCategory.Qh.{w}.obj P) (DerivedCategory.Qh.{w}.obj I)
        (extension_factors.hom.app P ≫ DerivedCategory.Qh.{w}.map t) =
      DerivedCategory.Qh.{w}.map
        ((context.adjunction.mapHomotopyCategory (.up ℤ)).homEquiv P I t) ≫
          restriction_unit.app I
  structure_iso : IsIso context.structureMap
  extension_qcoh : ∀ K : schemeDerivedCategory T, schemeDerivedQCohProperty T K →
    ∀ n : ℤ, ((DerivedCategory.homologyFunctor (SmallEtaleModules T) n).obj
      (extension.obj K)).IsQuasicoherent
  restriction_qcoh : ∀ K : DerivedCategory (SmallEtaleModules T),
    (∀ n : ℤ, ((DerivedCategory.homologyFunctor (SmallEtaleModules T) n).obj K).IsQuasicoherent) →
      schemeDerivedQCohProperty T (restriction.obj K)
  unit_iso : ∀ K : schemeDerivedCategory T, schemeDerivedQCohProperty T K →
    IsIso (adjunction.unit.app K)
  counit_iso : ∀ K : DerivedCategory (SmallEtaleModules T),
    (∀ n : ℤ, ((DerivedCategory.homologyFunctor (SmallEtaleModules T) n).obj K).IsQuasicoherent) →
      IsIso (adjunction.counit.app K)

attribute [instance] DerivedEtaleZariskiEquivalenceData.extension_additive
  DerivedEtaleZariskiEquivalenceData.restriction_additive

/-- Witnesses for the comparison square, tied to the ordinary square and derived counits.
Source: Stacks 08GH and 03FH
(blueprint: lem-sfb-derived-etale-zariski-equivalence). -/
structure DerivedEtaleZariskiSquareData {U T : Scheme.{u}} (h : U ⟶ T)
    (dU : DerivedEtaleZariskiEquivalenceData U)
    (dT : DerivedEtaleZariskiEquivalenceData T) where
  rightAdjoint : (smallEtaleModulePushforward h).IsRightAdjoint
  ordinary_right : smallEtaleModulePushforward h ⋙ dT.context.restriction ≅
    dU.context.restriction ⋙ pushforward h
  ordinary_right_sections : ∀ (G : SmallEtaleModules U) (W : T.Opens),
    (ordinary_right.hom.app G).app W =
      G.val.presheaf.map (AlgebraicGeometry.gabberPreimageEtaleIso h W).hom.op
  [source_extension_additive : dT.context.extension.Additive]
  [target_extension_additive : dU.context.extension.Additive]
  [pullback_additive : (smallEtaleModulePullback h rightAdjoint).Additive]
  [zariski_additive : (tensorPullback h).Additive]
  pullback : DerivedCategory (SmallEtaleModules T) ⥤ DerivedCategory (SmallEtaleModules U)
  pullback_counit : DerivedCategory.Qh.{w} ⋙ pullback ⟶
    (smallEtaleModulePullback h rightAdjoint).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w}
  pullback_derived : pullback.IsLeftDerivedFunctor pullback_counit
    (HomotopyCategory.quasiIso (SmallEtaleModules T) (.up ℤ))
  zariski_counit : DerivedCategory.Qh.{w} ⋙ AlgebraicGeometry.derivedPullback h ⟶
    (tensorPullback h).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings U.toRingedSpace))
  zariski_derived : (AlgebraicGeometry.derivedPullback h).IsLeftDerivedFunctor zariski_counit
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (.up ℤ))
  zariski_normalized :
    ∀ (P : HomotopyCategory (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (.up ℤ))
      (I : HomotopyCategory (SheafOfModules.{u} (moduleRings U.toRingedSpace)) (.up ℤ))
      (t : ((tensorPullback h).mapHomotopyCategory (.up ℤ)).obj P ⟶ I),
    (canonicalSchemeDerivedAdjunction h).homEquiv
      (DerivedCategory.Qh.{w}.obj P) (DerivedCategory.Qh.{w}.obj I)
      (zariski_counit.app P ≫ DerivedCategory.Qh.{w}.map t) =
    DerivedCategory.Qh.{w}.map
      (((Classical.choose (exists_tensorPullbackAdjunction h)).mapHomotopyCategory
        (.up ℤ)).homEquiv P I t) ≫
      (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).rightDerivedFunctorUnit.app I
  comparison : AlgebraicGeometry.derivedPullback h ⋙ dU.extension ≅ dT.extension ⋙ pullback
  comparison_representatives : ∀ P :
      HomotopyCategory (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (.up ℤ),
    comparison.hom.app (DerivedCategory.Qh.{w}.obj P) ≫
        pullback.map (dT.extension_factors.hom.app P) ≫
        pullback_counit.app ((dT.context.extension.mapHomotopyCategory (.up ℤ)).obj P) =
      dU.extension.map (zariski_counit.app P) ≫
        dU.extension_factors.hom.app (((tensorPullback h).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.{w}.map
          ((NatTrans.mapHomotopyCategory
            (zariskiEtalePullbackComparison h dU.context dT.context rightAdjoint
              ordinary_right).hom (.up ℤ)).app P)
  pullback_qcoh : ∀ K : DerivedCategory (SmallEtaleModules T),
    (∀ n : ℤ, ((DerivedCategory.homologyFunctor (SmallEtaleModules T) n).obj K).IsQuasicoherent) →
      ∀ n : ℤ, ((DerivedCategory.homologyFunctor (SmallEtaleModules U) n).obj
        (pullback.obj K)).IsQuasicoherent
  [pushforward_additive : (smallEtaleModulePushforward h).Additive]
  pushforward : DerivedCategory (SmallEtaleModules U) ⥤ DerivedCategory (SmallEtaleModules T)
  pushforward_unit : (smallEtaleModulePushforward h).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh.{w} ⟶ DerivedCategory.Qh.{w} ⋙ pushforward
  pushforward_derived : pushforward.IsRightDerivedFunctor pushforward_unit
    (HomotopyCategory.quasiIso (SmallEtaleModules U) (.up ℤ))
  pushforward_injective : ∀ I : CochainComplex (SmallEtaleModules U) ℤ,
    I.IsKInjective →
      IsIso (pushforward_unit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I))
  adjunction : pullback ⊣ pushforward
  adjunction_normalized :
    ∀ (P : HomotopyCategory (SmallEtaleModules T) (.up ℤ))
      (I : HomotopyCategory (SmallEtaleModules U) (.up ℤ))
      (t : ((smallEtaleModulePullback h rightAdjoint).mapHomotopyCategory (.up ℤ)).obj P ⟶ I),
      adjunction.homEquiv (DerivedCategory.Qh.{w}.obj P) (DerivedCategory.Qh.{w}.obj I)
        (pullback_counit.app P ≫ DerivedCategory.Qh.{w}.map t) =
      DerivedCategory.Qh.{w}.map
        (((smallEtaleModuleAdjunction h rightAdjoint).mapHomotopyCategory (.up ℤ)).homEquiv
          P I t) ≫ pushforward_unit.app I
  pushforward_qcoh : QuasiCompact h → QuasiSeparated h →
    ∀ K : DerivedCategory (SmallEtaleModules U),
    (∀ n : ℤ, ((DerivedCategory.homologyFunctor (SmallEtaleModules U) n).obj K).IsQuasicoherent) →
      ∀ n : ℤ, ((DerivedCategory.homologyFunctor (SmallEtaleModules T) n).obj
        (pushforward.obj K)).IsQuasicoherent
  pushforward_comparison_iso : QuasiCompact h → QuasiSeparated h →
    ∀ K : schemeDerivedCategory U, schemeDerivedQCohProperty U K →
      IsIso (adjunction.unit.app (dT.extension.obj ((schemeDerivedDirectImage h).obj K)) ≫
        pushforward.map
          (comparison.inv.app ((schemeDerivedDirectImage h).obj K) ≫
            dU.extension.map ((canonicalSchemeDerivedAdjunction h).counit.app K)))
  structure_iso : IsIso (smallEtaleStructureMap h rightAdjoint)
  structure_compatibility :
    (zariskiEtalePullbackComparison h dU.context dT.context rightAdjoint ordinary_right).hom.app
        (SheafOfModules.unit T.ringCatSheaf) ≫
      (smallEtaleModulePullback h rightAdjoint).map dT.context.structureMap ≫
      smallEtaleStructureMap h rightAdjoint =
    dU.context.extension.map (tensorPullbackObjUnitToUnit h) ≫ dU.context.structureMap

/-- The ordinary pullback on homotopy categories, retaining the square's additivity proof.
Source: Stacks 03FH (blueprint: lem-sfb-derived-etale-zariski-equivalence). -/
def DerivedEtaleZariskiSquareData.ordinaryPullbackHomotopy
    {U T : Scheme.{u}} {h : U ⟶ T}
    {dU : DerivedEtaleZariskiEquivalenceData U} {dT : DerivedEtaleZariskiEquivalenceData T}
    (s : DerivedEtaleZariskiSquareData h dU dT) :
    HomotopyCategory (SmallEtaleModules T) (.up ℤ) ⥤
      HomotopyCategory (SmallEtaleModules U) (.up ℤ) :=
  letI := s.pullback_additive
  (smallEtaleModulePullback h s.rightAdjoint).mapHomotopyCategory (.up ℤ)

/-- Termwise ordinary pullback, retaining the square's additivity proof.
Source: Stacks 03FH (blueprint: lem-sfb-derived-etale-zariski-equivalence). -/
def DerivedEtaleZariskiSquareData.ordinaryPullbackComplex
    {U T : Scheme.{u}} {h : U ⟶ T}
    {dU : DerivedEtaleZariskiEquivalenceData U} {dT : DerivedEtaleZariskiEquivalenceData T}
    (s : DerivedEtaleZariskiSquareData h dU dT) :
    CochainComplex (SmallEtaleModules T) ℤ ⥤ CochainComplex (SmallEtaleModules U) ℤ :=
  letI := s.pullback_additive
  (smallEtaleModulePullback h s.rightAdjoint).mapHomologicalComplex (.up ℤ)

/-- Simultaneous equivalences and comparison squares, with identity and composition
normalizations. The ordinary right comparisons are restriction along the canonical
base-change identifications; their left mates are therefore scalar-extension reassociation.
The homotopy and derived comparisons are fixed by the displayed representative equations.
Source: Stacks 08H8, 071Q, 08GH and 03FH
(blueprint: lem-sfb-derived-etale-zariski-equivalence). -/
structure DerivedEtaleZariskiSystem where
  [zariski_additive : ∀ {U T : Scheme.{u}} (h : U ⟶ T), (tensorPullback h).Additive]
  data : ∀ T : Scheme.{u}, DerivedEtaleZariskiEquivalenceData T
  square : ∀ {U T : Scheme.{u}} (h : U ⟶ T),
    DerivedEtaleZariskiSquareData h (data U) (data T)
  ordinary_right_comp : ∀ {V U T : Scheme.{u}} (g : V ⟶ U) (h : U ⟶ T),
    smallEtaleModulePushforward g ⋙ smallEtaleModulePushforward h ≅
      smallEtaleModulePushforward (g ≫ h)
  ordinary_right_comp_sections :
    ∀ {V U T : Scheme.{u}} (g : V ⟶ U) (h : U ⟶ T)
      (M : SmallEtaleModules V) (W : T.Etale)
      (m : ((smallEtaleModulePushforward g ⋙ smallEtaleModulePushforward h).obj M).val.obj
        (op W)),
      ((ordinary_right_comp g h).hom.app M).val.app (op W) m =
        M.val.presheaf.map
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g h).hom.app W).op m
  ordinary_left_comp : ∀ {V U T : Scheme.{u}} (g : V ⟶ U) (h : U ⟶ T),
    smallEtaleModulePullback h (square h).rightAdjoint ⋙
      smallEtaleModulePullback g (square g).rightAdjoint ≅
        smallEtaleModulePullback (g ≫ h) (square (g ≫ h)).rightAdjoint
  ordinary_left_comp_mate : ∀ {V U T : Scheme.{u}} (g : V ⟶ U) (h : U ⟶ T),
    ordinary_left_comp g h =
      (((conjugateIsoEquiv
        ((smallEtaleModuleAdjunction h (square h).rightAdjoint).comp
          (smallEtaleModuleAdjunction g (square g).rightAdjoint))
        (smallEtaleModuleAdjunction (g ≫ h) (square (g ≫ h)).rightAdjoint)).symm
          (ordinary_right_comp g h)).symm)
  homotopy_comp : ∀ {V U T : Scheme.{u}} (g : V ⟶ U) (h : U ⟶ T),
    (square h).ordinaryPullbackHomotopy ⋙ (square g).ordinaryPullbackHomotopy ≅
      (square (g ≫ h)).ordinaryPullbackHomotopy
  homotopy_comp_representatives :
    ∀ {V U T : Scheme.{u}} (g : V ⟶ U) (h : U ⟶ T)
      (P : CochainComplex (SmallEtaleModules T) ℤ),
      ∃ a : ((square h).ordinaryPullbackComplex ⋙
          (square g).ordinaryPullbackComplex).obj P ⟶
            (square (g ≫ h)).ordinaryPullbackComplex.obj P,
        (∀ n : ℤ, a.f n = (ordinary_left_comp g h).hom.app (P.X n)) ∧
        (homotopy_comp g h).hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
          (HomotopyCategory.quotient _ (.up ℤ)).map a
  derived_comp : ∀ {V U T : Scheme.{u}} (g : V ⟶ U) (h : U ⟶ T),
    (square h).pullback ⋙ (square g).pullback ≅ (square (g ≫ h)).pullback
  derived_comp_normalized :
    ∀ {V U T : Scheme.{u}} (g : V ⟶ U) (h : U ⟶ T)
      (P : HomotopyCategory (SmallEtaleModules T) (.up ℤ)),
      (derived_comp g h).hom.app (DerivedCategory.Qh.{w}.obj P) ≫
          (square (g ≫ h)).pullback_counit.app P =
        (square g).pullback.map ((square h).pullback_counit.app P) ≫
          (square g).pullback_counit.app ((square h).ordinaryPullbackHomotopy.obj P) ≫
            DerivedCategory.Qh.{w}.map ((homotopy_comp g h).hom.app P)
  comparison_comp : ∀ {V U T : Scheme.{u}} (g : V ⟶ U) (h : U ⟶ T)
      (K : schemeDerivedCategory T), schemeDerivedQCohProperty T K →
    (data V).extension.map ((canonicalDerivedPullbackComposition g h).hom.app K) ≫
        (square (g ≫ h)).comparison.hom.app K =
      (square g).comparison.hom.app ((AlgebraicGeometry.derivedPullback h).obj K) ≫
        (square g).pullback.map ((square h).comparison.hom.app K) ≫
          (derived_comp g h).hom.app ((data T).extension.obj K)
  ordinary_right_id : ∀ T : Scheme.{u}, smallEtaleModulePushforward (𝟙 T) ≅
    𝟭 (SmallEtaleModules T)
  ordinary_right_id_sections : ∀ (T : Scheme.{u}) (M : SmallEtaleModules T) (W : T.Etale)
      (m : ((smallEtaleModulePushforward (𝟙 T)).obj M).val.obj (op W)),
    ((ordinary_right_id T).hom.app M).val.app (op W) m =
      M.val.presheaf.map
        ((MorphismProperty.Over.pullbackId @Etale ⊤ T).inv.app W).op m
  ordinary_left_id : ∀ T : Scheme.{u},
    smallEtaleModulePullback (𝟙 T) (square (𝟙 T)).rightAdjoint ≅ 𝟭 (SmallEtaleModules T)
  ordinary_left_id_mate : ∀ T : Scheme.{u}, ordinary_left_id T =
    (((conjugateIsoEquiv (smallEtaleModuleAdjunction (𝟙 T) (square (𝟙 T)).rightAdjoint)
      (Adjunction.id (C := SmallEtaleModules T))).symm (ordinary_right_id T)).symm)
  homotopy_id : ∀ T : Scheme.{u}, (square (𝟙 T)).ordinaryPullbackHomotopy ≅
    𝟭 (HomotopyCategory (SmallEtaleModules T) (.up ℤ))
  homotopy_id_representatives : ∀ (T : Scheme.{u})
      (P : CochainComplex (SmallEtaleModules T) ℤ),
    ∃ a : (square (𝟙 T)).ordinaryPullbackComplex.obj P ⟶ P,
      (∀ n : ℤ, a.f n = (ordinary_left_id T).hom.app (P.X n)) ∧
      (homotopy_id T).hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        (HomotopyCategory.quotient _ (.up ℤ)).map a
  derived_id : ∀ T : Scheme.{u}, (square (𝟙 T)).pullback ≅
    𝟭 (DerivedCategory (SmallEtaleModules T))
  derived_id_normalized : ∀ (T : Scheme.{u})
      (P : HomotopyCategory (SmallEtaleModules T) (.up ℤ)),
    (derived_id T).hom.app (DerivedCategory.Qh.{w}.obj P) =
      (square (𝟙 T)).pullback_counit.app P ≫
        DerivedCategory.Qh.{w}.map ((homotopy_id T).hom.app P)
  zariski_id : ∀ T : Scheme.{u}, AlgebraicGeometry.derivedPullback (𝟙 T) ≅
    𝟭 (schemeDerivedCategory T)
  zariski_id_normalized : ∀ (T : Scheme.{u})
      (P : HomotopyCategory (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (.up ℤ)),
    (zariski_id T).hom.app (DerivedCategory.Qh.{w}.obj P) =
      (square (𝟙 T)).zariski_counit.app P ≫
        DerivedCategory.Qh.{w}.map
          ((NatTrans.mapHomotopyCategory
            (Adjunction.leftAdjointIdIso
              (Classical.choose (exists_tensorPullbackAdjunction (𝟙 T)))
              (pushforwardId T)).hom (.up ℤ)).app P ≫
          (Functor.mapHomotopyCategoryIdIso T.Modules (.up ℤ)).hom.app P)
  comparison_id : ∀ (T : Scheme.{u}) (K : schemeDerivedCategory T),
      schemeDerivedQCohProperty T K →
    (square (𝟙 T)).comparison.hom.app K ≫
        (derived_id T).hom.app ((data T).extension.obj K) =
      (data T).extension.map ((zariski_id T).hom.app K)

/-- Exact faithful tensor extension induces the unbounded quasi-coherent derived
adjoint equivalence, with canonical pullback, qcqs direct-image and coherent unit maps.

Source: Stacks Project, spaces-perfect.tex, Tags 08H8, 071Q, 08GH; descent.tex 03FH
(blueprint: lem-sfb-derived-etale-zariski-equivalence).

The `data` field states the equivalence in adjoint form: both functors preserve the
full subcategories and the specified derived unit and counit are invertible there.
The `square` fields state the natural pullback isomorphism, its representative equation,
and invertibility of its counit mate for qcqs direct images. The system fields impose
identity and composition compatibility with the normalized tensor comparisons.

Proof, following the DAG:
1. Start with a short exact sequence of arbitrary Zariski modules. At $x\in T$, its stalk
sequence is exact by [lem-weil-pbc-module-stalk-exact]. By [lem-sfb-etale-zariski-module-
geometric-stalk], the geometric stalk of its termwise $\epsilon_T^*$ image is the tensor of this
stalk sequence with $R^{\mathrm{sh}}$ over $R=\mathcal O_{T,x}$. This tensor sequence is exact by
[lem-sc-strict-henselization-faithfully-flat] and [def-weil-pbc-faithfully-flat-ring-map]. To
conclude sheaf exactness, forget module structure using [lem-weil-pbc-module-sheaves-colimits-
forgetful]. By [prop-weil-pbc-geometric-stalks-exact], the geometric stalk of the homology sheaf
of the image sequence is the homology of its stalk sequence, hence zero. By [lemma-weil-pbc-
geometric-stalk-conservative], the map from that homology sheaf to zero is an isomorphism.
Faithful exact forgetting then says its module homology is zero as well. This applies at each
position, so $\epsilon_T^*$ is exact on all modules.

2. If $\epsilon_T^*M=0$, [lem-sfb-etale-zariski-module-geometric-stalk] gives
$M_x\otimes_RR^{\mathrm{sh}}=0$. Every $x$ admits a geometric lift by choosing an algebraic
closure of its residue field [def-weil-algebraic-closure]. Faithful flatness [lem-sc-strict-
henselization-faithfully-flat, def-weil-pbc-faithfully-flat-ring-map], applied to $0\to M_x\to0$,
implies $M_x=0$. The exactness test [lem-weil-pbc-module-stalk-exact](5), applied to $0\to
M\to0$, gives $M=0$. If $\epsilon_T^*u=0$, exactness from step 1 gives
$\epsilon_T^*(\operatorname{im}u)=\operatorname{im}(\epsilon_T^*u)=0$, so $\operatorname{im}u=0$
and $u=0$. Apply this to differences of maps to obtain faithfulness.

3. Use the canonical unbounded derived adjunction $\epsilon_T^*\dashv R\epsilon_{T,*}$ of [lem-
weil-pbc-ringed-projection-mate-exact]; here $L\epsilon_T^*=\epsilon_T^*$ because step 1 shows
exactness. The ordinary QCoh equivalence [lem-trf-scheme-zariski-etale-quasi-coherent-
equivalence] identifies tensor pullback with associated etale modules and restriction with its
inverse, with their ordinary unit and counit. Thus $H^q(\epsilon_T^*F)=\epsilon_T^*H^q(F)$ is
quasi-coherent whenever $H^q(F)$ is. This defines the left functor on the desired full
subcategories, without imposing quasi-coherence on terms of a representative.

4. Let $E\in D_{\mathrm{QCoh}}(\mathcal O_{T,\mathrm{et}})$ and write $N^q=H^q(E)$. The affine
etale objects form a covering basis: cover the source scheme of any etale object by affine opens,
using [lem-weil-pbc-affine-opens-basis]. On an affine object $u:U\to T$, $N^q|_U$ is the etale
extension of a quasi-coherent Zariski module, by [def-trf-space-quasi-coherent-module, lem-trf-
scheme-zariski-etale-quasi-coherent-equivalence]. The localized site is $U_{\mathrm{et}}$ by
[lem-weil-pbc-etale-site-localization-open]. Therefore [lem-sc-etale-affine-qcoherent] gives
vanishing of its positive abelian cohomology; [lem-pe-ringed-site-derived-evaluation-slice] gives
the identical vanishing for module-derived evaluation. All sites are small, and enough injectives
follows from [prop-pur-kinjective-resolutions-exist]. Apply [lem-sfb-ringed-site-acyclic-basis-
cohomology] to obtain $H^q(R\Gamma(U,E))\cong N^q(U)$, naturally in $E$ and in affine etale $U$.
No lower bound on $E$ has been used.

5. Choose $E\to I$ K-injective by [prop-pur-kinjective-resolutions-exist]. By [def-pur-
kinjective-complex] and step 1, $\epsilon_{T,*}I$ is K-injective: a map from acyclic $A$ to it is
adjoint, including homotopies, to a map $\epsilon_T^*A\to I$, hence is null-homotopic. It
represents $R\epsilon_{T,*}E$. On an affine open $W$, its section complex is $I(W)$, since
$\epsilon_{T,*}$ is restriction. The module presheaf homology is consequently $W\mapsto
H^q(I(W))$. Exact module sheafification [lem-weil-pbc-module-presheaf-sheafification-exact]
identifies its sheafification with $H^q(\epsilon_{T,*}I)$. Step 4 identifies this presheaf on the
affine-open basis with $W\mapsto N^q(W)$. These identifications commute with restriction.
Sheafifying therefore gives $$H^q(R\epsilon_{T,*}E)\cong\epsilon_{T,*}N^q.$$ The right side is
quasi-coherent by [lem-trf-scheme-zariski-etale-quasi-coherent-equivalence]. Thus the right
derived functor also restricts to the asserted full subcategory.

6. Under step 5 and exact pullback, the cohomology of the canonical derived counit is the
ordinary counit $$\epsilon_T^*\epsilon_{T,*}N^q\longrightarrow N^q.$$ Indeed the step-4
comparison is the canonical edge map: on the affine basis a class in $H^q(I(U))$ maps to its
section in $H^q(E)(U)$, and counit evaluation applies the same restriction and scalar
multiplication as the ordinary module adjunction. This follows on local cycle representatives and
respects boundaries and restriction. The counit is an isomorphism by [lem-trf-scheme-zariski-
etale-quasi-coherent-equivalence]. Hence the derived counit is a quasi-isomorphism in every
degree, and therefore an isomorphism. For the derived unit $\eta_F:F\to
R\epsilon_{T,*}\epsilon_T^*F$, the triangle identity says its image under $\epsilon_T^*$ is
inverse to that counit. Step 2 and exactness imply that $\epsilon_T^*$ reflects zero cohomology
(apply zero detection to each $H^q$), hence reflects quasi-isomorphisms. Thus $\eta_F$ is also an
isomorphism. The specified adjunction, restricted using steps 3 and 5, now supplies the
equivalence with precisely its canonical unit and counit.

7. For $h:T'\to T$, [lem-trf-zariski-etale-functor-comparison-square] identifies
$\epsilon_{T,*}h_{\mathrm{et},*}$ with $h_*\epsilon_{T',*}$, including structural ring actions:
on an open $W\subseteq T$, both give $G(h^{-1}W)$ with the same action. This is the ring-
compatible square of topoi of 08GH. Apply the composition and 2-isomorphism comparisons of [lem-
sfb-ringed-derived-monoidal-comparisons] to its two composites. They give
$$\epsilon_{T'}^*Lh^*\cong L( h\epsilon_{T'})^*\cong L(\epsilon_T h_{\mathrm{et}})^*\cong
Lh_{\mathrm{et}}^*\epsilon_T^*.$$ Here $L\epsilon^*=\epsilon^*$ by exactness in steps 1–2. The
comparison is computed on K-flat complexes with flat terms, whose pullbacks remain K-flat with
flat terms by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Thus it is the derived
comparison of the specified square, with the stated iterated-scalar-extension representative, and
is natural on derived objects. The Zariski $Lh^*$ preserves quasi-coherent cohomology: [lem-pc-
derived-pullback-qcoh-component] proves this on every affine source chart mapping into an affine
target chart, and these charts cover $T'$. Step 6 and the comparison then show preservation on
the etale side as well.

8. Suppose $h:T'\to T$ is qcqs. Zariski $Rh_*$ preserves quasi-coherent cohomology by [lem-pc-
derived-direct-image-preserves-qcoh]. On the etale side, restrict to an affine open $W\subseteq
T$ and set $V=h^{-1}W$. By [lem-weil-pbc-qcqs-morphism-permanence], $V$ is qcqs, since $h$ is
qcqs and $W$ is affine. The preservation clause of [lem-sfb-space-derived-pushforward-coproducts]
applies to $V\to W$, as a map between qcqs representable algebraic spaces over $W$. By [lem-sfb-
space-derived-etale-chart-calculus], restriction of $Rh_{\mathrm{et},*}$ to $W$ is
$R(h|_V)_{\mathrm{et},*}$ and quasi-coherence of cohomology is local on the target. Its
preservation on all such $W$ proves preservation for $h_{\mathrm{et}}$. This uses no global
quasi-compactness assumption on $T$.

9. The ring-compatible square in step 7, together with the derived composition and 2-isomorphism
comparisons of [lem-sfb-ringed-derived-monoidal-comparisons], gives
$$\Psi:R\epsilon_{T,*}Rh_{\mathrm{et},*}\xrightarrow{\sim}Rh_*R\epsilon_{T',*}.$$ For $F\in
D_{\mathrm{QCoh}}(\mathcal O_{T'})$, define the comparison as the composite $$\epsilon_T^*Rh_*F\x
rightarrow{\epsilon_T^*Rh_*\eta_F}\epsilon_T^*Rh_*R\epsilon_{T',*}\epsilon_{T'}^*F\xrightarrow{\e
psilon_T^*\Psi^{-
1}}\epsilon_T^*R\epsilon_{T,*}Rh_{\mathrm{et},*}\epsilon_{T'}^*F\xrightarrow{\varepsilon}Rh_{\mat
hrm{et},*}\epsilon_{T'}^*F.$$ Step 6 makes the first arrow invertible, the middle arrow is the
composition comparison, and steps 6 and 8 make the final counit invertible. Thus this is a
natural isomorphism. The cited composition comparisons identify the specified composite
adjunctions, so the displayed unit-composition-counit formula is the canonical comparison for the
given square. This proves the qcqs direct-image clause without using [lem-sfb-scheme-derived-
etale-qcoh-comparison], whose newly landed proof depends on this item.

10. Check the remaining normalization on the K-flat representatives allowed in step 7. By [lem-
sfb-ringed-derived-monoidal-comparisons], all comparisons there come from ordinary pullback
composition and preserve the tensor unit. Locally, ordinary composition contracts $c\otimes
b\otimes m$ to $c\,h^{\sharp}(b)\otimes m$. For three scalar extensions, either parenthesization
sends $d\otimes c\otimes b\otimes m$ to $d\,k^{\sharp}(c)\,(kh)^{\sharp}(b)\otimes m$, by
associativity and the ring-map identity. Inserting an identity extension sends $1\otimes m$ to
$m$; the inverse inserts $1$. These formulas are compatible with restriction and the balancing
relations, so give equal sheaf maps and equal maps of complexes. Localizing gives the identity
and composition compatibilities for step 7 on all derived objects. For the structure module the
same formula is scalar multiplication, and it takes every scalar insertion $m\mapsto1\otimes m$
to that of the composite. Consequently the comparison identifies the prescribed structure modules
and scalar-insertion maps.
-/
theorem derived_etale_zariski_equivalence :
    Nonempty (DerivedEtaleZariskiSystem.{u, w}) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
