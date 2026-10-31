/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedGeneralizedLocalizationTest
import all WeilConjectures.CategoryTheory.ProperBaseChange.ElementRestrictionHom
import WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalization
import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
import WeilConjectures.CategoryTheory.NativeRingedRestrictionSheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.CategoryTheory.NativeRingedRestrictionDerivedHom
import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Native.NativeRingedRestrictionSlicesSupplement
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derived_zero_iff_slices
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (N : PresentationDerived R) :
    IsZero N ↔ ∀ U : C,
      let := HasDerivedCategory.standard (PresentationModules R)
      let := HasDerivedCategory.standard
        (SheafOfModules.{u} ((localCoefficientRings R).over U))
      IsZero ((Functor.mapDerivedCategory
        (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U)).obj N) := by
  let := HasDerivedCategory.standard (PresentationModules R)
  let (U : C) : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((localCoefficientRings R).over U)) :=
    HasDerivedCategory.standard _
  constructor
  · intro h U
    exact Functor.map_isZero _ h
  · intro h
    apply (DerivedCategory.isZero_iff N).mpr
    intro n
    let M := (DerivedCategory.homologyFunctor (PresentationModules R) n).obj N
    apply (IsZero.iff_id_eq_zero M).mpr
    ext U x
    have hz := (DerivedCategory.homologyFunctor _ n).map_isZero (h U.unop)
    have e := (Functor.mapDerivedCategoryHomologyFunctorIso
      (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U.unop) n).app N
    have hm : IsZero ((SheafOfModules.overFunctor.{u}
        (localCoefficientRings R) U.unop).obj M) := hz.of_iso e
    have hv := ((SheafOfModules.forget _) ⋙
      PresheafOfModules.evaluation _ (op (Over.mk (𝟙 U.unop)))).map_isZero hm
    exact (ModuleCat.isZero_iff_subsingleton.mp hv).elim _ _

private instance elementSliceDense
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J (Type u)) (X : A.obj.Elementsᵒᵖ) :
    (Over.post (X := X) (elementProjection A)).IsDenseSubsite
      ((elementTopology A).over X) (J.over ((elementProjection A).obj X)) := by
  let := projectionSlices A X
  refine { functorPushforward_mem_iff := ?_ }
  intro Y T
  rw [GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_functorPushforward_post, GrothendieckTopology.mem_over_iff]
  change (Sieve.overEquiv Y T).functorPushforward (elementProjection A) ∈
    J ((elementProjection A).obj Y.left) ↔ _
  exact (element_cover_iff A (Sieve.overEquiv Y T)).symm

private theorem element_test_comparison
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))
    (a : A ⟶ (presentationForget R).obj (SheafOfModules.unit (localCoefficientRings R)))
    (N : PresentationDerived R) (X : A.obj.Elementsᵒᵖ) :
    let := HasDerivedCategory.standard (PresentationModules R)
    let S := presentationElementRing R A
    let := HasDerivedCategory.standard (PresentationModules S)
    let := HasDerivedCategory.standard
      (SheafOfModules.{u} ((localCoefficientRings S).over X))
    let U := (elementProjection A).obj X
    let := HasDerivedCategory.standard (PresentationModules (R.over U))
    let B := SheafOfModules.overFunctor.{u} (localCoefficientRings S) X
    let P := Over.post (X := X) (elementProjection A)
    let := projectionSlices A X
    let : P.IsDenseSubsite ((elementTopology A).over X) (J.over U) := elementSliceDense A X
    let F := NativeRestriction.restrictModules.{u, u, u, u, u}
      (K := (elementTopology A).over X) P (R.over U)
    let : F.IsEquivalence := NativeRestriction.globalModulesEquivalence.{u, u, u, u, u}
      (K := (elementTopology A).over X) P (R.over U)
    let := HasDerivedCategory.standard
      (NativeRestriction.NativeModules.{u} (NativeRestriction.restrictedCommRing.{u, u, u, u, u}
        (K := (elementTopology A).over X) P (R.over U)))
    Nonempty (B.mapDerivedCategory.obj (presentationGeneralizedTest R A a N) ≅
      F.mapDerivedCategory.obj
        ((derivedInternalHom (J.over U) (R.over U)).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj
            (ringedSectionLocalization (R.over U)
              (ringedSliceSection R U (a.hom.app (op U) X.unop.2)))),
            (ringedDerivedRestriction R U).obj N))) := by
  let := HasDerivedCategory.standard (PresentationModules R)
  let S := presentationElementRing R A
  let := HasDerivedCategory.standard (PresentationModules S)
  let (Y : A.obj.Elementsᵒᵖ) : HasDerivedCategory.{u + 1} (PresentationModules (S.over Y)) :=
    HasDerivedCategory.standard _
  let (Y : A.obj.Elementsᵒᵖ) : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((localCoefficientRings S).over Y)) :=
    HasDerivedCategory.standard _
  let U := (elementProjection A).obj X
  let := HasDerivedCategory.standard (PresentationModules (R.over U))
  let B := SheafOfModules.overFunctor.{u} (localCoefficientRings S) X
  let : B.Additive := ringedSite_overFunctor_additive (elementTopology A) S X
  let : PreservesFiniteLimits B := ringedSite_overFunctor_limits (elementTopology A) S X
  let : PreservesFiniteColimits B := ringedSite_overFunctor_colimits (elementTopology A) S X
  let P := Over.post (X := X) (elementProjection A)
  let := projectionSlices A X
  let : P.IsDenseSubsite ((elementTopology A).over X) (J.over U) := elementSliceDense A X
  let F := NativeRestriction.restrictModules.{u, u, u, u, u}
    (K := (elementTopology A).over X) P (R.over U)
  let : F.IsEquivalence := NativeRestriction.globalModulesEquivalence.{u, u, u, u, u}
    (K := (elementTopology A).over X) P (R.over U)
  let : F.Additive := NativeRestriction.restrictModules_additive.{u, u, u, u, u}
    (K := (elementTopology A).over X) P (R.over U)
  let := HasDerivedCategory.standard
    (NativeRestriction.NativeModules.{u} (NativeRestriction.restrictedCommRing.{u, u, u, u, u}
      (K := (elementTopology A).over X) P (R.over U)))
  let E : PresentationModules R ⥤ PresentationModules S :=
    elementModulePullback.{u, u} (localCoefficientRings R) A
  let : E.Additive := presentationElementRestriction_additive R A
  let : PreservesFiniteLimits E := (presentationElementRestriction_exact R A).1
  let : PreservesFiniteColimits E := (presentationElementRestriction_exact R A).2.1
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} ((localCoefficientRings R).over U))
  let V := SheafOfModules.overFunctor.{u} (localCoefficientRings R) U
  let : V.Additive := ringedSite_overFunctor_additive J R U
  let : PreservesFiniteLimits V := ringedSite_overFunctor_limits J R U
  let : PreservesFiniteColimits V := ringedSite_overFunctor_colimits J R U
  let s := presentationGeneralizedSection R A a
  let t := ringedSliceSection R U (a.hom.app (op U) X.unop.2)
  let L := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSectionLocalizationOfUniverses S s)
  obtain ⟨e, _, _⟩ := ringedInternalHom_restriction (elementTopology A) S
  obtain ⟨q⟩ := NativeRestriction.derivedHomRestriction.{u, u, u, u, u, u + 1, u + 1}
    (K := (elementTopology A).over X) P (R.over U) (fun Y ↦ inferInstance)
    ((DerivedCategory.singleFunctor _ 0).obj (ringedSectionLocalization (R.over U) t))
    (V.mapDerivedCategory.obj N)
  have square : V ⋙ F ≅ E ⋙ B := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · exact (SheafOfModules.fullyFaithfulForget _).preimageIso
        (PresheafOfModules.isoMk (fun Y ↦ Iso.refl _) (by intros; ext x; rfl))
    · intro M M' f
      ext Y x
      rfl
  let dsquare := (Functor.mapDerivedCategoryCompIso V F).symm ≪≫
    Functor.mapDerivedCategoryNatIso square ≪≫ Functor.mapDerivedCategoryCompIso E B
  have en : F.mapDerivedCategory.obj (V.mapDerivedCategory.obj N) ≅
      B.mapDerivedCategory.obj (E.mapDerivedCategory.obj N) := dsquare.app N
  obtain ⟨lb⟩ := NativeRestriction.localizationRestriction.{u, u, u, u, u}
    (K := (elementTopology A).over X) (Over.forget X) S s
  obtain ⟨lf⟩ := NativeRestriction.localizationRestriction.{u, u, u, u, u}
    (K := (elementTopology A).over X) P (R.over U) t
  have sl : NativeRestriction.restrictedSection.{u, u, u, u, u}
      (K := (elementTopology A).over X) (Over.forget X) S s =
      NativeRestriction.restrictedSection.{u, u, u, u, u}
        (K := (elementTopology A).over X) P (R.over U) t := by
    ext Y
    have hn := NatTrans.naturality_apply a.hom Y.unop.hom.unop.val X.unop.2
    have hp := Y.unop.hom.unop.property
    change a.hom.app _ (A.obj.map Y.unop.hom.unop.val X.unop.2) =
      R.obj.map Y.unop.hom.unop.val (a.hom.app _ X.unop.2) at hn
    exact (congrArg (a.hom.app _) hp).symm.trans hn
  have loc : B.obj (ringedSectionLocalizationOfUniverses S s) ≅
      F.obj (ringedSectionLocalizationOfUniverses (R.over U) t) := by
    exact ((NativeRestriction.restrictModules_standardIso.{u, u, u, u, u}
      (K := (elementTopology A).over X) (Over.forget X) S).app _).symm ≪≫
      lb ≪≫ eqToIso (congrArg
        (ringedSectionLocalizationOfUniverses (S.over X)) sl) ≪≫ lf.symm
  have el : B.mapDerivedCategory.obj L ≅ F.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj (ringedSectionLocalization (R.over U) t)) :=
    (B.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso loc ≪≫
        ((F.mapDerivedCategorySingleFunctor 0).app _).symm
  refine ⟨(e X).app (op L, E.mapDerivedCategory.obj N) ≪≫ ?_ ≪≫ q.symm⟩
  exact (derivedInternalHom ((elementTopology A).over X) (S.over X)).mapIso
    (Iso.prod el.symm.op en.symm)

private theorem reflects_derived_zero
    {B D : Type*} [Category B] [Category D] [Abelian B] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] (M : DerivedCategory B) (h : IsZero (F.mapDerivedCategory.obj M)) :
    IsZero M := by
  apply (DerivedCategory.isZero_iff M).mpr
  intro n
  exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
    ((DerivedCategory.homologyFunctor _ n).map_isZero h)

/-- Vanishing of a generalized localization test is detected on all element slices.
Source: Stacks Project, sites-modules.tex, Tags 04IE and 04J4, and sites-cohomology.tex, Tag 08JB.
(blueprint: lem-weil-pbc-generalized-completeness-criterion).
Proof: restriction to each element slice and sectionwise detection. The nested
universe-sensitive derived comparison is split off here. -/
theorem presentationGeneralizedTest_isZero_iff
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))
    (a : A ⟶ (presentationForget R).obj (SheafOfModules.unit (localCoefficientRings R)))
    (N : PresentationDerived R) :
    IsZero (presentationGeneralizedTest R A a N) ↔
      ∀ (U : C) (x : A.obj.obj (op U)),
        let := HasDerivedCategory.standard (PresentationModules R)
        let := HasDerivedCategory.standard (PresentationModules (R.over U))
        IsZero ((derivedInternalHom (J.over U) (R.over U)).obj
          (op ((DerivedCategory.singleFunctor _ 0).obj
            (ringedSectionLocalization (R.over U)
              (ringedSliceSection R U (a.hom.app (op U) x)))),
            (ringedDerivedRestriction R U).obj N)) := by
  let := HasDerivedCategory.standard (PresentationModules R)
  let (U : C) : HasDerivedCategory.{u + 1} (PresentationModules (R.over U)) :=
    HasDerivedCategory.standard _
  let S := presentationElementRing R A
  let := HasDerivedCategory.standard (PresentationModules S)
  let (X : A.obj.Elementsᵒᵖ) : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((localCoefficientRings S).over X)) :=
    HasDerivedCategory.standard _
  let test (U : C) (x : A.obj.obj (op U)) : PresentationDerived (R.over U) :=
    (derivedInternalHom (J.over U) (R.over U)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization (R.over U)
          (ringedSliceSection R U (a.hom.app (op U) x)))),
        (ringedDerivedRestriction R U).obj N)
  rw [derived_zero_iff_slices S]
  have hx (X : A.obj.Elementsᵒᵖ) :
      IsZero ((Functor.mapDerivedCategory
        (SheafOfModules.overFunctor.{u} (localCoefficientRings S) X)).obj
          (presentationGeneralizedTest R A a N)) ↔
        IsZero (test ((elementProjection A).obj X) X.unop.2) := by
    let U := (elementProjection A).obj X
    let P := Over.post (X := X) (elementProjection A)
    let := projectionSlices A X
    let : P.IsDenseSubsite ((elementTopology A).over X) (J.over U) := elementSliceDense A X
    let F := NativeRestriction.restrictModules.{u, u, u, u, u}
      (K := (elementTopology A).over X) P (R.over U)
    let : F.IsEquivalence := NativeRestriction.globalModulesEquivalence.{u, u, u, u, u}
      (K := (elementTopology A).over X) P (R.over U)
    let : F.Additive := NativeRestriction.restrictModules_additive.{u, u, u, u, u}
      (K := (elementTopology A).over X) P (R.over U)
    let := HasDerivedCategory.standard
      (NativeRestriction.NativeModules.{u} (NativeRestriction.restrictedCommRing.{u, u, u, u, u}
        (K := (elementTopology A).over X) P (R.over U)))
    obtain ⟨e⟩ := element_test_comparison R A a N X
    constructor
    · intro h
      exact reflects_derived_zero F _ (h.of_iso e.symm)
    · intro h
      exact (F.mapDerivedCategory.map_isZero h).of_iso e
  constructor
  · intro h U x
    exact (hx (op (A.obj.elementsMk (op U) x))).mp (h _)
  · intro h X
    exact (hx X).mpr (h _ X.unop.2)
/-- Ordinary local completeness is equivalent to all generalized ideal tests.
Source: Stacks Project, algebraization.tex, Tags 0999 and 099J.
(blueprint: lem-weil-pbc-generalized-completeness-criterion).
Proof: apply the preceding slice criterion to every generalized ideal section and
use the identity section of the underlying module. -/
theorem presentation_complete_iff_generalized_tests
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (N : PresentationDerived R)
    (I : PresentationModules R)
    (ι : I ⟶ SheafOfModules.unit (localCoefficientRings R)) :
    presentationComplete R I ι N ↔
      ∀ (A : Sheaf J (Type u)) (b : A ⟶ (presentationForget R).obj I),
        IsZero (presentationGeneralizedTest R A (b ≫ (presentationForget R).map ι) N) := by
  let := HasDerivedCategory.standard (PresentationModules R)
  constructor
  · intro h A b
    rw [presentationGeneralizedTest_isZero_iff]
    intro U x
    exact h U (ι.val.app (op U) (b.hom.app (op U) x))
      ⟨b.hom.app (op U) x, rfl⟩
  · intro h U f hf
    obtain ⟨y, rfl⟩ := hf
    have hz := (presentationGeneralizedTest_isZero_iff R
      ((presentationForget R).obj I) ((presentationForget R).map ι) N).mp (by
        simpa only [Category.id_comp] using
          h ((presentationForget R).obj I) (𝟙 _))
    exact hz U y
end CategoryTheory
