/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedAmbient
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.Site.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
import all WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedAmbient
import all WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedTensorProjection
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedDetection
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.SixFunctors.CoefficientClosedStructure.ClosedTensorDualAdjunction
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleGenericStratumMate
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement

/-! The canonical comparison underlying the pro-etale stratum internal-Hom map. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

private theorem constantClosedData
    (A : Type u) [CommRing A] [Finite A]
    {X Z V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (k : V ⟶ X) [IsOpenImmersion k] [QuasiCompact k]
    (h : Set.range k.base = (Set.range i.base)ᶜ) :
    PreservesFiniteColimits (sfConstantModuleDirectImage i A) ∧
      IsIso (sfConstantModuleAdjunction i A).counit ∧
      (∀ N, IsZero ((sfConstantModulePullback k A).obj
        ((sfConstantModuleDirectImage i A).obj N))) ∧
      JointlyReflectIsomorphisms (pairFunctor
        (sfConstantModulePullback i A) (sfConstantModulePullback k A)) := by
  let R := proEtaleConstantRing X A
  let Ri := proEtaleConstantRing Z A
  let Rk := proEtaleConstantRing V A
  let ci := sfConstantCoefficientIso i A
  let ck := sfConstantCoefficientIso k A
  let W := ProEt.mk k
  have : IsOpenImmersion W.hom := ‹IsOpenImmersion k›
  have : QuasiCompact W.hom := ‹QuasiCompact k›
  obtain ⟨q, ⟨e⟩, ai, ak, hc, _, hz, _, _, _, hl, hr, _, _⟩ :=
    proEtale_ringed_open_closed i W h R
  have : IsIso ai.counit := NatIso.isIso_of_isIso_app _
  have := ai.fullyFaithfulROfIsIsoCounit.full
  have := ai.fullyFaithfulROfIsIsoCounit.faithful
  let ei := coefficientTransport i R Ri ci
  let ek := coefficientTransport k R Rk ck
  let di := directImageComparison i R Ri ci
  let lk := pullbackComparison k R Rk ck
    (ringedInverseImageAdjunction k R)
  have : (sfConstantModuleDirectImage i A).Full := Functor.Full.of_iso di.symm
  have : (sfConstantModuleDirectImage i A).Faithful := Functor.Faithful.of_iso di.symm
  have hcol : PreservesFiniteColimits (sfConstantModuleDirectImage i A) :=
    preservesFiniteColimits_of_natIso di.symm
  refine ⟨hcol, inferInstance, ?_, ?_⟩
  · intro N
    have h0 : IsZero ((proEtaleModuleInverseImage k R).obj
        ((proEtaleRingedDirectImage i R).obj (ei.functor.obj N))) :=
      IsZero.of_full_of_faithful_of_isZero q.functor _
        ((hz (ei.functor.obj N)).of_iso (e.app _))
    exact (ek.inverse.map_isZero h0).of_iso
      (lk.app _ ≪≫ ek.inverse.mapIso
        ((proEtaleModuleInverseImage k R).mapIso (di.app N)))
  · refine jointlyReflectIsomorphisms_pairFunctor _ _ ?_
    intro M N f hi hk
    have hzker : IsZero (kernel f) := proEtaleRingModule_isZero_of_open_closed
      i k h R Ri Rk ci ck _
      ((isZero_kernel_of_mono _).of_iso (PreservesKernel.iso _ f))
      ((isZero_kernel_of_mono _).of_iso (PreservesKernel.iso _ f))
    have hzcoker : IsZero (cokernel f) := proEtaleRingModule_isZero_of_open_closed
      i k h R Ri Rk ci ck _
      ((isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ f))
      ((isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ f))
    have : Mono f := Preadditive.mono_of_isZero_kernel _ hzker
    have : Epi f := Preadditive.epi_of_isZero_cokernel _ hzcoker
    exact isIso_of_mono_of_epi f

private theorem constantPullTensor
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty ((nativeModel Y (proEtaleConstantRing Y A)).tensor ⋙
        (sfConstantModulePullback f A).mapDerivedCategory ≅
      ((sfConstantModulePullback f A).mapDerivedCategory).prod
        (sfConstantModulePullback f A).mapDerivedCategory ⋙
          (nativeModel X (proEtaleConstantRing X A)).tensor) := by
  obtain ⟨a, _, _⟩ := (proEtaleCanonicalTensorPullback f
    (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (sfConstantCoefficientIso f A)
    (nativeModel Y (proEtaleConstantRing Y A))
    (nativeModel X (proEtaleConstantRing X A))).2
  exact ⟨a⟩

private theorem constantClosedProjection
    (A : Type u) [CommRing A] [Finite A]
    {X Z V : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (k : V ⟶ X) [IsOpenImmersion k] [QuasiCompact k]
    (h : Set.range k.base = (Set.range i.base)ᶜ) :
    Nonempty (((sfConstantModuleDirectImage i A).rightDerivedFunctor).prod (𝟭 _) ⋙
        (nativeModel X (proEtaleConstantRing X A)).tensor ≅
      (𝟭 _).prod (sfConstantModulePullback i A).mapDerivedCategory ⋙
        (nativeModel Z (proEtaleConstantRing Z A)).tensor ⋙
          (sfConstantModuleDirectImage i A).rightDerivedFunctor) := by
  let pi := sfConstantModulePullback i A
  let qi := sfConstantModuleDirectImage i A
  let pk := sfConstantModulePullback k A
  obtain ⟨hcol, hc, hz, hd⟩ := constantClosedData A i k h
  have : PreservesFiniteColimits qi := hcol
  have : IsIso (sfConstantModuleAdjunction i A).counit := hc
  have : PreservesLimitsOfSize.{0, 0} qi :=
    (sfConstantModuleAdjunction i A).rightAdjoint_preservesLimits
  let ad := exactDerivedAdjunction (sfConstantModuleAdjunction i A)
  have : ∀ N, IsIso (ad.counit.app N) :=
    fun N ↦ exactDerivedAdjunction_counit_isIso (sfConstantModuleAdjunction i A) N
  have : IsIso ad.counit := NatIso.isIso_of_isIso_app _
  have hdet := Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory pi pk hd
  have hzd (N : proEtaleDerivedCategory Z A) :
      IsZero (pk.mapDerivedCategory.obj (qi.mapDerivedCategory.obj N)) := by
    apply Functor.isZero_mapDerivedCategory_obj
    intro n
    exact (hz ((DerivedCategory.homologyFunctor _ n).obj N)).of_iso
      (pk.mapIso ((qi.mapDerivedCategoryHomologyFunctorIso n).app N)).symm
  obtain ⟨ei⟩ := constantPullTensor A i
  obtain ⟨ek⟩ := constantPullTensor A k
  let tX := (nativeModel X (proEtaleConstantRing X A)).tensor
  let tZ := (nativeModel Z (proEtaleConstantRing Z A)).tensor
  have hu (N : proEtaleDerivedCategory Z A) (K : proEtaleDerivedCategory X A) :
      IsIso (ad.unit.app (tX.obj (qi.mapDerivedCategory.obj N, K))) := by
    apply CategoryTheory.supportedUnit pi.mapDerivedCategory qi.mapDerivedCategory
      pk.mapDerivedCategory ad
      (fun f hi hk ↦ hdet.isIso_of_pairFunctor f hi hk) hzd
    let := RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2}
      (ProEt.topology V) (proEtaleConstantRing V A)
    obtain ⟨⟨m, ac, ev⟩, hm, _, _⟩ :=
      RingedDerivedNative.closedAdjunction.{u + 1, u, 0, u + 2}
        (ProEt.topology V) (proEtaleConstantRing V A)
    dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hm
    subst m
    have := (ac (pk.mapDerivedCategory.obj K)).isLeftAdjoint
    have h0 : IsZero ((nativeModel V (proEtaleConstantRing V A)).tensor.obj
        (pk.mapDerivedCategory.obj (qi.mapDerivedCategory.obj N),
          pk.mapDerivedCategory.obj K)) :=
      (MonoidalCategory.tensorRight (pk.mapDerivedCategory.obj K)).map_isZero (hzd N)
    exact h0.of_iso (ek.app (qi.mapDerivedCategory.obj N, K))
  obtain ⟨e⟩ := CategoryTheory.projectionOfSupportedUnit
    pi.mapDerivedCategory qi.mapDerivedCategory ad tX tZ ei hu
  let eQ := qi.rightDerivedFunctorIsoMapDerivedCategory
  exact ⟨Functor.isoWhiskerRight (NatIso.prod eQ (Iso.refl (𝟭 _))) tX ≪≫ e ≪≫
    Functor.isoWhiskerLeft ((𝟭 _).prod pi.mapDerivedCategory ⋙ tZ) eQ.symm⟩

private theorem openProjectionOfDetection
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms E]
    (q : D ⥤ C) (p : C ⥤ D) (r : C ⥤ E) (adj : q ⊣ p) [IsIso adj.unit]
    (tc : C × C ⥤ C) (td : D × D ⥤ D)
    (e : tc ⋙ p ≅ p.prod p ⋙ td)
    (detect : ∀ {X Y : C} (f : X ⟶ Y),
      IsIso (p.map f) → IsIso (r.map f) → IsIso f)
    (zero : ∀ N K, IsZero (r.obj (q.obj (td.obj (N, p.obj K)))))
    (zeroTensor : ∀ N K, IsZero (r.obj (tc.obj (q.obj N, K)))) :
    Nonempty (q.prod (𝟭 C) ⋙ tc ≅ (𝟭 D).prod p ⋙ td ⋙ q) := by
  let B := (𝟭 D).prod p ⋙ td
  let F := q.prod (𝟭 C) ⋙ tc
  let a := adj.whiskerRight (D × C)
  let b : (𝟭 D).prod p ≅ q.prod (𝟭 C) ⋙ p.prod p :=
    NatIso.prod (asIso adj.unit) (Iso.refl p)
  let gamma : B ≅ F ⋙ p :=
    Functor.isoWhiskerRight b td ≪≫ Functor.isoWhiskerLeft (q.prod (𝟭 C)) e.symm
  let beta : B ⋙ q ⟶ F := (a.homEquiv B F).symm gamma.hom
  have hcomp (N : D) (K : C) :
      adj.unit.app (B.obj (N, K)) ≫ p.map (beta.app (N, K)) =
        gamma.hom.app (N, K) := by
    have h := (a.homEquiv B F).apply_symm_apply gamma.hom
    rw [Adjunction.homEquiv_unit] at h
    have hh := congrArg (fun z ↦ z.app (N, K)) h
    simpa only [NatTrans.comp_app, a, Adjunction.whiskerRight_unit_app_app,
      Functor.whiskeringRight_obj_map, Functor.whiskerRight_app] using hh
  have hb : ∀ x, IsIso (beta.app x) := by
    intro ⟨N, K⟩
    apply detect
    · have : IsIso (adj.unit.app (B.obj (N, K)) ≫ p.map (beta.app (N, K))) :=
        (hcomp N K) ▸ inferInstance
      exact IsIso.of_isIso_comp_left (adj.unit.app (B.obj (N, K))) _
    · exact ⟨⟨0, (zero N K).eq_of_src _ _, (zeroTensor N K).eq_of_src _ _⟩⟩
  have : IsIso beta := NatIso.isIso_of_isIso_app beta
  exact ⟨(asIso beta).symm⟩

private noncomputable def constantOpenAdjunction
    (A : Type u) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] :
    sfIntrinsicExtensionByZero j A ⊣ sfConstantModulePullback j A :=
  (sfIntrinsicOpenAdjunction A j).ofNatIsoRight (openSquarePullbackModel A j).symm

private theorem constantOpenUnit
    (A : Type u) [CommRing A] [Finite A]
    {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] :
    IsIso (constantOpenAdjunction A j).unit := by
  have : (sfIntrinsicExtensionByZero j A).Full := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : (sfIntrinsicExtensionByZero j A).Faithful := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  infer_instance

private theorem constantOpenZero
    (A : Type u) [CommRing A] [Finite A]
    {V Z X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X)
    (h : Set.range j.base ∩ Set.range i.base = ∅)
    (N : proEtaleRingModules V (proEtaleConstantRing V A)) :
    IsZero ((sfConstantModulePullback i A).obj
      ((sfIntrinsicExtensionByZero j A).obj N)) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let e : sfIntrinsicExtensionByZero j A ⋙ sfConstantModulePullback i A ≅
      sfIntrinsicTransport A
        (ProEtale.openImmersionLowerShriek B j ⋙ ProEtale.upperStar B i) :=
    Functor.isoWhiskerLeft _ (openSquarePullbackModel A i) ≪≫
      (sfIntrinsicTransportComp A _ _).symm
  exact ((sfIntrinsicModuleEquivalence Z A).functor.map_isZero
    (ProEtale.isZero_upperStar_openImmersionLowerShriek B j i h
      ((sfIntrinsicModuleEquivalence V A).inverse.obj N))).of_iso (e.app N)

private theorem constantOpenProjection
    (A : Type u) [CommRing A] [Finite A]
    {V X : Scheme.{u}} [IsNoetherian X]
    (j : V ⟶ X) [IsOpenImmersion j] :
    Nonempty (((sfIntrinsicExtensionByZero j A).mapDerivedCategory).prod (𝟭 _) ⋙
        (nativeModel X (proEtaleConstantRing X A)).tensor ≅
      (𝟭 _).prod (sfConstantModulePullback j A).mapDerivedCategory ⋙
        (nativeModel V (proEtaleConstantRing V A)).tensor ⋙
          (sfIntrinsicExtensionByZero j A).mapDerivedCategory) := by
  let i := j.closedComplement
  let q := sfIntrinsicExtensionByZero j A
  let p := sfConstantModulePullback j A
  let r := sfConstantModulePullback i A
  let adj := constantOpenAdjunction A j
  have : IsIso adj.unit := constantOpenUnit A j
  let ad := exactDerivedAdjunction adj
  have hf := ad.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso q p).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso adj.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso _)
  have := hf.full
  have := hf.faithful
  have : IsIso ad.unit := ad.unit_isIso_of_L_fully_faithful
  obtain ⟨_, _, _, hd⟩ := constantClosedData A i j
    (by rw [Scheme.Hom.range_closedComplement, compl_compl])
  have hdet := Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory r p hd
  have hz (N : proEtaleDerivedCategory V A) :
      IsZero (r.mapDerivedCategory.obj (q.mapDerivedCategory.obj N)) := by
    apply Functor.isZero_mapDerivedCategory_obj
    intro n
    exact (constantOpenZero A j i
      (by rw [Scheme.Hom.range_closedComplement, Set.inter_compl_self])
      ((DerivedCategory.homologyFunctor _ n).obj N)).of_iso
        (r.mapIso ((q.mapDerivedCategoryHomologyFunctorIso n).app N)).symm
  obtain ⟨ej⟩ := constantPullTensor A j
  obtain ⟨ei⟩ := constantPullTensor A i
  apply openProjectionOfDetection q.mapDerivedCategory p.mapDerivedCategory
    r.mapDerivedCategory ad _ _ ej
    (fun f hp hr ↦ hdet.isIso_of_pairFunctor f hr hp)
  · intro N K
    exact hz _
  · intro N K
    let := RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2}
      (ProEt.topology (Arrow.mk i).left) (proEtaleConstantRing (Arrow.mk i).left A)
    obtain ⟨⟨m, ac, ev⟩, hm, _, _⟩ :=
      RingedDerivedNative.closedAdjunction.{u + 1, u, 0, u + 2}
        (ProEt.topology (Arrow.mk i).left) (proEtaleConstantRing (Arrow.mk i).left A)
    dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hm
    subst m
    have := (ac (r.mapDerivedCategory.obj K)).isLeftAdjoint
    have h0 : IsZero
        ((nativeModel (Arrow.mk i).left (proEtaleConstantRing (Arrow.mk i).left A)).tensor.obj
        (r.mapDerivedCategory.obj (q.mapDerivedCategory.obj N),
          r.mapDerivedCategory.obj K)) :=
      (@MonoidalCategory.tensorRight _ _
        (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2}
          (ProEt.topology (Arrow.mk i).left) (proEtaleConstantRing (Arrow.mk i).left A))
        (r.mapDerivedCategory.obj K)).map_isZero (hz N)
    exact h0.of_iso (ei.app (q.mapDerivedCategory.obj N, K))

private noncomputable def closedParametrized
    {C : Type*} [Category* C] {H : Cᵒᵖ × C ⥤ C}
    (S : WeilConjectures.CoefficientClosedStructure H) :
    (@MonoidalCategory.curriedTensor C _ S.monoidal).flip ⊣₂ Functor.curry.obj H := by
  let : MonoidalCategory C := S.monoidal
  refine ParametrizedAdjunction.mk' (fun P ↦ S.adjunction P) ?_
  intro P' P f N M g
  convert S.transpose_source f g using 1 <;>
    simp [WeilConjectures.CoefficientClosedStructure.transpose,
      WeilConjectures.CoefficientClosedStructure.tensor, Functor.curry,
      Functor.curryObj, Functor.flip, curriedTensor, id_tensorHom]

private noncomputable def constantPullComp
    (A : Type u) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X) :
    (sfConstantModulePullback (i ≫ j) A).mapDerivedCategory ≅
      (sfConstantModulePullback j A).mapDerivedCategory ⋙
        (sfConstantModulePullback i A).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso
    (openSquarePullbackModel A (i ≫ j) ≪≫ sfIntrinsicPullbackComp A i j ≪≫
      Functor.isoWhiskerRight (openSquarePullbackModel A j).symm _ ≪≫
      Functor.isoWhiskerLeft _ (openSquarePullbackModel A i).symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private noncomputable def constantStratumPullAdjunction
    (A : Type u) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X) :
    (sfConstantModulePullback j A).mapDerivedCategory ⋙
        (sfConstantModulePullback i A).mapDerivedCategory ⊣
      (sfConstantModuleDirectImage (i ≫ j) A).rightDerivedFunctor :=
  (sfConstantModuleAdjunction (i ≫ j) A).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
    (constantPullComp A i j)

private theorem composeProjection
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (q : E ⥤ D) (f : D ⥤ C) (p : C ⥤ D) (r : D ⥤ E)
    (tc : C × C ⥤ C) (td : D × D ⥤ D) (te : E × E ⥤ E)
    (ef : f.prod (𝟭 C) ⋙ tc ≅ (𝟭 D).prod p ⋙ td ⋙ f)
    (eq : q.prod (𝟭 D) ⋙ td ≅ (𝟭 E).prod r ⋙ te ⋙ q) :
    Nonempty ((q ⋙ f).prod (𝟭 C) ⋙ tc ≅
      (𝟭 E).prod (p ⋙ r) ⋙ te ⋙ q ⋙ f) := by
  let a : q.prod (𝟭 C) ⋙ (𝟭 D).prod p ≅ (𝟭 E).prod p ⋙ q.prod (𝟭 D) := Iso.refl _
  exact ⟨Functor.isoWhiskerLeft (q.prod (𝟭 C)) ef ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight a td) f ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft ((𝟭 E).prod p) eq) f⟩

private theorem homIsoOfTensorProjection
    {C D : Type*} [Category* C] [Category* D]
    {HX : Cᵒᵖ × C ⥤ C} {HS : Dᵒᵖ × D ⥤ D}
    (SX : WeilConjectures.CoefficientClosedStructure HX)
    (SS : WeilConjectures.CoefficientClosedStructure HS)
    (bX : @SymmetricCategory C _ SX.monoidal)
    (bS : @SymmetricCategory D _ SS.monoidal)
    (F : D ⥤ C) (G L : C ⥤ D) (R : D ⥤ C)
    (a : L ⊣ R) (b : F ⊣ G)
    (e : F.prod (𝟭 C) ⋙ SX.tensor ≅ (𝟭 D).prod L ⋙ SS.tensor ⋙ F) :
    Nonempty (F.op.prod (𝟭 C) ⋙ HX ≅ (𝟭 Dᵒᵖ).prod G ⋙ HS ⋙ R) := by
  let : MonoidalCategory C := SX.monoidal
  let : MonoidalCategory D := SS.monoidal
  let : SymmetricCategory C := bX
  let : SymmetricCategory D := bS
  let TX := MonoidalCategory.curriedTensor C
  let TS := MonoidalCategory.curriedTensor D
  let p (T : C) (P : D) : T ⊗ F.obj P ⟶ F.obj (L.obj T ⊗ P) :=
    (β_ T (F.obj P)).hom ≫ e.hom.app (P, T) ≫ F.map (β_ P (L.obj T)).hom
  have hp : ∀ T P, IsIso (p T P) := fun T P ↦ by dsimp [p]; infer_instance
  let := hp
  have hn (T T' : C) (P P' : D) (f : T ⟶ T') (g : P ⟶ P') :
      ((TX.map f).app (F.obj P) ≫ (TX.obj T').map (F.map g)) ≫ p T' P' =
        p T P ≫ F.map ((TS.map (L.map f)).app P ≫ (TS.obj (L.obj T')).map g) := by
    simp only [TX, TS, curriedTensor_map_app, curriedTensor_obj_map,
      ← tensorHom_def]
    have he := e.hom.naturality (X := (P, T)) (Y := (P', T')) (g, f)
    change (F.map g ⊗ₘ f) ≫ e.hom.app (P', T') =
      e.hom.app (P, T) ≫ F.map (g ⊗ₘ L.map f) at he
    dsimp only [p]
    simp only [Category.assoc]
    rw [braiding_naturality_assoc]
    rw [← Category.assoc (F.map g ⊗ₘ f), he]
    simp only [Category.assoc]
    rw [← F.map_comp, braiding_naturality, F.map_comp]
    rfl
  let pi := CategoryTheory.projectionBifunctorIso TX TS F L p hn
  obtain ⟨theta, _⟩ := CategoryTheory.internalHomIsoOfProjection
    (closedParametrized SS) (closedParametrized SX) a b pi
  exact ⟨Functor.isoWhiskerLeft _ (Functor.currying.counitIso.app HX).symm ≪≫
    theta ≪≫ Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _ (Functor.currying.counitIso.app HS)) R⟩

/-- The evaluation-mate comparison for the pro-etale locally closed immersion.

Proof: the ten-step proof of `lem-weil-stratum-ambient-hom`, steps 8--10
(blueprint: lem-weil-stratum-ambient-hom).  Choose K-flat representatives in
both tensor variables and K-injective representatives in the internal-Hom
variable.  The Hom-complex currying map, followed by the open and closed
projection comparisons and the two derived adjunctions, gives a map between
the displayed bifunctors.  The same chain calculation with the inverse
projection comparisons gives a two-sided inverse on every component.  The
construction is natural in the two variables because every comparison used
is natural.  This theorem records the canonical comparison before its final
`NatIso.ofComponents` packaging, and is therefore a strict sub-result of the
ambient internal-Hom assertion.
(blueprint: lem-weil-stratum-ambient-hom-comparison) -/
theorem stratumAmbientHomComparison
    (A : Type u) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} [IsNoetherian X]
    (i : S ⟶ U) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] :
    ∃ α :
      ((((sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
          (sfIntrinsicExtensionByZero j A).mapDerivedCategory).op.prod
          (𝟭 (proEtaleDerivedCategory X A))) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology X) (proEtaleConstantRing X A)) ⟶
        (((𝟭 (proEtaleDerivedCategory S A)ᵒᵖ).prod
          ((sfConstantModulePullback j A).mapDerivedCategory ⋙
            (sfIntrinsicClosedUpperShriek i
              (Scheme.Opens.ι (X := U) (⟨(Set.range i)ᶜ,
                (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩ :
                  U.Opens)) A).rightDerivedFunctor)) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology S) (proEtaleConstantRing S A) ⋙
            (sfConstantModuleDirectImage (i ≫ j) A).rightDerivedFunctor),
      ∀ p, IsIso (α.app p) := by
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : IsNoetherian U := ⟨⟩
  let V : U.Opens := ⟨(Set.range i)ᶜ,
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩
  let k := V.ι
  have hk : Set.range k.base = (Set.range i.base)ᶜ := Scheme.Opens.range_ι V
  obtain ⟨hcol, ⟨ai⟩⟩ := sfIntrinsicClosedAmbientAdjunction A i k
    (by rw [hk]; exact isCompl_compl)
  have : PreservesFiniteColimits (sfConstantModuleDirectImage i A) := hcol
  obtain ⟨ei⟩ := constantClosedProjection A i k hk
  obtain ⟨ej⟩ := constantOpenProjection A j
  let F := (sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory
  let G := (sfConstantModulePullback j A).mapDerivedCategory ⋙
    (sfIntrinsicClosedUpperShriek i k A).rightDerivedFunctor
  let L := (sfConstantModulePullback j A).mapDerivedCategory ⋙
    (sfConstantModulePullback i A).mapDerivedCategory
  let R := (sfConstantModuleDirectImage (i ≫ j) A).rightDerivedFunctor
  let b : F ⊣ G := ai.comp (exactDerivedAdjunction (constantOpenAdjunction A j))
  let a : L ⊣ R := constantStratumPullAdjunction A i j
  obtain ⟨ex⟩ := composeProjection
    (sfConstantModuleDirectImage i A).rightDerivedFunctor
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory
    (sfConstantModulePullback j A).mapDerivedCategory
    (sfConstantModulePullback i A).mapDerivedCategory _ _ _ ej ei
  obtain ⟨⟨mx, ax, nx⟩, hmx, _, _⟩ :=
    RingedDerivedNative.closedAdjunction.{u + 1, u, u, u + 2}
      (ProEt.topology X) (proEtaleConstantRing X A)
  dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hmx
  subst mx
  obtain ⟨⟨ms, ast, ns⟩, hms, _, _⟩ :=
    RingedDerivedNative.closedAdjunction.{u + 1, u, u, u + 2}
      (ProEt.topology S) (proEtaleConstantRing S A)
  dsimp only [WeilConjectures.CoefficientClosedStructure.monoidal] at hms
  subst ms
  let SX : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 2}
        (ProEt.topology X) (proEtaleConstantRing X A)) :=
    ⟨RingedDerivedNative.monoidal _ _, ax, nx⟩
  let SS : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 2}
        (ProEt.topology S) (proEtaleConstantRing S A)) :=
    ⟨RingedDerivedNative.monoidal _ _, ast, ns⟩
  obtain ⟨theta⟩ := homIsoOfTensorProjection SX SS
    (RingedDerivedNative.symmetric _ _) (RingedDerivedNative.symmetric _ _)
    F G L R a b ex
  exact ⟨theta.hom, fun p ↦ inferInstance⟩

end AlgebraicGeometry.ProEtale
