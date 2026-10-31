/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PbcQbarCompletedPullback
public import WeilConjectures.AlgebraicGeometry.PbcActualRingedExchange
public import WeilConjectures.AlgebraicGeometry.WeilCompletedTensorReflector
public import WeilConjectures.CategoryTheory.RingedPrincipalLocalTests
public import WeilConjectures.AlgebraicGeometry.CompletedConstantPresentationTransport
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.AutomorphismCompletionUnitComparison
import WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalTest
import WeilConjectures.CategoryTheory.NativeRingedRestrictionDivisibility
import WeilConjectures.AlgebraicGeometry.PrincipalIdealLocalTestCriterion
import all WeilConjectures.CategoryTheory.UnitPowerCompleteness
import WeilConjectures.AlgebraicGeometry.WeilCompletedKoszulLimitComparison

/-! # Quotient-tower completed adjunctions and their specified compositor

Source: Stacks Tags 099N(2),(5), 099J, 099K, 0A0E, 0DV0 and 0B65
(blueprint: lem-per-quotient-completed-compositor-unit).
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe c v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
set_option hygiene false in
local notation "F" => AsSmall.down.{v, c, 0} (C := C)
set_option hygiene false in
local notation "Jsmall" => (F).inducedTopology J
variable [(F).IsEquivalence]
variable (R : Sheaf J CommRingCat.{max c v})
set_option hygiene false in
local notation "S" => restrictedCommRing.{max c v, c, max c v, v, v} (K := Jsmall) F R
set_option hygiene false in
local notation "Rg" => NativeRings.{max c v, c, v} R
set_option hygiene false in
local notation "Rs" => NativeRings.{max c v, max c v, max c v} S
variable
  [HasSheafify J AddCommGrpCat.{max c v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max c v}]
  [HasSheafify Jsmall AddCommGrpCat.{max c v}] [(Jsmall).WEqualsLocallyBijective
    AddCommGrpCat.{max c v}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v}]
  [∀ U : AsSmall.{0} C, HasSheafify ((Jsmall).over U) AddCommGrpCat.{max c v}]
  [∀ U : AsSmall.{0} C, ((Jsmall).over U).WEqualsLocallyBijective AddCommGrpCat.{max c v}]
  [∀ U : C, HasSheafify (J.over U) CommRingCat.{max c v}]
  [∀ U : AsSmall.{0} C, HasSheafify ((Jsmall).over U) CommRingCat.{max c v}]
  [HasDerivedCategory.{w} (NativeModules.{max c v, c, v} R)]
  [HasDerivedCategory.{w} (NativeModules.{max c v, max c v, max c v} S)]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{max c v} ((Rg).over U))]
  [∀ U : AsSmall.{0} C, HasDerivedCategory.{w} (SheafOfModules.{max c v} ((Rs).over U))]
attribute [local instance] sliceDense globalModulesEquivalence sliceModulesEquivalence

private theorem reflectLocalTestZero {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] (G : A ⥤ B)
    [G.Faithful] [G.PreservesZeroMorphisms] (M : A) (h : IsZero (G.obj M)) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact G.zero_of_map_zero _ (by simpa using h)

private theorem smallModelCompleteZero
    (a : (R.obj ⋙ forget CommRingCat).sections)
    (N : DerivedCategory (NativeModules.{max c v, c, v} R)) :
    letI := globalModulesEquivalence.{max c v, c, max c v, v, v}
      (K := Jsmall) F R
    principalLocallyComplete.{c, v, v, w} R a N ↔
      principalLocallyComplete.{max c v, max c v, v, w} S
        (restrictedSection.{max c v, c, max c v, v, v} (K := Jsmall) F R a)
        ((restrictModules.{max c v, c, max c v, v, v} (K := Jsmall) F
          R).mapDerivedCategory.obj N) := by
  let := globalModulesEquivalence.{max c v, c, max c v, v, v}
    (K := Jsmall) F R
  constructor
  · intro h U s hs
    let s₀ := principalSliceSection.{c, v, v} R ((F).obj U)
      (s.val (op (Over.mk (𝟙 U))))
    have he : s = restrictedSection.{max c v, max c v, max c v, v, v} (K := (Jsmall).over U)
        (Over.post F) (R.over ((F).obj U)) s₀ := by
      rw [principalSliceSection_eta.{max c v, max c v, v} S U s]
      rfl
    rw [he] at hs ⊢
    have hz := h ((F).obj U) s₀
      ((localDivisibilityRestriction.{max c v, c, max c v, v, v} (K := Jsmall) F R a U s₀).mpr
        hs)
    obtain ⟨e⟩ := localTestRestriction.{max c v, c, max c v, v, v, w} (K := Jsmall) F R U N s₀
    exact (Functor.map_isZero _ hz).of_iso e.symm
  · intro h U s hs
    let V := AsSmall.up.{v, c, 0}.obj U
    have hs' := (localDivisibilityRestriction.{max c v, c, max c v, v, v} (K := Jsmall) F R a
      V s).mp hs
    have hz := h V _ hs'
    obtain ⟨e⟩ := localTestRestriction.{max c v, c, max c v, v, v, w} (K := Jsmall) F R V N s
    exact reflectLocalTestZero _ _ (hz.of_iso e)

end CategoryTheory.NativeRestriction
end

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.QuotientCompleted

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The global uniformizer section obtained from its constant residues in the actual limit.
Source: Stacks 099N, coefficient construction
(blueprint: lem-per-quotient-completed-compositor-unit). -/
def uniformizerSection (T : Scheme.{u}) :
    ((pbcAdicCompletion T (pbcIntegralDatum l E)).obj ⋙
      CategoryTheory.forget CommRingCat).sections :=
  (Functor.sectionsFunctor _).map
    (whiskerRight
      (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E))) ≫
        (adicDatumScalar T (intrinsicPresentationDatum (pbcIntegralDatum l E)) ≫
          (pbcCompletedComparison T (pbcIntegralDatum l E)).hom).hom)
      (CategoryTheory.forget CommRingCat))
    ⟨fun _ ↦ pbcUniformizer l E, fun _ ↦ rfl⟩

/-- The source's local RHom predicate, specialized from the existing principal local tests.
The standard localization on each actual slice keeps site sizes u+1/u.
Source: Stacks 0999 (blueprint: lem-per-quotient-completed-compositor-unit). -/
abbrev locallyComplete (T : Scheme.{u}) (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    Prop :=
  letI : ∀ U : T.ProEt, HasDerivedCategory (SheafOfModules.{u + 1}
      (((adicLisseForget T).obj (pbcAdicCompletion T (pbcIntegralDatum l E))).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  principalLocallyComplete.{u + 1, u, u}
    (pbcAdicCompletion T (pbcIntegralDatum l E)) (uniformizerSection l E T) K

/-- The local RHom condition is precisely the existing intrinsic complete predicate.
Source: Stacks 0999 and 0A0E
(blueprint: lem-per-quotient-completed-compositor-unit).
Proof: use the singleton uniformizer Koszul tower. Its image ideal consists of locally
uniformizer-divisible sections. The local Koszul reflector criterion identifies its
invertible-unit predicate with vanishing of the localization tests on every slice.
Transport through the specified completed coefficient comparison. -/
theorem complete_iff_local (T : Scheme.{u}) (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K ↔ locallyComplete l E T K := by
  let d := pbcIntegralDatum l E
  let R := pbcAdicCompletion T d
  let O := completedCechRing T d
  let a := uniformizerSection l E T
  let a' := completedCechScalar T d (pbcUniformizer l E)
  let F := completedCechDerivedEquiv T d
  let down := (completedCechSiteEquiv T).inverse
  let : (AsSmall.down.{u, u + 1, 0} (C := T.ProEt)).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, 0} (C := T.ProEt)).isEquivalence_inverse
  let : down.IsEquivalence := (completedCechSiteEquiv T).isEquivalence_inverse
  let : (AsSmall.down.{u, u + 1, 0} (C := T.ProEt)).IsDenseSubsite
      (completedCechTopology T) (ProEt.topology T) :=
    inferInstanceAs ((completedCechSiteEquiv T).inverse.IsDenseSubsite
      (completedCechTopology T) (ProEt.topology T))
  let : HasDerivedCategory.{u + 2}
      (NativeRestriction.NativeModules.{u + 1, u + 1, u + 1}
        (NativeRestriction.restrictedCommRing.{u + 1, u + 1, u + 1, u, u}
          (K := completedCechTopology T) (AsSmall.down.{u, u + 1, 0}) R)) :=
    HasDerivedCategory.standard _
  let H := NativeRestriction.restrictModules.{u + 1, u + 1, u + 1, u, u}
    (K := completedCechTopology T) (completedCechSiteEquiv T).inverse R
  have hH : H.IsEquivalence :=
    NativeRestriction.globalModulesEquivalence.{u + 1, u + 1, u + 1, u, u} _ R
  let : ∀ U : T.ProEt, HasDerivedCategory.{u + 2}
      (SheafOfModules.{u + 1} (((adicLisseForget T).obj R).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ U : completedCechSite T, HasDerivedCategory.{u + 2}
      (SheafOfModules.{u + 1} (((sheafCompose (completedCechTopology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ U : AsSmall.{0} T.ProEt, HasDerivedCategory.{u + 2}
      (SheafOfModules.{u + 1} ((NativeRestriction.NativeRings.{u + 1, u + 1, u + 1}
        (NativeRestriction.restrictedCommRing.{u + 1, u + 1, u + 1, u, u}
          (K := (AsSmall.down.{u, u + 1, 0}).inducedTopology (ProEt.topology T))
          (AsSmall.down.{u, u + 1, 0}) R)).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let j : H ≅ (completedCechModulesEquiv T d).functor :=
    NativeRestriction.restrictModules_standardIso.{u + 1, u + 1, u + 1, u, u} _ R
  let jD : H.mapDerivedCategory ≅ F.functor := Functor.mapDerivedCategoryNatIso j
  have hsmall : locallyComplete l E T K ↔
      principalLocallyComplete.{u + 1, u + 1, u} O a' (F.functor.obj K) := by
    change principalLocallyComplete.{u + 1, u, u} R a K ↔ _
    let ht : HasDerivedCategory.{u + 2}
        (NativeRestriction.NativeModules.{u + 1, u + 1, u + 1}
          (NativeRestriction.restrictedCommRing.{u + 1, u + 1, u + 1, u, u}
            (K := (AsSmall.down.{u, u + 1, 0}).inducedTopology (ProEt.topology T))
            (AsSmall.down.{u, u + 1, 0}) R)) := HasDerivedCategory.standard _
    have hs := NativeRestriction.smallModelCompleteZero.{u + 1, u, u + 2} R a K
    refine hs.trans ?_
    have ha : NativeRestriction.restrictedSection.{u + 1, u + 1, u + 1, u, u}
        (K := completedCechTopology T) (AsSmall.down.{u, u + 1, 0}) R a = a' := by
      apply Subtype.ext
      funext U
      rfl
    erw [ha]
    change principalLocallyComplete.{u + 1, u + 1, u} O a'
      (H.mapDerivedCategory.obj K) ↔ _
    exact principalLocallyComplete_iso.{u + 1, u + 1, u, u + 2} O a' (jD.app K)
  let : ∀ U : completedCechSite T, HasDerivedCategory.{u + 2}
      (ringedSiteModules.{u + 1} ((sheafCompose ((completedCechTopology T).over U)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (O.over U))) :=
    principalLocalTestSliceDerived O
  let I := image (ringedKoszulScalar O a')
  let ι := image.ι (ringedKoszulScalar O a')
  obtain ⟨D, _, _, hcrit, hnat⟩ := ringedKoszulCompletionReflector O 1 (fun _ ↦ a')
    I ι (principal_generators O a')
  let C := wfCompletionRepresentative T d K
  let real := DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨c, hc⟩ := completed_fiber_strict_limit_comparison T d 1
    (fun _ ↦ pbcUniformizer l E) C D
  let e : F.functor.obj (wfCompletionObj T d 1 (fun _ ↦ pbcUniformizer l E)
      (congrArg Ideal.span (Set.range_const (ι := Fin 1))) K) ≅
        D.completion.obj (F.functor.obj K) :=
    c ≪≫ D.completion.mapIso (F.functor.mapIso real)
  have he : F.functor.map (wfCompletionUnit T d 1 (fun _ ↦ pbcUniformizer l E)
      (congrArg Ideal.span (Set.range_const (ι := Fin 1))) K) ≫ e.hom =
        D.unit (F.functor.obj K) := by
    change F.functor.map (real.inv ≫ _) ≫ _ = _
    rw [F.functor.map_comp]
    change (F.functor.map real.inv ≫ _) ≫ c.hom ≫
      D.completion.map (F.functor.map real.hom) = _
    rw [Category.assoc, ← Category.assoc _ c.hom, hc, hnat,
      ← Category.assoc, ← F.functor.map_comp, real.inv_hom_id,
      F.functor.map_id, Category.id_comp]
  refine (wfComplete_iff T d 1 (fun _ ↦ pbcUniformizer l E)
    (congrArg Ideal.span (Set.range_const (ι := Fin 1))) K).symm.trans ?_
  change IsIso (wfCompletionUnit T d 1 (fun _ ↦ pbcUniformizer l E)
    (congrArg Ideal.span (Set.range_const (ι := Fin 1))) K) ↔ locallyComplete l E T K
  have hunit : IsIso (wfCompletionUnit T d 1 (fun _ ↦ pbcUniformizer l E)
      (congrArg Ideal.span (Set.range_const (ι := Fin 1))) K) ↔
        IsIso (D.unit (F.functor.obj K)) := by
    rw [← he, isIso_comp_right_iff]
    exact (isIso_iff_of_reflects_iso _ F.functor).symm
  exact hunit.trans ((hcrit _).trans
    ((principalLocallyComplete_iff O a' _).symm.trans hsmall.symm))

/-- The full unbounded complete category, with no constructibility requirement.
Source: Stacks 099N (blueprint: lem-per-quotient-completed-compositor-unit). -/
abbrev Complete (T : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E))

/-- The inclusion of exactly this full complete category.
Source: Stacks 099N (blueprint: lem-per-quotient-completed-compositor-unit). -/
abbrev inclusion (T : Scheme.{u}) :=
  ObjectProperty.ι (PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E))

private theorem actualHom_bijective (T : Scheme.{u})
    (M N : PbcCompletedDerived T (pbcIntegralDatum l E))
    (hN : PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) N) :
    Function.Bijective (fun f : (pbcActualCompletion (pbcIntegralDatum l E) T).obj M ⟶ N ↦
      (pbcActualCompletionUnit (pbcIntegralDatum l E) T).app M ≫ f) := by
  let P : ObjectProperty (PbcCompletedDerived T (pbcIntegralDatum l E)) :=
    PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E)
  let adj := Adjunction.ofIsRightAdjoint (ObjectProperty.ι P)
  let L : P.FullSubcategory := ⟨N, hN⟩
  let e := (P.fullyFaithfulι.homEquiv (X := P.ι.leftAdjoint.obj M) (Y := L)).symm.trans
    (adj.homEquiv M L)
  convert e.bijective using 1
  funext f
  dsimp only [e, Equiv.trans_apply]
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.FullyFaithful.homEquiv_symm_apply]
  rfl

private theorem reflectionFunctorsUnique
    {C : Type*} [Category* C] (P : C → Prop) (F G : C ⥤ C)
    (η : 𝟭 C ⟶ F) (ν : 𝟭 C ⟶ G)
    (hF : ∀ M, P (F.obj M)) (hG : ∀ M, P (G.obj M))
    (bF : ∀ M N, P N → Function.Bijective (fun f : F.obj M ⟶ N ↦ η.app M ≫ f))
    (bG : ∀ M N, P N → Function.Bijective (fun f : G.obj M ⟶ N ↦ ν.app M ≫ f)) :
    ∃! e : F ≅ G, ∀ M, η.app M ≫ e.hom.app M = ν.app M := by
  have hi (M : C) : ∃! e : F.obj M ≅ G.obj M, η.app M ≫ e.hom = ν.app M :=
    reflectionIso P (η.app M) (ν.app M) (hF M) (hG M) (bF M) (bG M)
  choose e he hu using hi
  let i : F ≅ G := NatIso.ofComponents e (by
    intro M N f
    apply (bF M (G.obj N) (hG N)).injective
    dsimp only
    rw [← Category.assoc, ← η.naturality f]
    dsimp only [Functor.id_map]
    rw [Category.assoc, he, ← Category.assoc, he]
    exact ν.naturality f)
  refine ⟨i, he, ?_⟩
  intro j hj
  apply Iso.ext
  ext M
  exact congrArg Iso.hom (hu M (j.app M) (hj M))

/-- The recorded reflector agrees with the specified singleton Koszul reflector,
including its precise degree-zero unit, as a natural isomorphism of functors.
Source: Stacks 0A0E and 099B
(blueprint: lem-per-quotient-completed-compositor-unit).
Proof: complete_iff_local identifies the two complete predicates. The two reflector
Hom bijections therefore give a unique unit-preserving isomorphism; its inverse and
naturality follow from the same uniqueness. The singleton generates the recorded ideal. -/
theorem koszul_identification (T : Scheme.{u}) :
    ∃! e : pbcActualCompletion (pbcIntegralDatum l E) T ≅
        wfCompletion T (pbcIntegralDatum l E) 1 (fun _ ↦ pbcUniformizer l E)
            (congrArg Ideal.span (Set.range_const (ι := Fin 1))) ⋙
          ObjectProperty.ι (WfIsComplete T (pbcIntegralDatum l E) 1
            (fun _ ↦ pbcUniformizer l E)
            (congrArg Ideal.span (Set.range_const (ι := Fin 1)))),
      ∀ M : PbcCompletedDerived T (pbcIntegralDatum l E),
        (pbcActualCompletionUnit (pbcIntegralDatum l E) T).app M ≫ e.hom.app M =
          wfCompletionUnit T (pbcIntegralDatum l E) 1 (fun _ ↦ pbcUniformizer l E)
            (congrArg Ideal.span (Set.range_const (ι := Fin 1))) M := by
  let d := pbcIntegralDatum l E
  let a := fun _ : Fin 1 ↦ pbcUniformizer l E
  let ha : Ideal.span (Set.range a) = d.ideal :=
    congrArg Ideal.span (Set.range_const (ι := Fin 1))
  let F := wfCompletion T d 1 a ha ⋙ ObjectProperty.ι (WfIsComplete T d 1 a ha)
  let η : 𝟭 _ ⟶ F :=
    { app := wfCompletionUnit T d 1 a ha
      naturality := fun {M N} f ↦
        ((Equiv.ofBijective _
          ((wfCompletionReflector T d 1 a ha).2 M (wfCompletionObj T d 1 a ha N)
            ((wfCompletionReflector T d 1 a ha).1 N))).apply_symm_apply _).symm }
  exact reflectionFunctorsUnique (PbcIsIntrinsicallyComplete T d)
    (pbcActualCompletion d T) F (pbcActualCompletionUnit d T) η
    (fun M ↦ (ObjectProperty.ι (PbcIsIntrinsicallyComplete T d)).leftAdjoint.obj M |>.property)
    (fun M ↦ (wfComplete_iff T d 1 a ha _).mp ((wfCompletionReflector T d 1 a ha).1 M))
    (actualHom_bijective l E T)
    (fun M N hN ↦ (wfCompletionReflector T d 1 a ha).2 M N
      ((wfComplete_iff T d 1 a ha N).mpr hN))

variable {X Y Z : Scheme.{u}}
variable [nX : IsNoetherian X] [nY : IsNoetherian Y] [nZ : IsNoetherian Z]
variable [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [dZ : Fact (∃ n : ℕ, topologicalKrullDim Z ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [iZ : Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]

include nX nY dX dY iX iY

set_option linter.unusedSectionVars false in
/-- The actual pulled-back quotient tower has complete derived limit.
Source: Stacks 099N(5), 099M and 0A0E
(blueprint: lem-per-quotient-completed-compositor-unit).
Proof: the coefficient integer ring is Noetherian, the positive quotients are finite
and perfect by their two-term free resolutions, and the residue is additively torsion.
Pull the full strict reduction tower of a K-flat representative, including all quotient
transitions and the augmentation. Constant-coefficient transport identifies its limit
and unit with Koszul completion. The reflector theorem gives local completeness. -/
theorem pull_complete (g : Y ⟶ X) (K : Complete l E X) :
    PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)
      ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj) := by
  obtain ⟨e, _, _⟩ := pbcActualCompletedPullback_tower (pbcIntegralDatum l E) g
  have hc := pbcActualCompletedPull_isComplete g (pbcIntegralDatum l E) K.obj
  obtain ⟨r, a, ha, C, real, hC⟩ := hc
  refine ⟨r, a, ha, C,
    real ≪≫ (pbcDerivedExtend (pbcCompletedComparison Y (pbcIntegralDatum l E)).inv).mapIso
      (e.app K).symm, ?_⟩
  change IsIso (real.inv ≫ _) at hC
  have := hC
  change IsIso ((_ ≫ real.inv) ≫ _)
  rw [Category.assoc]
  infer_instance

set_option linter.unusedSectionVars false in
/-- Ordinary unbounded derived direct image preserves the full complete categories.
Source: Stacks 099J, 099K (blueprint: lem-per-quotient-completed-compositor-unit).
Proof: test the completed coefficient map on every finite quotient projection. It carries
constant uniformizer to constant uniformizer, so the generated image ideal is exactly
the target uniformizer ideal. Apply ringed pushforward-completion to the ordinary
K-injective direct image. Its local RHom condition is complete_iff_local. No invertible
coefficient map, constructibility or boundedness is used. -/
theorem push_complete (g : Y ⟶ X) (L : Complete l E Y) :
    PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E)
      ((pbcActualDerivedPush g (pbcIntegralDatum l E)).obj L.obj) := by
  let d := pbcIntegralDatum l E
  let G := pbcActualDerivedPush g d
  obtain ⟨e, he, _⟩ := pbcActualDirectCompletionIso_exists g d
  have hL : IsIso ((pbcActualCompletionUnit d Y).app L.obj) :=
    (completeUnit_iff Y d L.obj).mp L.property
  have hcomp : IsIso ((pbcActualCompletionUnit d X).app (G.obj L.obj) ≫
      e.hom.app L.obj) := by
    rw [he]
    exact inferInstanceAs (IsIso (G.map ((pbcActualCompletionUnit d Y).app L.obj)))
  exact (completeUnit_iff X d _).mpr
    (IsIso.of_isIso_comp_right _ (e.hom.app L.obj))

/-- Restriction of the actual strict quotient-tower pullback, with its actual maps.
Source: Stacks 099N(5) (blueprint: lem-per-quotient-completed-compositor-unit). -/
def pull (g : Y ⟶ X) : Complete l E X ⥤ Complete l E Y :=
  ObjectProperty.lift _ (inclusion l E X ⋙
    pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) (pull_complete l E g)

/-- Restriction of the ordinary K-injective direct image to complete objects.
Source: Stacks 099J (blueprint: lem-per-quotient-completed-compositor-unit). -/
def push (g : Y ⟶ X) : Complete l E Y ⥤ Complete l E X :=
  ObjectProperty.lift _ (inclusion l E Y ⋙
    pbcActualDerivedPush g (pbcIntegralDatum l E)) (push_complete l E g)

/-- The specified quotient augmentation, restricted only in its source category.
Source: Stacks 099N(5) (blueprint: lem-per-quotient-completed-compositor-unit). -/
def gamma (g : Y ⟶ X) :
    inclusion l E X ⋙ pbcActualDerivedPull g (pbcIntegralDatum l E) ⟶
      pull l E g ⋙ inclusion l E Y :=
  whiskerLeft (inclusion l E X) (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g)

/-- The strict-tower pullback is the specified completion reflection, with its same unit.
This unique identification therefore respects the unit-preserving constant-coefficient
and quotient/Koszul transport, rather than only identifying its two endpoints.
Source: Stacks 099N(2),(5), 099M and 0A0E
(blueprint: lem-per-quotient-completed-compositor-unit).
Proof: the pulled strict finite-reduction tower is the reduction tower of ordinary
pullback after scalar restriction. Both transitions and augmentations agree. The
constant-completion equivalence carries its limit and augmentation to Koszul completion
and its unit. The Koszul reflector gives the isomorphism. Precomposition with the unit
is bijective into complete targets, hence determines the isomorphism uniquely and
makes it commute with the specified coefficient transport. -/
theorem reflector_identification (g : Y ⟶ X) :
    ∃! e : pull l E g ⋙ inclusion l E Y ≅
        inclusion l E X ⋙ pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
          pbcActualCompletion (pbcIntegralDatum l E) Y,
      gamma l E g ≫ e.hom =
        whiskerLeft (inclusion l E X)
          (pbcActualCompletedPullUnit g (pbcIntegralDatum l E)) := by
  obtain ⟨e, he, hu⟩ := pbcActualCompletedPullback_tower (pbcIntegralDatum l E) g
  refine ⟨e, ?_, ?_⟩
  · ext K
    exact he K
  · intro e' he'
    apply hu e'
    intro K
    exact congrArg (fun t ↦ t.app K) he'

omit nX nY dX dY iX iY in
private theorem normalizedCompletionIso
    {A B : Type*} [Category* A] [Category* B]
    (U F : A ⥤ B) (C : B ⥤ B) (η : U ⟶ F) (ν : 𝟭 B ⟶ C)
    (P : B → Prop) (hC : ∀ M, P (C.obj M))
    (hb : ∀ M N, P N → Function.Bijective (fun f : C.obj M ⟶ N ↦ ν.app M ≫ f))
    (hi : ∀ M, ∃ e : F.obj M ≅ C.obj (U.obj M), η.app M ≫ e.hom = ν.app (U.obj M)) :
    ∃! e : F ≅ U ⋙ C, η ≫ e.hom = whiskerLeft U ν := by
  choose e he using hi
  have hinj (M : A) (N : B) (hN : P N) :
      Function.Injective (fun f : F.obj M ⟶ N ↦ η.app M ≫ f) := by
    intro f g hfg
    have h : (e M).inv ≫ f = (e M).inv ≫ g := (hb (U.obj M) N hN).1 (by
      dsimp only
      rw [← he M]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hfg)
    exact (cancel_epi (e M).inv).mp h
  let j : F ≅ U ⋙ C := NatIso.ofComponents e (by
    intro M N f
    apply hinj M _ (hC (U.obj N))
    dsimp only
    rw [← Category.assoc, ← η.naturality f, Category.assoc, he N,
      ← Category.assoc, he M]
    exact ν.naturality (U.map f))
  refine ⟨j, ?_, ?_⟩
  · ext M
    exact he M
  · intro j' hj'
    apply Iso.ext
    ext M
    apply hinj M _ (hC (U.obj M))
    exact (congrArg (fun t ↦ t.app M) hj').trans (he M).symm

omit nX nY dX dY iX iY in
private theorem unit_transport
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B) (C : B ⥤ B)
    (η : 𝟭 B ⟶ C) {M N : A} (e : M ≅ N) :
    F.map e.inv ≫ η.app (F.obj M) ≫ C.map (F.map e.hom) = η.app (F.obj N) := by
  rw [← η.naturality]
  dsimp only [Functor.id_map]
  rw [← Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id, Category.id_comp]

/-- Restriction to constant coefficients gives the same quotient/Koszul completion
and its unit under every normalized coefficient presentation of the recorded construction.
Source: Stacks 099M, 0A0E and 099I
(blueprint: lem-per-quotient-completed-compositor-unit).
Proof: the common presentation data preserve the complete strict quotient tower and the
Koszul tower, including their augmentations. Apply completion_restriction from the
constant-completion equivalence. Its unit equation and reflector_identification give
the displayed equation. The reflector Hom bijection after constant restriction makes
the comparison unique and natural, so these are the fixed comparisons under transport. -/
theorem constant_identification (g : Y ⟶ X)
    (D : CompletedConstantPresentationData Y (pbcIntegralDatum l E)) :
    ∃! e : (pull l E g ⋙ inclusion l E Y) ⋙ D.equivalence.functor ⋙
          ConstantCompletion.dres (ConstantCompletion.coefficientMap
            (completedCechTopology Y) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal) ≅
        (inclusion l E X ⋙ pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
          D.equivalence.functor ⋙ ConstantCompletion.dres (ConstantCompletion.coefficientMap
            (completedCechTopology Y) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal)) ⋙
          ConstantCompletion.completion (completedCechTopology Y) (PbcIntegralRing l E)
            (pbcIntegralDatum l E).ideal false,
      whiskerRight (gamma l E g) (D.equivalence.functor ⋙
          ConstantCompletion.dres (ConstantCompletion.coefficientMap
            (completedCechTopology Y) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal)) ≫
          e.hom =
        whiskerLeft (inclusion l E X ⋙ pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
          D.equivalence.functor ⋙ ConstantCompletion.dres (ConstantCompletion.coefficientMap
            (completedCechTopology Y) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal))
          (ConstantCompletion.completionUnit (completedCechTopology Y) (PbcIntegralRing l E)
            (pbcIntegralDatum l E).ideal false) := by
  let := (pbcIntegralDatum l E).noetherian
  let J := completedCechTopology Y
  let A := PbcIntegralRing l E
  let I := (pbcIntegralDatum l E).ideal
  let R := ConstantCompletion.dres (ConstantCompletion.coefficientMap J A I)
  let B := ConstantCompletion.completion J A I true
  let C := ConstantCompletion.completion J A I false
  let νB := ConstantCompletion.completionUnit J A I true
  let νC := ConstantCompletion.completionUnit J A I false
  let U := inclusion l E X ⋙ pbcActualDerivedPull g (pbcIntegralDatum l E)
  let E' := D.equivalence.functor
  obtain ⟨er, her⟩ := ConstantCompletion.completion_restriction J A I
  obtain ⟨e₀, he₀, _⟩ := reflector_identification l E g
  obtain ⟨e₁, he₁, _⟩ := koszul_identification l E Y
  let a := fun _ : Fin 1 ↦ pbcUniformizer l E
  let ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal :=
    congrArg Ideal.span (Set.range_const (ι := Fin 1))
  obtain ⟨_, _, hC, hb, _⟩ := ConstantCompletion.koszul_quotient_reflector J A I false 1 a ha
  apply normalizedCompletionIso (U ⋙ E' ⋙ R)
    ((pull l E g ⋙ inclusion l E Y) ⋙ E' ⋙ R) C
    (whiskerRight (gamma l E g) (E' ⋙ R)) νC
    (ConstantCompletion.IsComplete (ConstantCompletion.finiteMap J A I false 0)) hC hb
  intro K
  let M := U.obj K
  let P := wfCompletionRepresentative Y (pbcIntegralDatum l E) M
  let real := DerivedCategory.Q.objObjPreimageIso M
  obtain ⟨k, hk⟩ := D.koszul 1 a ha P
  let k' := k ≪≫ B.mapIso (E'.mapIso real)
  have hk' : E'.map (wfCompletionUnit Y (pbcIntegralDatum l E) 1 a ha M) ≫ k'.hom =
      νB.app (E'.obj M) := by
    change E'.map (real.inv ≫ _) ≫ k.hom ≫ B.map (E'.map real.hom) = _
    rw [E'.map_comp, Category.assoc, ← Category.assoc _ k.hom, hk]
    exact unit_transport E' B νB real
  let q := (e₀.app K) ≪≫ (e₁.app M)
  let e := R.mapIso (E'.mapIso q ≪≫ k') ≪≫ er.symm.app (E'.obj M)
  refine ⟨e, ?_⟩
  have hq : (gamma l E g).app K ≫ q.hom = wfCompletionUnit Y (pbcIntegralDatum l E) 1 a ha M := by
    change _ ≫ (e₀.hom.app K ≫ e₁.hom.app M) = _
    rw [← Category.assoc]
    have h₀ := congrArg (fun t ↦ t.app K) he₀
    change _ ≫ e₀.hom.app K = (pbcActualCompletionUnit (pbcIntegralDatum l E) Y).app M at h₀
    rw [h₀, he₁ M]
  change R.map (E'.map ((gamma l E g).app K)) ≫
    R.map (E'.map q.hom ≫ k'.hom) ≫ er.inv.app (E'.obj M) = _
  rw [← R.map_comp_assoc, ← E'.map_comp_assoc, hq, hk']
  have hr := her (E'.obj M)
  change νC.app (R.obj (E'.obj M)) ≫ er.hom.app (E'.obj M) =
    R.map (νB.app (E'.obj M)) at hr
  rw [← hr, Category.assoc, er.hom_inv_id_app]
  exact Category.comp_id _

omit nX nY dX dY iX iY in
private theorem iso_unit_precomp
    {C : Type*} [Category* C] {M N L Q : C} (η : M ⟶ N) (ν : M ⟶ L)
    (e : N ≅ L) (f : N ⟶ Q) (h : η ≫ e.hom = ν) :
    η ≫ f = ν ≫ (e.inv ≫ f ≫ 𝟙 Q) := by
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id]

private theorem gamma_bijective (g : Y ⟶ X) (K : Complete l E X) (L : Complete l E Y) :
    Function.Bijective (fun f : (pull l E g).obj K ⟶ L ↦
      (gamma l E g).app K ≫ f.hom) := by
  obtain ⟨e, he, _⟩ := reflector_identification l E g
  let b := ((ObjectProperty.fullyFaithfulι
    (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E))).homEquiv
    (X := (pull l E g).obj K) (Y := L)).trans
    (Iso.homCongr (e.app K) (Iso.refl L.obj))
  have h (f : (pull l E g).obj K ⟶ L) :
      (gamma l E g).app K ≫ f.hom =
        (pbcActualCompletionUnit (pbcIntegralDatum l E) Y).app
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj) ≫ b f := by
    have hk := congrArg (fun t ↦ t.app K) he
    change (gamma l E g).app K ≫ e.hom.app K =
      (pbcActualCompletionUnit (pbcIntegralDatum l E) Y).app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj) at hk
    change (gamma l E g).app K ≫ f.hom =
      (pbcActualCompletionUnit (pbcIntegralDatum l E) Y).app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj) ≫
          (e.inv.app K ≫ f.hom ≫ 𝟙 L.obj)
    exact iso_unit_precomp _ _ (e.app K) f.hom hk
  have hb := (actualHom_bijective l E Y
    ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj) L.obj L.property).comp
      b.bijective
  convert hb using 1
  funext f
  exact h f

private def completedHomEquiv (g : Y ⟶ X) (K : Complete l E X) (L : Complete l E Y) :
    ((pull l E g).obj K ⟶ L) ≃ (K ⟶ (push l E g).obj L) :=
  (Equiv.ofBijective _ (gamma_bijective l E g K L)).trans
    ((pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).homEquiv K.obj L.obj) |>.trans
      ((ObjectProperty.fullyFaithfulι
        (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))).homEquiv
        (X := K) (Y := (push l E g).obj L)).symm

private theorem completedHomEquiv_formula (g : Y ⟶ X)
    (K : Complete l E X) (L : Complete l E Y) (f : (pull l E g).obj K ⟶ L) :
    (completedHomEquiv l E g K L f).hom =
      (pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).homEquiv K.obj L.obj
        ((gamma l E g).app K ≫ f.hom) := by
  simp only [completedHomEquiv, Equiv.trans_apply,
    Equiv.ofBijective_apply]
  rfl

/-- The uniquely normalized adjunction: precompose by the actual quotient augmentation,
then use the specified ordinary derived adjunction.
Source: Stacks 099K and 099N(2), and Tags 0037, 0DV0
(blueprint: lem-per-quotient-completed-compositor-unit).
Proof: the reflector Hom bijection is precomposition by gamma, and push_complete places
the right adjoint in the full complete category. Compose this natural bijection with
pbcActualDerivedAdjunction. The natural-Hom-bijection construction gives an adjunction;
its displayed Hom formula fixes every bijection, hence the adjunction uniquely. -/
theorem adjunction_existsUnique (g : Y ⟶ X) :
    ∃! adj : pull l E g ⊣ push l E g,
      ∀ (K : Complete l E X) (L : Complete l E Y) (f : (pull l E g).obj K ⟶ L),
        (adj.homEquiv K L f).hom =
          (pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).homEquiv K.obj L.obj
            ((gamma l E g).app K ≫ f.hom) := by
  let core : Adjunction.CoreHomEquiv (pull l E g) (push l E g) :=
    { homEquiv := completedHomEquiv l E g
      homEquiv_naturality_left_symm := by
        intro K' K L f t
        apply (completedHomEquiv l E g K' L).injective
        apply (inclusion l E X).map_injective
        rw [Equiv.apply_symm_apply]
        change f.hom ≫ t.hom =
          (completedHomEquiv l E g K' L
            ((pull l E g).map f ≫ (completedHomEquiv l E g K L).symm t)).hom
        rw [completedHomEquiv_formula]
        change f.hom ≫ t.hom =
          (pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).homEquiv K'.obj L.obj
            ((gamma l E g).app K' ≫ ((pull l E g).map f).hom ≫
              ((completedHomEquiv l E g K L).symm t).hom)
        rw [← Category.assoc]
        have hn := (gamma l E g).naturality f
        change (pbcActualDerivedPull g (pbcIntegralDatum l E)).map f.hom ≫
          (gamma l E g).app K = (gamma l E g).app K' ≫ ((pull l E g).map f).hom at hn
        rw [← hn, Category.assoc,
          (pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).homEquiv_naturality_left]
        rw [← completedHomEquiv_formula, Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro K L L' f t
        apply (inclusion l E X).map_injective
        change (completedHomEquiv l E g K L' (f ≫ t)).hom =
          (completedHomEquiv l E g K L f).hom ≫
            (pbcActualDerivedPush g (pbcIntegralDatum l E)).map t.hom
        rw [completedHomEquiv_formula, completedHomEquiv_formula]
        change (pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).homEquiv K.obj L'.obj
            ((gamma l E g).app K ≫ f.hom ≫ t.hom) = _
        rw [← Category.assoc]
        exact (pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).homEquiv_naturality_right
          ((gamma l E g).app K ≫ f.hom) t.hom }
  let adj := Adjunction.mkOfHomEquiv core
  have hformula : ∀ K L f, (adj.homEquiv K L f).hom =
      (pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).homEquiv K.obj L.obj
        ((gamma l E g).app K ≫ f.hom) := by
    intro K L f
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    exact completedHomEquiv_formula l E g K L f
  refine ⟨adj, hformula, ?_⟩
  intro adj' h'
  apply Adjunction.ext
  ext K
  rw [← adj'.homEquiv_id, ← adj.homEquiv_id, h', hformula]

/-- The adjunction selected by its unique specified Hom formula.
Source: Stacks 099K (blueprint: lem-per-quotient-completed-compositor-unit). -/
def adjunction (g : Y ⟶ X) : pull l E g ⊣ push l E g :=
  (adjunction_existsUnique l E g).exists.choose

private theorem adjunction_formula (g : Y ⟶ X)
    (K : Complete l E X) (L : Complete l E Y) (f : (pull l E g).obj K ⟶ L) :
    ((adjunction l E g).homEquiv K L f).hom =
      (pbcActualDerivedAdjunction g (pbcIntegralDatum l E)).homEquiv K.obj L.obj
        ((gamma l E g).app K ≫ f.hom) :=
  (adjunction_existsUnique l E g).exists.choose_spec K L f

omit nX nY dX dY iX iY in
private theorem conjugate_transpose
    {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G G' : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G')
    (e : F' ≅ F) {M : C} {N : D} (f : F.obj M ⟶ N) :
    b.homEquiv M N (e.hom.app M ≫ f) =
      a.homEquiv M N f ≫ (conjugateIsoEquiv a b e).hom.app N := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, ← unit_conjugateEquiv a b]
  simp only [Category.assoc]
  exact congrArg (fun t ↦ a.unit.app M ≫ t)
    (((conjugateIsoEquiv a b e).hom.naturality f).symm)

omit nX nY dX dY iX iY in
private theorem conjugate_inverse_transpose
    {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G G' : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G')
    (e : F' ≅ F) {M : C} {N : D} (f : F'.obj M ⟶ N) :
    a.homEquiv M N (e.inv.app M ≫ f) =
      b.homEquiv M N f ≫ (conjugateIsoEquiv a b e).inv.app N :=
  conjugate_transpose b a e.symm f

omit nX nY dX dY iX iY in
private theorem conjugate_unit
    {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G G' : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G')
    (e : F' ≅ F) (M : C) :
    b.homEquiv M (F.obj M) (e.hom.app M) =
      a.unit.app M ≫ (conjugateIsoEquiv a b e).hom.app (F.obj M) := by
  simpa only [Category.comp_id, Adjunction.homEquiv_id] using
    conjugate_transpose a b e (𝟙 (F.obj M))

omit nX nY dX dY iX iY in
private theorem conjugate_id
    {C : Type*} [Category* C] {F G : C ⥤ C} (b : F ⊣ G)
    (e : F ≅ 𝟭 C) (M : C) :
    b.homEquiv M M (e.hom.app M) =
      (conjugateIsoEquiv Adjunction.id b e).hom.app M := by
  simpa only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp, Functor.id_obj] using
    conjugate_unit Adjunction.id b e M

include nZ dZ iZ

/-- The canonical ordinary direct-image composition restricted through the full inclusions.
Source: Stacks 0D6D, 0DV0 (blueprint: lem-per-quotient-completed-compositor-unit). -/
def rightComp (g : Y ⟶ X) (h : Z ⟶ Y) :
    push l E (h ≫ g) ≅ push l E h ⋙ push l E g :=
  Functor.fullyFaithfulCancelRight (inclusion l E X)
    (isoWhiskerLeft (inclusion l E Z)
      (pbcActualDerivedDirectCompIso h g (pbcIntegralDatum l E)).symm)

/-- The compositor is precisely the conjugate of canonical direct-image composition
for these adjunctions and their specified composite adjunction.
Source: Stacks 0B65 and 0DV0 (blueprint: lem-per-quotient-completed-compositor-unit). -/
def compositor (g : Y ⟶ X) (h : Z ⟶ Y) :
    pull l E g ⋙ pull l E h ≅ pull l E (h ≫ g) :=
  (conjugateIsoEquiv (adjunction l E (h ≫ g))
    ((adjunction l E g).comp (adjunction l E h))).symm (rightComp l E g h)

/-- The compositor equation for the actual quotient units as natural transformations.
Source: Stacks 099N(2),(5), 0B65, 0DV0
(blueprint: lem-per-quotient-completed-compositor-unit).
Proof: expand each completed Hom transpose by adjunction_existsUnique. Source naturality
of the ordinary h-adjunction moves gamma_g through its transpose, without requiring
ordinary P_g K complete. Conjugation gives the same right-composition map for the
completed and ordinary composite adjunctions. Apply this to the identity of the
completed composite pullback. Injectivity of the ordinary composite Hom bijection gives
the displayed equation. All constituent maps are natural, so this is an equation of
natural transformations before any quotient unit is inverted. -/
theorem compositor_unit (g : Y ⟶ X) (h : Z ⟶ Y) :
    whiskerRight (gamma l E g) (pbcActualDerivedPull h (pbcIntegralDatum l E)) ≫
        whiskerLeft (pull l E g) (gamma l E h) ≫
        whiskerRight (compositor l E g h).hom (inclusion l E Z) =
      whiskerLeft (inclusion l E X)
          (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv ≫
        gamma l E (h ≫ g) := by
  let ag := pbcActualDerivedAdjunction g (pbcIntegralDatum l E)
  let ah := pbcActualDerivedAdjunction h (pbcIntegralDatum l E)
  let ac := pbcActualDerivedAdjunction (h ≫ g) (pbcIntegralDatum l E)
  let bg := adjunction l E g
  let bh := adjunction l E h
  let bc := adjunction l E (h ≫ g)
  let a := pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)
  let b := compositor l E g h
  ext K
  let L := (pull l E (h ≫ g)).obj K
  have ht (f : ((pull l E g) ⋙ pull l E h).obj K ⟶ L) :
      (ag.comp ah).homEquiv K.obj L.obj
        ((pbcActualDerivedPull h (pbcIntegralDatum l E)).map ((gamma l E g).app K) ≫
          (gamma l E h).app ((pull l E g).obj K) ≫ f.hom) =
        ((bg.comp bh).homEquiv K L f).hom := by
    rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
    change ag.homEquiv K.obj _ (ah.homEquiv _ _ (_ ≫ (_ ≫ f.hom))) = _
    rw [ah.homEquiv_naturality_left]
    change ag.homEquiv K.obj _ ((gamma l E g).app K ≫
        ah.homEquiv ((pull l E g).obj K).obj L.obj
          ((gamma l E h).app ((pull l E g).obj K) ≫ f.hom)) =
      (bg.homEquiv K ((push l E h).obj L)
        (bh.homEquiv ((pull l E g).obj K) L f)).hom
    erw [← adjunction_formula l E h, ← adjunction_formula l E g]
  have hb : ((bg.comp bh).homEquiv K L (b.hom.app K)).hom =
      (bc.unit.app K).hom ≫
        (pbcActualDerivedDirectCompIso h g (pbcIntegralDatum l E)).inv.app L.obj := by
    have he := conjugate_unit bc (bg.comp bh) b K
    have he' : (conjugateIsoEquiv bc (bg.comp bh) b) = rightComp l E g h :=
      (conjugateIsoEquiv bc (bg.comp bh)).apply_symm_apply _
    rw [he'] at he
    apply_fun (inclusion l E X).map at he
    rw [Functor.map_comp] at he
    change _ = _ ≫ (inclusion l E X).map ((rightComp l E g h).hom.app L) at he
    rw [rightComp, Functor.fullyFaithfulCancelRight_hom_app,
      Functor.map_preimage] at he
    exact he
  apply ((ag.comp ah).homEquiv K.obj L.obj).injective
  change (ag.comp ah).homEquiv K.obj L.obj
      ((pbcActualDerivedPull h (pbcIntegralDatum l E)).map ((gamma l E g).app K) ≫
        (gamma l E h).app ((pull l E g).obj K) ≫ (b.hom.app K).hom) =
    (ag.comp ah).homEquiv K.obj L.obj
      (a.inv.app K.obj ≫ (gamma l E (h ≫ g)).app K)
  rw [ht, hb]
  have ha := conjugate_inverse_transpose (ag.comp ah) ac a
    ((gamma l E (h ≫ g)).app K)
  change _ = _ ≫ (pbcActualDerivedDirectCompIso h g (pbcIntegralDatum l E)).inv.app L.obj at ha
  erw [ha]
  apply congrArg (fun t ↦ t ≫
    (pbcActualDerivedDirectCompIso h g (pbcIntegralDatum l E)).inv.app L.obj)
  change (bc.unit.app K).hom = ac.homEquiv K.obj L.obj ((gamma l E (h ≫ g)).app K)
  have hunit := adjunction_formula l E (h ≫ g) K L (𝟙 L)
  rw [Adjunction.homEquiv_id] at hunit
  change (bc.unit.app K).hom = ac.homEquiv K.obj L.obj
    ((gamma l E (h ≫ g)).app K ≫ 𝟙 L.obj) at hunit
  exact hunit.trans (congrArg (ac.homEquiv K.obj L.obj) (Category.comp_id _))

omit nX nY nZ dX dY dZ iX iY iZ

variable (T : Scheme.{u}) [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- Restriction of the specified ordinary direct-image identity comparison.
Source: Stacks 0D6D (blueprint: lem-per-quotient-completed-compositor-unit). -/
def rightId : push l E (𝟙 T) ≅ 𝟭 (Complete l E T) :=
  Functor.fullyFaithfulCancelRight (inclusion l E T)
    (isoWhiskerLeft (inclusion l E T)
      (pbcActualDerivedDirectIdIso (pbcIntegralDatum l E) T))

/-- The identity analogue, conjugated using exactly the specified restricted adjunction.
Source: Stacks 0B65 and the identity adjunction
(blueprint: lem-per-quotient-completed-compositor-unit). -/
def identity : pull l E (𝟙 T) ≅ 𝟭 (Complete l E T) :=
  (conjugateIsoEquiv (Adjunction.id (C := Complete l E T))
    (adjunction l E (𝟙 T))).symm (rightId l E T).symm

/-- The quotient augmentation followed by the conjugate identity is the ordinary identity.
Source: Stacks 099N, 0B65 (blueprint: lem-per-quotient-completed-compositor-unit).
Proof: the conjugate unit equation sends the completed identity under its Hom bijection
to the inverse right identity comparison. The ordinary identity has the same transpose
by ordinary adjunction compatibility. Expand the completed Hom formula and use the
ordinary Hom bijection's injectivity. Naturality gives the displayed natural equation.
No completion unit has been assumed invertible or cancelled. -/
theorem identity_unit :
    gamma l E (𝟙 T) ≫ whiskerRight (identity l E T).hom (inclusion l E T) =
      whiskerLeft (inclusion l E T)
        (pbcActualDerivedPullIdIso (pbcIntegralDatum l E) T).hom := by
  let a := pbcActualDerivedAdjunction (𝟙 T) (pbcIntegralDatum l E)
  let b := adjunction l E (𝟙 T)
  let e := pbcActualDerivedPullIdIso (pbcIntegralDatum l E) T
  ext K
  apply (a.homEquiv K.obj K.obj).injective
  change a.homEquiv K.obj K.obj
      ((gamma l E (𝟙 T)).app K ≫ ((identity l E T).hom.app K).hom) = _
  rw [← adjunction_formula]
  have hb := conjugate_id b (identity l E T) K
  have hd : conjugateIsoEquiv (Adjunction.id (C := Complete l E T)) b
      (identity l E T) = (rightId l E T).symm :=
    (conjugateIsoEquiv _ _).apply_symm_apply _
  rw [hd] at hb
  have ha := conjugate_id a e K.obj
  erw [hb]
  change ((rightId l E T).inv.app K).hom = _
  rw [rightId, Functor.fullyFaithfulCancelRight_inv_app]
  change (inclusion l E T).map ((inclusion l E T).preimage _) = _
  rw [Functor.map_preimage]
  change (pbcActualDerivedDirectIdIso (pbcIntegralDatum l E) T).inv.app K.obj = _
  change _ = (a.homEquiv K.obj K.obj) (e.hom.app K.obj)
  exact ha.symm

end AlgebraicGeometry.Scheme.QuotientCompleted
