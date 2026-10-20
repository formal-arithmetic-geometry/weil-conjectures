/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic
import Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.ProEtaleLeftComplete
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence

/-!
# Proper direct image preserves open support on the full pro-etale derived category

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b),
compactification independence (blueprint: lem-sp-proper-open-derived-support).
Stacks Project, Tag 09AG, supplies only the degree-zero specialization vanishing used
in the proof, rather than the full derived support assertion stated here.
-/

@[expose] public section

set_option autoImplicit false

section

-- Keep the ordinary localization and coefficient sizes fixed while elaborating the proof.
attribute [-instance] HasDerivedCategory.ofIsGrothendieckAbelian
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable local instance (priority := 3000) fixed_sheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

private noncomputable local instance (priority := 3000) fixed_locallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

private noncomputable local instance fixed_derived (X : Scheme.{u}) (A : Type u) [CommRing A] :
    HasDerivedCategory.{u + 2} (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  HasDerivedCategory.standard _

private theorem fixed_groth (X : Scheme.{u}) (A : Type u) [CommRing A] :
    IsGrothendieckAbelian.{u + 1}
      (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
    (ProEt.topology X) (proEtaleConstantRing X A)).1

private local instance fixed_kInjective (X : Scheme.{u}) (A : Type u) [CommRing A] :
    Abelian.HasKInjectiveResolutions (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  proEtaleRingModules_hasKInjectiveResolutions X (proEtaleConstantRing X A)

private theorem sheaf_proper_open_support
    {X T₁ T₂ : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (comm : j₁ ≫ f = j₂) (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    IsIso ((sfIntrinsicOpenAdjunction A j₂).counit.app
      ((proEtaleConstantModuleDirectImage f A).obj
        ((sfIntrinsicExtensionByZero j₁ A).obj M))) := by
  let s : X ⟶ CategoryTheory.Limits.pullback f j₂ :=
    CategoryTheory.Limits.pullback.lift j₁ (𝟙 X) (by simpa using comm)
  have hs : s ≫ CategoryTheory.Limits.pullback.fst f j₂ = j₁ := by simp [s]
  have : IsOpenImmersion (s ≫ CategoryTheory.Limits.pullback.fst f j₂) := by
    rw [hs]
    infer_instance
  have : IsOpenImmersion s := IsOpenImmersion.of_comp s (CategoryTheory.Limits.pullback.fst f j₂)
  let e := (sfIntrinsicOpenComp A s (CategoryTheory.Limits.pullback.fst f j₂)).app M
  let N := (sfIntrinsicExtensionByZero s A).obj M
  have := sfProperOpenSheafComparison_isIso A f j₂
  let d := asIso ((sfProperOpenSheafComparison A
    (CategoryTheory.Limits.pullback.snd f j₂)
    (CategoryTheory.Limits.pullback.fst f j₂) j₂ f
    (IsPullback.of_hasPullback f j₂).flip).app N)
  have : (sfIntrinsicExtensionByZero j₂ A).Full := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : (sfIntrinsicExtensionByZero j₂ A).Faithful := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  let e' : (sfIntrinsicExtensionByZero j₁ A).obj M ≅
      (sfIntrinsicExtensionByZero (CategoryTheory.Limits.pullback.fst f j₂) A).obj N := by
    simpa only [hs, Functor.comp_obj] using e
  apply (sfIntrinsicOpenAdjunction A j₂).isIso_counit_app_of_iso
  exact (proEtaleConstantModuleDirectImage f A).mapIso e' ≪≫ d.symm

private theorem derived_support_of_complex
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    (adj : F ⊣ G) [F.Full] [F.Faithful]
    (adjD : F.mapDerivedCategory ⊣ G.mapDerivedCategory)
    (L : CochainComplex D ℤ)
    (hL : ∀ n : ℤ, IsIso (adj.counit.app (L.X n))) :
    IsIso (adjD.counit.app (DerivedCategory.Q.obj L)) := by
  have : IsIso adj.unit := inferInstance
  have ff := adjD.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso adj.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso C)
  have := ff.full
  have := ff.faithful
  let C := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let φ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (C.obj L) ⟶ L :=
    { f n := adj.counit.app (L.X n)
      comm' _ _ _ := (adj.counit.naturality _).symm }
  have : ∀ n : ℤ, IsIso (φ.f n) := hL
  have : IsIso φ := HomologicalComplex.Hom.isIso_of_components φ
  apply adjD.isIso_counit_app_of_iso
  exact ((F.mapDerivedCategoryFactors.app (C.obj L)) ≪≫
    DerivedCategory.Q.mapIso (asIso φ)).symm

private noncomputable def acyclic_complex_computation
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [CategoryTheory.Limits.PreservesFiniteLimits F]
    (L : CochainComplex.Plus C) (hL : ∀ n, F.rightAcyclic (L.obj.X n)) :
    F.rightDerivedFunctor.obj (DerivedCategory.Q.obj L.obj) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj L.obj) := by
  have := F.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic L hL
  exact (F.rightDerivedFunctorPlusCompatibility.app (DerivedCategory.Plus.Q.obj L)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      (asIso (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient C).obj L))).symm

private theorem bounded_support
    {C D E B : Type*} [Category* C] [Category* D] [Category* E] [Category* B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B] [EnoughInjectives C] [EnoughInjectives D]
    [Abelian.HasKInjectiveResolutions D]
    (J : C ⥤ D) (P : D ⥤ E) (F : B ⥤ E) (G : E ⥤ B)
    [J.Additive] [P.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits P]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) [F.Full] [F.Faithful]
    (adjD : F.mapDerivedCategory ⊣ G.mapDerivedCategory)
    (hs : ∀ M, IsIso (adj.counit.app (P.obj (J.obj M))))
    (ha : ∀ (M : C) [Injective M], P.rightAcyclic (J.obj M))
    (K : DerivedCategory C) (n : ℤ) [K.IsGE n] :
    IsIso (adjD.counit.app (P.rightDerivedFunctor.obj (J.mapDerivedCategory.obj K))) := by
  let K' : DerivedCategory.Plus C := ⟨K, ⟨n, inferInstance⟩⟩
  have : K'.IsGE n := (K'.isGE_ι_obj_iff n).1 (show K.IsGE n from inferInstance)
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K' n
  let L' := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  let L'' := J.mapCochainComplexPlus.obj L'
  have hac (q : ℤ) : P.rightAcyclic (L''.obj.X q) := by
    have : Injective (L'.obj.X q) := inferInstanceAs (Injective (L.obj.X q).obj)
    exact ha (L'.obj.X q)
  let d : P.rightDerivedFunctor.obj (J.mapDerivedCategory.obj K) ≅
      DerivedCategory.Q.obj ((P.mapHomologicalComplex _).obj L''.obj) :=
    P.rightDerivedFunctor.mapIso
      (J.mapDerivedCategory.mapIso (DerivedCategory.Plus.ι.mapIso e).symm ≪≫
        J.mapDerivedCategoryFactors.app L'.obj) ≪≫
      acyclic_complex_computation P L'' hac
  have hh : IsIso (adjD.counit.app
      (DerivedCategory.Q.obj ((P.mapHomologicalComplex _).obj L''.obj))) := by
    apply derived_support_of_complex F G adj adjD
    intro q
    exact hs (L'.obj.X q)
  exact (NatTrans.isIso_app_iff_of_iso adjD.counit d).2 hh

private theorem bounded_proper_open_support
    {X T₁ T₂ : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (comm : j₁ ≫ f = j₂) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory X A) (n : ℤ)
    [DerivedCategory.IsGE.{u + 2, u + 1, u + 2}
      (C := proEtaleRingModules X (proEtaleConstantRing X A)) K n] :
    IsIso ((exceptionalOpenAdjunction j₂ A).counit.app
      ((proEtaleConstantDerivedDirectImage f A).obj
        ((sfIntrinsicDerivedOpen A j₁).obj K))) := by
  have hgroth (T : Scheme.{u}) :
      IsGrothendieckAbelian.{u + 1}
        (proEtaleRingModules T (proEtaleConstantRing T A)) := fixed_groth T A
  have := hgroth X
  have := hgroth T₁
  have : EnoughInjectives (proEtaleRingModules X (proEtaleConstantRing X A)) :=
    IsGrothendieckAbelian.enoughInjectives.{u + 1, u + 1, u + 2}
  have : EnoughInjectives (proEtaleRingModules T₁ (proEtaleConstantRing T₁ A)) :=
    IsGrothendieckAbelian.enoughInjectives.{u + 1, u + 1, u + 2}
  have : (sfIntrinsicExtensionByZero j₂ A).Full := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : (sfIntrinsicExtensionByZero j₂ A).Faithful := by
    unfold sfIntrinsicExtensionByZero
    infer_instance
  have : PreservesFiniteLimits (proEtaleConstantModuleDirectImage f A) :=
    (proEtaleConstantModuleDirectImage_additive_leftExact f A).2
  apply bounded_support.{u + 1, u + 2, u + 1, u + 2, u + 1, u + 2, u + 1,
      u + 2, u + 2, u + 2, u + 2, u + 2} (sfIntrinsicExtensionByZero j₁ A)
    (proEtaleConstantModuleDirectImage f A) (sfIntrinsicExtensionByZero j₂ A)
    (sfIntrinsicPullback A j₂) (sfIntrinsicOpenAdjunction A j₂)
    (exceptionalOpenAdjunction j₂ A) (sheaf_proper_open_support f j₁ j₂ comm A) ?_ K n
  intro M hM k
  exact (isZero_higherDirectImage_open_injective_of_proper A f (𝟙 X) j₁ j₂
    (by simpa using comm) M (k + 1) (by omega)).of_iso
    ((proEtaleConstantModuleDirectImage f A).homologyRightDerivedFunctorObjSingleFunctorIso
      ((sfIntrinsicExtensionByZero j₁ A).obj M) (k + 1)).symm

private theorem kernel_preserves_products
    {C D : Type*} [Category* C] [Category* D] [Abelian D]
    (I : Type*) [HasProductsOfShape I C]
    (F G H : C ⥤ D) (a : F ⟶ G) (b : G ⟶ H)
    (hab : ∀ M, a.app M ≫ b.app M = 0)
    (hk : ∀ M, IsLimit (KernelFork.ofι (a.app M) (hab M)))
    [PreservesLimitsOfShape (Discrete I) G]
    [PreservesLimitsOfShape (Discrete I) H] :
    PreservesLimitsOfShape (Discrete I) F := by
  classical
  have h (K : I → C) : PreservesLimit (Discrete.functor K) F := by
    let P := ∏ᶜ K
    let cg := Fan.mk (G.obj P) (fun n ↦ G.map (Pi.π K n))
    let ch := Fan.mk (H.obj P) (fun n ↦ H.map (Pi.π K n))
    let hg : IsLimit cg := isLimitOfHasProductOfPreservesLimit G K
    let hh : IsLimit ch := isLimitOfHasProductOfPreservesLimit H K
    let lift (s : Fan (fun n ↦ F.obj (K n))) : s.pt ⟶ G.obj P :=
      Fan.IsLimit.lift hg (fun n ↦ s.proj n ≫ a.app (K n))
    have hz (s : Fan (fun n ↦ F.obj (K n))) : lift s ≫ b.app P = 0 := by
      apply Fan.IsLimit.hom_ext hh
      intro n
      dsimp [ch]
      change (lift s ≫ b.app P) ≫ H.map (Pi.π K n) = 0 ≫ H.map (Pi.π K n)
      rw [Category.assoc, ← b.naturality, ← Category.assoc]
      change (lift s ≫ cg.proj n) ≫ b.app (K n) = _
      rw [Fan.IsLimit.fac]
      simp [hab, Category.assoc]
    let l (s : Fan (fun n ↦ F.obj (K n))) : s.pt ⟶ F.obj P :=
      (hk P).lift (KernelFork.ofι (lift s) (hz s))
    apply preservesLimit_of_preserves_limit_cone (productIsProduct K)
    apply (isLimitMapConeFanMkEquiv F K _).symm.toFun
    refine Fan.IsLimit.mk _ l (fun s n ↦ ?_) (fun s m hm ↦ ?_)
    · have : Mono (a.app (K n)) := mono_of_isLimit_fork (hk (K n))
      apply (cancel_mono (a.app (K n))).1
      change (l s ≫ F.map (Pi.π K n)) ≫ a.app (K n) = _
      rw [Category.assoc, a.naturality, ← Category.assoc]
      change ((hk P).lift (KernelFork.ofι (lift s) (hz s)) ≫
        (KernelFork.ofι (a.app P) (hab P)).ι) ≫ cg.proj n = _
      rw [Fork.IsLimit.lift_ι]
      exact Fan.IsLimit.fac hg _ n
    · have : Mono (a.app P) := mono_of_isLimit_fork (hk P)
      apply (cancel_mono (a.app P)).1
      apply Fan.IsLimit.hom_ext hg
      intro n
      dsimp [cg]
      change ∀ n, m ≫ F.map (Pi.π K n) = s.proj n at hm
      rw [Category.assoc, ← a.naturality, ← Category.assoc, hm]
      change _ = ((hk P).lift (KernelFork.ofι (lift s) (hz s)) ≫
        (KernelFork.ofι (a.app P) (hab P)).ι) ≫ cg.proj n
      rw [Fork.IsLimit.lift_ι]
      change s.proj n ≫ a.app (K n) = lift s ≫ cg.proj n
      exact (Fan.IsLimit.fac hg (fun n ↦ s.proj n ≫ a.app (K n)) n).symm
  let := h
  exact preservesLimitsOfShape_of_discrete F

private theorem products_of_essSurj
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (I : Type*) [HasProductsOfShape I C]
    (Q : C ⥤ D) [Q.EssSurj] (F : D ⥤ E)
    [PreservesLimitsOfShape (Discrete I) Q]
    [PreservesLimitsOfShape (Discrete I) (Q ⋙ F)] :
    PreservesLimitsOfShape (Discrete I) F := by
  classical
  have h (K : I → D) : PreservesLimit (Discrete.functor K) F := by
    let K' := fun n ↦ Q.objPreimage (K n)
    let e : Discrete.functor K' ⋙ Q ≅ Discrete.functor K :=
      Discrete.natIso (fun n ↦ Q.objObjPreimageIso (K n.as))
    have : PreservesLimit (Discrete.functor K' ⋙ Q) F :=
      preservesLimit_of_preserves_limit_cone
        (isLimitOfPreserves Q (limit.isLimit (Discrete.functor K')))
        (isLimitOfPreserves (Q ⋙ F) (limit.isLimit (Discrete.functor K')))
    exact preservesLimit_of_iso_diagram F e
  let := h
  exact preservesLimitsOfShape_of_discrete F

private theorem derived_products_of_Q
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (I : Type*) [HasProductsOfShape I C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete I) F]
    [PreservesLimitsOfShape (Discrete I) (DerivedCategory.Q (C := C))]
    [PreservesLimitsOfShape (Discrete I) (DerivedCategory.Q (C := D))] :
    PreservesLimitsOfShape (Discrete I) F.mapDerivedCategory := by
  have : PreservesLimitsOfShape (Discrete I)
      (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact products_of_essSurj I DerivedCategory.Q F.mapDerivedCategory

private noncomputable abbrev fixed_forget (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) :=
  sheafCompose (ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

private noncomputable def fixed_pullback_forget_iso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ProEtale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ fixed_forget Λ X ≅
      fixed_forget Λ Y ⋙ ProEtale.upperStar AddCommGrpCat.{u + 1} f := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let Z := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  have : Z.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (Int.castRingHom Λ)).isLeftAdjoint
  have : (Z ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    inferInstance
  have : U.IsLeftAdjoint :=
    inferInstanceAs (Z ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  have : (ProEt.topology X).PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification (ProEt.topology X) U
  let L := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op
  let P := sheafToPresheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)
  let Q := presheafToSheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let R := presheafToSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}
  let W := (Functor.whiskeringRight X.ProEtᵒᵖ _ _).obj U
  have : U.PreservesLeftKanExtensions L := by
    intro F
    have : U.PreservesPointwiseLeftKanExtension F L := by
      intro c
      let : PreservesColimitsOfShape (CostructuredArrow L c) U :=
        (Adjunction.ofIsLeftAdjoint U).leftAdjoint_preservesColimits.preservesColimitsOfShape
      let : PreservesColimit (CostructuredArrow.proj L c ⋙ F) U :=
        PreservesColimitsOfShape.preservesColimit
      exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit U F L c
    exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise U F L
  let e := sheafComposeNatIso (ProEt.topology X) U
    (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)
  let e' := U.lanCompIsoOfPreserves L
  change (P ⋙ L.lan ⋙ Q) ⋙ sheafCompose _ U ≅ _
  refine (Functor.associator P (L.lan ⋙ Q) (sheafCompose _ U)) ≪≫ ?_
  refine Functor.isoWhiskerLeft P
    ((Functor.associator L.lan Q (sheafCompose _ U)) ≪≫
      Functor.isoWhiskerLeft L.lan e.symm ≪≫
      (Functor.associator L.lan W R).symm ≪≫
      Functor.isoWhiskerRight e' R) ≪≫ ?_
  exact Iso.refl _

private theorem fixed_pullback_products (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    CategoryTheory.Limits.PreservesLimitsOfShape (Discrete ℕ)
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have hforget (T : Scheme.{u}) :
      PreservesLimitsOfShape (Discrete ℕ) (fixed_forget Λ T) := by
    have : PreservesLimitsOfShape (Discrete ℕ)
        (fixed_forget Λ T ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
        (sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj U))
    exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have := hforget X
  have := hforget Y
  have : PreservesLimitsOfShape (Discrete ℕ)
      (ProEtale.upperStar AddCommGrpCat.{u + 1} f) :=
    by
      have h := (proEtale_immersion_inverseImage_preservesLimits f).2.1
      have : PreservesLimitsOfShape (Discrete (ULift.{u + 1} ℕ))
          (ProEtale.upperStar AddCommGrpCat.{u + 1} f) := h.preservesLimitsOfShape
      exact preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  have : ReflectsLimitsOfShape (Discrete ℕ) (fixed_forget Λ X) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape (Discrete ℕ)
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f ⋙ fixed_forget Λ X) :=
    preservesLimitsOfShape_of_natIso (fixed_pullback_forget_iso Λ f).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (fixed_forget Λ X)

private theorem fixed_open_products (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    PreservesLimitsOfShape (Discrete ℕ)
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j) := by
  let Z : TopologicalSpace.Closeds X :=
    ⟨(Set.range j)ᶜ, (Scheme.Hom.isOpenEmbedding j).isOpen_range.isClosed_compl⟩
  let i := (IdealSheafData.vanishingIdeal Z).subschemeι
  have hi : Set.range j = (Set.range i)ᶜ := by simp [i, Z]
  let C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let F := ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j
  let Q := ProEtale.upperStar (ModuleCat.{u + 1} Λ) j
  let H := ProEtale.upperStar (ModuleCat.{u + 1} Λ) i ⋙
    ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i
  let a : Q ⋙ F ⟶ 𝟭 C :=
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).counit
  let b : 𝟭 C ⟶ H :=
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit
  have hm (M : C) := ProEtale.exact_openClosedSequence Λ i j hi M
  have hab (M : C) : a.app M ≫ b.app M = 0 := ((hm M).2.2.sc 0).zero
  have hk (M : C) : IsLimit (KernelFork.ofι (a.app M) (hab M)) := by
    have : Mono (a.app M) := (hm M).1
    have he := (hm M).2.2.exact 0 (by omega)
    change (ShortComplex.mk (a.app M) (b.app M) _).Exact at he
    exact he.fIsKernel
  have := fixed_pullback_products Λ i
  have : PreservesLimitsOfShape (Discrete ℕ) H := comp_preservesLimitsOfShape _ _
  have : PreservesLimitsOfShape (Discrete ℕ) (Q ⋙ F) :=
    kernel_preserves_products ℕ (Q ⋙ F) (𝟭 C) H a b hab hk
  have : PreservesLimitsOfShape (Discrete ℕ) Q :=
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) j).rightAdjoint_preservesLimits.preservesLimitsOfShape
  have : Q.EssSurj := ⟨fun N ↦ ⟨F.obj N,
    ⟨(asIso ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) j).unit.app N)).symm⟩⟩⟩
  exact products_of_essSurj ℕ Q F

private theorem intrinsic_open_products (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    PreservesLimitsOfShape (Discrete ℕ) (sfIntrinsicExtensionByZero j A) := by
  have := fixed_open_products (ULift.{u + 1, u} A) j
  unfold sfIntrinsicExtensionByZero
  infer_instance

private theorem intrinsic_pullback_products (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsImmersion j] :
    PreservesLimitsOfShape (Discrete ℕ) (sfIntrinsicPullback A j) := by
  have := fixed_pullback_products (ULift.{u + 1, u} A) j
  unfold sfIntrinsicPullback sfIntrinsicTransport
  infer_instance

private theorem support_of_homotopyLimit
    {C D : Type*} [Category C] [Category D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) [F.Full] [F.Faithful]
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [F.Additive] [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F] [PreservesLimitsOfShape (Discrete ℕ) G]
    {T : ℕᵒᵖ ⥤ D} (c : Cone T)
    (hc : CategoryTheory.Pretriangulated.IsHomotopyLimit c)
    (h : ∀ n : ℕ, IsIso (adj.counit.app (T.obj (Opposite.op n)))) :
    IsIso (adj.counit.app c.pt) := by
  let e : (T ⋙ G) ⋙ F ≅ T := NatIso.ofComponents
    (fun n ↦ by have := h n.unop; exact asIso (adj.counit.app (T.obj n)))
    (by intro a b f; exact adj.counit.naturality (T.map f))
  let c' := (Cone.postcompose e.hom).obj (F.mapCone (G.mapCone c))
  have hh : CategoryTheory.Pretriangulated.IsHomotopyLimit c' :=
    ((hc.map G).map F).of_iso e c' (Iso.refl _) (by intro n; simp [c'])
  obtain ⟨d, _⟩ := hc.exists_iso hh
  exact adj.isIso_counit_app_of_iso d

private theorem postnikov_homotopyLimit
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    (L : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ) :
    ∃ (c : Cone (ProEt.postnikovTower L ⋙ DerivedCategory.Q.{u + 2, u + 1, u + 2})),
      c.pt = DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj L ∧
      CategoryTheory.Pretriangulated.IsHomotopyLimit c := by
  let C := proEtaleRingModules X (proEtaleConstantRing X A)
  let R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)
  have : HasExactLimitsOfShape (Discrete ℕ) C := ProEt.products_exact.{u, u + 1, 0} X R ℕ
  let T := ProEt.postnikovTower L
  let V := fun n : ℕ ↦ T.obj (Opposite.op n)
  let P := ∏ᶜ V
  let φ : P ⟶ P := towerTransitionEndomorphism
    (WeilConjectures.integralOperationsTowerStep T)
  let M := CochainComplex.mappingCocone φ
  let p : Fan (fun n : ℕ ↦ (T ⋙ DerivedCategory.Q.{u + 2, u + 1, u + 2}).obj (Opposite.op n)) :=
    Fan.mk (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P)
      (fun n ↦ DerivedCategory.Q.{u + 2, u + 1, u + 2}.map (Pi.π V n))
  let hp : IsLimit p := DerivedCategory.isLimitFanQ V
  have hm : DerivedCategory.Q.{u + 2, u + 1, u + 2}.map φ = 𝟙 p.pt -
      CategoryTheory.Pretriangulated.towerShift hp := by
    apply Fan.IsLimit.hom_ext hp
    intro n
    calc
      DerivedCategory.Q.map φ ≫ p.proj n = DerivedCategory.Q.map
          (Pi.π V n - Pi.π V (n + 1) ≫ T.map (homOfLE n.le_succ).op) := by
        change DerivedCategory.Q.map φ ≫ DerivedCategory.Q.map (Pi.π V n) = _
        rw [← Functor.map_comp]
        congr 1
        simp only [φ, towerTransitionEndomorphism, Preadditive.sub_comp,
          towerProductShift, Pi.lift_π]
        rfl
      _ = _ := by
        rw [Functor.map_sub, Functor.map_comp]
        simp only [Preadditive.sub_comp,
          Pretriangulated.towerShift, Fan.IsLimit.fac]
        rfl
  let t := DerivedCategory.Q.{u + 2, u + 1, u + 2}.mapTriangle.obj
    (CochainComplex.mappingCocone.triangle φ)
  have ht := DerivedCategory.mappingCocone_triangle_distinguished φ
  have hz : t.mor₁ ≫ (𝟙 p.pt - CategoryTheory.Pretriangulated.towerShift hp) = 0 := by
    rw [← hm]
    exact CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂ t ht
  let c : Cone (T ⋙ DerivedCategory.Q.{u + 2, u + 1, u + 2}) :=
    { pt := t.obj₁
      π := NatTrans.ofOpSequence (fun n ↦ t.mor₁ ≫ p.proj n) (by
        intro n
        have hh := congrArg (fun g ↦ g ≫ p.proj n) hz
        dsimp only [Functor.const_obj_map]
        erw [Category.id_comp]
        have h := hh
        simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
          zero_comp, Pretriangulated.towerShift, Fan.IsLimit.fac,
          sub_eq_zero] at h
        exact h) }
  have hc : CategoryTheory.Pretriangulated.IsHomotopyLimit c := by
    refine ⟨p, hp, t.mor₃, ?_⟩
    apply CategoryTheory.Pretriangulated.isomorphic_distinguished t ht
    refine CategoryTheory.Pretriangulated.Triangle.isoMk _ _
      (Iso.refl (DerivedCategory.Q.obj M)) (Iso.refl (DerivedCategory.Q.obj P))
      (Iso.refl (DerivedCategory.Q.obj P)) ?_ ?_ ?_
    · change Fan.IsLimit.lift hp (fun n ↦ c.π.app (Opposite.op n)) ≫ 𝟙 _ =
        𝟙 _ ≫ DerivedCategory.Q.map (CochainComplex.mappingCocone.fst φ)
      simp only [Category.comp_id, Category.id_comp]
      apply Fan.IsLimit.hom_ext hp
      intro n
      simp only [c, NatTrans.ofOpSequence_app, Fan.IsLimit.fac]
      change t.mor₁ ≫ p.proj n = t.mor₁ ≫ p.proj n
      rfl
    · change (𝟙 p.pt - Pretriangulated.towerShift hp) ≫ 𝟙 _ =
        𝟙 _ ≫ DerivedCategory.Q.map φ
      simpa only [Category.comp_id, Category.id_comp] using hm.symm
    · change t.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = 𝟙 _ ≫ t.mor₃
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  have : QuasiIso (ProEt.postnikovComparison L) := ProEt.left_complete_quasiIso.{u, u + 1} X R L
  let e : DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj M ≅
      DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj L :=
    (asIso (DerivedCategory.Q.{u + 2, u + 1, u + 2}.map (ProEt.postnikovComparison L))).symm
  let d : Cone (T ⋙ DerivedCategory.Q.{u + 2, u + 1, u + 2}) :=
    { pt := DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj L
      π :=
        { app n := e.inv ≫ c.π.app n
          naturality a b g := by
            simpa [Category.assoc] using congrArg (e.inv ≫ ·) (c.w g).symm } }
  exact ⟨d, rfl, hc.of_iso (Iso.refl _) d e (by intro n; simp [d])⟩

/-- The actual open-adjunction counit is invertible on the proper direct image of an
extension by zero, for every object of the ordinary unbounded derived category.

Source: Weil blueprint, `sec-smooth-purity/sk-prop-sf-existence`, clause (b),
compactification independence; the agent-extracted support obligation
(blueprint: lem-sp-proper-open-derived-support).

Proof in words (the ten steps of the node):
1. First prove the sheaf-level support assertion. Let $F$ be an $A_X$-module sheaf on
   $X_{\mathrm{proet}}$. Give $T_2\setminus j_2(X)$ its reduced induced closed subscheme
   $i_2:Z\hookrightarrow T_2$ using [lem-weil-pbc-reduced-induced-closed-subscheme]. Work over any
   affine open $O\subset T_2$. By [lem-exc-closed-inverse-image-formula], to show
   $i_2^*(u_*j_{1!}F)|_{Z\cap O}=0$ it suffices to show $(u_*j_{1!}F)(v(V))=0$ for every affine
   ind-etale basis object $V$ over $Z\cap O$. Indeed, the inverse image is the sheafification of
   these values. By [lem-weil-pbc-affine-closed-site-functor-properties], $W=v(V)$ is affine over
   $O$, $W\times_{T_2}Z=V$, and every point of $W$ specializes to a point of $V$. The same formula
   is valid on underlying abelian sheaves of our constant modules: the scalar action is simply
   retained under the inverse-image construction of [def-weil-pbc-proetale-operations]. Uses:
   lem-weil-pbc-reduced-induced-closed-subscheme, lem-exc-closed-inverse-image-formula,
   lem-weil-pbc-affine-closed-site-functor-properties, def-weil-pbc-proetale-operations.
2. Put $P=T_1\times_{T_2}W$ and $Z_P=P\times_{T_2}Z$. Every point $t\in P$ specializes to a point
   of $Z_P$. In fact the image of the closed subset $\overline{\{t\}}\subset P$ under $P\to W$ is
   closed, since $u$ is universally closed by [def-weil-proper-morphism]. It contains the image of
   $t$ and therefore a specialization of that image in $V$; a point of $\overline{\{t\}}$ over
   that specialization gives the required point of $Z_P$. Properness is preserved by
   [lem-weil-pbc-proper-base-change], so $P$ is quasi-compact and separated over the affine $W$.
   The complement of $Z_P$ is a quasi-compact open immersion, being the pullback of $j_2$ by
   [lem-pc-quasi-compact-base-change, lem-weil-pbc-open-immersion-base-change]. Uses:
   def-weil-proper-morphism, lem-weil-pbc-proper-base-change, lem-pc-quasi-compact-base-change,
   lem-weil-pbc-open-immersion-base-change.
3. Cover $Z_P$ by finitely many affine opens $P_a=\operatorname{Spec}R_a$ of $P$. Write $Z_P\cap
   P_a=V(I_a)$. Since its complementary open is quasi-compact, a finite principal-open subcover
   writes $V(I_a)=V(f_{a1},\ldots,f_{as_a})$ with $f_{ab}\in I_a$. By
   [lem-weil-pbc-wcontractible-closed-localization], $P_a^\sim=\operatorname{Spec}(S_a^{-1}R_a)$,
   where $S_a$ consists of elements invertible modulo $I_a$, has image exactly the points of $P_a$
   specializing to $Z_P\cap P_a$. Every point of $P$ specializes to a point of $Z_P$, hence is in
   some $P_a$ and in the image of $P_a^\sim$. These finitely many affine ind-Zariski maps are a
   pro-etale cover of $P$: on an affine open $Q$ of $P$, the intersection $P_a\cap Q$ is affine,
   since it is the pullback of the closed diagonal of $P\to W$ inside the affine $P_a\times_WQ$. A
   closed immersion is affine by [def-weil-closed-immersion], and closed immersions pull back by
   [lem-weil-pbc-closed-immersion-base-change]. The localization pullback to this intersection is
   affine too, so the inverse images of $Q$ are affine and jointly surjective. The same
   closed-base-change lemma makes $Z_P$ and its affine restrictions closed subschemes. Stability
   in [lem-weil-pbc-ind-etale-stability] and [def-weil-pbc-proetale-covering] justify the site
   claim. Viewed over $T_1$, each $P_a^\sim$ is affine weakly etale and all its points specialize
   to the closed inverse image of $Z$; this follows from the localization description and
   weakly-etale base-change/composition in that same stability lemma. That closed subscheme is
   disjoint from $j_1(X)$ because $uj_1=j_2$. Thus
   [lem-weil-pbc-proetale-shriek-specialization-zero] gives $(j_{1!}F)(P_a^\sim)=0$. The sheaf
   equalizer axiom makes $(j_{1!}F)(P)=0$. By the direct-image section formula in
   [def-weil-pbc-proetale-operations], this is $(u_*j_{1!}F)(W)=0$. Uses:
   lem-weil-pbc-wcontractible-closed-localization, lem-weil-pbc-ind-etale-stability,
   def-weil-pbc-proetale-covering, lem-weil-pbc-proetale-shriek-specialization-zero,
   def-weil-pbc-proetale-operations, lem-weil-pbc-closed-immersion-base-change,
   def-weil-closed-immersion.
4. Steps 1-3 show $i_2^*(u_*j_{1!}F)=0$. The exact sequence of
   [lem-weil-pbc-proetale-ringed-open-closed], applied on $T_2$ with $M_F=u_*j_{1!}F$, now reads
   $0\to j_{2!}j_2^*M_F\xrightarrow{\varepsilon}M_F\to0$. Its first arrow is the specified
   open-adjunction counit, so it is an isomorphism, naturally in every sheaf $F$. Notice that this
   argument uses neither geometric-stalk conservativity nor a higher-cohomology consequence of Tag
   09AG. Uses: lem-weil-pbc-proetale-ringed-open-closed.
5. Now let $K$ be bounded below. By [prop-pur-kinjective-resolutions-exist] the module categories
   on these small sites are Grothendieck abelian with enough injectives, and
   [lem-weil-pbc-dplus-injective-representative] supplies a bounded-below complex $J^\bullet$ of
   injective $A_X$-module sheaves representing $K$. Since $j_{1!}$ is exact
   [lem-weil-extension-by-zero-exact], $j_{1!}J^\bullet$ represents $j_{1!}K$. Apply
   [lem-sp-proetale-open-injective-proper-acyclic] to the square with $C=E=X$, $r=1_X$, $B=T_1$,
   $D=T_2$, $k=j_1$, $i=j_2$, $p=u$; identity is proper directly from its defining conditions. All
   open immersions are quasi-compact by hypothesis. Every term $j_{1!}J^a$ is $u_*$-acyclic. The
   bounded-below complexes clause of [lemma-weil-pbc-leray-acyclicity] consequently computes
   $M=Ru_*j_{1!}K$ by $u_*j_{1!}J^\bullet$. Step 4 makes the actual counit an isomorphism in every
   degree of this representing complex. Its localization is therefore exactly the derived counit
   $j_{2!}j_2^*M\to M$ of [prop-exc-open-adjoint], and is an isomorphism. Uses:
   prop-pur-kinjective-resolutions-exist, lem-weil-pbc-dplus-injective-representative,
   lem-weil-extension-by-zero-exact, lem-sp-proetale-open-injective-proper-acyclic,
   lemma-weil-pbc-leray-acyclicity, prop-exc-open-adjoint.
6. Here is the elementary sheaf-product argument, replacing a separate product lemma. For a
   quasi-compact open $j:U\hookrightarrow T$, choose its reduced closed complement
   $i:Z\hookrightarrow T$ by [lem-weil-pbc-reduced-induced-closed-subscheme]. Put $P=\prod_a
   j_!F_a$ for a countable family of constant-$A$ module sheaves. By
   [lem-weil-pbc-proetale-ringed-open-closed] and preservation of products by both immersion
   inverse images [lem-weil-pbc-proetale-immersion-limit-preservation], we have $i^*P=\prod_a
   i^*j_!F_a=0$ and $j^*P=\prod_a j^*j_!F_a\cong\prod_aF_a$. The same open-closed sequence
   therefore makes the counit $j_!j^*P\to P$ an isomorphism. Under the displayed identification
   its composite with each projection $P\to j_!F_a$ is $j_!$ of the corresponding projection, by
   naturality of the counit and the open unit $j^*j_!\cong1$. Thus it is precisely the canonical
   product comparison $j_!(\prod_aF_a)\to\prod_a j_!F_a$. This applies to $j=j_1$ and uses
   identified constant coefficient rings throughout. Uses:
   lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-proetale-ringed-open-closed,
   lem-weil-pbc-proetale-immersion-limit-preservation.
7. Countable products in pro-etale module categories are exact by
   [lem-weil-proetale-countable-products-exact]. By [lem-pc-ringed-space-product-kinjective],
   products of K-injective representatives represent derived products. Termwise products of
   arbitrary representing complexes also represent derived products: resolve each factor by a
   K-injective, take the product of the quasi-isomorphisms, and use exactness of products to see
   that its cone, the product of the acyclic cones, is acyclic. Thus an exact functor preserving
   countable sheaf products preserves countable derived products. Apply this to $j_{1!}$ using its
   product preservation proved in step 6 and [lem-weil-extension-by-zero-exact]. Also apply it to
   $i_2^*$: [lem-weil-pbc-proetale-immersion-limit-preservation] states both its exactness and its
   preservation of all sheaf limits for identified coefficient rings. Here the coefficients are
   constant $A$, with their canonical inverse-image identification. These exact functors induce
   triangulated functors by [lem-sf-exact-functor-derived-triangulated]. Uses:
   lem-weil-proetale-countable-products-exact, lem-pc-ringed-space-product-kinjective,
   lem-weil-extension-by-zero-exact, lem-sf-exact-functor-derived-triangulated,
   lem-weil-pbc-proetale-immersion-limit-preservation.
8. The functor $Ru_*$ is triangulated and right adjoint to exact inverse image by
   [def-weil-pbc-proetale-operations]. Hence it preserves countable derived products by
   [lem-weil-pbc-right-adjoint-preserves-limits]. Together with step 7, this says that
   $F=Ru_*j_{1!}$ and $i_2^*F$ are triangulated and preserve countable products. Recall
   [def-weil-derived-limit]: a tower $(N_n,t_n)$ has a homotopy-limit triangle
   $L\to\prod_nN_n\xrightarrow{1-s}\prod_nN_n\to L[1]$, where
   $\operatorname{pr}_ns=t_n\operatorname{pr}_{n+1}$. Applying $F$ preserves this triangle and,
   under its canonical product comparisons, preserves precisely $1-s$, since it preserves each
   projection and each transition. The same holds for $i_2^*$. We use only this triangle property;
   no uniqueness of a third arrow between triangles or of an arbitrary triangulated homotopy-limit
   comparison is assumed. Uses: def-weil-pbc-proetale-operations,
   lem-weil-pbc-right-adjoint-preserves-limits, def-weil-derived-limit.
9. For arbitrary $K$, put $K_n=\tau_{\geq-n}K$. Every pro-etale object has a cover by affine
   weakly contractible objects by [lem-weil-pbc-proetale-affine-wcontractible-covering-family]. On
   such an object evaluation is exact: a section of the target of a module epimorphism has locally
   a lift, the corresponding epimorphism of sheaves of lifts has a section by weak
   contractibility, and left exactness is the sheaf equalizer property. Hence $H^p(W,F)=0$ for
   $p>0$ and every module sheaf $F$, by applying the exact evaluation to an injective resolution.
   Apply [lem-kun-site-truncation-derived-limit] with this covering family and $d=0$. Its
   hypotheses hold for every negative cohomology sheaf of $K$, and it gives the triangle
   $K\to\prod_nK_n\xrightarrow{1-s}\prod_nK_n\to K[1]$. Thus the required lower-truncation
   homotopy limit is $K$ itself, with its canonical truncation maps. Uses:
   lem-weil-pbc-proetale-affine-wcontractible-covering-family,
   lem-kun-site-truncation-derived-limit.
10. For each $K_n$, step 5 gives $j_{2!}j_2^*F(K_n)\xrightarrow{\sim}F(K_n)$. The exact sheaf
   sequence in [lem-weil-pbc-proetale-ringed-open-closed] yields, on any representing complex $C$,
   a short exact sequence of complexes $0\to j_{2!}j_2^*C\to C\to i_{2*}i_2^*C\to0$. The closed
   counit $i_2^*i_{2*}\cong\operatorname{id}$ and $i_2^*j_{2!}=0$ are also in that cited
   statement. It follows that $i_2^*F(K_n)=0$. Apply $i_2^*F$ to the truncation triangle of step
   9. By step 8 its two product terms are products of these zero objects. The resulting triangle
   has the form $i_2^*F(K)\to0\to0\to i_2^*F(K)[1]$, whence $i_2^*F(K)=0$ by the exact Hom
   sequence. In the short exact sequence of complexes just displayed for a representative $C$ of
   $F(K)$, $i_2^*C$ is therefore acyclic. Exactness of $i_{2*}$, again stated by the cited ringed
   open-closed lemma, makes $i_{2*}i_2^*C$ acyclic. Thus its first arrow is a quasi-isomorphism.
   That arrow is termwise the specified open counit, so its localization is exactly
   $j_{2!}j_2^*Ru_*j_{1!}K\to Ru_*j_{1!}K$, as required. This identifies the actual counit,
   without using a possibly noncanonical isomorphism between homotopy limits. Uses:
   lem-weil-pbc-proetale-ringed-open-closed.
-/
theorem isIso_proper_open_derived_support
    {X T₁ T₂ : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (_comm : j₁ ≫ f = j₂) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory X A) :
    IsIso ((exceptionalOpenAdjunction j₂ A).counit.app
      ((proEtaleConstantDerivedDirectImage f A).obj ((sfIntrinsicDerivedOpen A j₁).obj K))) := by
  let C := proEtaleRingModules X (proEtaleConstantRing X A)
  let D := proEtaleRingModules T₁ (proEtaleConstantRing T₁ A)
  let E := proEtaleRingModules T₂ (proEtaleConstantRing T₂ A)
  have hex (T : Scheme.{u}) : HasExactLimitsOfShape (Discrete ℕ)
      (proEtaleRingModules T (proEtaleConstantRing T A)) :=
    ProEt.products_exact.{u, u + 1, 0} T ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T A)) ℕ
  have := hex X
  have := hex T₁
  have := hex T₂
  let J₁ := sfIntrinsicExtensionByZero j₁ A
  let J₂ := sfIntrinsicExtensionByZero j₂ A
  let G₂ := sfIntrinsicPullback A j₂
  let P := proEtaleConstantModuleDirectImage f A
  have : PreservesLimitsOfShape (Discrete ℕ) J₁ := intrinsic_open_products A j₁
  have : PreservesLimitsOfShape (Discrete ℕ) J₂ := intrinsic_open_products A j₂
  have : PreservesLimitsOfShape (Discrete ℕ) G₂ := intrinsic_pullback_products A j₂
  have : PreservesLimitsOfShape (Discrete ℕ) J₁.mapDerivedCategory :=
    derived_products_of_Q ℕ J₁
  have : PreservesLimitsOfShape (Discrete ℕ) J₂.mapDerivedCategory :=
    derived_products_of_Q ℕ J₂
  have : PreservesLimitsOfShape (Discrete ℕ) G₂.mapDerivedCategory :=
    derived_products_of_Q ℕ G₂
  have : PreservesLimitsOfShape (Discrete ℕ) P.rightDerivedFunctor :=
    (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction
      |>.rightAdjoint_preservesLimits.preservesLimitsOfShape
  have : J₂.Full := by unfold J₂ sfIntrinsicExtensionByZero; infer_instance
  have : J₂.Faithful := by unfold J₂ sfIntrinsicExtensionByZero; infer_instance
  let adj := exceptionalOpenAdjunction j₂ A
  have ff := adj.fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso J₂ G₂).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso (sfIntrinsicOpenAdjunction A j₂).unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso C)
  have := ff.full
  have := ff.faithful
  let Φ := J₁.mapDerivedCategory ⋙ P.rightDerivedFunctor
  let L := DerivedCategory.Q.{u + 2, u + 1, u + 2}.objPreimage K
  obtain ⟨c, hpt, hc⟩ := postnikov_homotopyLimit X A L
  have hs : IsIso (adj.counit.app (Φ.obj (DerivedCategory.Q.obj L))) := by
    rw [← hpt]
    apply support_of_homotopyLimit J₂.mapDerivedCategory G₂.mapDerivedCategory adj
      (Φ.mapCone c) (hc.map Φ)
    intro n
    have : (DerivedCategory.Q.obj (ProEt.postnikovTower L |>.obj
        (Opposite.op n))).IsGE (-(n : ℤ)) := by
      change (DerivedCategory.Q.obj (L.truncGE (-(n : ℤ)))).IsGE (-(n : ℤ))
      infer_instance
    exact bounded_proper_open_support f j₁ j₂ _comm A
      (DerivedCategory.Q.obj (ProEt.postnikovTower L |>.obj (Opposite.op n)))
      (-(n : ℤ))
  exact (NatTrans.isIso_app_iff_of_iso adj.counit
    (Φ.mapIso (DerivedCategory.Q.objObjPreimageIso K))).1 hs

end AlgebraicGeometry.Scheme

end
