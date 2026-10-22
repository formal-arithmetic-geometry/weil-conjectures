/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.FiniteComparisonCoefficients
public import Sheaf.Paper.FiniteComparisonModelRealization
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import all Sheaf.Paper.FiniteComparisonModelRealization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
import all Sheaf.AlgebraicGeometry.CoefficientTorFlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import all Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.Paper.ProEtaleFiniteModelLocalConstancy
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.Flat
import all Sheaf.Paper.FiniteComparisonCoefficients
import all Sheaf.Paper.FiniteDiscreteEncodedPresentation
import all Sheaf.Paper.FiniteDiscreteRestrictionEncoding
import all Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import all Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
import all Sheaf.Paper.InternalModuleAbEquivalence
import all Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.Paper.CompletedIntegralCoefficients
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
import Sheaf.Paper.FiniteDiscreteConstructibleEncoding
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel

/-! # Coefficient presentation of the finite comparison predicates

Source: blueprint finite comparison, coefficient paragraph, and Stacks Tags 03CY,
09AJ and 09AL (blueprint: lem-ctf-finite-comparison-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c d h k w
open CategoryTheory CategoryTheory.Limits
section FiniteComparisonProof

-- Fix the coefficient universes only within these private proofs.
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

open MonoidalCategory
open scoped CategoryTheory.Obj

@[instance_reducible] private def monoidalOfOplaxIsos
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (μ : ∀ M N : C, F.obj (M ⊗ N) ≅ F.obj M ⊗ F.obj N)
    (hn : ∀ {M M' N N' : C} (f : M ⟶ M') (g : N ⟶ N'),
      F.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (F.map f ⊗ₘ F.map g))
    (ha : ∀ M N P : C,
      (μ (M ⊗ N) P).hom ≫ (μ M N).hom ▷ F.obj P ≫ (α_ _ _ _).hom =
        F.map (α_ M N P).hom ≫ (μ M (N ⊗ P)).hom ≫ F.obj M ◁ (μ N P).hom)
    (hl : ∀ M : C,
      (μ (𝟙_ C) M).hom ≫ ε.hom ▷ F.obj M ≫ (λ_ _).hom = F.map (λ_ M).hom)
    (hr : ∀ M : C,
      (μ M (𝟙_ C)).hom ≫ F.obj M ◁ ε.hom ≫ (ρ_ _).hom = F.map (ρ_ M).hom) :
    F.Monoidal := by
  refine (Functor.CoreMonoidal.mk' (F := F) ε.symm (fun M N ↦ (μ M N).symm)
    (fun f N ↦ ?_) (fun M f ↦ ?_) ha (fun M ↦ ?_) (fun M ↦ ?_)).toMonoidal
  · simpa only [Iso.symm_inv, CategoryTheory.Functor.map_id, tensorHom_id] using (hn f (𝟙 N)).symm
  · simpa only [Iso.symm_inv, CategoryTheory.Functor.map_id, id_tensorHom] using (hn (𝟙 M) f).symm
  · apply (cancel_mono (λ_ _).hom).mp
    dsimp only [Iso.symm_inv]
    rw [Iso.inv_hom_id, Category.assoc, Category.assoc, hl,
      ← F.map_comp, Iso.inv_hom_id]
    exact (F.map_id M).symm
  · apply (cancel_mono (ρ_ _).hom).mp
    dsimp only [Iso.symm_inv]
    rw [Iso.inv_hom_id, Category.assoc, Category.assoc, hr,
      ← F.map_comp, Iso.inv_hom_id]
    exact (F.map_id M).symm

attribute [local irreducible] monoidalOfOplaxIsos

open InternalAbelianSheafModule in
private theorem sectionMonoidal_exists
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [UnivLE.{max c h, w}] [HasSheafify J Ab.{w}]
    [(J.W (A := Ab.{w})).IsMonoidal]
    (R : Sheaf J Ab.{w}) [MonObj R] [IsCommMonObj R] :
    Nonempty (InternalAbelianSheafModule.sectionModuleEquivalence J R).functor.Monoidal := by
  obtain ⟨e, e₀, hh⟩ := (internal_section_tensor_comparison J R).2
  refine ⟨monoidalOfOplaxIsos (sectionModuleEquivalence J R).functor e₀ e ?_ ?_ ?_ ?_⟩
  · intro M M' N N' f g
    exact hh.2.2.1 M M' N N' f g
  · exact hh.2.2.2.1
  · exact hh.2.2.2.2.1
  · exact hh.2.2.2.2.2.1

open InternalAbelianSheafModule in
@[instance_reducible] private def sectionMonoidal
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [UnivLE.{max c h, w}] [HasSheafify J Ab.{w}]
    [(J.W (A := Ab.{w})).IsMonoidal]
    (R : Sheaf J Ab.{w}) [MonObj R] [IsCommMonObj R] :
    (InternalAbelianSheafModule.sectionModuleEquivalence J R).functor.Monoidal :=
  Classical.choice (sectionMonoidal_exists J R)

attribute [local irreducible] sectionMonoidal

@[instance_reducible] private def monoidalOfAdjointEquivalence
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (E : C ≌ D) (L : C ⥤ D) (adj : L ⊣ E.inverse) [L.Monoidal] :
    E.functor.Monoidal :=
  Functor.Monoidal.transport (adj.leftAdjointUniq E.toAdjunction)

@[instance_reducible] private def monoidalOfInverse
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (E : C ≌ D) (F : C ⥤ D) (G : D ⥤ C) [G.Monoidal]
    (i : F ≅ E.functor) (j : G ≅ E.inverse) : F.Monoidal := by
  letI : E.inverse.Monoidal := Functor.Monoidal.transport j
  letI : E.functor.Monoidal := E.symm.inverseMonoidal
  exact Functor.Monoidal.transport i.symm

private theorem monoidalOfInverse_exists
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (E : C ≌ D) (F : C ⥤ D) (G : D ⥤ C)
    (hG : Nonempty G.Monoidal) (i : F ≅ E.functor) (j : G ≅ E.inverse) :
    Nonempty F.Monoidal := by
  obtain ⟨mG⟩ := hG
  let := mG
  exact ⟨monoidalOfInverse E F G i j⟩

attribute [local irreducible] monoidalOfAdjointEquivalence monoidalOfInverse

private theorem monoidal_action_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (P : C ⥤ D) (F : D ⥤ E) (S : C ⥤ E)
    [P.LaxMonoidal] [F.LaxMonoidal] [S.LaxMonoidal]
    (τ : S ≅ P ⋙ F) [NatTrans.IsMonoidal τ.inv]
    (R N : C) (act : R ⊗ N ⟶ N) :
    (Functor.LaxMonoidal.μ F (P.obj R) (P.obj N) ≫
        F.map (Functor.LaxMonoidal.μ P R N ≫ P.map act)) ≫ τ.inv.app N =
      F.obj (P.obj R) ◁ τ.inv.app N ≫ τ.inv.app R ▷ S.obj N ≫
        Functor.LaxMonoidal.μ S R N ≫ S.map act := by
  have h₁ := τ.inv.naturality act
  have h₂ := NatTrans.IsMonoidal.tensor (τ := τ.inv) R N
  rw [Functor.LaxMonoidal.comp_μ] at h₂
  rw [whisker_exchange_assoc, ← tensorHom_def_assoc, ← reassoc_of% h₂,
    ← h₁, F.map_comp, Category.assoc, Category.assoc]
  rfl

private theorem constantScalarMonoidal_exists
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Type (max c h)) [CommRing R] :
    Nonempty (ConstantScalarRestriction.restriction J R).Monoidal := by
  exact ⟨(ConstantScalarRestriction.ordinary J R).braided.toMonoidal⟩

@[instance_reducible] private def constantScalarMonoidal
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (R : Type (max c h)) [CommRing R] :
    (ConstantScalarRestriction.restriction J R).Monoidal :=
  Classical.choice (constantScalarMonoidal_exists J R)

attribute [local irreducible] constantScalarMonoidal

private theorem ringScalarMonoidal_exists
    {C : Type c} [Category.{h} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify J Ab.{w}] [J.WEqualsLocallyBijective Ab.{w}]
    {R S : Sheaf J CommRingCat.{w}} (i : R ≅ S) :
    Nonempty (SheafOfModules.scalarRestriction i.hom).Monoidal := by
  let : HasDerivedCategory.{max c h (w + 1)} (SheafOfModules.scalarModules J R) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{max c h (w + 1)} (SheafOfModules.scalarModules J S) :=
    HasDerivedCategory.standard _
  obtain ⟨t⟩ :=
    SheafOfModules.ringIso_tensor_transport.{c, h, w, max c h (w + 1), max c h (w + 1)} i
  exact ⟨t.monoidal.toMonoidal⟩

@[instance_reducible] private def ringScalarMonoidal
    {C : Type c} [Category.{h} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify J Ab.{w}] [J.WEqualsLocallyBijective Ab.{w}]
    {R S : Sheaf J CommRingCat.{w}} (i : R ≅ S) :
    (SheafOfModules.scalarRestriction i.hom).Monoidal :=
  Classical.choice (ringScalarMonoidal_exists i)

attribute [local irreducible] ringScalarMonoidal


private theorem map_eq_of_equivalence {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.IsEquivalence] (P : ObjectProperty C) (Q : ObjectProperty D)
    [Q.IsClosedUnderIsomorphisms] (h : ∀ K, P K ↔ Q (F.obj K)) : P.map F = Q := by
  classical
  funext L
  apply propext
  constructor
  · rintro ⟨K, hK, ⟨e⟩⟩
    exact Q.prop_of_iso e ((h K).mp hK)
  · intro hL
    let K := F.objPreimage L
    let e := F.objObjPreimageIso L
    exact ⟨K, (h K).mpr (Q.prop_of_iso e.symm hL), ⟨e⟩⟩

private theorem bounded_cohomology_transport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) :
    (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor C q).obj K)) ↔
    (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor D q).obj (F.mapDerivedCategory.obj K))) := by
  constructor
  · rintro ⟨a, b, hab, h⟩
    exact ⟨a, b, hab, fun q hq ↦
      F.isZero_homologyFunctor_mapDerivedCategory_obj (h q hq)⟩
  · rintro ⟨a, b, hab, h⟩
    exact ⟨a, b, hab, fun q hq ↦
      F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj (h q hq)⟩

attribute [local instance] CategoryTheory.moduleMonoidal CategoryTheory.moduleSymmetric
  CategoryTheory.moduleClosed CategoryTheory.modulePreadditive CategoryTheory.moduleGrothendieck
  CategoryTheory.flatResolution CategoryTheory.standardDerived

private theorem coefficient_finite_native
    {C : Type w} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) (K : ConstantCompletion.D R) :
    (∃ a b : ℤ, HasCoefficientModelTorAmplitude R K a b) ↔
      DerivedCategory.finiteTorAmplitude (ConstantCompletion.Mod R) K := by
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, (CategoryTheory.nativeTor_iff R K a b h.1).mpr h⟩
  · rintro ⟨a, b, h⟩
    have hh := h.mono (min_le_left a b) le_rfl
    exact ⟨min a b, b,
      (CategoryTheory.nativeTor_iff R K _ b (min_le_right a b)).mp hh⟩

private local instance coefficientFixedMonoidal
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type w) [CommRing A] : (coefficientModelFixedScalars J A).Monoidal := by
  letI : (ConstantScalarRestriction.restriction J A).Monoidal :=
    (ConstantScalarRestriction.ordinary J A).braided.toMonoidal
  let i : ConstantScalarRestriction.restriction J A ≅ coefficientModelFixedScalars J A :=
    CategoryTheory.restrictionIso J A
  exact Functor.Monoidal.transport i

private theorem bounded_iff_interval
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) :
    DerivedCategory.TStructure.t.bounded K ↔
      ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor C q).obj K) := by
  rw [← DerivedCategory.exists_homologyConcentratedIn_iff_bounded]
  constructor
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨min a b, b, min_le_right a b, fun q hq ↦ hq.elim
      (fun h ↦ (DerivedCategory.isGE_iff K a).mp ha q (h.trans_le (min_le_left a b)))
      (fun h ↦ (DerivedCategory.isLE_iff K b).mp hb q h)⟩
  · rintro ⟨a, b, _, hh⟩
    exact ⟨a, b, (DerivedCategory.isGE_iff K a).mpr (fun q h ↦ hh q (.inl h)),
      (DerivedCategory.isLE_iff K b).mpr (fun q h ↦ hh q (.inr h))⟩

private def leftSquareOfRight
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (L' : E ⥤ H) (R' : H ⥤ E) (adj' : L' ⊣ R')
    (F : C ≌ E) (G : D ≌ H) (i : R ⋙ F.functor ≅ G.functor ⋙ R') :
    L ⋙ G.functor ≅ F.functor ⋙ L' := by
  let a := adj.comp G.toAdjunction
  let b := F.toAdjunction.comp adj'
  let h : (G.inverse ⋙ R) ⋙ F.functor ≅ R' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G.inverse i ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.counitIso R' ≪≫ Functor.leftUnitor R'
  let h' : (R' ⋙ F.inverse) ⋙ F.functor ≅ R' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R' F.counitIso ≪≫
      Functor.rightUnitor R'
  let r := ((Functor.FullyFaithful.ofFullyFaithful F.functor).whiskeringRight _)
    |>.preimageIso (h ≪≫ h'.symm)
  exact ((conjugateIsoEquiv a b).symm r).symm

private def localFinite {C : Type c} [Category.{h} C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    (F : Sheaf J (ModuleCat.{w} A)) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ (U : C) (f : U ⟶ V), S f →
    ∃ M : ModuleCat.{w} A, Module.Finite A M ∧
      Nonempty (F.over U ≅ (constantSheaf (J.over U) (ModuleCat.{w} A)).obj M)

private theorem localFinite_precomp
    {C : Type c} {D : Type d} [Category.{h} C] [Category.{k} D]
    [HasPullbacks C] [HasPullbacks D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsEquivalence] [G.IsContinuous J K] [G.IsCocontinuous J K]
    (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    [∀ V : D, HasSheafify (K.over V) (ModuleCat.{w} A)]
    [HasLimitsOfSize.{h, max c h k} (ModuleCat.{w} A)]
    (F : Sheaf K (ModuleCat.{w} A)) (hF : localFinite K A F) :
    localFinite J A ((G.sheafPushforwardContinuous (ModuleCat.{w} A) J K).obj F) := by
  let : G.PreservesOneHypercovers J K :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (CoverPreserving.of_isContinuous G J K)
  intro V
  obtain ⟨S, hS, hm⟩ := hF (G.obj V)
  refine ⟨S.functorPullback G, G.cover_lift J K hS, fun U f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hm (G.obj U) (G.map f) hf
  let H : Over U ⥤ Over (G.obj U) := Over.post G
  let r : ((G.sheafPushforwardContinuous (ModuleCat.{w} A) J K).obj F).over U ≅
      (H.sheafPushforwardContinuous (ModuleCat.{w} A)
        (J.over U) (K.over (G.obj U))).obj (F.over (G.obj U)) :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let ce := (H.pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{w} A) (J.over U) (K.over (G.obj U))).symm.app
      ((Functor.const (Over (G.obj U))ᵒᵖ).obj M)
  exact ⟨M, hM, ⟨r ≪≫
    (H.sheafPushforwardContinuous (ModuleCat.{w} A)
      (J.over U) (K.over (G.obj U))).mapIso e ≪≫ ce⟩⟩

private theorem localFinite_iso
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    {F G : Sheaf J (ModuleCat.{w} A)} (e : F ≅ G) (hF : localFinite J A F) :
    localFinite J A G := by
  intro V
  obtain ⟨S, hS, hm⟩ := hF V
  refine ⟨S, hS, fun U f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := hm U f hf
  exact ⟨M, hM, ⟨(J.overPullback (ModuleCat.{w} A) U).mapIso e.symm ≪≫ i⟩⟩

private theorem localFinite_site_equivalence
    {C : Type c} {D : Type d} [Category.{h} C] [Category.{k} D]
    [HasPullbacks C] [HasPullbacks D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
    [e.inverse.IsDenseSubsite K J] (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    [∀ V : D, HasSheafify (K.over V) (ModuleCat.{w} A)]
    [HasLimitsOfSize.{h, max c h k} (ModuleCat.{w} A)]
    [HasLimitsOfSize.{k, max d k h} (ModuleCat.{w} A)]
    (F : Sheaf J (ModuleCat.{w} A)) :
    localFinite J A F ↔ localFinite K A ((e.sheafCongr J K (ModuleCat.{w} A)).functor.obj F) := by
  constructor
  · exact localFinite_precomp K J e.inverse A F
  · intro hF
    have hh := localFinite_precomp J K e.functor A
      ((e.sheafCongr J K (ModuleCat.{w} A)).functor.obj F) hF
    exact localFinite_iso J A ((e.sheafCongr J K (ModuleCat.{w} A)).unitIso.app F).symm hh

private def finiteModelSieve {C : Type c} [Category.{h} C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [HasSheafify J (ModuleCat.{w} A)]
    (F : Sheaf J (ModuleCat.{w} A)) (V : C) : Sieve V where
  arrows U _ := ∃ M : ModuleCat.{w} A, Module.Finite A M ∧
    Nonempty (F.over U ≅ ((constantSheaf J (ModuleCat.{w} A)).obj M).over U)
  downward_closed := by
    rintro U W f ⟨M, hM, ⟨e⟩⟩ g
    let G := (constantSheaf J (ModuleCat.{w} A)).obj M
    exact ⟨M, hM, ⟨(F.pushforwardOverMapIso g).symm ≪≫
      (J.overMapPullback (ModuleCat.{w} A) g).mapIso e ≪≫ G.pushforwardOverMapIso g⟩⟩

private theorem localFinite_iff_sieve
    {C : Type c} [Category.{h} C] [HasTerminal C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [HasSheafify J (ModuleCat.{w} A)]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    [∀ (U : C) (P : (Over U)ᵒᵖ ⥤ ModuleCat.{w} A),
      (Over.forget U).op.HasPointwiseRightKanExtension P]
    (F : Sheaf J (ModuleCat.{w} A)) :
    localFinite J A F ↔ finiteModelSieve J A F (⊤_ C) ∈ J (⊤_ C) := by
  constructor
  · intro hf
    obtain ⟨S, hS, hm⟩ := hf (⊤_ C)
    apply J.superset_covering _ hS
    intro U f hf
    obtain ⟨M, hM, ⟨e⟩⟩ := hm U f hf
    exact ⟨M, hM, ⟨e ≪≫ ((J.overPullbackConstantSheafIso (ModuleCat.{w} A) U).app M).symm⟩⟩
  · intro hf V
    refine ⟨(finiteModelSieve J A F (⊤_ C)).pullback (terminal.from V),
      J.pullback_stable _ hf, fun U f hf ↦ ?_⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := hf
    exact ⟨M, hM, ⟨e ≪≫ (J.overPullbackConstantSheafIso (ModuleCat.{w} A) U).app M⟩⟩

private theorem ordinary_presentation (R : Type w) [CommRing R] [IsNoetherianRing R]
    (P : ModuleCat.{w} R) [Module.Finite R P] :
    ∃ n m : ℕ, ∃ g : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R),
      Nonempty (P ≅ cokernel g) := by
  let := Module.finitePresentation_of_finite R P
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R P
  exact ⟨n, m, ModuleCat.ofHom g,
    ⟨(ModuleCat.isColimitCokernelCofork (ModuleCat.ofHom g) (ModuleCat.ofHom f)
      hgf hf).coconePointUniqueUpToIso (colimit.isColimit (parallelPair (ModuleCat.ofHom g) 0))⟩⟩

private theorem internal_constant_fp {C : Type c} [Category.{h} C]
    (J : GrothendieckTopology C) (R : Type (max c h)) [CommRing R] [IsNoetherianRing R]
    [HasSheafify J Ab.{max c h}] [(J.W (A := Ab.{max c h})).IsMonoidal]
    [HasLimitsOfSize.{h, c} (ModuleCat.{max c h} R)]
    [HasSheafify J (ModuleCat.{max c h} R)]
    (P : ModuleCat.{max c h} R) [Module.Finite R P] :
    ∃ M : Mod (Sheaf J Ab.{max c h}) (Sheaf.sheafifyRingPresheaf J
        ((Functor.const Cᵒᵖ).obj (RingCat.of R))),
      Mod.IsFinitelyPresented _ M ∧
        Nonempty ((ConstantInternalModuleSheafEncoding.sheafEncoding J R
          (internalToModule R) rfl).obj M ≅ (constantSheaf J (ModuleCat.{max c h} R)).obj P) := by
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J R (internalToModule R) rfl
  let S := constantSheaf J (ModuleCat.{max c h} R)
  let rr : (internalToModule R).obj (Mod.regular (AddCommGrpCat.of R)) ≅ ModuleCat.of R R :=
    ModuleCat.isoMk (Iso.refl _) (fun r ↦ by ext x; rfl)
  let e (n : ℕ) : H.obj (Mod.finiteFree _ n) ≅ S.obj (ModuleCat.of R (Fin n → R)) :=
    ConstantInternalModuleSheafEncoding.encFiniteFreeIso J R (internalToModule R) rfl n ≪≫
      S.mapIso (biproduct.mapIso (fun _ ↦ rr) ≪≫ ModuleCat.biproductIsoPi _)
  obtain ⟨n, m, g, ⟨eg⟩⟩ := ordinary_presentation R P
  let ff := Functor.FullyFaithful.ofFullyFaithful H
  let g' := ff.preimage ((e m).hom ≫ S.map g ≫ (e n).inv)
  let eH : H.obj (cokernel g') ≅ S.obj P :=
    PreservesCokernel.iso H g' ≪≫
      cokernel.mapIso _ _ (e m) (e n) (by simp [g', ff]) ≪≫
      (PreservesCokernel.iso S g).symm ≪≫ S.mapIso eg.symm
  let M := H.objPreimage (S.obj P)
  exact ⟨M, ⟨n, m, g', ⟨ff.preimageIso (H.objObjPreimageIso _ ≪≫ eH.symm)⟩⟩,
    ⟨H.objObjPreimageIso _⟩⟩

private def internalConstantPresheafFunctor
    {C : Type c} [Category.{h} C] (R : Type w) [CommRing R] :
    Mod Ab.{w} (AddCommGrpCat.of R) ⥤
      Mod (Cᵒᵖ ⥤ Ab.{w}) (ConstantInternalModuleSheafEncoding.A (C := Cᵒᵖ) R) where
  obj N :=
    { X := (Functor.const Cᵒᵖ).obj N.X
      mod := ModObj.mk' _
        { app := fun _ ↦ Mod.act (A := AddCommGrpCat.of R) N.X
          naturality := fun _ ↦ by simp }
        (by
          apply NatTrans.ext
          funext U
          exact ModObj.one_smul_self (AddCommGrpCat.of R) N.X)
        (by
          apply NatTrans.ext
          funext U
          exact ModObj.mul_smul_self (AddCommGrpCat.of R) N.X) }
  map f := Mod.homMk ((Functor.const Cᵒᵖ).map f.hom) (by
    apply NatTrans.ext
    funext U
    exact Mod.act_hom f)
  map_id N := by ext U; rfl
  map_comp f g := by ext U; rfl

private theorem internalConstantPresheaf_action
    {C : Type c} [Category.{h} C] (R : Type w) [CommRing R]
    (N : Mod Ab.{w} (AddCommGrpCat.of R)) :
    Functor.LaxMonoidal.μ (Functor.const Cᵒᵖ) (AddCommGrpCat.of R) N.X ≫
      (Functor.const Cᵒᵖ).map (Mod.act N.X) =
        Mod.act ((internalConstantPresheafFunctor (C := C) R).obj N).X := by
  ext U
  rfl

private def internalConstantFunctor
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
    (R : Type w) [CommRing R] :
    Mod Ab.{w} (AddCommGrpCat.of R) ⥤
      Mod (Sheaf J Ab.{w}) ((presheafToSheaf J Ab.{w}).obj
        (ConstantInternalModuleSheafEncoding.A (C := Cᵒᵖ) R)) :=
  internalConstantPresheafFunctor R ⋙
    (presheafToSheaf J Ab.{w}).mapMod (ConstantInternalModuleSheafEncoding.A (C := Cᵒᵖ) R)

@[irreducible] private def internalConstantEncoding
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
    (R : Type w) [CommRing R]
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [HasLimitsOfSize.{h, c} (ModuleCat.{w} R)]
    [PreservesLimitsOfSize.{h, c} (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [ReflectsLimitsOfSize.{h, c} (forget₂ (ModuleCat.{w} R) Ab.{w})]
    [HasSheafify J (ModuleCat.{w} R)] :
    internalConstantFunctor J R ⋙
      ConstantInternalModuleSheafEncoding.sheafEncoding J R (internalToModule R) rfl ≅
        internalToModule R ⋙ constantSheaf J (ModuleCat.{w} R) := by
  let P := ConstantInternalModuleSheafEncoding.modulePresheafEncoding (C := C) R
    (internalToModule R)
  let T := internalConstantPresheafFunctor (C := C) R
  let i : T ⋙ P ≅ internalToModule R ⋙ Functor.const Cᵒᵖ := by
    refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun U ↦ ?_) ?_) ?_
    · exact ModuleCat.isoMk (Iso.refl _) (fun r ↦ by ext m; rfl)
    · intro U V f
      ext m
      rfl
    · intro M N f
      ext U m
      rfl
  let S := (presheafToSheaf J Ab.{w}).mapMod
    (ConstantInternalModuleSheafEncoding.A (C := Cᵒᵖ) R)
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J R (internalToModule R) rfl
  change (T ⋙ S) ⋙ H ≅ _
  exact Functor.associator T S H ≪≫
    Functor.isoWhiskerLeft T
      (ConstantInternalModuleSheafEncoding.encSheafifyIso J R (internalToModule R) rfl) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight i _ ≪≫
    Functor.associator _ _ _

private theorem internalConstantAction
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
    (R : Type w) [CommRing R] (N : Mod Ab.{w} (AddCommGrpCat.of R)) :
    @Mod.act _ _ _ _ _ ((internalConstantFunctor J R).obj N).X
      ((internalConstantFunctor J R).obj N).mod =
      Functor.LaxMonoidal.μ (constantSheaf J Ab.{w}) (AddCommGrpCat.of R) N.X ≫
        (constantSheaf J Ab.{w}).map (Mod.act N.X) := by
  simp only [internalConstantFunctor, Functor.comp_obj, Functor.act_mapMod_obj]
  dsimp only [constantSheaf]
  erw [Functor.LaxMonoidal.comp_μ]
  rw [Category.assoc]
  dsimp only [Functor.comp_map]
  erw [← Functor.map_comp]
  exact congrArg (fun k ↦ Functor.LaxMonoidal.μ (presheafToSheaf J Ab.{w})
    (ConstantInternalModuleSheafEncoding.A (C := Cᵒᵖ) R)
    ((Functor.const Cᵒᵖ).obj N.X) ≫ (presheafToSheaf J Ab.{w}).map k)
      (internalConstantPresheaf_action (C := C) R N).symm

private theorem sectionScalarComposite_exists
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{max c h} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
    [HasSheafify J Ab.{max c h}] [J.WEqualsLocallyBijective Ab.{max c h}]
    [(J.W (A := Ab.{max c h})).IsMonoidal]
    (R : Type (max c h)) [CommRing R]
    (Λ : Sheaf J Ab.{max c h}) [MonObj Λ] [IsCommMonObj Λ]
    (f : realizationRing J R ⟶ InternalAbelianSheafModule.sectionRingSheaf J Λ)
    [IsIso f] :
    Nonempty ((InternalAbelianSheafModule.sectionModuleEquivalence J Λ).functor ⋙
      SheafOfModules.scalarRestriction f ⋙ ConstantScalarRestriction.restriction J R).Monoidal := by
  let := sectionMonoidal.{c, h, max c h} J Λ
  let : (SheafOfModules.scalarRestriction f).Monoidal :=
    ringScalarMonoidal.{c, h, max c h} (asIso f)
  let : (ConstantScalarRestriction.restriction J R).Monoidal :=
    constantScalarMonoidal.{c, h} J R
  exact ⟨inferInstance⟩


namespace AlgebraicGeometry.ProEtale

private def etaleSites (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) (ModuleCat.{u + 1} A) ≌
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)
  letI : (AsSmall.down : AsSmall.{u + 1} X.Etale ⥤ X.Etale).IsEquivalence :=
    e.isEquivalence_inverse
  letI : e.inverse.IsDenseSubsite
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) X.smallEtaleTopology :=
    inferInstanceAs ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
      X.Etale).IsDenseSubsite
        ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
          X.Etale).inducedTopology X.smallEtaleTopology) X.smallEtaleTopology)
  exact (e.sheafCongr X.smallEtaleTopology
    (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) (ModuleCat.{u + 1} A)).symm

private local instance etaleSites_monoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (etaleSites X A).functor.Monoidal := by
  let G : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤ X.Etale := AsSmall.down
  letI : G.IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)).isEquivalence_inverse
  let J := Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X
  let K := X.smallEtaleTopology
  let L := Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{u + 1} A) J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    (ModuleCat.{u + 1} A) J K
  letI : L.Monoidal :=
    Functor.sheafPullbackConstruction.sheafPullbackMonoidal G (ModuleCat.{u + 1} A) J K
  exact monoidalOfAdjointEquivalence (etaleSites X A) L adj

private theorem etaleSites_localFinite
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X)
      (ModuleCat.{u + 1} A)) :
    IsCoefficientModelLocallyConstantFinite _ A F ↔
      localFinite X.smallEtaleTopology A ((etaleSites X A).functor.obj F) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)
  let : (AsSmall.down : AsSmall.{u + 1} X.Etale ⥤ X.Etale).IsEquivalence :=
    e.isEquivalence_inverse
  let : e.inverse.IsDenseSubsite
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) X.smallEtaleTopology :=
    inferInstanceAs ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
      X.Etale).IsDenseSubsite
        ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
          X.Etale).inducedTopology X.smallEtaleTopology) X.smallEtaleTopology)
  let : e.functor.IsDenseSubsite X.smallEtaleTopology
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) := by
    infer_instance
  let : e.symm.inverse.IsDenseSubsite X.smallEtaleTopology
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) :=
    inferInstanceAs (e.functor.IsDenseSubsite _ _)
  let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} A) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  exact localFinite_site_equivalence _ _ e.symm A F

private def etaleSitePullbackSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    Scheme.coefficientEtaleFixedPullback.{u, u + 1} f A ⋙ (etaleSites X A).functor ≅
      (etaleSites Y A).functor ⋙ Etale.upperStar (ModuleCat.{u + 1} A) f := by
  let R := (Scheme.coefficientEtaleBaseChange.{u, u + 1} f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} A) (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} Y)
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X)
  let i : R ⋙ (etaleSites Y A).functor ≅
      (etaleSites X A).functor ⋙ Etale.lowerStar (ModuleCat.{u + 1} A) f :=
    NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U ↦ Iso.refl _)))
  exact leftSquareOfRight _ R
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _)
    _ _ (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (etaleSites Y A) (etaleSites X A) i

private def proSites (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (ModuleCat.{u + 1} A) ≌
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  letI : (AsSmall.down : AsSmall.{u + 1} X.ProEt ⥤ X.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  letI : e.inverse.IsDenseSubsite
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (Scheme.ProEt.topology X) :=
    inferInstanceAs ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤
      X.ProEt).IsDenseSubsite
        ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤
          X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X))
  exact (e.sheafCongr (Scheme.ProEt.topology X)
    (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (ModuleCat.{u + 1} A)).symm

private local instance proSites_monoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (proSites X A).functor.Monoidal := by
  let G : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤ X.ProEt := AsSmall.down
  letI : G.IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).isEquivalence_inverse
  let J := Scheme.coefficientProEtaleModelTopology.{u, u + 1} X
  let K := (Scheme.ProEt.topology X)
  let L := Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{u + 1} A) J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    (ModuleCat.{u + 1} A) J K
  letI : L.Monoidal :=
    Functor.sheafPullbackConstruction.sheafPullbackMonoidal G (ModuleCat.{u + 1} A) J K
  exact monoidalOfAdjointEquivalence (proSites X A) L adj

private theorem proSites_localFinite
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X)
      (ModuleCat.{u + 1} A)) :
    IsCoefficientModelLocallyConstantFinite _ A F ↔
      localFinite (Scheme.ProEt.topology X) A ((proSites X A).functor.obj F) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  let : (AsSmall.down : AsSmall.{u + 1} X.ProEt ⥤ X.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  let : e.inverse.IsDenseSubsite
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (Scheme.ProEt.topology X) :=
    inferInstanceAs ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤
      X.ProEt).IsDenseSubsite
        ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤
          X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X))
  let : e.functor.IsDenseSubsite (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) := by
    infer_instance
  let : e.symm.inverse.IsDenseSubsite (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) :=
    inferInstanceAs (e.functor.IsDenseSubsite _ _)
  let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} A) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  exact localFinite_site_equivalence _ _ e.symm A F

private def proSitePullbackSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    Scheme.coefficientProEtaleFixedModulePullback.{u, u + 1} f A ⋙ (proSites X A).functor ≅
      (proSites Y A).functor ⋙ ProEtale.upperStar (ModuleCat.{u + 1} A) f := by
  let R := (Scheme.coefficientProEtaleModelBaseChange.{u, u + 1} f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} A) (Scheme.coefficientProEtaleModelTopology.{u, u + 1} Y)
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X)
  let i : R ⋙ (proSites Y A).functor ≅
      (proSites X A).functor ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} A) f :=
    NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U ↦ Iso.refl _)))
  exact leftSquareOfRight _ R
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _)
    _ _ (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (proSites Y A) (proSites X A) i

private theorem etale_localFinite_iff
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    localFinite X.smallEtaleTopology A F ↔
      ∃ d : Scheme.LocallyConstantDatum F, ∀ i : d.cover.I₀,
        ∃ M : ModuleCat.{u + 1} A, Finite M ∧
          Nonempty (F.over (d.cover.etalePrecoverageToEtale i) ≅
            (constantSheaf (X.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
              (ModuleCat.{u + 1} A)).obj M) := by
  classical
  rw [localFinite_iff_sieve X.smallEtaleTopology A F]
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let S := finiteModelSieve X.smallEtaleTopology A F T
  have hmem : finiteModelSieve X.smallEtaleTopology A F (⊤_ X.Etale) ∈
      X.smallEtaleTopology (⊤_ X.Etale) ↔ S ∈ X.smallEtaleTopology T := by
    let e := (Scheme.Etale.isTerminalMkId X).uniqueUpToIso terminalIsTerminal
    change _ ↔ (finiteModelSieve X.smallEtaleTopology A F (⊤_ X.Etale)).pullback
      e.hom ∈ X.smallEtaleTopology T
    exact GrothendieckTopology.pullback_mem_iff_of_isIso.symm
  rw [hmem]
  constructor
  · intro hS
    have hx := (Scheme.mem_smallEtaleTopology_iff S).mp hS
    choose V g hg hx using hx
    have hc : ∀ x : X, ∃ i y, (V i).hom y = x := by
      intro x
      obtain ⟨y, hy⟩ := hx x
      refine ⟨x, y, ?_⟩
      have hw : (g x).left = (V x).hom :=
        (Category.comp_id _).symm.trans (MorphismProperty.Over.w (g x))
      change (g x).left y = x at hy
      exact (congrArg (fun f : (V x).left ⟶ X ↦ f y) hw.symm).trans hy
    let C : Scheme.Cover.{u} Scheme.etalePrecoverage X :=
      Scheme.Cover.mkOfCovers X (fun x ↦ (V x).left) (fun x ↦ (V x).hom) hc
    have hm (i : C.I₀) : ∃ M : ModuleCat.{u + 1} A, Finite M ∧
        Nonempty (F.over (C.etalePrecoverageToEtale i) ≅
          (constantSheaf (X.smallEtaleTopology.over (C.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj M) := by
      obtain ⟨M, hM, ⟨e⟩⟩ := hg i
      have he := e ≪≫ (X.smallEtaleTopology.overPullbackConstantSheafIso
        (ModuleCat.{u + 1} A) (V i)).app M
      exact ⟨M, (Module.finite_iff_finite (R := A)).mp hM, ⟨he⟩⟩
    refine ⟨⟨C, fun i ↦ ?_⟩, hm⟩
    obtain ⟨M, _, ⟨e⟩⟩ := hm i
    exact Sheaf.isConstant_of_iso _ e
  · rintro ⟨d, hd⟩
    let V := d.cover.etalePrecoverageToEtale
    let t (i : d.cover.I₀) : V i ⟶ T := MorphismProperty.Over.homMk (d.cover.f i)
    have hcover : Sieve.ofArrows V t ∈ X.smallEtaleTopology T := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff t).mpr
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨i, y, hy⟩ := d.cover.exists_eq x
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨y, hy⟩⟩
    apply X.smallEtaleTopology.superset_covering _ hcover
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro U f ⟨i⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := hd i
    let := hM
    exact ⟨M, Module.Finite.of_finite, ⟨e ≪≫
      ((X.smallEtaleTopology.overPullbackConstantSheafIso (ModuleCat.{u + 1} A) (V i)).app M).symm⟩⟩

open Scheme in
private theorem pro_localFinite_iff
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    localFinite (Scheme.ProEt.topology X) A F ↔ IsFiniteLocallyConstant A F := by
  rw [localFinite_iff_sieve]
  let e : ProEt.mk (𝟙 X) ≅ ⊤_ X.ProEt :=
    (ProEt.isTerminalMkId X).uniqueUpToIso terminalIsTerminal
  have hmem : finiteModelSieve (ProEt.topology X) A F (⊤_ X.ProEt) ∈
      ProEt.topology X (⊤_ X.ProEt) ↔
        finiteModelSieve (ProEt.topology X) A F (ProEt.mk (𝟙 X)) ∈
          ProEt.topology X (ProEt.mk (𝟙 X)) := by
    change _ ↔ (finiteModelSieve (ProEt.topology X) A F (⊤_ X.ProEt)).pullback e.hom ∈ _
    exact GrothendieckTopology.pullback_mem_iff_of_isIso.symm
  rw [hmem]
  constructor
  · intro h
    obtain ⟨P, hP, hPS⟩ := ProEt.mem_topology_iff.mp h
    obtain ⟨I, U, f, rfl⟩ := P.exists_eq_ofArrows
    have hcov : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
        proetalePrecoverage X := by
      rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
      change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
        proetalePrecoverage X at hP
      have hw (i : I) : (f i).left = (U i).hom := by
        have hw := MorphismProperty.Over.w (f i)
        change (f i).left ≫ 𝟙 X = (U i).hom at hw
        exact (Category.comp_id _).symm.trans hw
      simpa only [hw] using hP
    refine ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom, hcov, fun i ↦ ?_⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := hPS _ _ ⟨i⟩
    let D := ModuleCat.{u + 1} A
    have : (ProEt.sliceEquiv X (U i)).inverse.IsDenseSubsite
        (ProEt.topology (U i).left) ((ProEt.topology X).over (U i)) :=
      ProEt.sliceDense X (U i)
    let E := (ProEt.sliceEquiv X (U i)).sheafCongr
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left) D
    let r : E.functor.obj (F.over (U i)) ≅
        (localizationRestriction D (U i).hom (U i).prop).obj F :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    let c := ((ProEt.sliceEquiv X (U i)).constantSheafSheafCongrIso
      ((ProEt.topology X).over (U i)) (ProEt.topology (U i).left)
      D (Over.mkIdTerminal (X := U i))).app M
    exact ⟨M, (Module.finite_iff_finite (R := A)).mp hM,
      ⟨(upperStarIsoLocalizationRestriction D (U i).hom (U i).prop).app F ≪≫
        r.symm ≪≫ E.functor.mapIso (e ≪≫
          ((ProEt.topology X).overPullbackConstantSheafIso D (U i)).app M) ≪≫ c⟩⟩
  · intro h
    obtain ⟨I, U, f, hf, he⟩ := finiteModels_over A F h
    apply (ProEt.topology X).superset_covering
      ((Sieve.generate_le_iff _ _).mpr ?_) (Precoverage.generate_mem_toGrothendieck hf)
    rintro V g ⟨i⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := he i
    exact ⟨M, (Module.finite_iff_finite (R := A)).mpr hM, ⟨e ≪≫
      (((ProEt.topology X).overPullbackConstantSheafIso
        (ModuleCat.{u + 1} A) (U i)).app M).symm⟩⟩

private theorem pro_localFinite_small_cover
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    localFinite (Scheme.ProEt.topology X) A F ↔
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
        ∃ M : ModuleCat.{u + 1} A, Finite M ∧
          Nonempty ((upperStar (ModuleCat.{u + 1} A) (C.f i)).obj F ≅
            (constantSheaf (Scheme.ProEt.topology (C.X i)) (ModuleCat.{u + 1} A)).obj M) := by
  rw [pro_localFinite_iff]
  constructor
  · rintro ⟨I, U, f, hf, hm⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage X :=
      ⟨⟨I, U, f⟩, hf⟩
    let : Precoverage.Small.{u} Scheme.proetalePrecoverage := by
      change Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale)
      infer_instance
    exact ⟨C.restrictIndexOfSmall.{u}, fun i ↦ hm _⟩
  · rintro ⟨C, hm⟩
    refine ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down, ?_,
      fun i ↦ hm i.down⟩
    convert C.mem₀ using 1
    funext U f
    apply propext
    constructor
    · rintro ⟨i⟩
      exact ⟨i.down⟩
    · rintro ⟨i⟩
      exact ⟨ULift.up i⟩

private theorem coefficient_etale_global
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :
    Scheme.IsCoefficientConstructibleEtaleModule.{u, u + 1} X A F ↔
      ∃ S : Scheme.Stratification X, ∀ i,
        IsCoefficientModelLocallyConstantFinite
          (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} (S.domain i)) A
          ((Scheme.coefficientEtaleFixedPullback.{u, u + 1} (S.immersion i) A).obj
            ((coefficientModelFixedScalars _ A).obj F)) := by
  let P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop := fun {Y} f ↦
    IsCoefficientModelLocallyConstantFinite
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} Y) A
      ((Scheme.coefficientEtaleFixedPullback.{u, u + 1} f A).obj
        ((coefficientModelFixedScalars _ A).obj F))
  have h := Scheme.affine_local_stratification_iff X P
    (fun f g h ↦ Scheme.etaleFinite_comp f g A _ h)
  constructor
  · intro hF
    obtain ⟨S, _, hS⟩ := h.mp (fun U hU ↦ by
      obtain ⟨S, hc, hS⟩ := hF U hU
      exact ⟨Scheme.constructibleStratification S hc, hc, hS⟩)
    exact ⟨S, hS⟩
  · rintro ⟨S, hS⟩ U hU
    obtain ⟨T, hc, hT⟩ := h.mpr ⟨S, S.isConstructible_stratum, hS⟩ U hU
    exact ⟨Scheme.finiteStratification T, hc, hT⟩

private theorem coefficient_etale_constructible
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :
    Scheme.IsCoefficientConstructibleEtaleModule.{u, u + 1} X A F ↔
      Scheme.IsConstructibleEtaleModuleSheaf
        ((finiteComparisonEtaleModelRealization X A).obj F) := by
  rw [coefficient_etale_global]
  change (∃ S : Scheme.Stratification X, _) ↔ ∃ S : Scheme.Stratification X, _
  apply exists_congr
  intro S
  apply forall_congr'
  intro i
  rw [etaleSites_localFinite]
  let e := (etaleSitePullbackSquare (S.immersion i) A).app
    ((coefficientModelFixedScalars _ A).obj F)
  exact (show localFinite _ A _ ↔ localFinite _ A _ from
    ⟨localFinite_iso _ A e, localFinite_iso _ A e.symm⟩).trans
      (etale_localFinite_iff _ A _)

private theorem etale_constructible_iso
    {X : Scheme.{u}} {A : Type (u + 1)} [CommRing A] [Finite A]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (e : F ≅ G)
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    Scheme.IsConstructibleEtaleModuleSheaf G := by
  have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mpr
    (Scheme.IsConstructibleSheaf.of_iso e)

private theorem coefficient_etale_bounded
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (K : ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :
    Scheme.IsCoefficientBoundedConstructibleEtale.{u, u + 1} X A K ↔
      Etale.DerivedCategory.isBoundedConstructible A X
        ((finiteComparisonEtaleModelRealization X A).mapDerivedCategory.obj K) := by
  let E := finiteComparisonEtaleModelRealization X A
  unfold Scheme.IsCoefficientBoundedConstructibleEtale
    Etale.DerivedCategory.isBoundedConstructible
  apply and_congr _ (bounded_cohomology_transport E K)
  apply forall_congr'
  intro q
  let e := (E.mapDerivedCategoryHomologyFunctorIso q).app K
  exact (coefficient_etale_constructible X A _).trans
    ⟨etale_constructible_iso e, etale_constructible_iso e.symm⟩

private local instance etale_bounded_iso
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A] :
    (Etale.DerivedCategory.isBoundedConstructible A X).IsClosedUnderIsomorphisms where
  of_iso e h := by
    refine ⟨fun q ↦ etale_constructible_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e) (h.1 q), ?_⟩
    obtain ⟨a, b, hab, hz⟩ := h.2
    exact ⟨a, b, hab, fun q hq ↦ (hz q hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso e).symm⟩

private theorem coefficient_pro_global
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :
    Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, u + 1} X A F ↔
      ∃ S : Scheme.Stratification X, ∀ i,
        IsCoefficientModelLocallyConstantFinite
          (Scheme.coefficientProEtaleModelTopology.{u, u + 1} (S.domain i)) A
          ((Scheme.coefficientProEtaleFixedModulePullback.{u, u + 1}
            (S.immersion i) A).obj ((coefficientModelFixedScalars _ A).obj F)) := by
  let P : ∀ {Y : Scheme.{u}}, (Y ⟶ X) → Prop := fun {Y} f ↦
    IsCoefficientModelLocallyConstantFinite
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} Y) A
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, u + 1} f A).obj
        ((coefficientModelFixedScalars _ A).obj F))
  have h := Scheme.affine_local_stratification_iff X P
    (fun f g h ↦ Scheme.proFinite_comp f g A _ h)
  have h' : (∀ U : X.Opens, AlgebraicGeometry.IsAffineOpen U →
      ∃ S : Scheme.Stratification U.toScheme,
        (∀ i, Topology.IsConstructible (S.stratum i)) ∧
        ∀ i, P (S.immersion i ≫ U.ι)) ↔
      ∃ S : Scheme.Stratification X, ∀ i, P (S.immersion i) := by
    exact h.trans ⟨fun ⟨S, _, hS⟩ ↦ ⟨S, hS⟩,
      fun ⟨S, hS⟩ ↦ ⟨S, S.isConstructible_stratum, hS⟩⟩
  simpa only [Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf,
    Scheme.finiteLocalModels_iff_presentation, P] using h'

private local instance etaleRealization_monoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (finiteComparisonEtaleModelRealization X A).Monoidal :=
  inferInstanceAs (coefficientModelFixedScalars _ A ⋙ (etaleSites X A).functor).Monoidal

private local instance proRealization_monoidal (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (finiteComparisonProEtaleModelRealization X A).Monoidal :=
  inferInstanceAs (coefficientModelFixedScalars _ A ⋙ (proSites X A).functor).Monoidal

private theorem coefficient_etale_finiteTor
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (K : ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :
    (∃ a b : ℤ, HasCoefficientModelTorAmplitude _ K a b) ↔
      _root_.DerivedCategory.finiteTorAmplitude _
        ((finiteComparisonEtaleModelRealization X A).mapDerivedCategory.obj K) := by
  rw [coefficient_finite_native]
  let E := finiteComparisonEtaleModelRealization X A
  let := E.preservesFlat_of_isEquivalence
  apply exists_congr
  intro a
  apply exists_congr
  intro b
  exact (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff E a b K).symm

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]


omit [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B] [Finite B] in
private theorem fixedModuleLimits :
    HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
  ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}

attribute [local instance] fixedModuleLimits

private theorem modelStratifiedConstructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsFiniteConstantStratified Λ X M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  let α := condensedPullbackHom Λ (S.immersion a)
  apply localFinitePresentation_of_comap (inv α)
  have h := HasFiniteConstantLocalModel.isLocallyFinitelyPresented Λ _ (hS a)
  have e := (Mod.extendScalarsIsoComapInv α).app
    (((upperStar Ab.{u + 1} (S.immersion a)).mapMod (condensedRingObj Λ X)).obj M)
  exact localFinitePresentation_of_iso e h

private theorem modelOfIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ X N) :
    HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (C.f i)).mapIso e ≪≫ eP⟩⟩

section InternalRealization

variable (X : Scheme.{u})
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
    ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
      Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

private def realizedSectionRing := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
  (Scheme.ProEt.topology X) (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)

private def realizedSectionUnit :
    (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} B)) ⟶
      (realizedSectionRing B X).obj := by
  let J := Scheme.ProEt.topology X
  let R := ULift.{u + 1} B
  let P := (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of R)
  let mP := (Functor.const X.ProEtᵒᵖ).monObjObj (AddCommGrpCat.of R)
  let mQ := Sheaf.monObj_presheafToSheaf_obj J
    (((Functor.const X.ProEtᵒᵖ).obj (RingCat.of R)) ⋙ forget₂ RingCat Ab)
  have hm : (presheafToSheaf J Ab.{u + 1}).monObjObj P = mQ := by
    exact congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _
      (presheafToSheaf J Ab.{u + 1}) _ _ m) (constantRingMonObj (C := X.ProEtᵒᵖ) R)
  let f := (finiteDiscreteSchemeRingIso B X eR).hom
  have hf := IsMonHom.of_eq f hm.symm rfl (hf := (inferInstance : IsMonHom f))
  have hu := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
  have hmap := FiniteDiscreteOrdinary.monHomMapExplicit (sheafToPresheaf J Ab.{u + 1})
    ((presheafToSheaf J Ab.{u + 1}).monObjObj P) _ f hf
  let φ := toSheafify J P ≫ f.hom
  letI : @IsMonHom _ _ _ _ _ mP
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)) φ :=
    FiniteDiscreteOrdinary.monHomCompExplicit mP _ _ _ _ hu hmap
  exact FiniteDiscreteOrdinary.constantSectionRingMapAux J R
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) φ

private def realizedSectionMap :
    realizationRing (Scheme.ProEt.topology X) (ULift.{u + 1} B) ⟶ realizedSectionRing B X :=
  ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv _
    (realizedSectionRing B X)).symm (realizedSectionUnit B X eR)

omit [DiscreteTopology B] [Finite B] in
private theorem realizedSectionMap_unit (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} B) :
    (realizedSectionMap B X eR).hom.app U
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} B)))).app U a) =
      (finiteDiscreteSchemeRingIso B X eR).hom.hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))).app U a) := by
  exact ConcreteCategory.congr_hom (congr_app
    (((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).homEquiv _
      (realizedSectionRing B X)).apply_symm_apply (realizedSectionUnit B X eR)) U) a

private local instance realizedSectionMap_isIso : IsIso (realizedSectionMap B X eR) := by
  let J := Scheme.ProEt.topology X
  let R := ULift.{u + 1} B
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} Ab.{u + 1}
  let F := sheafCompose J V
  have : J.PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification J V
  let e := (constantCommuteCompose J V).app (CommRingCat.of R)
  let g := F.map (realizedSectionMap B X eR)
  have hg : e.inv ≫ g = (finiteDiscreteSchemeRingIso B X eR).hom := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X).property
    have he : toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (V.obj (CommRingCat.of R))) ≫
        e.inv.hom = Functor.whiskerRight
          (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of R))) V := by
      change _ ≫ (sheafifyMap J (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of R) V).inv ≫
        (sheafifyComposeIso J V _).hom) = _
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
        sheafComposeIso_hom_fac]
      ext U a
      rfl
    change _ ≫ (e.inv.hom ≫ g.hom) = _
    rw [← Category.assoc, he]
    ext U a
    exact realizedSectionMap_unit B X eR U a
  have : IsIso (e.inv ≫ g) := hg.symm ▸ inferInstance
  have : IsIso g := by
    have hh : g = e.hom ≫ (e.inv ≫ g) := by simp
    rw [hh]
    infer_instance
  exact isIso_of_reflects_iso (realizedSectionMap B X eR) F

@[irreducible] private def pointConstantComparison
    (N : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B))) :
    ((upperStarFromPoint X).mapMod (Profinite.continuousMapRingObj.{u} B)).obj
      ((Mod.comap eR.inv).obj
        ((internalConstantFunctor (coherentTopology Profinite.{u})
          (ULift.{u + 1} B)).obj N)) ≅
      (Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv).obj
        ((internalConstantFunctor (Scheme.ProEt.topology X) (ULift.{u + 1} B)).obj N) := by
  let F := upperStarFromPoint X
  let R := AddCommGrpCat.of (ULift.{u + 1} B)
  let P := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let S := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let τ := constantSchemeIso X
  let mP := Sheaf.monObj_presheafToSheaf_obj (coherentTopology Profinite.{u})
    (((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ⋙
      forget₂ RingCat Ab)
  let mS := Sheaf.monObj_presheafToSheaf_obj (Scheme.ProEt.topology X)
    (((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ⋙
      forget₂ RingCat Ab)
  let transfer (m : MonObj (P.obj R)) : MonObj (F.obj (P.obj R)) :=
    @Functor.monObjObj _ _ _ _ _ _ F _ _ m
  letI : MonObj (P.obj R) := mP
  letI : MonObj (S.obj R) := mS
  letI : MonObj (F.obj (P.obj R)) := transfer mP
  let θ := τ.inv.app R
  let hθ : @IsMonHom _ _ _ _ _ (transfer mP) mS θ :=
    IsMonHom.of_eq θ
      (congrArg transfer (constantSheafRingMonObj (coherentTopology Profinite.{u})
        (ULift.{u + 1} B)))
      (constantSheafRingMonObj (Scheme.ProEt.topology X) (ULift.{u + 1} B))
      (hf := Functor.isMonHom_compAlgHom P F τ.inv R)
  let T := @Mod.comap _ _ _ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _
    (F.obj (P.obj R)) (S.obj R) (transfer mP) mS θ hθ
  let j : (F.mapMod (P.obj R)).obj
      ((internalConstantFunctor (coherentTopology Profinite.{u})
        (ULift.{u + 1} B)).obj N) ≅
      T.obj
        ((internalConstantFunctor (Scheme.ProEt.topology X)
          (ULift.{u + 1} B)).obj N) := by
    refine Mod.isoMk (τ.symm.app N.X) ?_
    simp only [Functor.act_mapMod_obj, Mod.act_comap_obj, internalConstantAction]
    change (Functor.LaxMonoidal.μ F (P.obj R) (P.obj N.X) ≫
        F.map (Functor.LaxMonoidal.μ P R N.X ≫ P.map (Mod.act N.X))) ≫ τ.inv.app N.X =
      F.obj (P.obj R) ◁ τ.inv.app N.X ≫ τ.inv.app R ▷ S.obj N.X ≫
        Functor.LaxMonoidal.μ S R N.X ≫ S.map (Mod.act N.X)
    exact monoidal_action_comparison P F S τ R N.X (Mod.act N.X)
  refine (Functor.mapModComapIso F eR.inv).app _ ≪≫
    (Mod.comap (F.map eR.inv)).mapIso j ≪≫
    ((Mod.comapComp (F.map eR.inv) θ).symm.app _) ≪≫ ?_
  apply (Mod.comapCongr _).app
  simp only [θ, τ, finiteDiscreteSchemeRingIso_eq,
    Iso.trans_inv, Functor.mapIso_inv]
  rfl


omit [DiscreteTopology B] in
private theorem pointFiniteModel
    (P : ModuleCat.{u + 1} (ULift.{u + 1} B)) [Module.Finite (ULift.{u + 1} B) P] :
    ∃ Q : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousMapRingObj.{u} B),
      Mod.IsFinitelyPresented _ Q ∧
        Nonempty (((upperStarFromPoint X).mapMod
          (Profinite.continuousMapRingObj.{u} B)).obj Q ≅
            (CondensedRing.finiteDiscreteCoefficientEquivalence B eR
              (internalToModule (ULift.{u + 1} B)) rfl X).functor.obj
                ((constantSheaf (Scheme.ProEt.topology X)
                  (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj P)) := by
  let R := ULift.{u + 1} B
  let J := coherentTopology Profinite.{u}
  let N := moduleToInternalObj R P
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J R (internalToModule R) rfl
  let C := (internalConstantFunctor J R).obj N
  let e : H.obj C ≅ (constantSheaf J (ModuleCat.{u + 1} R)).obj P :=
    (internalConstantEncoding J R).app N ≪≫
      (constantSheaf J (ModuleCat.{u + 1} R)).mapIso (CategoryTheory.realizationIso R P)
  obtain ⟨M, ⟨n, m, g, ⟨eg⟩⟩, ⟨eM⟩⟩ := internal_constant_fp J R P
  let c : C ≅ cokernel g :=
    (Functor.FullyFaithful.ofFullyFaithful H).preimageIso (e ≪≫ eM.symm) ≪≫ eg
  let F := Mod.comap (D := Sheaf J Ab.{u + 1}) eR.inv
  let : F.IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso eR.inv).isEquivalence_functor
  let : F.Additive := Functor.additive_of_preserves_binary_products _
  let free (k : ℕ) : F.obj (Mod.finiteFree _ k) ≅ Mod.finiteFree _ k :=
    F.mapBiproduct (fun _ : Fin k ↦ Mod.regular _) ≪≫
      biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv eR.inv))
  refine ⟨F.obj C, finitePresentation_map_of_presentation F free g c, ⟨?_⟩⟩
  let HX := ConstantInternalModuleSheafEncoding.sheafEncoding (Scheme.ProEt.topology X) R
    (internalToModule R) rfl
  let CX := (internalConstantFunctor (Scheme.ProEt.topology X) R).obj N
  let eX : HX.obj CX ≅ (constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} R)).obj P :=
    (internalConstantEncoding (Scheme.ProEt.topology X) R).app N ≪≫
      (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)).mapIso
        (CategoryTheory.realizationIso R P)
  let j : CX ≅ HX.inv.obj ((constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} R)).obj P) :=
    HX.asEquivalence.unitIso.app CX ≪≫ HX.inv.mapIso eX
  unfold CondensedRing.finiteDiscreteCoefficientEquivalence
  change _ ≅ (Mod.comap (asIso (finiteDiscreteSchemeRingIso B X eR).hom).inv).obj _
  exact pointConstantComparison B X eR N ≪≫
    (Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv).mapIso j ≪≫
    (Mod.comapCongr (by
      apply (cancel_mono (finiteDiscreteSchemeRingIso B X eR).hom).mp
      simp)).app _

@[irreducible] private def realizedConstantCounit (X : Scheme.{u}) :
    finiteComparisonConstantRealization X B ⋙
      ConstantInternalModuleSheafEncoding.sheafEncoding (Scheme.ProEt.topology X)
        (ULift.{u + 1} B) (internalToModule (ULift.{u + 1} B)) rfl ≅ 𝟭 _ := by
  let J := Scheme.ProEt.topology X
  let R := ULift.{u + 1} B
  let A := ConstantInternalModuleSheafEncoding.A (C := X.ProEtᵒᵖ) R
  let G := internalToModule R
  let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding J R G rfl
  let L := finiteComparisonConstantRealization X B
  let E := sheafToPresheaf J (ModuleCat.{u + 1} R) ⋙ finiteComparisonPresheaf X B
  let P := ConstantInternalModuleSheafEncoding.modulePresheafEncoding (C := X.ProEt) R G
  let adj := (sheafificationAdjunction J Ab.{u + 1}).mapModAdjunction A
  have hu (M : Sheaf J (ModuleCat.{u + 1} R)) : IsIso (adj.unit.app (E.obj M)) := by
    rw [← isIso_iff_of_reflects_iso _ (Mod.forget A)]
    change IsIso ((adj.unit.app (E.obj M)).hom)
    rw [Adjunction.mapModAdjunction_unit_app_hom]
    exact isIso_toSheafify J
      ((sheafCompose J (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})).obj M).property
  let η := Functor.whiskerRight (Functor.whiskerLeft E adj.unit) P
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact Functor.map_isIso P (adj.unit.app (E.obj M))
  let e0 : E ⋙ P ≅ sheafToPresheaf J (ModuleCat.{u + 1} R) :=
    Functor.isoWhiskerLeft _ (finiteComparisonPresheafEncodingIso X B)
  let e : (L ⋙ H) ⋙ sheafToPresheaf J (ModuleCat.{u + 1} R) ≅
      (𝟭 _) ⋙ sheafToPresheaf J (ModuleCat.{u + 1} R) :=
    (asIso η).symm ≪≫ e0
  exact ((fullyFaithfulSheafToPresheaf J (ModuleCat.{u + 1} R)).whiskeringRight _)
    |>.preimageIso e

@[irreducible] private def realizedEncodingIso :
    finiteComparisonRealization B X eR ≅
      (CondensedRing.finiteDiscreteCoefficientEquivalence B eR
        (internalToModule (ULift.{u + 1} B)) rfl X).functor := by
  let H := ConstantInternalModuleSheafEncoding.sheafEncoding (Scheme.ProEt.topology X)
    (ULift.{u + 1} B) (internalToModule (ULift.{u + 1} B)) rfl
  let i : finiteComparisonConstantRealization X B ≅ H.inv :=
    Iso.isoCompInverse (H := H.asEquivalence) (realizedConstantCounit B X) ≪≫
      Functor.leftUnitor H.inv
  unfold finiteComparisonRealization CondensedRing.finiteDiscreteCoefficientEquivalence
  exact Functor.isoWhiskerRight i
      (Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv) ≪≫
    Functor.isoWhiskerLeft H.inv (Mod.comapCongr (by
      apply (cancel_mono (finiteDiscreteSchemeRingIso B X eR).hom).mp
      simp))

private def realizedInverse :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) ⥤
        Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)).functor ⋙
    SheafOfModules.scalarRestriction.{u + 1, u, u + 1} (realizedSectionMap B X eR) ⋙
    ConstantScalarRestriction.restriction (Scheme.ProEt.topology X) (ULift.{u + 1} B)

omit [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B] [Finite B] in
private theorem realizedFixedUnit (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} B) :
    (((constantCommuteCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of (ULift.{u + 1} B))).hom.app U)
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B)))).app U a) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} B)))).app U a := by
  let J := Scheme.ProEt.topology X
  let R := ULift.{u + 1} B
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let e := (constantCommuteCompose J V).app (CommRingCat.of R)
  have he : toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (V.obj (CommRingCat.of R))) ≫
      e.inv.hom = Functor.whiskerRight
        (toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of R))) V := by
    change _ ≫ (sheafifyMap J (Functor.constComp X.ProEtᵒᵖ (CommRingCat.of R) V).inv ≫
      (sheafifyComposeIso J V _).hom) = _
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
      sheafComposeIso_hom_fac]
    ext U a
    rfl
  exact ConcreteCategory.congr_hom (congr_app he U) a

@[irreducible] private def realizedInverseIso :
    realizedInverse B X eR ≅
      (CondensedRing.finiteDiscreteCoefficientEquivalence B eR
        (internalToModule (ULift.{u + 1} B)) rfl X).inverse := by
  unfold CondensedRing.finiteDiscreteCoefficientEquivalence
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · refine ModuleCat.isoMk (Iso.refl _) (fun a ↦ ?_)
    ext m
    symm
    change (Mod.act (A := condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)
      M.X).hom.app U
        (((Functor.LaxMonoidal.μ
          (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) M.X).app U)
          (_ ⊗ₜ[ℤ] m)) = _
    erw [realizedFixedUnit B X, realizedSectionMap_unit B X eR]
    change _ = (Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} B))
      (((ConstantInternalModuleSheafEncoding.presheafToFunctor
        (C := X.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
          ((ConstantInternalModuleSheafEncoding.moduleLocalizationRight
            (Scheme.ProEt.topology X)
            (ConstantInternalModuleSheafEncoding.A (C := X.ProEtᵒᵖ)
              (ULift.{u + 1} B))).obj
                ((Mod.comap (finiteDiscreteSchemeRingIso B X eR).hom).obj M))).obj U).X).hom
                  (a ⊗ₜ[ℤ] m)
    rw [CondensedRing.encoding_action B eR X M U]
    simp only [AddCommGrpCat.comp_apply]
    rfl
  · intro U V f
    ext m
    rfl
  · intro M N f
    ext U m
    rfl

-- The auxiliary coefficient instances have an undetermined max universe here.
-- Use the same constructions at the fixed coefficient universe in this helper.
attribute [-instance]
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
omit [DiscreteTopology B] [Finite B] in
private theorem realizedInverseMonoidal_exists :
    Nonempty (realizedInverse B X eR).Monoidal := by
  let J := Scheme.ProEt.topology X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify J Ab.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  let : J.WEqualsLocallyBijective Ab.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  exact sectionScalarComposite_exists.{u + 1, u} J (ULift.{u + 1} B)
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)
    (realizedSectionMap B X eR)

omit [DiscreteTopology B] [Finite B] in
private theorem finiteRealizationMonoidal_exists :
    Nonempty (finiteComparisonRealization B X eR).Monoidal := by
  let E := CondensedRing.finiteDiscreteCoefficientEquivalence B eR
    (internalToModule (ULift.{u + 1} B)) rfl X
  exact monoidalOfInverse_exists E (finiteComparisonRealization B X eR)
    (realizedInverse B X eR) (realizedInverseMonoidal_exists B X eR)
    (realizedEncodingIso B X eR) (realizedInverseIso B X eR)

private local instance finiteRealizationMonoidal :
    (finiteComparisonRealization B X eR).Monoidal :=
  Classical.choice (finiteRealizationMonoidal_exists B X eR)

@[irreducible] private def encodingForwardPullback {Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))) :
    (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} B) f).obj
      ((CondensedRing.finiteDiscreteCoefficientEquivalence B eR
        (internalToModule (ULift.{u + 1} B)) rfl X).functor.obj F) ≅
    (CondensedRing.finiteDiscreteCoefficientEquivalence B eR
      (internalToModule (ULift.{u + 1} B)) rfl Y).functor.obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj F) := by
  let EX := CondensedRing.finiteDiscreteCoefficientEquivalence B eR
    (internalToModule (ULift.{u + 1} B)) rfl X
  let EY := CondensedRing.finiteDiscreteCoefficientEquivalence B eR
    (internalToModule (ULift.{u + 1} B)) rfl Y
  let G := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f
  let L := CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} B) f
  let i := CondensedRing.encodingPullbackNatIso B eR
    (internalToModule (ULift.{u + 1} B)) rfl X Y f
  exact (EY.counitIso.app (L.obj (EX.functor.obj F))).symm ≪≫
    EY.functor.mapIso ((i.app (EX.functor.obj F)).symm) ≪≫
    EY.functor.mapIso (G.mapIso (EX.unitIso.app F).symm)

omit [DiscreteTopology B] in
private theorem finiteLocalModel_of_ordinary
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)))
    (hF : IsFiniteLocallyConstant (ULift.{u + 1} B) F) :
    HasFiniteConstantLocalModel (Profinite.continuousMapRingObj.{u} B) X
      ((CondensedRing.finiteDiscreteCoefficientEquivalence B eR
        (internalToModule (ULift.{u + 1} B)) rfl X).functor.obj F) := by
  obtain ⟨C, hC⟩ := (pro_localFinite_small_cover X (ULift.{u + 1} B) F).mp
    ((pro_localFinite_iff X (ULift.{u + 1} B) F).mpr hF)
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
  let : Finite P := hP
  let : Module.Finite (ULift.{u + 1} B) P :=
    (Module.finite_iff_finite (R := ULift.{u + 1} B)).mpr hP
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := pointFiniteModel B (C.X i) eR P
  exact ⟨Q, hQ, ⟨encodingForwardPullback B X eR (C.f i) F ≪≫
    (CondensedRing.finiteDiscreteCoefficientEquivalence B eR
      (internalToModule (ULift.{u + 1} B)) rfl (C.X i)).functor.mapIso eP ≪≫ eQ.symm⟩⟩

omit [DiscreteTopology B] [Finite B] in
private theorem constantConstructible_iso
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified
      (Profinite.continuousMapRingObj.{u} B) X M) :
    IsFiniteConstantStratified (Profinite.continuousMapRingObj.{u} B) X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun i ↦ modelOfIso _
    ((CondensedRing.upperStar _ (S.immersion i)).mapIso e.symm) (hS i)⟩

private theorem encoding_constructible_iff
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))) :
    IsConstructible (ULift.{u + 1} B) F ↔
      IsConstantModelConstructible (Profinite.continuousMapRingObj.{u} B) X
        ((CondensedRing.finiteDiscreteCoefficientEquivalence B eR
          (internalToModule (ULift.{u + 1} B)) rfl X).functor.obj F) := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, fun i ↦ ?_⟩
    exact modelOfIso _ (encodingForwardPullback B X eR (S.immersion i) F)
      (finiteLocalModel_of_ordinary B (S.domain i) eR _ (hS i))
  · intro h
    let E := CondensedRing.finiteDiscreteCoefficientEquivalence B eR
      (internalToModule (ULift.{u + 1} B)) rfl X
    have h' := CondensedRing.finiteDiscreteCoefficient_constructible B eR
      (internalToModule (ULift.{u + 1} B)) rfl X (E.functor.obj F)
      (modelStratifiedConstructible _ X _ h)
    exact isConstructible_of_iso (E.unitIso.app F).symm h'

private theorem realized_constructible_iff
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))) :
    IsConstructible (ULift.{u + 1} B) F ↔
      IsConstantModelConstructible (Profinite.continuousMapRingObj.{u} B) X
        ((finiteComparisonRealization B X eR).obj F) := by
  classical
  let e := (realizedEncodingIso B X eR).app F
  rw [encoding_constructible_iff B X eR F]
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, if_pos hX]
  exact ⟨constantConstructible_iso B X e.symm,
    constantConstructible_iso B X e⟩

end InternalRealization

attribute [local instance] finiteRealizationMonoidal


private theorem coefficient_pro_constructible
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (u + 1)) [CommRing A] [Finite A] [IsNoetherianRing A]
    (F : ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :
    Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, u + 1} X A F ↔
      IsConstructible A ((finiteComparisonProEtaleModelRealization X A).obj F) := by
  rw [coefficient_pro_global]
  change (∃ S : Scheme.Stratification X, _) ↔ ∃ S : Scheme.Stratification X, _
  apply exists_congr
  intro S
  apply forall_congr'
  intro i
  rw [proSites_localFinite]
  let e := (proSitePullbackSquare (S.immersion i) A).app
    ((coefficientModelFixedScalars _ A).obj F)
  exact (show localFinite _ A _ ↔ localFinite _ A _ from
    ⟨localFinite_iso _ A e, localFinite_iso _ A e.symm⟩).trans
      (pro_localFinite_iff _ A _)

private theorem coefficient_pro_bounded
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]
    (K : ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (ULift.{u + 1} B))) :
    coefficientBoundedConstructibleProEtale.{u, u + 1} X (ULift.{u + 1} B) K ↔
      constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} B) X
        ((finiteComparisonRealization B X eR).mapDerivedCategory.obj
          ((finiteComparisonProEtaleModelRealization X (ULift.{u + 1} B)).mapDerivedCategory.obj
            K)) := by
  let F := finiteComparisonProEtaleModelRealization X (ULift.{u + 1} B)
  let G := finiteComparisonRealization B X eR
  let : G.IsEquivalence := (finiteComparisonRealization_exact B X eR).1
  unfold coefficientBoundedConstructibleProEtale constantModelBoundedConstructible
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [and_comm (a := DerivedCategory.TStructure.t.bounded _)]
  apply and_congr
  · apply forall_congr'
    intro n
    let e := (F.mapDerivedCategoryHomologyFunctorIso n).app K
    let f := (G.mapDerivedCategoryHomologyFunctorIso n).app (F.mapDerivedCategory.obj K)
    exact (coefficient_pro_constructible X (ULift.{u + 1} B) _).trans
      ((show IsConstructible _ _ ↔ IsConstructible _ _ from
        ⟨isConstructible_of_iso e, isConstructible_of_iso e.symm⟩).trans
        ((realized_constructible_iff B X eR _).trans (by
          classical
          have hX : CompactSpace X ∧ QuasiSeparatedSpace X :=
            ⟨inferInstance, inferInstance⟩
          simp only [IsConstantModelConstructible, if_pos hX]
          exact ⟨constantConstructible_iso B X f,
            constantConstructible_iso B X f.symm⟩)))
  · rw [bounded_iff_interval]
    exact (bounded_cohomology_transport F K).trans
      (bounded_cohomology_transport G (F.mapDerivedCategory.obj K))

private local instance constantModel_bounded_iso
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    (constantModelBoundedConstructible
      (Profinite.continuousMapRingObj.{u} B) X).IsClosedUnderIsomorphisms where
  of_iso e h := by
    refine ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1, fun q ↦ ?_⟩
    classical
    have hh := h.2 q
    have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
    simp only [IsConstantModelConstructible, if_pos hX] at hh ⊢
    exact constantConstructible_iso B X ((DerivedCategory.homologyFunctor _ q).mapIso e) hh

private theorem coefficient_pro_finiteTor
    (X : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]
    (K : ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (ULift.{u + 1} B))) :
    Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u + 1} X (ULift.{u + 1} B) K ↔
      _root_.DerivedCategory.finiteTorAmplitude _
        ((finiteComparisonRealization B X eR).mapDerivedCategory.obj
          ((finiteComparisonProEtaleModelRealization X (ULift.{u + 1} B)).mapDerivedCategory.obj
            K)) := by
  change (∃ a b : ℤ, HasCoefficientModelTorAmplitude _ K a b) ↔ _
  rw [coefficient_finite_native]
  let F := finiteComparisonProEtaleModelRealization X (ULift.{u + 1} B)
  let G := finiteComparisonRealization B X eR
  let : G.IsEquivalence := (finiteComparisonRealization_exact B X eR).1
  let := F.preservesFlat_of_isEquivalence
  let := G.preservesFlat_of_isEquivalence
  apply exists_congr
  intro a
  apply exists_congr
  intro b
  exact (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff F a b K).symm.trans
    (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff G a b
      (F.mapDerivedCategory.obj K)).symm

end AlgebraicGeometry.ProEtale

end FiniteComparisonProof

namespace AlgebraicGeometry.ProEtale

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

attribute [local instance] etale_bounded_iso constantModel_bounded_iso in
-- Fix the coefficient universes only within these private proofs.
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify in
/-- The specified model realizations identify the two coefficient presentations of
bounded finite-Tor constructibility.
This is a change of coefficient presentation, independently of any equivalence between
the etale and pro-etale constructible subcategories.

Source: blueprint finite comparison, coefficient paragraph; Stacks Tags 03CY, 09AJ,
09AL and 08G1 (blueprint: lem-ctf-finite-comparison-presentation).

Proof: restriction to constant scalars is the exact equivalence proved in
coefficientModelFixedScalars_isEquivalence. Compose with the AsSmall site equivalences,
as in the definitions of the two model realizations. Their inverses identify the same
sections and scalar actions. On the etale site finite locally constant modules and
finite locally closed stratifications are unchanged by these equivalences. For the
pro-etale site use the finite-discrete coefficient ring isomorphism: a finite matrix
between regular condensed modules consists of constant scalar entries; its cokernel
is the constant sheaf of the corresponding finitely presented B-module. Conversely
any finitely generated B-module has such a finite presentation, since the finite ring
B is Noetherian. Pullback commutes with these presentations and with scalar transport,
so local trivializations on each stratum identify the two constructibility predicates.
The qcqs affine-local and finite global stratification conventions agree by finite
stratification gluing. Exactness identifies cohomology and reflects zero objects, hence
preserves the same finite cohomological bounds. These coefficient equivalences are
strong monoidal: sectionwise tensor products and their sheafifications agree on pure
tensors. Thus K-flat representatives and tensor tests in degree zero give the same Tor
interval on either side, including reflection by the inverse equivalence. This proves
the two replete-image equalities.

Empty schemes, zero rings, and zero complexes are covered by these constructions. -/
theorem finiteComparisonPresentation (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    let A := ULift.{u + 1} B
    letI : IsNoetherianRing A := inferInstance
    letI : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
      HasDerivedCategory.standard _
    let P : ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
      fun K ↦ Scheme.IsCoefficientBoundedConstructibleEtale.{u, u + 1} X A K ∧
        ∃ a b : ℤ, HasCoefficientModelTorAmplitude _ K a b
    let Q : ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
      fun K ↦ coefficientBoundedConstructibleProEtale.{u, u + 1} X A K ∧
        Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u + 1} X A K
    P.map (finiteComparisonEtaleModelRealization X A).mapDerivedCategory =
        finiteComparisonEtaleGenerators B X ∧
    Q.map (finiteComparisonProEtaleModelRealization X A).mapDerivedCategory =
        finiteComparisonProEtaleGenerators B eR X := by
  dsimp only
  constructor
  · let : (finiteComparisonEtaleGenerators B X).IsClosedUnderIsomorphisms := by
      unfold finiteComparisonEtaleGenerators
      infer_instance
    apply map_eq_of_equivalence
    intro K
    exact and_congr (coefficient_etale_bounded X (ULift.{u + 1} B) K)
      (coefficient_etale_finiteTor X (ULift.{u + 1} B) K)
  · let : (finiteComparisonProEtaleGenerators B eR X).IsClosedUnderIsomorphisms := by
      change ((constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} B) X ⊓
        _root_.DerivedCategory.finiteTorAmplitude _).inverseImage
          (finiteComparisonRealization B X eR).mapDerivedCategory).IsClosedUnderIsomorphisms
      infer_instance
    apply map_eq_of_equivalence
    intro K
    exact and_congr (coefficient_pro_bounded B X eR K)
      (coefficient_pro_finiteTor B X eR K)

end AlgebraicGeometry.ProEtale
