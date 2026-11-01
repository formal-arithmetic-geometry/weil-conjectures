/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionData
import WeilConjectures.AlgebraicGeometry.LocallyClosedCoefficientImmersion.LocallyClosedModuleExtensionModel
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionAssociativityPart
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionBinary
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionBoundary
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionUnitPart

/-! Normalized locally closed module extension: assembly from the fixed model. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Witnesses for the exact module extensions in the assertion. The open adjunction and
closed counit normalize restriction. The coefficients of every arrow are inverse images.
Source: Stacks, Tags 09AA, 09BM, 09BN, 03DI and 03DJ
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure LocallyClosedExtensionData where
  extension : ∀ {S X : LocallyClosedCoefficients.{u}}, LocallyClosedCoefficientImmersion S X →
    proEtaleRingModules S.scheme S.ring ⥤ proEtaleRingModules X.scheme X.ring
  additive : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (extension a).Additive
  finiteLimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteLimits (extension a)
  finiteColimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteColimits (extension a)
  restriction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), extension a ⋙ a.pull ≅ 𝟭 _
  openAdjunction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsOpenImmersion a.hom),
    extension a ⊣ a.pull
  openNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsOpenImmersion a.hom),
    LocallyClosedOpenNormalization (extension a) a.pull (restriction a) (openAdjunction a ha)
  closedComparison : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsClosedImmersion a.hom),
    extension a ≅ a.push
  closedNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsClosedImmersion a.hom),
    LocallyClosedClosedNormalization (extension a) a.push a.pull (restriction a)
      (proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).counit
      (closedComparison a ha)
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    extension b ⋙ extension a ≅ extension (a.comp b)
  identity : ∀ X : LocallyClosedCoefficients.{u},
    extension (.identity X) ≅ 𝟭 (proEtaleRingModules X.scheme X.ring)

attribute [instance] LocallyClosedExtensionData.additive LocallyClosedExtensionData.finiteLimits
  LocallyClosedExtensionData.finiteColimits

namespace LocallyClosedExtensionData

/-- The actual termwise extension on the ordinary unbounded derived categories.
Source: Stacks, Tags 015F and 05RU
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
abbrev derived (E : LocallyClosedExtensionData.{u}) {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) := (E.extension a).mapDerivedCategory

/-- Normalized comparison laws on module sheaves. The two factorization orders follow
by composing `gamma` with `closedComparison` and the open adjunction; normalization
and the Hom bijection make the comparison between any two factorizations unique.
Source: Stacks, Tags 02V0 and 09AH, composite consequence described in the node proof
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure Coherent (E : LocallyClosedExtensionData.{u}) : Prop where
  full : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (E.extension a).Full
  faithful : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), (E.extension a).Faithful
  homBijection : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (M N : proEtaleRingModules S.scheme S.ring),
    Function.Bijective (fun f : (E.extension a).obj M ⟶ (E.extension a).obj N ↦
      (E.restriction a).inv.app M ≫ a.pull.map f ≫ (E.restriction a).hom.app N)
  normalized : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    LocallyClosedBinaryNormalization (E.extension a) (E.extension b) a.pull b.pull
      (a.comp b).pull (E.extension (a.comp b)) (E.restriction a) (E.restriction b)
      (E.restriction (a.comp b)) (a.pullComp b) (E.gamma a b)
  innerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : a.comp (.identity S) = a,
      E.gamma a (.identity S) ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerRight (E.identity S) (E.extension a) ≪≫
          Functor.leftUnitor (E.extension a)
  outerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      E.gamma (.identity X) a ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerLeft (E.extension a) (E.identity X) ≪≫
          Functor.rightUnitor (E.extension a)
  associative : ∀ {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T),
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (E.gamma b d) (E.extension a) ≪≫ E.gamma a (b.comp d) =
        Functor.associator (E.extension d) (E.extension b) (E.extension a) ≪≫
          Functor.isoWhiskerLeft (E.extension d) (E.gamma a b) ≪≫ E.gamma (a.comp b) d ≪≫
            eqToIso (congrArg E.extension h)

end LocallyClosedExtensionData

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage

private theorem restriction_hom_bijective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    [F.Full] [F.Faithful] (r : F ⋙ L ≅ 𝟭 C) (M N : C) :
    Function.Bijective (fun f : F.obj M ⟶ F.obj N ↦
      r.inv.app M ≫ L.map f ≫ r.hom.app N) := by
  have hr (f : M ⟶ N) : r.inv.app M ≫ L.map (F.map f) ≫ r.hom.app N = f := by
    simpa using congrArg (fun g ↦ r.inv.app M ≫ g) (r.hom.naturality f)
  constructor
  · intro f g h
    obtain ⟨f, rfl⟩ := F.map_surjective f
    obtain ⟨g, rfl⟩ := F.map_surjective g
    change r.inv.app M ≫ L.map (F.map f) ≫ r.hom.app N =
      r.inv.app M ≫ L.map (F.map g) ≫ r.hom.app N at h
    rw [hr, hr] at h
    exact congrArg F.map h
  · intro f
    exact ⟨F.map f, hr f⟩

private theorem restriction_injective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    [F.Full] [F.Faithful] (r : F ⋙ L ≅ 𝟭 C)
    {A : D} {M N : C} (e : A ≅ F.obj M) {f g : A ⟶ F.obj N}
    (h : L.map f = L.map g) : f = g := by
  apply (cancel_epi e.inv).mp
  apply (restriction_hom_bijective F L r M N).injective
  simp only [Functor.map_comp, h]

private theorem normalized_existsUnique
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D) (L : D ⥤ C)
    [H.Full] [H.Faithful] (r : H ⋙ L ≅ 𝟭 C) (A : D) (M : C)
    (t : L.obj A ⟶ M)
    (h : ∃ e : A ≅ H.obj M, LocallyClosedObjectNormalization H L r t e) :
    ∃! e : A ≅ H.obj M, LocallyClosedObjectNormalization H L r t e := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply restriction_injective H L r e
  apply (cancel_mono (r.hom.app M)).mp
  exact he'.trans he.symm

private theorem model_binary_existsUnique {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (M : proEtaleRingModules T.scheme T.ring) :
    ∃! e : a.modelExtension.obj (b.modelExtension.obj M) ≅ (a.comp b).modelExtension.obj M,
      LocallyClosedObjectNormalization (a.comp b).modelExtension (a.comp b).pull
        (a.comp b).modelRestriction
        (LocallyClosedCompositeRestrictionMap a.modelExtension b.modelExtension a.pull b.pull
          (a.comp b).pull a.modelRestriction b.modelRestriction (a.pullComp b) M) e := by
  exact normalized_existsUnique (a.comp b).modelExtension (a.comp b).pull
    (a.comp b).modelRestriction (a.modelExtension.obj (b.modelExtension.obj M)) M _
    (locallyClosedModel_binary_exists a b M)

-- An objectwise normalized comparison is automatically natural. This is the
-- categorical glue between the geometric binary lemma and the final system.

private def normalizedNatIso
    {C D : Type*} [Category C] [Category D] (F H : C ⥤ D) (L : D ⥤ C)
    [H.Full] [H.Faithful] (r : H ⋙ L ≅ 𝟭 C) (s : F ⋙ L ≅ 𝟭 C)
    (e : ∀ M, F.obj M ≅ H.obj M)
    (he : ∀ M, L.map (e M).hom ≫ r.hom.app M = s.hom.app M) : F ≅ H :=
  NatIso.ofComponents e (by
    intro M N f
    apply restriction_injective H L r (e M)
    apply (cancel_mono (r.hom.app N)).mp
    simp only [Functor.map_comp, Category.assoc]
    have hr : L.map (H.map f) ≫ r.hom.app N = r.hom.app M ≫ f :=
      r.hom.naturality f
    rw [he, hr, ← Category.assoc, he]
    exact s.hom.naturality f)

private def compositeRestriction
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Ea : B ⥤ C) (Eb : A ⥤ B) (La : C ⥤ B) (Lb : B ⥤ A) (Lab : C ⥤ A)
    (ra : Ea ⋙ La ≅ 𝟭 B) (rb : Eb ⋙ Lb ≅ 𝟭 A) (c : Lab ≅ La ⋙ Lb) :
    (Eb ⋙ Ea) ⋙ Lab ≅ 𝟭 A :=
  NatIso.ofComponents (fun M ↦ c.app (Ea.obj (Eb.obj M)) ≪≫
    Lb.mapIso (ra.app (Eb.obj M)) ≪≫ rb.app M) (by
    intro M N f
    simp only [Functor.comp_map, Functor.id_map, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom]
    have hc := c.hom.naturality (Ea.map (Eb.map f))
    have ha := ra.hom.naturality (Eb.map f)
    have hb := rb.hom.naturality f
    simp only [Functor.comp_map, Functor.id_map] at hc ha hb
    calc
      _ = c.hom.app _ ≫ Lb.map (La.map (Ea.map (Eb.map f))) ≫
          Lb.map (ra.hom.app (Eb.obj N)) ≫ rb.hom.app N := by
        rw [← Category.assoc, hc, Category.assoc]
      _ = c.hom.app _ ≫ Lb.map
          (La.map (Ea.map (Eb.map f)) ≫ ra.hom.app (Eb.obj N)) ≫ rb.hom.app N := by
        rw [Lb.map_comp, Category.assoc]
      _ = c.hom.app _ ≫ Lb.map
          (ra.hom.app (Eb.obj M) ≫ Eb.map f) ≫ rb.hom.app N := by rw [ha]
      _ = c.hom.app _ ≫ Lb.map (ra.hom.app (Eb.obj M)) ≫
          Lb.map (Eb.map f) ≫ rb.hom.app N := by rw [Lb.map_comp, Category.assoc]
      _ = _ := by rw [hb]; simp only [Category.assoc])

private theorem compositeRestriction_hom
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Ea : B ⥤ C) (Eb : A ⥤ B) (La : C ⥤ B) (Lb : B ⥤ A) (Lab : C ⥤ A)
    (ra : Ea ⋙ La ≅ 𝟭 B) (rb : Eb ⋙ Lb ≅ 𝟭 A) (c : Lab ≅ La ⋙ Lb) (M : A) :
    (compositeRestriction Ea Eb La Lb Lab ra rb c).hom.app M =
      c.hom.app (Ea.obj (Eb.obj M)) ≫ Lb.map (ra.hom.app (Eb.obj M)) ≫ rb.hom.app M := rfl

@[irreducible] private def uniqueChoice {A : Type*} {P : A → Prop}
    (h : ∃! x, P x) : A := h.choose

private structure NormalizedComponent {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (M : proEtaleRingModules T.scheme T.ring) where
  iso : a.modelExtension.obj (b.modelExtension.obj M) ≅ (a.comp b).modelExtension.obj M
  normalized : LocallyClosedObjectNormalization (a.comp b).modelExtension
    (a.comp b).pull (a.comp b).modelRestriction
    (LocallyClosedCompositeRestrictionMap a.modelExtension b.modelExtension a.pull b.pull
      (a.comp b).pull a.modelRestriction b.modelRestriction (a.pullComp b) M) iso

private theorem normalizedComponent_existsUnique {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (M : proEtaleRingModules T.scheme T.ring) :
    ∃! _e : NormalizedComponent a b M, True := by
  obtain ⟨e, he, hu⟩ := model_binary_existsUnique a b M
  refine ⟨⟨e, he⟩, trivial, ?_⟩
  rintro ⟨e', he'⟩ _
  have h : e' = e := hu e' he'
  subst e'
  rfl

private structure BinaryComparison
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Ea : B ⥤ C) (Eb : A ⥤ B) (La : C ⥤ B) (Lb : B ⥤ A) (Lab : C ⥤ A)
    (H : A ⥤ C) (ra : Ea ⋙ La ≅ 𝟭 B) (rb : Eb ⋙ Lb ≅ 𝟭 A)
    (rh : H ⋙ Lab ≅ 𝟭 A) (c : Lab ≅ La ⋙ Lb) where
  iso : Eb ⋙ Ea ≅ H
  normalized : LocallyClosedBinaryNormalization Ea Eb La Lb Lab H ra rb rh c iso

private theorem binaryComparison_nonempty
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Ea : B ⥤ C) (Eb : A ⥤ B) (La : C ⥤ B) (Lb : B ⥤ A) (Lab : C ⥤ A)
    (H : A ⥤ C) [H.Full] [H.Faithful]
    (ra : Ea ⋙ La ≅ 𝟭 B) (rb : Eb ⋙ Lb ≅ 𝟭 A)
    (rh : H ⋙ Lab ≅ 𝟭 A) (c : Lab ≅ La ⋙ Lb)
    (e : ∀ M, Ea.obj (Eb.obj M) ≅ H.obj M)
    (he : ∀ M, LocallyClosedObjectNormalization H Lab rh
      (LocallyClosedCompositeRestrictionMap Ea Eb La Lb Lab ra rb c M) (e M)) :
    Nonempty (BinaryComparison Ea Eb La Lb Lab H ra rb rh c) := ⟨{
  iso := normalizedNatIso (Eb ⋙ Ea) H Lab rh
    (compositeRestriction Ea Eb La Lb Lab ra rb c) e (fun M ↦ by
      rw [compositeRestriction_hom]
      exact he M)
  normalized := fun M ↦ he M }⟩

@[irreducible] private def binaryComparisonFromComponents
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Ea : B ⥤ C) (Eb : A ⥤ B) (La : C ⥤ B) (Lb : B ⥤ A) (Lab : C ⥤ A)
    (H : A ⥤ C) [H.Full] [H.Faithful]
    (ra : Ea ⋙ La ≅ 𝟭 B) (rb : Eb ⋙ Lb ≅ 𝟭 A)
    (rh : H ⋙ Lab ≅ 𝟭 A) (c : Lab ≅ La ⋙ Lb)
    (e : ∀ M, Ea.obj (Eb.obj M) ≅ H.obj M)
    (he : ∀ M, LocallyClosedObjectNormalization H Lab rh
      (LocallyClosedCompositeRestrictionMap Ea Eb La Lb Lab ra rb c M) (e M)) :
    BinaryComparison Ea Eb La Lb Lab H ra rb rh c :=
  Classical.choice (binaryComparison_nonempty Ea Eb La Lb Lab H ra rb rh c e he)

@[irreducible] private def modelBinaryComparison
    {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (Q : ∀ M, NormalizedComponent a b M) :
    BinaryComparison a.modelExtension b.modelExtension a.pull b.pull (a.comp b).pull
      (a.comp b).modelExtension a.modelRestriction b.modelRestriction
      (a.comp b).modelRestriction (a.pullComp b) :=
  binaryComparisonFromComponents a.modelExtension b.modelExtension a.pull b.pull (a.comp b).pull
    (a.comp b).modelExtension a.modelRestriction b.modelRestriction
    (a.comp b).modelRestriction (a.pullComp b)
    (fun M ↦ (Q M).iso) (fun M ↦ (Q M).normalized)

@[irreducible] private def compositionFromComponents
    (Q : ∀ {S X T : LocallyClosedCoefficients.{u}}
      (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
      (M : proEtaleRingModules T.scheme T.ring), NormalizedComponent a b M) :
    LocallyClosedModelComposition.{u} where
  gamma := fun a b ↦ (modelBinaryComparison a b (Q a b)).iso
  normalized := fun a b ↦ (modelBinaryComparison a b (Q a b)).normalized

private structure OpenNormalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) where
  adj : F ⊣ L
  normalized : LocallyClosedOpenNormalization F L r adj

private theorem openNormalization_nonempty
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C)
    (h : ∃ adj : F ⊣ L, LocallyClosedOpenNormalization F L r adj) :
    Nonempty (OpenNormalization F L r) := ⟨⟨h.choose, h.choose_spec⟩⟩

@[irreducible] private def openNormalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C)
    (h : ∃ adj : F ⊣ L, LocallyClosedOpenNormalization F L r adj) :
    OpenNormalization F L r := Classical.choice (openNormalization_nonempty F L r h)

private structure ClosedNormalization
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C) where
  iso : F ≅ P
  normalized : LocallyClosedClosedNormalization F P L r d iso

private theorem closedNormalization_nonempty
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C)
    (h : ∃ e : F ≅ P, LocallyClosedClosedNormalization F P L r d e) :
    Nonempty (ClosedNormalization F P L r d) := ⟨⟨h.choose, h.choose_spec⟩⟩

@[irreducible] private def closedNormalization
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C)
    (h : ∃ e : F ≅ P, LocallyClosedClosedNormalization F P L r d e) :
    ClosedNormalization F P L r d :=
  Classical.choice (closedNormalization_nonempty F P L r d h)

private theorem assembleFixedModel (G : LocallyClosedModelComposition.{u}) :
    ∃ E : LocallyClosedExtensionData.{u}, E.NormalizedComposition := by
  obtain ⟨identity, inner, outer, assoc⟩ := locallyClosedModel_unit_associativity G
  refine ⟨{
    extension := fun a ↦ a.modelExtension
    additive := fun a ↦ inferInstance
    finiteLimits := fun a ↦ inferInstance
    finiteColimits := fun a ↦ inferInstance
    restriction := fun a ↦ a.modelRestriction
    openAdjunction := fun a ha ↦ (openNormalization a.modelExtension a.pull a.modelRestriction
      ((locallyClosedModel_boundary a).1 ha)).adj
    openNormalization := fun a ha ↦ (openNormalization a.modelExtension a.pull a.modelRestriction
      ((locallyClosedModel_boundary a).1 ha)).normalized
    closedComparison := fun a ha ↦ (closedNormalization a.modelExtension a.push a.pull
      a.modelRestriction
      (proEtaleRingModuleAdjunction a.hom _ _ a.coefficient).counit
      ((locallyClosedModel_boundary a).2 ha)).iso
    closedNormalization := fun a ha ↦ (closedNormalization a.modelExtension a.push a.pull
      a.modelRestriction
      (proEtaleRingModuleAdjunction a.hom _ _ a.coefficient).counit
      ((locallyClosedModel_boundary a).2 ha)).normalized
    gamma := G.gamma
    identity := identity }, ?_⟩
  exact ⟨G.normalized, inner, outer, assoc⟩

/-- Exact locally closed extension on module sheaves, with normalized factorization
comparisons and unital, associative composition.

Source: Stacks, proetale.tex Tags 09AA, 09BM, 09BN and 09AH; sites-modules.tex
Tags 03DI and 03DJ; schemes.tex Tag 02V0; blueprint main-20261015,
det-prop-scalar-six-pullback proof (2)
(blueprint: lem-sfb-locally-closed-module-extension-coherence).

Proof: construct a fixed closed-then-open extension, using a locally closed
factorization, the actual closed direct image and the identified open extension.
The open factor is a fully faithful left adjoint and the closed factor a fully
faithful right adjoint. Their exactness and additivity compose; the inverse open
unit, the closed counit and canonical inverse-image composition give restriction.
The model module proves these assertions for the constructed functor.

The boundary lemma compares this fixed model to the actual open and closed
extensions. Its proof uses restriction to intersections and shrinking of an open
ambient neighbourhood of the closed support; these preserve the specified units
and counits. The binary lemma constructs an objectwise normalized isomorphism by
interchanging the middle open and closed factors, composing pure factors, and
comparing with the chosen factorization.

Restriction is injective on maps between objects in the extension image: the
extension is fully faithful and its composite with restriction is the identity.
This proves uniqueness of the objectwise comparison. The normalization formulas
and naturality of restriction then prove naturality of the chosen comparisons,
so they assemble into gamma. Finally the formal unit/associativity lemma supplies
identity comparisons and the three coherence laws: restriction turns each pair
of paths into the same canonical inverse-image pasting, and its injectivity makes
the original paths equal. Assemble this data and the boundary normalizations into
the required system. The three unfinished comparison lemmas are in separate
modules, each with its source and proof in words.
-/
theorem locallyClosedModuleExtensionCoherence :
    ∃ E : LocallyClosedExtensionData.{u}, E.NormalizedComposition := by
  exact assembleFixedModel (compositionFromComponents
    (fun a b M ↦ uniqueChoice (normalizedComponent_existsUnique a b M)))

end AlgebraicGeometry.Scheme
