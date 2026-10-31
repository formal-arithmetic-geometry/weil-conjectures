/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits

/-!
# The ring structure on sheafified section localization

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(blueprint: def-weil-pbc-ringed-section-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{u})
variable (s : (R.obj ⋙ forget CommRingCat).sections)

/-- The localization restrictions preserve identities as ring maps.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both maps extend the identity of R(U); uniqueness of localization lifts applies. -/
theorem ringedLocalizationRing_map_id (U : Cᵒᵖ) :
    ringedSectionLocalizationMap R s (𝟙 U) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (R := R.obj.obj U) (Submonoid.powers (s.val U))
  ext r
  simp [ringedSectionLocalizationMap]

/-- The localization restrictions preserve composites as ring maps.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both composites extend the same restriction of R, by naturality of s;
uniqueness of localization lifts gives equality. -/
theorem ringedLocalizationRing_map_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    ringedSectionLocalizationMap R s (f ≫ g) =
      (ringedSectionLocalizationMap R s g).comp (ringedSectionLocalizationMap R s f) := by
  apply IsLocalization.ringHom_ext (R := R.obj.obj U) (Submonoid.powers (s.val U))
  ext r
  simp [ringedSectionLocalizationMap, Functor.map_comp]

/-- The actual presheaf of commutative rings U ↦ R(U)[1/s(U)].
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingPresheaf : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (ringedSectionLocalizationCarrier R s U)
  map f := CommRingCat.ofHom (ringedSectionLocalizationMap R s f)
  map_id U := congrArg CommRingCat.ofHom (ringedLocalizationRing_map_id R s U)
  map_comp f g := congrArg CommRingCat.ofHom (ringedLocalizationRing_map_comp R s f g)

/-- The section localization algebra maps commute with restrictions.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: each localization lift extends exactly the specified restriction map. -/
theorem ringedLocalizationRing_unit_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    R.obj.map f ≫ CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrier R s V)) =
      CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrier R s U)) ≫
        (ringedLocalizationRingPresheaf R s).map f := by
  ext r
  simp [ringedLocalizationRingPresheaf, ringedSectionLocalizationMap]

/-- The sectionwise algebra map into localization.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingPresheafUnit : R.obj ⟶ ringedLocalizationRingPresheaf R s where
  app U := CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrier R s U))
  naturality _ _ f := ringedLocalizationRing_unit_naturality R s f

/-- Sheafified section localization as a sheaf of commutative rings.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRing : Sheaf J CommRingCat.{u} :=
  (presheafToSheaf J CommRingCat.{u}).obj (ringedLocalizationRingPresheaf R s)

/-- The canonical map of ring sheaves from R to R[1/s].
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingUnit : R ⟶ ringedLocalizationRing R s :=
  ⟨ringedLocalizationRingPresheafUnit R s ≫
    toSheafify J (ringedLocalizationRingPresheaf R s)⟩

set_option maxHeartbeats 1600000 in
-- Budget for elaborating both ring and module sheafification constructions.
/-- The ring-sheaf construction is the original module sheafification, with the
canonical identification on every local fraction.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both underlying module sheaves represent restriction-compatible linear
maps out of the section-localization presheaf. Ring sheafification carries the
sectionwise scalar action, since multiplication and its identities sheafify.
The two sheafification universal properties give mutually inverse module maps;
they agree on every section of the presheaf, giving the displayed normalization. -/
theorem ringedLocalizationRing_moduleComparison :
    ∃ e :
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map
          (ringedLocalizationRingUnit R s))).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRing R s))) ≅ ringedSectionLocalization R s,
      ∀ (U : Cᵒᵖ) (x : ringedSectionLocalizationCarrier R s U),
        e.hom.val.app U ((toSheafify J (ringedLocalizationRingPresheaf R s)).app U x) =
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
              (ringedSectionLocalizationPresheaf R s)).app U) x := by
  classical
  have comparison {B : Sheaf J RingCat.{u}}
      (P : PresheafOfModules.{u} B.obj) (A : SheafOfModules.{u} B)
      (φ : P ⟶ A.val)
      [PresheafOfModules.IsLocallyInjective J φ]
      [PresheafOfModules.IsLocallySurjective J φ] :
      ∃ e : A ≅ (PresheafOfModules.sheafification (𝟙 B.obj)).obj P,
        φ ≫ e.hom.val =
          (PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P := by
    let M := (PresheafOfModules.sheafification (𝟙 B.obj)).obj P
    let η : P ⟶ M.val :=
      (PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P
    have : PresheafOfModules.IsLocallyInjective J η := by
      change Presheaf.IsLocallyInjective J (toSheafify J P.presheaf)
      infer_instance
    have : PresheafOfModules.IsLocallySurjective J η := by
      change Presheaf.IsLocallySurjective J (toSheafify J P.presheaf)
      infer_instance
    let g : M ⟶ A := ⟨(PresheafOfModules.homEquivOfIsLocallyBijective
      (f := η) A.isSheaf).symm φ⟩
    have hg : η ≫ g.val = φ := by
      exact (PresheafOfModules.homEquivOfIsLocallyBijective
        (f := η) A.isSheaf).apply_symm_apply φ
    let f : A ⟶ M := ⟨(PresheafOfModules.homEquivOfIsLocallyBijective
      (f := φ) M.isSheaf).symm η⟩
    have hf : φ ≫ f.val = η := by
      exact (PresheafOfModules.homEquivOfIsLocallyBijective
        (f := φ) M.isSheaf).apply_symm_apply η
    have hfg : f ≫ g = 𝟙 A := by
      apply (SheafOfModules.fullyFaithfulForget _).map_injective
      apply (PresheafOfModules.homEquivOfIsLocallyBijective (f := φ) A.isSheaf).injective
      change φ ≫ (f.val ≫ g.val) = φ ≫ 𝟙 A.val
      rw [← Category.assoc, hf, hg, Category.comp_id]
    have hgf : g ≫ f = 𝟙 M := by
      apply (SheafOfModules.fullyFaithfulForget _).map_injective
      apply (PresheafOfModules.homEquivOfIsLocallyBijective (f := η) M.isSheaf).injective
      change η ≫ (g.val ≫ f.val) = η ≫ 𝟙 M.val
      rw [← Category.assoc, hg, hf, Category.comp_id]
    exact ⟨⟨f, g, hfg, hgf⟩, hf⟩
  let P := ringedSectionLocalizationPresheaf R s
  let A := (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map
      (ringedLocalizationRingUnit R s))).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRing R s)))
  let ι := toSheafify J (ringedLocalizationRingPresheaf R s)
  let φ : P ⟶ A.val := PresheafOfModules.homMk
    (Functor.whiskerRight ι
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
        intro U r x
        change R.obj.obj U at r
        change ringedSectionLocalizationCarrier R s U at x
        change (ι.app U).hom (r • x) = _
        rw [Algebra.smul_def, (ι.app U).hom.map_mul]
        rfl)
  have : PresheafOfModules.IsLocallyInjective J φ := by
    change Presheaf.IsLocallyInjective J
      (Functor.whiskerRight ι
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
    rw [← Presheaf.isLocallyInjective_forget_iff]
    change Presheaf.IsLocallyInjective J
      (Functor.whiskerRight ι (forget CommRingCat))
    infer_instance
  have : PresheafOfModules.IsLocallySurjective J φ := by
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight ι
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
    rw [Presheaf.isLocallySurjective_iff_whisker_forget]
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight ι (forget CommRingCat))
    infer_instance
  obtain ⟨e, he⟩ := comparison P A φ
  refine ⟨e, ?_⟩
  intro U x
  exact DFunLike.congr_fun (congrArg (fun k ↦ (k.app U).hom) he) x

end CategoryTheory
