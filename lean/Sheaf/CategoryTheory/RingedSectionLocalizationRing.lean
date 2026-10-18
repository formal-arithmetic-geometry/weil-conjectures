/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.CategoryTheory.RingedSectionLocalization
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
  sorry

/-- The localization restrictions preserve composites as ring maps.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both composites extend the same restriction of R, by naturality of s;
uniqueness of localization lifts gives equality. -/
theorem ringedLocalizationRing_map_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    ringedSectionLocalizationMap R s (f ≫ g) =
      (ringedSectionLocalizationMap R s g).comp (ringedSectionLocalizationMap R s f) := by
  sorry

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
  sorry

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
  sorry

end CategoryTheory
