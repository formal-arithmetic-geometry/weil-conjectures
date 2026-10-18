/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NE, N6, Q14
-/
module

public import Sheaf.CategoryTheory.RingedSectionLocalizationRing

/-!
# Section localization with independent site universes

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(blueprint: def-weil-pbc-ringed-section-localization).
The construction is the same sectionwise localization followed by sheafification.
This interface allows a site with different object and morphism universes. Sheafification
is parameterized by its existing instances in the chosen coefficient universe. The previous
small-category interface is retained by the public import.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uC vC

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (O : Sheaf J CommRingCat.{u})

/-- Sectionwise carrier of the localization, using Mathlib's actual ring localization.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization). -/
abbrev ringedSectionLocalizationCarrierOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :=
  Localization.Away (M := O.obj.obj X) (s.val X)

/-- The image of a global section is invertible after localization on the target object.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization).
Proof: naturality identifies the restricted section with the target section, whose image
in its localization is a unit by `IsLocalization.Away.algebraMap_isUnit`. -/
theorem ringedSectionLocalization_isUnitOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    IsUnit ((algebraMap (O.obj.obj Y) (ringedSectionLocalizationCarrierOfUniverses O s Y))
      (O.obj.map a ((s.val X : O.obj.obj X)))) := by
  sorry

/-- Restriction on sectionwise localizations, given by the localization universal property.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedSectionLocalizationMapOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    ringedSectionLocalizationCarrierOfUniverses O s X →+*
      ringedSectionLocalizationCarrierOfUniverses O s Y :=
  IsLocalization.Away.lift (R := O.obj.obj X) (s.val X)
    (g := (algebraMap (O.obj.obj Y) (ringedSectionLocalizationCarrierOfUniverses O s Y)).comp
      (O.obj.map a).hom)
    (ringedSectionLocalization_isUnitOfUniverses O s a)

/-- Localization restriction is semilinear over restriction of coefficients.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization).
Proof: the localization lift extends the restriction ring homomorphism; apply
multiplicativity to the scalar action defined by the algebra map. -/
theorem ringedSectionLocalizationMap_smulOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y)
    (r : O.obj.obj X) (x : ringedSectionLocalizationCarrierOfUniverses O s X) :
    ringedSectionLocalizationMapOfUniverses O s a (r • x) =
      O.obj.map a r • ringedSectionLocalizationMapOfUniverses O s a x := by
  sorry

/-- The linear form of localization restriction.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedSectionLocalizationLinearMapOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    ModuleCat.of (O.obj.obj X) (ringedSectionLocalizationCarrierOfUniverses O s X) ⟶
      (ModuleCat.restrictScalars (O.obj.map a).hom).obj
        (ModuleCat.of (O.obj.obj Y) (ringedSectionLocalizationCarrierOfUniverses O s Y)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (O.obj.obj X) (ringedSectionLocalizationCarrierOfUniverses O s X))
    (Y := (ModuleCat.restrictScalars (O.obj.map a).hom).obj
      (ModuleCat.of (O.obj.obj Y) (ringedSectionLocalizationCarrierOfUniverses O s Y)))
    { toFun := ringedSectionLocalizationMapOfUniverses O s a
      map_add' := (ringedSectionLocalizationMapOfUniverses O s a).map_add
      map_smul' := ringedSectionLocalizationMap_smulOfUniverses O s a }

/-- Identity compatibility of sectionwise localization restriction.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization).
Proof: both sides extend the identity ring map, so localization uniqueness identifies them. -/
theorem ringedSectionLocalizationLinearMap_idOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) (X : Cᵒᵖ) :
    ringedSectionLocalizationLinearMapOfUniverses O s (𝟙 X) =
      (ModuleCat.restrictScalarsId' (O.obj.map (𝟙 X)).hom
        (congrArg CommRingCat.Hom.hom (O.obj.map_id X))).inv.app _ := by
  sorry

/-- Composition compatibility of sectionwise localization restriction.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization).
Proof: both maps extend the composite restriction on the coefficient ring; uniqueness
of localization lifts identifies them, including the restriction-of-scalars comparison. -/
theorem ringedSectionLocalizationLinearMap_compOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y Z : Cᵒᵖ}
    (a : X ⟶ Y) (b : Y ⟶ Z) :
    ringedSectionLocalizationLinearMapOfUniverses O s (a ≫ b) =
      ringedSectionLocalizationLinearMapOfUniverses O s a ≫
        (ModuleCat.restrictScalars (O.obj.map a).hom).map
          (ringedSectionLocalizationLinearMapOfUniverses O s b) ≫
        (ModuleCat.restrictScalarsComp' (O.obj.map a).hom (O.obj.map b).hom
          (O.obj.map (a ≫ b)).hom
          (congrArg CommRingCat.Hom.hom (O.obj.map_comp a b))).inv.app _ := by
  sorry

/-- The presheaf of modules `V ↦ O(V)[1/s(V)]`, with the actual localization lifts
as its restriction maps.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedSectionLocalizationPresheafOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    PresheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj where
  obj X := ModuleCat.of (O.obj.obj X) (ringedSectionLocalizationCarrierOfUniverses O s X)
  map a := ringedSectionLocalizationLinearMapOfUniverses O s a
  map_id X := ringedSectionLocalizationLinearMap_idOfUniverses O s X
  map_comp a b := ringedSectionLocalizationLinearMap_compOfUniverses O s a b

/-- Localization of the ring sheaf as a module sheaf, obtained by sheafifying the
sectionwise localization presheaf.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedSectionLocalizationOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) :=
  (PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).obj
      (ringedSectionLocalizationPresheafOfUniverses O s)

/-- The sectionwise units form a section of the localization presheaf.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization).
Proof: the restriction maps are ring homomorphisms and therefore preserve one. -/
theorem ringedSectionLocalizationPresheaf_one_naturalOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    (ringedSectionLocalizationPresheafOfUniverses O s).map a
      (1 : ringedSectionLocalizationCarrierOfUniverses O s X) =
        (1 : ringedSectionLocalizationCarrierOfUniverses O s Y) := by
  sorry

/-- The canonical map from the ring sheaf to its localization as a module sheaf.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedSectionLocalizationUnitOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      ringedSectionLocalizationOfUniverses O s :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    ((ringedSectionLocalizationPresheafOfUniverses O s).unitHomEquiv.symm
      (PresheafOfModules.sectionsMk
        (fun X ↦ (1 : ringedSectionLocalizationCarrierOfUniverses O s X))
        (fun {_ _} a ↦ ringedSectionLocalizationPresheaf_one_naturalOfUniverses O s a)) ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app
          (ringedSectionLocalizationPresheafOfUniverses O s))

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u})
variable (s : (R.obj ⋙ forget CommRingCat).sections)

/-- The localization restrictions preserve identities as ring maps.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both maps extend the identity of R(U); uniqueness of localization lifts applies. -/
theorem ringedLocalizationRing_map_idOfUniverses (U : Cᵒᵖ) :
    ringedSectionLocalizationMapOfUniverses R s (𝟙 U) = RingHom.id _ := by
  sorry

/-- The localization restrictions preserve composites as ring maps.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both composites extend the same restriction of R, by naturality of s;
uniqueness of localization lifts gives equality. -/
theorem ringedLocalizationRing_map_compOfUniverses {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    ringedSectionLocalizationMapOfUniverses R s (f ≫ g) =
      (ringedSectionLocalizationMapOfUniverses R s g).comp
        (ringedSectionLocalizationMapOfUniverses R s f) := by
  sorry

/-- The actual presheaf of commutative rings U ↦ R(U)[1/s(U)].
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingPresheafOfUniverses : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (ringedSectionLocalizationCarrierOfUniverses R s U)
  map f := CommRingCat.ofHom (ringedSectionLocalizationMapOfUniverses R s f)
  map_id U := congrArg CommRingCat.ofHom (ringedLocalizationRing_map_idOfUniverses R s U)
  map_comp f g := congrArg CommRingCat.ofHom (ringedLocalizationRing_map_compOfUniverses R s f g)

/-- The section localization algebra maps commute with restrictions.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: each localization lift extends exactly the specified restriction map. -/
theorem ringedLocalizationRing_unit_naturalityOfUniverses {U V : Cᵒᵖ} (f : U ⟶ V) :
    R.obj.map f ≫
        CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R s V)) =
      CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R s U)) ≫
        (ringedLocalizationRingPresheafOfUniverses R s).map f := by
  sorry

/-- The sectionwise algebra map into localization.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingPresheafUnitOfUniverses :
    R.obj ⟶ ringedLocalizationRingPresheafOfUniverses R s where
  app U := CommRingCat.ofHom (algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R s U))
  naturality _ _ f := ringedLocalizationRing_unit_naturalityOfUniverses R s f

/-- Sheafified section localization as a sheaf of commutative rings.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingOfUniverses : Sheaf J CommRingCat.{u} :=
  (presheafToSheaf J CommRingCat.{u}).obj (ringedLocalizationRingPresheafOfUniverses R s)

/-- The canonical map of ring sheaves from R to R[1/s].
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedLocalizationRingUnitOfUniverses : R ⟶ ringedLocalizationRingOfUniverses R s :=
  ⟨ringedLocalizationRingPresheafUnitOfUniverses R s ≫
    toSheafify J (ringedLocalizationRingPresheafOfUniverses R s)⟩

/-- The ring-sheaf construction is the original module sheafification, with the
canonical identification on every local fraction.
Source: Stacks Tags 0996 and 099E (blueprint: def-weil-pbc-ringed-section-localization).
Proof: both underlying module sheaves represent restriction-compatible linear
maps out of the section-localization presheaf. Ring sheafification carries the
sectionwise scalar action, since multiplication and its identities sheafify.
The two sheafification universal properties give mutually inverse module maps;
they agree on every section of the presheaf, giving the displayed normalization. -/
theorem ringedLocalizationRing_moduleComparisonOfUniverses :
    ∃ e :
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map
          (ringedLocalizationRingUnitOfUniverses R s))).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRingOfUniverses R s))) ≅ ringedSectionLocalizationOfUniverses R s,
      ∀ (U : Cᵒᵖ) (x : ringedSectionLocalizationCarrierOfUniverses R s U),
        e.hom.val.app U ((toSheafify J (ringedLocalizationRingPresheafOfUniverses R s)).app U x) =
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
              (ringedSectionLocalizationPresheafOfUniverses R s)).app U) x := by
  sorry


end CategoryTheory
