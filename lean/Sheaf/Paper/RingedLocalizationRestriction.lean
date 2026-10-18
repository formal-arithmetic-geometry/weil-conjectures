/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.RingedLocalizationModels
public import Sheaf.Algebra.Homology.SliceModuleSheafification

/-! # Restriction of fraction sheaves and localized complexes

Source: Stacks Project, Tags 04IX, 08JB and 0996.
(blueprint: lem-weil-pbc-ringed-localization-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.LocalizationRHom

section General

variable {D E : Type u} [SmallCategory D] [SmallCategory E]
  {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  (F : D ⥤ E) [Functor.IsContinuous F K L]
  (T : Sheaf L CommRingCat.{u})

/-- Restrict a section by precomposition with the site functor.
Source: Stacks 04IX (blueprint: lem-weil-pbc-ringed-localization-restriction). -/
def restrictedSection (s : (T.obj ⋙ forget CommRingCat).sections) :
    (((F.sheafPushforwardContinuous CommRingCat K L).obj T).obj ⋙
      forget CommRingCat).sections :=
  ⟨fun W ↦ s.val (F.op.obj W), fun a ↦ s.property (F.op.map a)⟩

/-- Restricting a fraction presheaf restricts its coefficient section.
Source: Stacks 04IX (blueprint: lem-weil-pbc-ringed-localization-restriction).
The comparison is the identity on fractions; both restriction ring maps are the
same universal localization lift. -/
def restrictionPresheafIso (s : (T.obj ⋙ forget CommRingCat).sections) :
    (PresheafOfModules.pushforward₀ F
      ((sheafCompose L (forget₂ CommRingCat.{u} RingCat.{u})).obj T).obj).obj
        (ringedSectionLocalizationPresheaf T s) ≅
    ringedSectionLocalizationPresheaf
      ((F.sheafPushforwardContinuous CommRingCat K L).obj T)
      (restrictedSection F T s) := by
  refine PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) ?_
  intro X Y b
  ext x
  rfl

end General

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

/-- Sheafification commutes with the further slice restriction used here.
Source: Stacks 03CY, 03DH and 04IX
(blueprint: lem-weil-pbc-ringed-localization-restriction). -/
def sheafificationOverMapIso {U V : C} (a : V ⟶ U) :
    PresheafOfModules.sheafification
      (𝟙 ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (R.over U)).obj) ⋙
      SheafOfModules.overMap.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a ≅
    PresheafOfModules.pushforward₀ (Over.map a)
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U)).obj ⋙
      PresheafOfModules.sheafification
        (R₀ := ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (R.over V)).obj)
        (R := (sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over V))
        (𝟙 ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (R.over V)).obj) :=
  SheafOfModules.sliceSheafificationIso (J := J.over V) (K := J.over U) (Over.map a)
    ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))

/-- A fraction presheaf restricted further in a slice has the restricted denominator.
Source: Stacks 04IX and 0996
(blueprint: lem-weil-pbc-ringed-localization-restriction). -/
def coefficientPresheafIso {U V : C} (a : V ⟶ U) (f : R.obj.obj (op U)) :
    (PresheafOfModules.pushforward₀ (Over.map a)
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U)).obj).obj
      (ringedSectionLocalizationPresheaf (R.over U) (ringedSliceSection R U f)) ≅
    ringedSectionLocalizationPresheaf (R.over V)
      (ringedSliceSection R V (R.obj.map a.op f)) := by
  have h : restrictedSection (K := J.over V) (L := J.over U) (Over.map a) (R.over U)
      (ringedSliceSection R U f) = ringedSliceSection R V (R.obj.map a.op f) := by
    apply Subtype.ext
    funext W
    change R.obj.map (W.unop.hom ≫ a).op f =
      R.obj.map W.unop.hom.op (R.obj.map a.op f)
    rw [op_comp, R.obj.map_comp]
    rfl
  exact restrictionPresheafIso (K := J.over V) (L := J.over U) (Over.map a) (R.over U)
    (ringedSliceSection R U f) ≪≫
      eqToIso (congrArg (ringedSectionLocalizationPresheaf (R.over V)) h)

/-- The actual coefficient sheaf comparison, induced by the fraction identity.
Source: Stacks 04IX and 0996
(blueprint: lem-weil-pbc-ringed-localization-restriction). -/
def coefficientSheafIso {U V : C} (a : V ⟶ U) (f : R.obj.obj (op U)) :
    (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a).obj
        (localizationSliceCoefficient R U f) ≅
      localizationSliceCoefficient R V (R.obj.map a.op f) :=
  (sheafificationOverMapIso R a).app
      (ringedSectionLocalizationPresheaf (R.over U) (ringedSliceSection R U f)) ≪≫
    (PresheafOfModules.sheafification
      (R₀ := ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (R.over V)).obj)
        (R := (sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over V))
      (𝟙 ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (R.over V)).obj)).mapIso (coefficientPresheafIso R a f)

end CategoryTheory.LocalizationRHom
