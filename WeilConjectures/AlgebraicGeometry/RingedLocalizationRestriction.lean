/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SliceModuleSheafification
public import WeilConjectures.AlgebraicGeometry.RingedLocalizationModels

/-! # Restriction of fraction sheaves and localized complexes

.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
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

/-- Restrict a section by precomposition with the site functor. -/
def restrictedSection (s : (T.obj ⋙ forget CommRingCat).sections) :
    (((F.sheafPushforwardContinuous CommRingCat K L).obj T).obj ⋙
      forget CommRingCat).sections :=
  ⟨fun W ↦ s.val (F.op.obj W), fun a ↦ s.property (F.op.map a)⟩

/-- Restricting a fraction presheaf restricts its coefficient section.

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

end CategoryTheory.LocalizationRHom
