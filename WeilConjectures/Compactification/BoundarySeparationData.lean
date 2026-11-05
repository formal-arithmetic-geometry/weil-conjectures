/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.BoundaryPreparation
public import WeilConjectures.Compactification.IdealSheafPower

/-!
# Separation data for boundary pieces

This file records, as standalone declarations, the auxiliary nodes of the blueprint
subsection "Separating boundary closures" (`sk-lem-nagata-sketch-boundary`) whose content is
used inline in `AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures`.

## Main definitions

- `AlgebraicGeometry.Scheme.IdealSheafData.separationPreparationCenter`: the center of the
  Tag 080P preparation (blueprint: `lemma-nagata-separate-closed-data-exists`);
- `AlgebraicGeometry.Scheme.IdealSheafData.separationPreparationBlowupSubscheme`: the
  `U_Z`-admissible blow-up `Bl_C(Z) → Z` of that preparation;
- `AlgebraicGeometry.separationPreparationBlowup`: the blow-up of `X` along the composite
  center `C ↪ Z ↪ X` (blueprint: `def-nagata-separate-closed-subschemes`, second paragraph);
- `AlgebraicGeometry.Scheme.IdealSheafData.constructibleClosedExtension`: the ideal
  `Ext_{X,U}(J_U(T))` of a constructible closed subset `T ⊆ U`;
- `AlgebraicGeometry.constructibleSeparationBlowup`: the constructible-boundary separation
  blow-up `CSepBl_U(T₁, T₂)` (blueprint: `def-nagata-separate-constructible-closed`).

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_eq_bot_of_support_eq_top`: a
  finite-type nil ideal sheaf on a quasi-compact scheme is nilpotent (blueprint:
  `lemma-nagata-finite-type-nil-ideal-nilpotent`);
- `AlgebraicGeometry.range_strictTransformMap_eq_closure`: the underlying set of the strict
  transform of a closed subscheme is the closure of the inverse image of its part over `U`;
- `AlgebraicGeometry.exists_separationPreparation`: the Tag 080P preparation (blueprint:
  `lemma-nagata-separate-closed-data-exists`);
- `AlgebraicGeometry.disjoint_closure_preimage_constructibleSeparationBlowup`: the closures of
  the inverse images of `T₁`, `T₂` in `CSepBl_U(T₁, T₂)` are disjoint (blueprint:
  `lemma-nagata-separate-constructible-closed`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ### Finite-type nil ideals -/

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}

end Scheme.IdealSheafData

/-! ### The underlying set of a strict transform -/

section StrictTransformRange

variable {X Y X' : Scheme.{u}} (f : Y ⟶ X) (π : X' ⟶ X) (U : X.Opens)

end StrictTransformRange

/-! ### The Tag 080P preparation for separating two closed boundaries -/

section SeparationPreparation

variable {X : Scheme.{u}} {U : X.Opens}

end SeparationPreparation

/-! ### The constructible-boundary separation blow-up as a construction -/

section ConstructibleSeparation

variable {X : Scheme.{u}} {U : X.Opens}

/-- The finite-type ideal `Ext_{X,U}(J_U(T))` on `X` attached to a constructible closed subset
`T` of a quasi-compact open `U` of a qcqs scheme (the ideals `𝓘ᵢ` of blueprint
`def-nagata-separate-constructible-closed`): `J_U(T)` is the chosen finite-type ideal on `U`
with vanishing set `T` (`Scheme.exists_finiteType_ideal_coe_support_eq_compl`, Stacks Tag
01PH), and `Ext_{X,U}` is the chosen finite-type extension to `X`
(`Scheme.IdealSheafData.exists_finiteType_comap_eq`, Stacks Tag 01PF). -/
def Scheme.IdealSheafData.constructibleClosedExtension [CompactSpace X] [QuasiSeparatedSpace X]
    (hU : IsCompact (U : Set X)) {T : Set U.toScheme} (hT : IsClosed T) (hc : IsCompact Tᶜ) :
    X.IdealSheafData :=
  haveI : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  haveI : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  (exists_finiteType_comap_eq U hU
    (U.toScheme.exists_finiteType_ideal_coe_support_eq_compl ⟨Tᶜ, hT.isOpen_compl⟩ hc).choose
    (U.toScheme.exists_finiteType_ideal_coe_support_eq_compl ⟨Tᶜ, hT.isOpen_compl⟩
      hc).choose_spec.1).choose

/-- The ideal `Ext_{X,U}(J_U(T))` is of finite type and cuts out `T` on `U`. -/
lemma Scheme.IdealSheafData.constructibleClosedExtension_spec [CompactSpace X]
    [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X)) {T : Set U.toScheme}
    (hT : IsClosed T) (hc : IsCompact Tᶜ) :
    (constructibleClosedExtension hU hT hc).ofFiniteType ∧
      U.ι ⁻¹' ((constructibleClosedExtension hU hT hc).support : Set X) = T := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme := quasiSeparatedSpace_of_quasiSeparated U.ι
  have hJ := (U.toScheme.exists_finiteType_ideal_coe_support_eq_compl ⟨Tᶜ, hT.isOpen_compl⟩
    hc).choose_spec
  have hI := (exists_finiteType_comap_eq U hU _ hJ.1).choose_spec
  refine ⟨hI.1, ?_⟩
  rw [← coe_support_comap]
  unfold constructibleClosedExtension
  rw [hI.2, hJ.2]
  exact compl_compl T

/-- The common support of the two extended ideals misses `U`. -/
lemma Scheme.IdealSheafData.disjoint_support_constructibleClosedExtension [CompactSpace X]
    [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X)) {T₁ T₂ : Set U.toScheme}
    (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂) (hc₁ : IsCompact T₁ᶜ) (hc₂ : IsCompact T₂ᶜ)
    (hdisj : Disjoint T₁ T₂) :
    Disjoint (U : Set X) (((constructibleClosedExtension hU hT₁ hc₁).support : Set X) ∩
      ((constructibleClosedExtension hU hT₂ hc₂).support : Set X)) := by
  have hpre₁ := (constructibleClosedExtension_spec hU hT₁ hc₁).2
  have hpre₂ := (constructibleClosedExtension_spec hU hT₂ hc₂).2
  rw [Set.disjoint_left]
  rintro x hxU ⟨hx1, hx2⟩
  obtain ⟨t, rfl⟩ : x ∈ Set.range U.ι := by
    rwa [Scheme.Opens.range_ι]
  exact Set.disjoint_left.mp hdisj (hpre₁ ▸ Set.mem_preimage.mpr hx1)
    (hpre₂ ▸ Set.mem_preimage.mpr hx2)

/-- **The constructible-boundary separation blow-up** `CSepBl_U(T₁, T₂)` (blueprint:
`def-nagata-separate-constructible-closed`): the closed-boundary separation blow-up
`SepBl_U(Z₁, Z₂)` (`separationBlowup`) of the closed subschemes `Zᵢ = V(𝓘ᵢ)` cut out by the
extended ideals `𝓘ᵢ = Ext_{X,U}(J_U(Tᵢ))`
(`Scheme.IdealSheafData.constructibleClosedExtension`). -/
def constructibleSeparationBlowup [CompactSpace X] [QuasiSeparatedSpace X]
    (hU : IsCompact (U : Set X)) {T₁ T₂ : Set U.toScheme} (hT₁ : IsClosed T₁)
    (hT₂ : IsClosed T₂) (hc₁ : IsCompact T₁ᶜ) (hc₂ : IsCompact T₂ᶜ) (hdisj : Disjoint T₁ T₂) :
    IsAdmissible X U :=
  separationBlowup (Scheme.IdealSheafData.constructibleClosedExtension hU hT₁ hc₁)
    (Scheme.IdealSheafData.constructibleClosedExtension hU hT₂ hc₂)
    (Scheme.IdealSheafData.constructibleClosedExtension_spec hU hT₁ hc₁).1
    (Scheme.IdealSheafData.constructibleClosedExtension_spec hU hT₂ hc₂).1
    (Scheme.IdealSheafData.disjoint_support_constructibleClosedExtension hU hT₁ hT₂ hc₁ hc₂
      hdisj)

/-- **Properties of constructible-boundary separation**, for the explicit construction
(blueprint: `lemma-nagata-separate-constructible-closed`): the closures of the inverse
images of `T₁` and `T₂` in `CSepBl_U(T₁, T₂)` are disjoint. The closure of the inverse image
of `Tᵢ` lies in the strict transform of `V(𝓘ᵢ)`, and these strict transforms are disjoint
(`disjoint_range_strictTransformMap_sup`). -/
theorem disjoint_closure_preimage_constructibleSeparationBlowup [CompactSpace X]
    [QuasiSeparatedSpace X] (hU : IsCompact (U : Set X)) {T₁ T₂ : Set U.toScheme}
    (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂) (hc₁ : IsCompact T₁ᶜ) (hc₂ : IsCompact T₂ᶜ)
    (hdisj : Disjoint T₁ T₂) :
    Disjoint
      (closure ((constructibleSeparationBlowup hU hT₁ hT₂ hc₁ hc₂ hdisj).I.blowupMap ⁻¹'
        (U.ι '' T₁)))
      (closure ((constructibleSeparationBlowup hU hT₁ hT₂ hc₁ hc₂ hdisj).I.blowupMap ⁻¹'
        (U.ι '' T₂))) := by
  have h₁ := Scheme.IdealSheafData.constructibleClosedExtension_spec hU hT₁ hc₁
  have h₂ := Scheme.IdealSheafData.constructibleClosedExtension_spec hU hT₂ hc₂
  exact (disjoint_range_strictTransformMap_sup _ _ h₁.1 h₂.1).mono
    ((constructibleSeparationBlowup hU hT₁ hT₂ hc₁ hc₂
      hdisj).closure_preimage_subset_range_strictTransformMap _ h₁.2.symm.le)
    ((constructibleSeparationBlowup hU hT₁ hT₂ hc₁ hc₂
      hdisj).closure_preimage_subset_range_strictTransformMap _ h₂.2.symm.le)

end ConstructibleSeparation

end AlgebraicGeometry
