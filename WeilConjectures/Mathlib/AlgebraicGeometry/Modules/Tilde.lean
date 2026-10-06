/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Sections of quasi-coherent modules over basic opens of an affine open

Let `M` be a quasi-coherent `𝒪_X`-module, `W` an affine open subscheme of `X` and `f ∈ Γ(X, W)`.
Then the restriction `Γ(M, W) → Γ(M, D(f))` is a localization at the powers of `f`. We record the
two halves of this statement elementwise: every section over `D(f)` becomes, after multiplication
by a power of `f`, the restriction of a section over `W`; and a section over `W` vanishing on `D(f)`
is killed by a power of `f`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_map_eq_pow_smul_of_isAffineOpen`
- `AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_zero_of_isAffineOpen`
- `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpen`: the two halves together.
- `AlgebraicGeometry.Scheme.Modules.flat_sections_of_isInvertible`: the sections of an invertible
  module over an affine open are flat.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The image of any open of `Spec Γ(X, W)` under `fromSpec` lies in the affine open `W`. -/
lemma IsAffineOpen.fromSpec_image_le {W : X.Opens} (hW : IsAffineOpen W)
    (U : (Spec Γ(X, W)).Opens) : hW.fromSpec ''ᵁ U ≤ W :=
  (hW.fromSpec.image_le_opensRange U).trans hW.opensRange_fromSpec.le

set_option backward.isDefEq.respectTransparency false in
/-- Transporting `r ∈ Γ(X, W)` to `Γ(Spec Γ(X, W), U)` and then back along `fromSpec.appIso U`
is the restriction of `r` to `fromSpec ''ᵁ U`. -/
lemma IsAffineOpen.ΓSpecIso_inv_map_appIso_inv {W : X.Opens} (hW : IsAffineOpen W)
    (U : (Spec Γ(X, W)).Opens) :
    (Scheme.ΓSpecIso Γ(X, W)).inv ≫ (Spec Γ(X, W)).presheaf.map U.leTop.op ≫
      (hW.fromSpec.appIso U).inv =
      X.presheaf.map (homOfLE (hW.fromSpec_image_le U)).op := by
  rw [← cancel_mono (hW.fromSpec.appIso U).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Scheme.Hom.appIso_hom, hW.fromSpec.naturality_assoc, hW.fromSpec_app_self]
  simp only [Category.assoc, ← Functor.map_comp]
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Under `restrictAppIso` along `fromSpec`, the `Γ(X, W)`-action on sections of the restricted
module over `U` corresponds to the action of the restriction to `fromSpec ''ᵁ U`. -/
lemma restrictAppIso_fromSpec_smul (M : X.Modules) {W : X.Opens} (hW : IsAffineOpen W)
    {U : (Spec Γ(X, W)).Opens} (r : Γ(X, W)) (x : Γ(M.restrict hW.fromSpec, U)) :
    dsimp% (M.restrictAppIso hW.fromSpec U).hom (r • x) =
      X.presheaf.map (homOfLE (hW.fromSpec_image_le U)).op r •
        (M.restrictAppIso hW.fromSpec U).hom x := by
  rw [smul_Spec_def, smul_restrictAppIso_hom_apply, ← hW.ΓSpecIso_inv_map_appIso_inv U]
  rfl

variable (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]

/-- The restriction of a quasi-coherent module along `fromSpec` of an affine open is
localizing. -/
lemma isLocalizing_restrict_fromSpec {W : X.Opens} (hW : IsAffineOpen W) :
    IsLocalizing (modulesSpecToSheaf.obj (M.restrict hW.fromSpec)) :=
  (isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Let `M` be quasi-coherent, `W` an affine open and `f ∈ Γ(X, W)`. Every section of `M` over
`D(f)` becomes the restriction of a section over `W` after multiplication by a power of `f`. -/
lemma exists_map_eq_pow_smul_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W))
    (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, W)), M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s := by
  have hW' : W ≤ hW.fromSpec ''ᵁ ⊤ := by
    rw [Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]
  have hD : hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen f ≤ X.basicOpen f :=
    (hW.fromSpec_image_basicOpen f).le
  have hD' : X.basicOpen f ≤ hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen f :=
    (hW.fromSpec_image_basicOpen f).ge
  have := isLocalizing_restrict_fromSpec M hW f
  obtain ⟨⟨t', _, hm⟩, h⟩ := IsLocalizedModule.surj (.powers f)
    ((modulesSpecToSheaf.obj (M.restrict hW.fromSpec)).obj.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom
    ((M.restrictAppIso hW.fromSpec _).inv (M.presheaf.map (homOfLE hD).op s))
  obtain ⟨n, rfl⟩ := hm
  refine ⟨n, M.presheaf.map (homOfLE hW').op ((M.restrictAppIso hW.fromSpec ⊤).hom t'), ?_⟩
  replace h : f ^ n • (M.restrictAppIso hW.fromSpec _).inv (M.presheaf.map (homOfLE hD).op s) =
      (M.restrict hW.fromSpec).presheaf.map
        (homOfLE (le_top : (PrimeSpectrum.basicOpen f : (Spec Γ(X, W)).Opens) ≤ ⊤)).op t' := h
  have h1 := congr(M.presheaf.map (homOfLE hD').op
    ((M.restrictAppIso hW.fromSpec (PrimeSpectrum.basicOpen f)).hom $h))
  rw [restrictAppIso_fromSpec_smul, map_smul, Iso.inv_hom_id_apply,
    map_restrictAppIso_hom_apply] at h1
  have e1 : (homOfLE hD).op ≫ (homOfLE hD').op = 𝟙 _ := Subsingleton.elim _ _
  have e2 : (homOfLE (hW.fromSpec_image_le (PrimeSpectrum.basicOpen f))).op ≫
      (homOfLE hD').op = (homOfLE (X.basicOpen_le f)).op := Subsingleton.elim _ _
  have e3 : (homOfLE (hW.fromSpec.image_mono (le_top :
      (PrimeSpectrum.basicOpen f : (Spec Γ(X, W)).Opens) ≤ ⊤))).op ≫ (homOfLE hD').op =
      (homOfLE hW').op ≫ (homOfLE (X.basicOpen_le f)).op := Subsingleton.elim _ _
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply, e1, e2, e3,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, map_pow] at h1
  rw [← Functor.map_comp_apply]
  exact h1.symm

set_option backward.isDefEq.respectTransparency false in
/-- Let `M` be quasi-coherent, `W` an affine open and `f ∈ Γ(X, W)`. A section of `M` over `W`
whose restriction to `D(f)` vanishes is killed by a power of `f`. -/
lemma exists_pow_smul_eq_zero_of_isAffineOpen {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W))
    (t : Γ(M, W)) (ht : M.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  have hW' : W ≤ hW.fromSpec ''ᵁ ⊤ := by
    rw [Hom.image_top_eq_opensRange, hW.opensRange_fromSpec]
  have hD : hW.fromSpec ''ᵁ PrimeSpectrum.basicOpen f ≤ X.basicOpen f :=
    (hW.fromSpec_image_basicOpen f).le
  let t' := (M.restrictAppIso hW.fromSpec ⊤).inv
    (M.presheaf.map (homOfLE (hW.fromSpec_image_le ⊤)).op t)
  have h0 : (M.restrict hW.fromSpec).presheaf.map
      (homOfLE (le_top : (PrimeSpectrum.basicOpen f : (Spec Γ(X, W)).Opens) ≤ ⊤)).op t' = 0 := by
    have := congr((M.restrictAppIso hW.fromSpec _).inv
      (M.presheaf.map (homOfLE hD).op $ht))
    rw [map_zero, map_zero, ← Functor.map_comp_apply] at this
    dsimp only [t']
    rw [restrictAppIso_inv_map_apply, ← Functor.map_comp_apply]
    convert this using 4
    exact congrArg _ (Subsingleton.elim _ _)
  have := isLocalizing_restrict_fromSpec M hW f
  have hz := (IsLocalizedModule.eq_zero_iff (.powers f)
    ((modulesSpecToSheaf.obj (M.restrict hW.fromSpec)).obj.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom (m := t')).mp
  obtain ⟨⟨_, hm⟩, hn⟩ := hz h0
  obtain ⟨n, rfl⟩ := hm
  refine ⟨n, ?_⟩
  rw [Submonoid.smul_def] at hn
  have := congr(M.presheaf.map (homOfLE hW').op ((M.restrictAppIso hW.fromSpec ⊤).hom $hn))
  rw [restrictAppIso_fromSpec_smul, map_zero, map_zero, map_smul, Iso.inv_hom_id_apply] at this
  have hid : (homOfLE (hW.fromSpec_image_le ⊤)).op ≫ (homOfLE hW').op =
      𝟙 (Opposite.op W) := Subsingleton.elim _ _
  simp only [← Functor.map_comp_apply, hid, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply] at this
  exact this

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

open Opposite

variable {X : Scheme.{u}}

/-- Let `M` be a quasi-coherent `𝒪_X`-module, `U` an affine open and `g ∈ Γ(X, U)`. Then the
restriction map `Γ(M, U) → Γ(M, D(g))` is a localization at the powers of `g`, the
`Γ(X, U)`-module structure on `Γ(M, D(g))` being restriction of scalars along
`Γ(X, U) → Γ(X, D(g))`. -/
lemma isLocalizedModule_basicOpen (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) :
    letI : Module Γ(X, U) Γ(M, X.basicOpen g) :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
    IsLocalizedModule.Away g
      { toFun := M.presheaf.map (homOfLE (X.basicOpen_le g)).op
        map_add' := map_add _
        map_smul' := map_smul M _ : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen g) } := by
  let : Module Γ(X, U) Γ(M, X.basicOpen g) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen g))
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun y ↦ ?_, fun {x₁ x₂} h ↦ ?_⟩
  · obtain ⟨n, rfl⟩ := hx
    have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen g) (g ^ n)) := by
      rw [map_pow]
      exact (X.toRingedSpace.isUnit_res_basicOpen g).pow n
    rw [Module.End.isUnit_iff]
    refine ⟨fun a b hab ↦ ?_, fun m ↦ ⟨hu.unit⁻¹ • m, ?_⟩⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply] at hab
      exact hu.smul_left_cancel.mp hab
    · rw [Module.algebraMap_end_apply]
      exact smul_inv_smul hu.unit m
  · obtain ⟨n, t, ht⟩ := exists_map_eq_pow_smul_of_isAffineOpen M hU g y
    rw [← map_pow] at ht
    exact ⟨⟨t, ⟨g ^ n, n, rfl⟩⟩, ht.symm⟩
  · obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen M hU g (x₁ - x₂)
      ((map_sub _ x₁ x₂).trans (sub_eq_zero.mpr h))
    exact ⟨⟨g ^ n, n, rfl⟩, sub_eq_zero.mp ((smul_sub _ _ _).symm.trans hn)⟩

/-- The sections of an invertible `𝒪_X`-module over an affine open `U` form a flat
`Γ(X, U)`-module. -/
lemma flat_sections_of_isInvertible (M : X.Modules) [M.IsInvertible] {U : X.Opens}
    (hU : IsAffineOpen U) : Module.Flat Γ(X, U) Γ(M, U) := by
  let s : Set Γ(X, U) := {g | ∃ Y : X.Opens, X.basicOpen g ≤ Y ∧
    Nonempty (M.over Y ≅ SheafOfModules.unit (X.ringCatSheaf.over Y))}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨Y, hxY, ⟨e⟩⟩ := exists_mem_over_iso_unit M x
    obtain ⟨g, hgY, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxY⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, Y, hgY, ⟨e⟩⟩, hxg⟩
  let _ (r : s) : Module Γ(X, U) Γ(M, X.basicOpen r.1) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r.1))
  have _ (r : s) := isLocalizedModule_basicOpen M hU r.1
  refine Module.flat_of_isLocalized_span Γ(X, U) Γ(M, U) s hs
    (fun r ↦ Γ(M, X.basicOpen r.1)) (fun r ↦
      { toFun := M.presheaf.map (homOfLE (X.basicOpen_le r.1)).op
        map_add' := map_add _
        map_smul' := map_smul M _ }) fun r ↦ ?_
  obtain ⟨Y, hY, ⟨e⟩⟩ := r.2
  have := Module.Flat.of_linearEquiv (sectionsLinearEquivOfOverIsoUnit e hY)
  have := hU.isLocalization_basicOpen r.1
  have := IsLocalization.flat Γ(X, X.basicOpen r.1) (.powers r.1)
  have : IsScalarTower Γ(X, U) Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(X, U) Γ(X, X.basicOpen r.1) Γ(M, X.basicOpen r.1)

end AlgebraicGeometry.Scheme.Modules
