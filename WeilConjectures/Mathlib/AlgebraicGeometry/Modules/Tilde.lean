/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

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
