/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution

/-!
# The Čech resolution over an arbitrary base

Let `f : X ⟶ S` be separated and `U` a finite open cover of `X` such that every inclusion
`U i ⟶ X` followed by `f` is an affine morphism. Then all finite intersections of the `U i` are
affine over `S`, the terms of the sheafified Čech complex `Č(U, ℱ)` of a quasi-coherent
`𝒪_X`-module are `f_*`-acyclic, and `R^q f_* ℱ` is the `q`-th cohomology sheaf of `f_* Č(U, ℱ)`
(`AlgebraicGeometry.Scheme.Modules.higherDirectImageIsoCechResolutionOfIsAffineHom`). This
generalises `AlgebraicGeometry.Scheme.Modules.higherDirectImageIsoCechResolution`, where `S` is
affine and the `U i` are affine opens.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)

lemma isAffineOpen_ι_preimage_iff {V W : X.Opens} :
    IsAffineOpen (V.ι ⁻¹ᵁ W) ↔ IsAffineOpen (V ⊓ W) := by
  rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, ι_image_preimage]

/-- The composite `V ⟶ X ⟶ S` is affine if and only if `V ∩ f⁻¹ Z` is affine for every affine
open `Z` of `S`. -/
lemma isAffineHom_ι_comp_iff {V : X.Opens} :
    IsAffineHom (V.ι ≫ f) ↔ ∀ Z : S.Opens, IsAffineOpen Z → IsAffineOpen (V ⊓ f ⁻¹ᵁ Z) :=
  ⟨fun h Z hZ ↦ isAffineOpen_ι_preimage_iff.1 (h.isAffine_preimage Z hZ),
    fun h ↦ ⟨fun Z hZ ↦ isAffineOpen_ι_preimage_iff.2 (h Z hZ)⟩⟩

/-- For `f` separated, the intersection of two opens which are affine over `S` is affine over
`S`. -/
lemma isAffineHom_inf_ι_comp [IsSeparated f] {V₁ V₂ : X.Opens} (h₁ : IsAffineHom (V₁.ι ≫ f))
    (h₂ : IsAffineHom (V₂.ι ≫ f)) : IsAffineHom ((V₁ ⊓ V₂).ι ≫ f) := by
  rw [isAffineHom_ι_comp_iff] at h₁ h₂ ⊢
  intro Z hZ
  have H := isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal f)) Z hZ
  have := H (V₁ ⊓ f ⁻¹ᵁ Z) inf_le_right (V₂ ⊓ f ⁻¹ᵁ Z) inf_le_right (h₁ Z hZ) (h₂ Z hZ)
  rwa [inf_inf_distrib_right]

/-- For `f` separated, finite intersections of opens which are affine over `S` are affine over
`S`. -/
lemma isAffineHom_iInf_ι_comp [IsSeparated f] {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineHom ((U i).ι ≫ f)) {k : ℕ} (y : Fin (k + 1) → ι) :
    IsAffineHom ((⨅ l, U (y l)).ι ≫ f) := by
  have key : ∀ (s : Finset (Fin (k + 1))), s.Nonempty →
      IsAffineHom ((⨅ l ∈ s, U (y l)).ι ≫ f) := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a =>
      rw [show ⨅ l ∈ ({a} : Finset (Fin (k + 1))), U (y l) = U (y a) by simp]
      exact hU (y a)
    | cons a s ha hs ih =>
      rw [Finset.cons_eq_insert, Finset.iInf_insert]
      exact isAffineHom_inf_ι_comp f (hU _) ih
  have h := key Finset.univ Finset.univ_nonempty
  rwa [show ⨅ l ∈ (Finset.univ : Finset (Fin (k + 1))), U (y l) = ⨅ l, U (y l) by simp] at h

/-- For an open `V` of a scheme `X` separated over `S` such that `V ⟶ S` is affine, and a
quasi-coherent `ℱ`, the module `j_* (ℱ|_V)` is `f_*`-acyclic: the inclusion `j : V ⟶ X` and the
composite `V ⟶ S` are affine morphisms. -/
theorem rightAcyclic_extendRestrict_of_isAffineHom [IsSeparated f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) [ℱ.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineHom (V.ι ≫ f)) :
    (pushforward f).rightAcyclic ((extendRestrictFunctor V).obj ℱ) := by
  have := isGrothendieckAbelian V
  have : IsAffineHom V.ι := IsAffineHom.of_comp V.ι f
  exact rightAcyclic_pushforward_obj_of_isZero V.ι f _
    (fun q ↦ isZero_higherDirectImage_of_isAffineHom _ _ q.succ_pos)
    (fun q ↦ isZero_higherDirectImage_of_isAffineHom _ _ q.succ_pos)

variable {ι : Type u} (U : ι → X.Opens)

/-- **The terms of the Čech complex are `f_*`-acyclic**, for `f` separated, a finite family of
opens `U i` which are affine over `S`, and a quasi-coherent module. -/
theorem rightAcyclic_cechResolution_X_of_isAffineHom [IsSeparated f] [Finite ι]
    [HasInjectiveResolutions X.Modules] (hU : ∀ i, IsAffineHom ((U i).ι ≫ f)) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] (k : ℕ) : (pushforward f).rightAcyclic ((cechResolution U ℱ).X k) := by
  have : (pushforward f).rightAcyclic.IsClosedUnderFiniteProducts := .mk'
  change (pushforward f).rightAcyclic
    (∏ᶜ fun y : Fin (k + 1) → ι ↦ (cechPresheaf ℱ).obj (op (∏ᶜ fun l ↦ U (y l))))
  refine ObjectProperty.prop_product _ fun y ↦ ?_
  exact rightAcyclic_extendRestrict_of_isAffineHom f ℱ
    ((piObj_eq_iInf U y).symm ▸ isAffineHom_iInf_ι_comp f U hU y)

/-- **The Čech resolution computes the higher direct images over an arbitrary base.** Let
`f : X ⟶ S` be separated, `U` a finite open cover of `X` such that every `U i ⟶ S` is an affine
morphism, and `ℱ` a quasi-coherent `𝒪_X`-module. Then `R^q f_* ℱ` is the `q`-th cohomology sheaf
of the complex `f_* Č(U, ℱ)` of `𝒪_S`-modules.

(blueprint: `lem-pc-cech-resolution`) -/
noncomputable def higherDirectImageIsoCechResolutionOfIsAffineHom [IsSeparated f] [Finite ι]
    [HasInjectiveResolutions X.Modules] (hU : ∀ i, IsAffineHom ((U i).ι ≫ f))
    (hU' : ⨆ i, U i = ⊤) (ℱ : X.Modules) [ℱ.IsQuasicoherent] (q : ℕ) :
    (higherDirectImage f q).obj ℱ ≅
      (((pushforward f).mapHomologicalComplex _).obj (cechResolution U ℱ)).homology q :=
  have := quasiIso_cechResolutionι U ℱ hU'
  (pushforward f).rightDerivedObjIsoOfResolution (cechResolutionι U ℱ)
    (rightAcyclic_cechResolution_X_of_isAffineHom f U hU ℱ) q

end AlgebraicGeometry.Scheme.Modules
