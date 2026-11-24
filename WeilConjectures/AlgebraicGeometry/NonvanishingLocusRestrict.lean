/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample

/-! # Nonvanishing loci under restriction along an open immersion

## References

* Stacks Project, Properties, Lemma 01PV, and Modules, Lemma 01CY.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

private theorem inverse_stalk_germ (x : X) (U : X.Opens) (hx : x ∈ U)
    (r : X.presheaf.obj (op U)) :
    (asIso (f.stalkMap x)).inv (X.presheaf.germ U x hx r) =
      Y.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ ((f.appIso U).inv r) := by
  have h : (f.appIso U).inv ≫ Y.presheaf.germ (f ''ᵁ U) (f x) ⟨x, hx, rfl⟩ ≫
      f.stalkMap x = X.presheaf.germ U x hx := by
    rw [f.germ_stalkMap, f.appIso_inv_app_assoc]
    exact X.presheaf.germ_res (eqToHom (f.preimage_image_eq U)) x (by simpa using hx)
  apply (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).injective
  change (X.presheaf.germ U x hx ≫ inv (f.stalkMap x) ≫ f.stalkMap x) r =
    ((f.appIso U).inv ≫ Y.presheaf.germ (f ''ᵁ U) (f x) _ ≫ f.stalkMap x) r
  rw [IsIso.inv_hom_id, Category.comp_id, h]

private theorem restrict_stalk_smul (x : X) (M : Y.Modules)
    (r : X.presheaf.stalk x) (m : ↑(TopCat.Presheaf.stalk (M.restrict f).val.presheaf x)) :
    let e : TopCat.Presheaf.stalk (M.restrict f).val.presheaf x ≅
        TopCat.Presheaf.stalk M.val.presheaf (f x) := (restrictStalkNatIso f x).app M
    e.hom (r • m) = (asIso (f.stalkMap x)).inv r • e.hom m := by
  dsimp only
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, b, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq (M.restrict f).val.presheaf m hxU
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV a]
  rw [← PresheafOfModules.germ_smul]
  rw [inverse_stalk_germ]
  have he (c : (M.restrict f).val.presheaf.obj (op V)) :
      ((restrictStalkNatIso f x).app M).hom
          (TopCat.Presheaf.germ (M.restrict f).val.presheaf V x hxV c) =
        TopCat.Presheaf.germ M.val.presheaf (f ''ᵁ V) (f x) ⟨x, hxV, rfl⟩ c :=
    congrArg (fun t ↦ t c) (germ_restrictStalkNatIso_hom_app f x M hxV)
  exact (he _).trans ((PresheafOfModules.germ_smul M.val (f x) (f ''ᵁ V)
    ⟨x, hxV, rfl⟩ ((f.appIso V).inv (X.presheaf.map (homOfLE hVU).op a)) b).trans
      (congrArg (fun z ↦ Y.presheaf.germ (f ''ᵁ V) (f x) ⟨x, hxV, rfl⟩
        ((f.appIso V).inv (X.presheaf.map (homOfLE hVU).op a)) • z) (he b).symm))

private theorem restrict_stalk_membership (x : X) (M : Y.Modules)
    (m : ↑(TopCat.Presheaf.stalk (M.restrict f).val.presheaf x)) :
    let e : TopCat.Presheaf.stalk (M.restrict f).val.presheaf x ≅
        TopCat.Presheaf.stalk M.val.presheaf (f x) := (restrictStalkNatIso f x).app M
    m ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) _) ↔
      e.hom m ∈ (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) •
        (⊤ : Submodule (Y.presheaf.stalk (f x)) _) := by
  dsimp only
  let e : ↑(TopCat.Presheaf.stalk (M.restrict f).val.presheaf x) ≃+
      ↑(TopCat.Presheaf.stalk M.val.presheaf (f x)) :=
    ((restrictStalkNatIso f x).app M).addCommGroupIsoToAddEquiv
  let φ := (asIso (f.stalkMap x)).symm.commRingCatIsoToRingEquiv
  have hsmul (r : X.presheaf.stalk x) (a : ↑(TopCat.Presheaf.stalk
      (M.restrict f).val.presheaf x)) : e (r • a) = φ r • e a :=
    restrict_stalk_smul f x M r a
  have hmem (r : X.presheaf.stalk x) :
      r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
        φ r ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) := by
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MulEquiv.isUnit_map]
  constructor
  · intro hm
    change e m ∈ _
    refine Submodule.smul_induction_on hm ?_ ?_
    · intro r hr a ha
      rw [hsmul]
      exact Submodule.smul_mem_smul ((hmem r).mp hr) (Submodule.mem_top)
    · intro a b ha hb
      exact (map_add e a b) ▸ Submodule.add_mem _ ha hb
  · intro hm
    change e m ∈ _ at hm
    have hinv (r : Y.presheaf.stalk (f x))
        (a : ↑(TopCat.Presheaf.stalk M.val.presheaf (f x))) :
        e.symm (r • a) = φ.symm r • e.symm a := by
      apply e.injective
      rw [e.apply_symm_apply, hsmul, φ.apply_symm_apply, e.apply_symm_apply]
    have h : e.symm (e m) ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) _) := by
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro r hr a ha
        rw [hinv]
        exact Submodule.smul_mem_smul ((hmem (φ.symm r)).mpr (by simpa using hr))
          (Submodule.mem_top)
      · intro a b ha hb
        exact (map_add e.symm a b) ▸ Submodule.add_mem _ ha hb
    simpa only [e.symm_apply_apply] using h

/-- Restriction along an open immersion preserves the nonvanishing locus of a section.
No invertibility or affineness hypothesis is needed for this compatibility
(Stacks, Tags 01PV and 01CY). -/
theorem nonvanishingLocus_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (s : M.val.presheaf.obj (op ⊤)) :
    nonvanishingLocus (M.restrict f)
        ((M.restrictAppIso f ⊤).inv (M.presheaf.map (homOfLE le_top).op s)) =
      f ⁻¹' nonvanishingLocus M s := by
  ext x
  let b : (M.restrict f).val.presheaf.obj (op ⊤) :=
    (M.restrictAppIso f ⊤).inv (M.presheaf.map (homOfLE le_top).op s)
  have h := restrict_stalk_membership f x M
    (TopCat.Presheaf.germ (M.restrict f).val.presheaf ⊤ x trivial b)
  have hg : ((restrictStalkNatIso f x).app M).hom
      (TopCat.Presheaf.germ (M.restrict f).val.presheaf ⊤ x trivial b) =
      TopCat.Presheaf.germ M.val.presheaf ⊤ (f x) trivial s := by
    exact (congrArg (fun t ↦ t b)
      (germ_restrictStalkNatIso_hom_app f x M (U := ⊤) trivial)).trans
        (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE (le_top : f ''ᵁ ⊤ ≤ ⊤)) (f x)
          (show f x ∈ f ''ᵁ ⊤ from ⟨x, trivial, rfl⟩) s)
  change _ ∉ _ ↔ _ ∉ _
  apply not_congr
  exact h.trans (congrArg (fun a ↦ a ∈
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) •
      (⊤ : Submodule (Y.presheaf.stalk (f x))
        ↑(TopCat.Presheaf.stalk M.val.presheaf (f x)))) hg).to_iff

end AlgebraicGeometry.Scheme.Modules
