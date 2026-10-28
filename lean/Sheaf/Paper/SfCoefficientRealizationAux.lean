/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-! Private linear lifting calculations for the sectionwise realization comparison.
Source: Stacks Tags 00YV and 03DA
(blueprint: lem-sf-realization-restriction-linear-lift). -/

@[expose] public section
set_option autoImplicit false
set_option linter.privateModule false
universe u
open CategoryTheory CategoryTheory.Limits

-- Lift the scalar and the section to a common cover to compare the two actions.
private theorem sheafify_restrict_smul
    {D : Type (u + 1)} [Category.{u} D] {J : GrothendieckTopology D}
    {R₀ S₀ : Dᵒᵖ ⥤ RingCat.{u + 1}} {R S : Sheaf J RingCat.{u + 1}}
    (α : R₀ ⟶ R.obj) (β : S₀ ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    (γ : R₀ ⟶ S₀) (δ : R ⟶ S) (h : α ≫ δ.hom = γ ≫ β)
    (M : PresheafOfModules.{u + 1} R₀) (N : PresheafOfModules.{u + 1} S₀)
    (F G : Sheaf J AddCommGrpCat.{u + 1}) (η : M.presheaf ⟶ F.obj)
    (ζ : N.presheaf ⟶ G.obj)
    [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]
    [Presheaf.IsLocallyInjective J ζ] [Presheaf.IsLocallySurjective J ζ]
    (τ : M.presheaf ⟶ N.presheaf) (f : F ⟶ G)
    (hτ : ∀ (U : Dᵒᵖ) (r : R₀.obj U) (x : M.obj U),
      τ.app U (r • x) = @SMul.smul _ (N.obj U) inferInstance (γ.app U r) (τ.app U x))
    (hf : η ≫ f.hom = τ ≫ ζ) (U : Dᵒᵖ) (r : R.obj.obj U) (x : F.obj.obj U) :
    f.hom.app U (PresheafOfModules.Sheafify.smul α η r x) =
      PresheafOfModules.Sheafify.smul β ζ (δ.hom.app U r) (f.hom.app U x) := by
  have hf' (V : Dᵒᵖ) (y : M.obj V) :
      f.hom.app V (η.app V y) = ζ.app V (τ.app V y) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hf V) y
  apply G.isSeparated _ _ (J.intersection_covering
    (Presheaf.imageSieve_mem J α r) (Presheaf.imageSieve_mem J η x))
  rintro V i ⟨⟨r₀, hr₀⟩, ⟨x₀, hx₀⟩⟩
  rw [← NatTrans.naturality_apply f.hom i.op,
    PresheafOfModules.Sheafify.map_smul_eq α η _ _ i.op r₀ hr₀ x₀ hx₀, hf']
  rw [PresheafOfModules.Sheafify.map_smul_eq β ζ _ _ i.op
    (γ.app _ r₀) (by
      have hh := ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op V)) r₀
      change δ.hom.app _ (α.app _ r₀) = β.app _ (γ.app _ r₀) at hh
      rw [← hh, hr₀]
      exact NatTrans.naturality_apply δ.hom i.op r) (τ.app _ x₀) (by
      rw [← hf', hx₀]
      exact NatTrans.naturality_apply f.hom i.op x)]
  exact congrArg (ζ.app _) (hτ _ r₀ x₀)

private noncomputable def lift_module_hom
    {D : Type (u + 1)} [Category.{u} D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u + 1}}
    {E : Type*} [Category* E] (F G : E ⥤ SheafOfModules.{u + 1} R)
    (e : F ⋙ SheafOfModules.toSheaf R ≅ G ⋙ SheafOfModules.toSheaf R)
    (he : ∀ (M : E) (U : Dᵒᵖ) (r : R.obj.obj U) (x : (F.obj M).val.obj U),
      (e.hom.app M).hom.app U (r • x) =
        @SMul.smul _ ((G.obj M).val.obj U) inferInstance r
          ((e.hom.app M).hom.app U x)) : F ⟶ G :=
  { app M := ⟨PresheafOfModules.homMk (e.hom.app M).hom (he M)⟩
    naturality := by
      intro M N f
      apply (SheafOfModules.toSheaf R).map_injective
      exact e.hom.naturality f }

private theorem lift_module_hom_app
    {D : Type (u + 1)} [Category.{u} D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u + 1}}
    {E : Type*} [Category* E] (F G : E ⥤ SheafOfModules.{u + 1} R)
    (e : F ⋙ SheafOfModules.toSheaf R ≅ G ⋙ SheafOfModules.toSheaf R)
    (he : ∀ (M : E) (U : Dᵒᵖ) (r : R.obj.obj U) (x : (F.obj M).val.obj U),
      (e.hom.app M).hom.app U (r • x) =
        @SMul.smul _ ((G.obj M).val.obj U) inferInstance r
          ((e.hom.app M).hom.app U x))
    (M : E) :
    (SheafOfModules.toSheaf R).map ((lift_module_hom F G e he).app M) = e.hom.app M := by
  rfl

attribute [local irreducible] lift_module_hom

private theorem lift_module_iso
    {D : Type (u + 1)} [Category.{u} D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u + 1}}
    {E : Type*} [Category* E] (F G : E ⥤ SheafOfModules.{u + 1} R)
    (e : F ⋙ SheafOfModules.toSheaf R ≅ G ⋙ SheafOfModules.toSheaf R)
    (he : ∀ (M : E) (U : Dᵒᵖ) (r : R.obj.obj U) (x : (F.obj M).val.obj U),
      (e.hom.app M).hom.app U (r • x) =
        @SMul.smul _ ((G.obj M).val.obj U) inferInstance r
          ((e.hom.app M).hom.app U x)) :
    ∃! i : F ≅ G, ∀ (M : E) (U : Dᵒᵖ) (x : (F.obj M).val.obj U),
      (i.hom.app M).val.app U x = (e.hom.app M).hom.app U x := by
  let η := lift_module_hom F G e he
  have hη (M : E) : (SheafOfModules.toSheaf R).map (η.app M) = e.hom.app M :=
    lift_module_hom_app F G e he M
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    have : IsIso ((SheafOfModules.toSheaf R).map (η.app M)) := by
      rw [hη]
      infer_instance
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)
  refine ⟨asIso η, ?_, ?_⟩
  · intro M U x
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun k ↦ k.hom) (hη M)) U) x
  · intro i hi
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (SheafOfModules.toSheaf R).map_injective
    change (SheafOfModules.toSheaf R).map (i.hom.app M) =
      (SheafOfModules.toSheaf R).map (η.app M)
    rw [hη]
    ext U x
    exact hi M U x

private noncomputable abbrev moduleRealization
    {D : Type (u + 1)} [Category.{u} D] (J : GrothendieckTopology D)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (Λ : Type (u + 1)) [Ring Λ] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Dᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :=
  sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
    AlgebraicGeometry.ProEtale.finiteCoefficientModulePresheaf D Λ ⋙
    PresheafOfModules.sheafification α

private theorem realization_restrict_smul
    {D : Type (u + 1)} [Category.{u} D] (J : GrothendieckTopology D)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {Λ₁ Λ₂ : Type (u + 1)} [CommRing Λ₁] [CommRing Λ₂]
    (R S : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Dᵒᵖ).obj (RingCat.of Λ₁) ⟶ R.obj)
    (β : (Functor.const Dᵒᵖ).obj (RingCat.of Λ₂) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    (φ : Λ₁ →+* Λ₂) (δ : R ⟶ S)
    (hs : α ≫ δ.hom = (Functor.const Dᵒᵖ).map (RingCat.ofHom φ) ≫ β) :
    ∀ (M : Sheaf J (ModuleCat.{u + 1} Λ₂)) (U : Dᵒᵖ)
      (r : R.obj.obj U) (x : ((moduleRealization J Λ₂ S β).obj M).val.obj U),
      @SMul.smul _ (((SheafOfModules.restrictScalars.{u + 1} δ).obj
        ((moduleRealization J Λ₂ S β).obj M)).val.obj U) inferInstance r x =
      @SMul.smul _ (((moduleRealization J Λ₁ R α).obj
        ((sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ)).obj M)).val.obj U)
        inferInstance r x := by
  intro M U r x
  let M₁ := (AlgebraicGeometry.ProEtale.finiteCoefficientModulePresheaf D Λ₁).obj
    ((sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ)).obj M).obj
  let M₂ := (AlgebraicGeometry.ProEtale.finiteCoefficientModulePresheaf D Λ₂).obj M.obj
  exact (sheafify_restrict_smul α β ((Functor.const Dᵒᵖ).map (RingCat.ofHom φ)) δ hs
    M₁ M₂ ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj M₁.presheaf)
    ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj M₂.presheaf)
    (toSheafify J _) (toSheafify J _) (𝟙 _) (𝟙 _) (by intro V a y; rfl)
    (by simp only [Category.id_comp]; rfl) U r x).symm

/-- Module realization commutes uniquely with scalar restriction on sections.
Source: Stacks Tags 00YV and 03DA.
Proof: compare scalar actions after lifting a scalar and a section to a common
cover. Separatedness proves linearity of identity. The faithful forgetful functor
reflects invertibility, and equality on sections proves uniqueness.
(blueprint: lem-sf-realization-restriction-linear-lift). -/
private theorem realization_restrict_existsUnique
    {D : Type (u + 1)} [Category.{u} D] (J : GrothendieckTopology D)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {Λ₁ Λ₂ : Type (u + 1)} [CommRing Λ₁] [CommRing Λ₂]
    (R S : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Dᵒᵖ).obj (RingCat.of Λ₁) ⟶ R.obj)
    (β : (Functor.const Dᵒᵖ).obj (RingCat.of Λ₂) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    (φ : Λ₁ →+* Λ₂) (δ : R ⟶ S)
    (hs : α ≫ δ.hom = (Functor.const Dᵒᵖ).map (RingCat.ofHom φ) ≫ β) :
    ∃! e : moduleRealization J Λ₂ S β ⋙ SheafOfModules.restrictScalars.{u + 1} δ ≅
        sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ) ⋙ moduleRealization J Λ₁ R α,
      ∀ (M : Sheaf J (ModuleCat.{u + 1} Λ₂)) (U : Dᵒᵖ)
        (x : ((moduleRealization J Λ₂ S β).obj M).val.obj U),
        (e.hom.app M).val.app U x = x := by
  exact lift_module_iso
    (moduleRealization J Λ₂ S β ⋙ SheafOfModules.restrictScalars.{u + 1} δ)
    (sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ) ⋙ moduleRealization J Λ₁ R α)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro M N f; ext U x; rfl))
    (realization_restrict_smul J R S α β φ δ hs)

