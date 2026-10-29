/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-!
# Finite coefficients on the small pro-etale site

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node def-weil-pbc-proetale-modules (blueprint: def-weil-pbc-proetale-modules).

## Main definitions

* `finiteCoefficientRingSheaf`: sheafified continuous functions on connected components.
* `FiniteCoefficientModules`: left modules over this ring sheaf.
* `FiniteCoefficientDerivedCategory` and `FiniteCoefficientDerivedCategoryPlus`: the
  unbounded localization and its strictly full bounded below subcategory.
* `finiteCoefficientEtaleRingSheaf` and `FiniteCoefficientEtaleDerivedCategory`: etale
  coefficients, using the canonical fixed-ring module-sheaf presentation.
* `finiteCoefficientDerivedComparison`: the exact module inverse image on complexes.
* `isBoundedConstructibleFiniteCoefficient`: the essential image of bounded constructible
  etale complexes, with its full subcategory `FiniteCoefficientBoundedConstructibleDerivedCategory`.
-/

@[expose] public section

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- A diagram of left modules is a module presheaf over the constant ring presheaf.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientModulePresheaf (C : Type uC) [Category.{vC} C]
    (Λ : Type (u + 1)) [Ring Λ] :
    (Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ) ⥤
      PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj F :=
    { obj U := F.obj U
      map f := ModuleCat.ofHom (F.map f).hom
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map f :=
    { app U := f.app U
      naturality g := by ext x; exact ConcreteCategory.congr_hom (f.naturality g) x }
  map_id F := by ext U x; rfl
  map_comp f g := by ext U x; rfl

private noncomputable def coefficientModulePresheafFullyFaithful
    (C : Type uC) [Category.{vC} C] (Λ : Type (u + 1)) [Ring Λ] :
    (finiteCoefficientModulePresheaf C Λ).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private theorem coefficientRealization_isEquivalence
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (Λ : Type (u + 1)) [Ring Λ] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    (sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
      finiteCoefficientModulePresheaf C Λ ⋙
      PresheafOfModules.sheafification.{u + 1} α).IsEquivalence := by
  have : (finiteCoefficientModulePresheaf C Λ).Full :=
    (coefficientModulePresheafFullyFaithful C Λ).full
  have : (finiteCoefficientModulePresheaf C Λ).Faithful :=
    (coefficientModulePresheafFullyFaithful C Λ).faithful
  let E := sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
    finiteCoefficientModulePresheaf C Λ
  let S := PresheafOfModules.sheafification.{u + 1} α
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α
  have hunit (F : Sheaf J (ModuleCat.{u + 1} Λ)) :
      IsIso ((PresheafOfModules.sheafificationAdjunction α).unit.app (E.obj F)) := by
    rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
    simp only [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    apply isIso_toSheafify
    exact ((sheafCompose J
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F).property
  let η : E ⟶ (E ⋙ S) ⋙ G :=
    Functor.whiskerLeft E (PresheafOfModules.sheafificationAdjunction α).unit
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hunit
  have : (E ⋙ S).Faithful := Functor.Faithful.of_comp_iso (asIso η).symm
  have : (E ⋙ S).Full := Functor.Full.of_comp_faithful_iso (asIso η).symm
  have : (E ⋙ S).EssSurj := by
    refine ⟨fun M ↦ ?_⟩
    let P := (PresheafOfModules.restrictScalars α).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    let F' : Sheaf J (ModuleCat.{u + 1} Λ) :=
      ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M.isSheaf⟩
    refine ⟨F', ⟨?_⟩⟩
    exact asIso ((PresheafOfModules.sheafificationAdjunction α).counit.app M)
  change (E ⋙ S).IsEquivalence
  exact Functor.IsEquivalence.mk

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

end AlgebraicGeometry.ProEtale
