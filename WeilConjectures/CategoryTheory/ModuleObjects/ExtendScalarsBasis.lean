/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapBiproduct
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Bases of extensions of commutative algebra objects

Let `φ : R ⟶ S` be a morphism of commutative algebra objects and `s : Fin d → Γ S` global sections
of `S` which form a basis of `S` over `R`, in the sense that the `R`-linear map `Rᵈ ⟶ φ^* S`,
`(rᵢ) ↦ ∑ φ(rᵢ) sᵢ`, is an isomorphism. Then for every `R`-module `M` the maps
`M ⟶ φ^* (S ⊗_R M)`, `m ↦ sᵢ ⊗ m` (the unit of extension and restriction of scalars followed by
the action of `sᵢ`) exhibit `φ^* (S ⊗_R M)` as `Mᵈ`
(`CategoryTheory.Mod.isIso_biproductDesc_unit_smulEnd`): by the projection formula
`φ^* (S ⊗_R M) ≅ φ^* S ⊗_R M` they become the maps `M ≅ R ⊗_R M ⟶ φ^* S ⊗_R M` induced by
`r ↦ φ(r) sᵢ`.

The action of a global section on a tensor product `M ⊗_S N` is its action on `M`
(`CategoryTheory.Mod.globalSmul_tensorObj`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

section Tensor

variable {S : C} [MonObj S] [IsCommMonObj S] (s : Γ S)

/-- The action of a global section `s` on a relative tensor product `M ⊗_S N` is the action of
`s` on `M`, tensored with `N`. -/
lemma globalSmul_tensorObj (M N : Mod C S) :
    globalSmul s.hom (M ⊗ N) = (smulEnd s M ▷ N).hom := by
  rw [← cancel_epi (tensorObjπ M N), tensorObjπ_whiskerRight, smulEnd_hom, globalSmul, globalSmul,
    leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, whiskerLeft_tensorπ_smul]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_left_assoc]
  monoidal

/-- The action of a global section `s` commutes with the left unitor: on `𝟙 ⊗_S N` it is the
action of `s` on the unit, tensored with `N`. -/
@[reassoc]
lemma smulEnd_comp_leftUnitor_inv (N : Mod C S) :
    smulEnd s N ≫ (λ_ N).inv = (λ_ N).inv ≫ smulEnd s (𝟙_ (Mod C S)) ▷ N := by
  refine Mod.hom_ext _ _ ?_
  rw [comp_hom', comp_hom', ← globalSmul_tensorObj, smulEnd_hom]
  exact globalSmul_naturality s.hom (λ_ N).inv

end Tensor

variable {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S)
  [IsMonHom φ]

/-- Under the projection formula `φ^* (S ⊗_R M) ≅ φ^* S ⊗_R M`, the unit `M ⟶ φ^* (S ⊗_R M)`
followed by the action of a global section `s` of `S` is the map `M ≅ R ⊗_R M ⟶ φ^* S ⊗_R M`
induced by `r ↦ φ(r) s`. -/
lemma unit_comp_map_smulEnd_comp_extendScalarsCompComapIso_hom (s : Γ S) (M : Mod C R) :
    (extendRestrictAdjunction φ).unit.app M ≫
        (comap φ).map (smulEnd s ((extendScalars φ).obj M)) ≫
          (extendScalarsCompComapIso φ).hom.app M =
      (λ_ M).inv ≫ (comapUnitHom φ ≫ (comap φ).map (smulEnd s (𝟙_ (Mod C S)))) ▷ M := by
  let := comapLaxMonoidal φ
  have he : (extendScalarsCompComapIso φ).hom.app M =
      (comap φ).map (λ_ ((extendScalars φ).obj M)).inv ≫
        (projectionIso φ (𝟙_ (Mod C S)) M).inv := rfl
  rw [he, ← Functor.map_comp_assoc, smulEnd_comp_leftUnitor_inv,
    ← cancel_mono (projectionIso φ (𝟙_ (Mod C S)) M).hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, projectionIso_hom, projectionHom,
    extendRestrictAdjunction_unit_app, Functor.map_comp,
    ← Functor.LaxMonoidal.left_unitality_inv_assoc, ← Functor.LaxMonoidal.μ_natural_left,
    comp_whiskerRight]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
  exact leftUnitor_inv_naturality_assoc _ _

variable [Abelian C] [MonoidalPreadditive C]

/-- **Extension of scalars along a finite free morphism with a basis of global sections.** Let
`s : Fin d → Γ S` be global sections of `S` such that the map `Rᵈ ⟶ S`,
`(rᵢ) ↦ ∑ φ(rᵢ) sᵢ`, is an isomorphism. Then for every `R`-module `M`, the maps
`M ⟶ φ^* (S ⊗_R M)`, `m ↦ sᵢ ⊗ m`, given by the unit followed by the action of `sᵢ`, exhibit
`φ^* (S ⊗_R M)` as the direct sum of `d` copies of `M`. -/
theorem isIso_biproductDesc_unit_smulEnd [HasFiniteBiproducts C] {d : ℕ} (s : Fin d → Γ S)
    (hs : IsIso (biproduct.desc fun i : Fin d ↦ φ ≫ globalSmul (s i).hom (regular S)))
    (M : Mod C R) :
    IsIso (biproduct.desc fun i : Fin d ↦ (extendRestrictAdjunction φ).unit.app M ≫
      (comap φ).map (smulEnd (s i) ((extendScalars φ).obj M))) := by
  replace hs : IsIso (biproduct.desc fun i : Fin d ↦
      comapUnitHom φ ≫ (comap φ).map (smulEnd (s i) (𝟙_ (Mod C S)))) := by
    rw [← isIso_iff_of_reflects_iso _ (forget R), Functor.isIso_map_biproduct_desc_iff]
    exact hs
  have h : (biproduct.desc fun i : Fin d ↦ (extendRestrictAdjunction φ).unit.app M ≫
        (comap φ).map (smulEnd (s i) ((extendScalars φ).obj M))) ≫
        (extendScalarsCompComapIso φ).hom.app M =
      (biproduct.mapIso fun _ ↦ (λ_ M).symm).hom ≫
        (rightDistributor (fun _ : Fin d ↦ 𝟙_ (Mod C R)) M).inv ≫
          (biproduct.desc fun i : Fin d ↦
            comapUnitHom φ ≫ (comap φ).map (smulEnd (s i) (𝟙_ (Mod C S)))) ▷ M := by
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    rw [biproduct.ι_desc_assoc, Category.assoc,
      unit_comp_map_smulEnd_comp_extendScalarsCompComapIso_hom, biproduct.mapIso_hom,
      biproduct.ι_map_assoc, Iso.symm_hom,
      biproduct_ι_comp_rightDistributor_inv_assoc, ← comp_whiskerRight, biproduct.ι_desc]
  rw [← isIso_comp_right_iff _ ((extendScalarsCompComapIso φ).hom.app M), h]
  infer_instance

end CategoryTheory.Mod
