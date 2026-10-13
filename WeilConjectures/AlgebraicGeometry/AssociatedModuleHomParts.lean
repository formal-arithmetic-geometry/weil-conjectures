/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AssociatedModule

@[expose] public section

universe u
open CategoryTheory Opposite TopologicalSpace
open scoped ChangeOfRings
namespace AlgebraicGeometry
variable (X : SheafedSpace CommRingCat.{u})

/-- A morphism out of the tensor presheaf `U ↦ O_X(U) ⊗_R M` is determined by its values on the
global pure tensors `1 ⊗ m`: every `1 ⊗ m` over `U` is the restriction of `1 ⊗ m` over `X`,
so naturality determines the component at `U` on generators
(Stacks, Modules, Lemma 01BH (4); blueprint: associated-module-hom-injective). -/
theorem associatedModulePresheaf_hom_ext
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))))
    {F : PresheafOfModules.{u} (associatedRingSheaf X).obj}
    {h₁ h₂ : associatedModulePresheaf X M ⟶ F}
    (h : ∀ m : M,
      (ModuleCat.ExtendRestrictScalarsAdj.Unit.map
          (associatedRestriction X (op (⊤ : Opens (X : Type u)))).hom ≫
        (ModuleCat.restrictScalars _).map (h₁.app (op ⊤))) m =
      (ModuleCat.ExtendRestrictScalarsAdj.Unit.map
          (associatedRestriction X (op (⊤ : Opens (X : Type u)))).hom ≫
        (ModuleCat.restrictScalars _).map (h₂.app (op ⊤))) m) :
    h₁ = h₂ := by
  ext1 U
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  have hm := (Classical.choose_spec (associatedExtension_restriction_existsUnique X M
    (homOfLE (le_top : U.unop ≤ ⊤)).op)).1 1 m
  rw [map_one] at hm
  rw [← hm]
  erw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, h m]
  rfl

/-- Injectivity part of the associated-module Hom correspondence
 (blueprint: associated-module-hom-injective).
Source: Stacks Project, Modules, Lemma 01BH assertion (4).
Proof: the universal property of sheafification and generation by pure tensors show that a
morphism is determined by its composite with the canonical section map.
-/
theorem associatedModuleHom_injective
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))))
    (G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (X : Type u))
        (forget₂ CommRingCat RingCat)).obj X.sheaf)) :
    Function.Injective
      (fun (φ : associatedModule X M ⟶ G) =>
        associatedModuleCanonicalSection X M ≫
          φ.val.app (op (⊤ : Opens (X : Type u)))) := by
  intro φ ψ hφψ
  have hσ : associatedModuleSheafificationMap X M ≫ ψ.val =
      associatedModuleSheafificationMap X M ≫ φ.val :=
    associatedModulePresheaf_hom_ext X M fun m ↦ (ConcreteCategory.congr_hom hφψ m).symm
  obtain ⟨k, -, hk⟩ := associatedModuleSheafificationMap_universal X M G
    (associatedModuleSheafificationMap X M ≫ φ.val)
  exact (hk φ rfl).trans (hk ψ hσ).symm

/-- Surjectivity part of the associated-module Hom correspondence
 (blueprint: associated-module-hom-surjective).
Source: Stacks Project, Modules, Lemma 01BH assertion (4).
Proof: an R-linear map on global sections induces a presheaf-module map by tensor
universality, and sheafification factors it uniquely through the associated module.
-/
theorem associatedModuleHom_surjective
    (M : ModuleCat (X.presheaf.obj (op (⊤ : Opens (X : Type u)))))
    (G : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (X : Type u))
        (forget₂ CommRingCat RingCat)).obj X.sheaf)) :
    Function.Surjective
      (fun (φ : associatedModule X M ⟶ G) =>
        associatedModuleCanonicalSection X M ≫
          φ.val.app (op (⊤ : Opens (X : Type u)))) := by
  sorry

end AlgebraicGeometry
