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
  sorry

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
