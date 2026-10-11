/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Tensor-Hom adjunction on a ringed space

Source: Stacks Project, Modules, Lemma 01CN, the morphism correspondence
(blueprint: lem-weil-pbc-module-tensor-hom-adjunction).
-/

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

namespace SheafOfModules

set_option autoImplicit false

/-- Tensor-Hom correspondence, linear over global sections, characterized on local pure
tensors and natural in the first factor. The tensor product `A ⊗ G` is the source's
`SheafOfModules.monoidalCategory R` [def-pur-sheaf-tensor-product]; `t_W` is the
sheafification unit followed by `SheafOfModules.tensorObjIsoSheafification`.
Source: Stacks Project, Modules, Lemma 01CN
(blueprint: lem-weil-pbc-module-tensor-hom-adjunction).

Proof: (1) On opens, internal Hom consists of module maps on the slice; restriction
restricts these maps, and scalars act sectionwise [def-pur-sheaf-hom].
(2) Apply Algebra 00DE [lem-weil-pbc-module-tensor-hom-currying] on every open to the
bilinear map `(a,g) ↦ (φ_W(a))_W(g)`, obtaining a linear map from the section tensor product.
(3) These maps commute with restrictions: check on pure tensors using naturality of `φ`
and of the local maps it gives. Pure tensors generate, so they define a presheaf morphism
[def-pur-sheaf-tensor-product, def-weil-presheaf-modules-sheafification].
(4) Conversely, a presheaf tensor morphism `ψ` gives at `a ∈ A(W)` the local map with
component on `W' ⊆ W` given by `g ↦ ψ_W'(a|_W' ⊗ g)`. Naturality of `ψ` makes this a local
module morphism; linearity and restriction compatibility give a map into internal Hom.
(5) The constructions are inverse by evaluation on local sections and generation by pure
 tensors [lem-weil-pbc-module-tensor-hom-currying, def-pur-sheaf-hom].
(6) The universal property of module sheafification transports the presheaf morphism to
 a unique sheaf morphism with the displayed evaluation formula
[def-weil-presheaf-modules-sheafification, def-pur-sheaf-tensor-product].
(7) Sectionwise evaluation commutes with addition and multiplication by a global section;
 uniqueness makes the correspondence linear [def-pur-sheaf-modules-hom-module].
(8) Precomposing by `α` gives the same evaluation formula as precomposing the tensor
 morphism by the sheafification of `α ⊗ id`; uniqueness gives naturality.
-/
theorem exists_tensorHom_linearEquiv (X : Type u) [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (G F : SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) :
    letI := monoidalCategory R
    letI : ∀ M N : SheafOfModules.{u}
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R),
        Module (RingCat.sectionsSubring
          ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).obj) (M ⟶ N) :=
      homModule R.obj ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).property
    ∃ e : ∀ A : SheafOfModules.{u}
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R),
        (A ⟶ homObj (R := R) G F) ≃ₗ[RingCat.sectionsSubring
          ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).obj] (A ⊗ G ⟶ F),
      (∀ (A : SheafOfModules.{u}
          ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))
          (φ : A ⟶ homObj (R := R) G F),
        (∀ (W : Opens X) (a : A.val.obj (op W)) (g : G.val.obj (op W)),
          (e A φ).val.app (op W)
              ((tensorObjIsoSheafification A G).inv.val.app (op W)
                (((PresheafOfModules.sheafificationAdjunction.{u}
                  (𝟙 ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).obj)).unit.app
                  (A.val ⊗ G.val)).app (op W) (a ⊗ₜ[R.obj.obj (op W)] g))) =
            (φ.val.app (op W) a).app (op (Over.mk (𝟙 W))) g) ∧
        ∀ ψ : A ⊗ G ⟶ F,
          (∀ (W : Opens X) (a : A.val.obj (op W)) (g : G.val.obj (op W)),
            ψ.val.app (op W)
                ((tensorObjIsoSheafification A G).inv.val.app (op W)
                  (((PresheafOfModules.sheafificationAdjunction.{u}
                  (𝟙 ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).obj)).unit.app
                    (A.val ⊗ G.val)).app (op W) (a ⊗ₜ[R.obj.obj (op W)] g))) =
              (φ.val.app (op W) a).app (op (Over.mk (𝟙 W))) g) → ψ = e A φ) ∧
      (∀ (A A' : SheafOfModules.{u}
          ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))
          (α : A' ⟶ A) (φ : A ⟶ homObj (R := R) G F),
        e A' (α ≫ φ) = (α ⊗ₘ 𝟙 G) ≫ e A φ) := by
  sorry

end SheafOfModules
