/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# The tensor change-of-rings adjunction on sheaves of modules

Source: Stacks Project, Sheaves on Spaces, Lemma 6.20.2, Tag 008A
(blueprint: lem-pc-module-change-of-rings-adjunction).
-/

universe u

open CategoryTheory TopologicalSpace
open scoped ChangeOfRings

namespace SheafOfModules

variable (X : TopCat.{u}) (A B : X.Sheaf CommRingCat.{u}) (α : A ⟶ B)

set_option hygiene false in
local notation "𝓙" => Opens.grothendieckTopology X
set_option hygiene false in
local notation "𝓡" S => (sheafCompose 𝓙 (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓪" => (sheafCompose 𝓙 (forget₂ CommRingCat.{u} RingCat.{u})).map α
set_option hygiene false in
local notation "𝓣" M => changeOfRings.{u, u, u} (J := 𝓙) (R₁ := A) (R₂ := B) α M
set_option hygiene false in
local notation "η" M => CategoryTheory.toSheafify 𝓙
  (changeOfRingsPresheaf.{u, u, u} (J := 𝓙) (R₁ := A) (R₂ := B) α M).presheaf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Change of rings by the sheafified sectionwise tensor product is left adjoint to
restriction of scalars. The hom correspondence first applies the sheafification unit
to `1 ⊗ m`, then evaluates the map. Its naturality in both modules is part of `adj`.
Source: Stacks Project, Tag 008A (blueprint: lem-pc-module-change-of-rings-adjunction).

Proof: (1) Apply the sectionwise tensor adjunction and compatibility with restrictions
(`lem-pc-presheaf-change-of-rings-adjunction`, Tag 006R) to obtain the natural presheaf
hom bijection. The right-hand homs are sheaf homs since both modules are sheaves
(`def-weil-sheaf-of-modules-category`). (2) Apply the sheafification universal property
(`def-weil-presheaf-modules-sheafification`, Tag 0089) to the presheaf of tensors
(`def-pur-sheaf-tensor-product`). Since the target is a sheaf, precomposition with the
sheafification unit is a bijection. (3) Compose these natural bijections. They send `u`
to `m ↦ u(η(1 ⊗ m))`. Naturality defines the change-of-rings functor on morphisms and
supplies the adjunction; its objects are the already defined `changeOfRings α M`.
The equality `h` only transports between this functor's objects and those tensors. -/
theorem exists_changeOfRingsAdjunction :
    ∃ (E : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
      (h : ∀ M : SheafOfModules.{u} (𝓡 A), E.obj M = 𝓣 M)
      (adj : E ⊣ restrictScalars 𝓪),
      ∀ (M : SheafOfModules.{u} (𝓡 A)) (N : SheafOfModules.{u} (𝓡 B))
        (f : (𝓣 M) ⟶ N) (U : (Opens X)ᵒᵖ) (m : M.val.obj U),
        ((adj.homEquiv M N) (eqToHom (h M) ≫ f)).val.app U m =
          f.val.app U ((η M).app U
            ((1 : B.presheaf.obj U) ⊗ₜ[A.presheaf.obj U, (α.hom.app U).hom] m)) := by
  sorry

end SheafOfModules
