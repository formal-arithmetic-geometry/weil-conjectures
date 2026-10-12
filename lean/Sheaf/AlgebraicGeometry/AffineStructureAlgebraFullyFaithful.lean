/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Full faithfulness of the affine structure-algebra functor

Source: Stacks Project, Morphisms, Lemma 01SA, with the local argument in steps 5--6 of
lem-weil-pbc-affine-morphism-relative-spec
(blueprint: lem-weil-pbc-affine-structure-algebra-fully-faithful).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option hygiene false in
local notation "𝒪⁎" f:max => Under.mk (⟨(f).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (f).base).obj (Scheme.sheaf _))

/-- The canonical contravariant structure-algebra functor is full and faithful.
Source: Stacks Project, Morphisms, Lemma 01SA; Constructions, Lemmas 01LT and 01LY
(blueprint: lem-weil-pbc-affine-structure-algebra-fully-faithful).

Proof: On an affine open U of S, both inverse images are affine. The Gamma--Spec
adjunction identifies morphisms between them with ring maps on sections. The condition
of being over U is exactly compatibility with the structure maps from O_S(U).
If two S-morphisms have the same image under F, hmap gives equality of their section
maps over every affine U, hence equality of their restrictions by the adjunction.
These inverse images cover the source, so scheme-morphism gluing gives equality globally.
For fullness, an algebra morphism gives on every affine U the unique U-morphism
corresponding to its section map. Naturality of the algebra morphism and uniqueness for
maps into affine schemes give compatibility over inclusions of affine opens. For two
arbitrary affine opens, cover their intersection by smaller affine opens and apply the
same uniqueness there. Scheme-morphism gluing now gives a global S-morphism. Its image
under F has the prescribed components on all affine opens by hmap; sheaf-morphism
uniqueness on an affine basis gives equality with the original algebra morphism.
This argument also covers the empty scheme, whose empty open cover detects equality. -/
theorem affine_structure_algebra_full_faithful (S : Scheme.{u})
    (F : (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ⥤
      ObjectProperty.FullSubcategory
        (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent))
    (hobj : ∀ Y, (F.obj (op Y)).obj = 𝒪⁎ Y.obj.hom)
    (hmap : ∀ (Y Y') (h : Y ⟶ Y') (V : S.Opens),
      (F.map h.op).hom.right.hom.app (op V) =
        eqToHom (by rw [hobj Y']; rfl) ≫
          h.hom.left.appLE (Y'.obj.hom ⁻¹ᵁ V) (Y.obj.hom ⁻¹ᵁ V)
            (by rw [← Over.w h.hom, Scheme.Hom.comp_preimage]) ≫
          eqToHom (by rw [hobj Y]; rfl)) :
    F.Full ∧ F.Faithful := by sorry

end AlgebraicGeometry
